open! IStd
open Graph
open PulseBasicInterface
open PulseDomainInterface

module L = Logging
module CFG = ProcCfg.Normal


(** {1. Core Data Structures & State Management} *)

(** The core data type representing a potential transformation. This is the output of the planning phase. *)
type reuse_candidate = {
    reused_pvar: Pvar.t; (* The variable to reuse, e.g., 'q' *)
  }

type skip_metrics =
  { total_aliases: int  (** Total number of aliased pointers found for the bug. *)
  ; true_slice_size: int  (** Total number of unguarded dereferences (crash sites). *)
  ; initial_candidate_plans: int  (** Number of guards before filtering and merging. *)
  ; final_guard_count: int  (** Number of guards after compaction (Cost_G for the whole patch). *)
  ; imprecision_cost: int  (** Nodes guarded besides the slice nodes (Cost_L for this specific plan). *)
  ; nodes_in_scope: int  (** Total nodes in this plan's scope. *) }

type replace_metrics =
  { cost: int  (** Modification Cost (Cost_Rep). *)
  ; total_aliases: int  (** Total number of aliased pointers found for the bug. *) }

type intermediate_plan =
| ISkip of
    { lca_node: Procdesc.Node.t
    ; join_node: Procdesc.Node.t
    ; pointer_exprs: Exp.t list
    ; slice_nodes: Procdesc.Node.t list }
| IEvade of {proc_start_node: Procdesc.Node.t; pointer_expr: Exp.t}

type transformation_plan =
| Skip of { 
    lca_node : Procdesc.Node.t;
    join_node : Procdesc.Node.t;
    pointer_exprs : Exp.t list;
    slice_nodes : Procdesc.Node.t list;
    metrics: skip_metrics }
| Evade of {
    proc_start_node: Procdesc.Node.t;
    pointer_expr: Exp.t;
  }
| Replace of {
    def_site_node: Procdesc.Node.t;
    pvar: Pvar.t;
    pvar_typ: Typ.t;
    reuse_info: reuse_candidate option;
    all_aliases: Exp.t list;
    metrics: replace_metrics }
| NoPlanGenerated of {
    reason: string;
    npe_location: Location.t;
    pointer_expr_str: string
  }


(** A simple cache to avoid reporting the same transformation plan multiple times for a single procedure. *)
let logged_transformations_cache : transformation_plan list ref = ref []
let last_proc_name = ref (Procname.from_string_c_fun "")

(* This function clears the cache when we start a new procedure - used for LOGGING*)
let clear_cache_if_new_proc (current_proc_name : Procname.t) =
  if not (Procname.equal !last_proc_name current_proc_name) then (
    L.d_printfln "[transformation] New procedure %a, clearing transformation cache." Procname.pp current_proc_name;
    (* Just reset the list to empty *)
    logged_transformations_cache := [];
    last_proc_name := current_proc_name
  )

(* This function clears the cache when we start a new procedure - used for FILE-SAVING*)  
let clear_cache_for_proc () =
  logged_transformations_cache := []
(** A record containing all necessary information about a given bug report from Pulse. *)
type 'payload bug_info = {
  ptr_expr   : Exp.t;
  ptr_var    : Var.t option;
  diag_trace : Trace.t;
  err_node   : Procdesc.Node.t;
  astate     : AbductiveDomain.t;
  analysis: ('payload) InterproceduralAnalysis.t;
  av_opt: AbstractValue.t option;
}


(** {2. Low-Level & CFG Utilities} *)

(** A collection of modules to compute dominators and post-dominators on the Infer CFG.
    This is boilerplate required to interface with the Ocamlgraph library. *)

(* Use ocamlgraph's dominators functor to get the dominators *)
module GDoms = Dominator.Make (ProcCfg.MakeOcamlGraph (CFG))
module NodeSet = Stdlib.Set.Make(struct
  type t = Procdesc.Node.t
  let compare = Procdesc.Node.compare
end)

module PostDominators = struct
  module ReversedCFG = ProcCfg.Backward (ProcCfg.Exceptional)
  module ReversedOcamlGraph = ProcCfg.MakeOcamlGraph (ReversedCFG)

  (*
    Build the final adapter for the Dominators functor.
    We define the graph type `t` to be the
    actual tuple type from the exceptional graph.
  *)
  module DominatorGraph :
    Dominator.G with type t = ReversedOcamlGraph.t and type V.t = Procdesc.Node.t = struct
    type t = ReversedOcamlGraph.t
    module V = ReversedOcamlGraph.V

    let pred = ReversedOcamlGraph.pred
    let succ = ReversedOcamlGraph.succ

    let get_all_nodes pdesc =
      let start_node = Procdesc.get_start_node pdesc in
      let exit_node = Procdesc.get_exit_node pdesc in
      let all_nodes = Procdesc.get_nodes pdesc in
      let complete_nodes = start_node :: exit_node :: all_nodes in
      List.dedup_and_sort ~compare:Procdesc.Node.compare complete_nodes

    let fold_vertex f g acc =
      let pdesc, _ = g in
      List.fold (get_all_nodes pdesc) ~init:acc ~f:(fun acc' node -> f node acc')

    let iter_vertex f g =
      let pdesc, _ = g in
      List.iter (get_all_nodes pdesc) ~f

    let nb_vertex g =
      let pdesc, _ = g in
      List.length (get_all_nodes pdesc)

    let iter_succ f g v = ReversedOcamlGraph.iter_succ f g v
  end

  module D = Dominator.Make (DominatorGraph)
  let compute_idom = D.compute_idom
end

(** Computes the Lowest Common Post-Dominator (LCPD) of two nodes. *)
let lcpd ipdom_fun x y =
  let safe_get_parent node =
    try Some (ipdom_fun node)
    (*
      Catch the wildcard exception '_'. This will catch ANY exception that
      occurs during the call to `ipdom_fun`, including raw exceptions from
      C++ bindings or other unexpected OCaml exceptions.
    *)
    with _ -> None
  in

  let rec collect_ancestors n acc =
    let acc' = Procdesc.NodeSet.add n acc in
    match safe_get_parent n with
    | Some parent when not (Procdesc.Node.equal n parent) ->
        collect_ancestors parent acc'
    | _ ->
        acc'
  in
  let anc_x = collect_ancestors x Procdesc.NodeSet.empty in
  let rec climb m =
    if Procdesc.NodeSet.mem m anc_x then m
    else match safe_get_parent m with Some parent -> climb parent | None -> m
  in
  climb y

(* Checks if `node` is dominated by `dominator`. *)
let is_dominated_by ~dominator ~node idom=
  let rec climb current =
    if Procdesc.Node.equal current dominator then true
    else
      (*
        We wrap the call to `idom` in a try-with block. If the node `current`
        is not in the dominator tree (e.g., it's in dead code).
      *)
      let parent_opt = try Some (idom current) with _ -> None in
      match parent_opt with
      | Some parent when not (Procdesc.Node.equal parent current) ->
          climb parent
      | _ ->
          (* No parent found, or it's the root. The climb is over. *)
          false
  in
  climb node

(** Checks if [pdominator] post-dominates [node] in the CFG. *)
let is_post_dominated_by ~pdominator ~node ipdom_fun =
  let ipdom_fun = Lazy.force ipdom_fun in
  let rec climb current =
    if Procdesc.Node.equal current pdominator then true
    else
      let parent = try ipdom_fun current with _ -> current in
      if Procdesc.Node.equal parent current then false else climb parent
  in
  climb node


(** Normalizes a scope tuple (start, end) to ensure the start node always dominates the end node. *)
let normalize_scope (node1, node2) idom =
  if is_dominated_by ~dominator:node1 ~node:node2 idom then (node1, node2) else (node2, node1)

(** Given a single crash site, finds the minimal enclosing syntactic scope (e.g., the `if` block or `for` loop body).
    This is a critical heuristic. The raw LCA of a single node is itself, but to create a valid guard,
    we need to find the boundaries of the construct it belongs to. This function walks the CFG and
    post-dominator tree to find the appropriate start and end nodes for a guard. *)
let find_minimal_scope (slice : Procdesc.Node.t list) ipdom_fun proc_desc lca idom =
  let slice_locs = List.map slice ~f:(fun n -> (Procdesc.Node.get_loc n).line) in
  L.d_printfln "[transformation-scope] >> find_minimal_scope for slice with %d node(s) at C lines: [%a]"
    (List.length slice) (Pp.seq ~sep:", " Int.pp) slice_locs;

  let lca_of_slice, lcpd_of_slice =
    match slice with
    | [] ->
        L.d_printfln "[transformation-scope]    - Case: Empty slice. Returning procedure boundaries.";
        (Procdesc.get_start_node proc_desc, Procdesc.get_exit_node proc_desc)
    | first :: rest ->
        L.d_printfln "[transformation-scope]    - Case: Non-empty slice. Calculating overall LCA and LCPD.";
        let lca_val = List.fold rest ~init:first ~f:lca in
        let lcpd_fun = lcpd (Lazy.force ipdom_fun) in
        let lcpd_val = List.fold rest ~init:first ~f:lcpd_fun in
        (lca_val, lcpd_val)
  in

  (* Adjust LCA to handle Prune nodes. *)
  let start_node =
    match Procdesc.Node.get_kind lca_of_slice with
    | Prune_node _ ->
        (match Procdesc.Node.get_succs lca_of_slice with
        | [then_branch_start]
          when List.for_all slice ~f:(fun slice_node ->
                    is_dominated_by ~dominator:then_branch_start ~node:slice_node idom) ->
            L.d_printfln "[transformation-scope]    - Adjusting start node from Prune node.";
            then_branch_start
        | _ -> lca_of_slice)
    | _ -> lca_of_slice
  in

  (* ADJUST LCPD: We want the end of the syntactic block. *)
  let end_node =
    (* Find the first node that is a post-dominator of the calculated LCPD.
        This will find the exit node of the enclosing block. *)

    (*COULD BE A POTENTIAL PROBLEM*) 
    let find_end_node current_node =
      let succs = Procdesc.Node.get_succs current_node in
      match succs with
      | [] -> current_node
      | [next_node] ->
          (* If the LCPD is a Prune node, we need to adjust it to the successor that post-dominates the slice. *)
          (match Procdesc.Node.get_kind current_node with
          | Prune_node _ ->
              let is_post_dom_of_slice n = List.for_all slice ~f:(fun sn -> is_post_dominated_by ~pdominator:n ~node:sn ipdom_fun) in
              if is_post_dom_of_slice next_node then
                next_node
              else
                current_node
          | _ -> current_node)
      | _ -> current_node
    in
    find_end_node lcpd_of_slice
  in

  L.d_printfln "[transformation-scope] << Returning final scope: start node %a (line %d), end node %a (line %d)"
    Procdesc.Node.pp start_node (Procdesc.Node.get_loc start_node).line
    Procdesc.Node.pp end_node (Procdesc.Node.get_loc end_node).line;

  (start_node, end_node)

(** Counts the total number of CFG nodes within a given control-flow scope. *)
let count_nodes_in_scope ~proc_desc ~idom ~ipdom_fun ~start_node ~end_node =
  (* let ipdom = Lazy.force ipdom_fun in *)
  let is_inside_scope node =
    is_dominated_by ~dominator:start_node ~node idom
    && is_post_dominated_by ~pdominator:end_node ~node ipdom_fun
  in
  let all_nodes = Procdesc.get_nodes proc_desc in
  List.fold all_nodes ~init:0 ~f:(fun acc node ->
      (* Change: Instead of counting instructions, just count the node itself. *)
      if is_inside_scope node then acc + 1 else acc )

(** {3. Alias & State Analysis} *)

(** Given a pointer's abstract value, finds all stack variables that are aliases.
    This is a "semantic" alias analysis, as it queries Pulse's internal model directly.
    It works by canonicalizing the abstract value of the pointer and then iterating
    through the stack to find all other variables that map to the same canonical value. *)

(** Stack aliases: normalize each local’s addr before comparing to [rep]. *)
let collect_stack_aliases
    (astate: AbductiveDomain.t)
    (rep_raw: AbstractValue.t)
  : (Var.t * Exp.t) list =
  (* Step 1. Canonicalize the abstract value of the pointer we are looking for. *)
  let canonical_rep_to_match =
    let canon_v = AbductiveDomain.CanonValue.canon' astate rep_raw in
    AbductiveDomain.CanonValue.downcast canon_v
  in
  (* Step 2. Fold over the ENTIRE abstract stack. *)
  AbductiveDomain.Stack.fold
    (fun stack_var value_origin acc ->

      let stack_av, _ = ValueOrigin.addr_hist value_origin in
      (* Step 3. For each variable on the stack, get its canonical representative. *)
      let current_var_canonical_rep =
        let canon_v = AbductiveDomain.CanonValue.canon' astate stack_av in
        AbductiveDomain.CanonValue.downcast canon_v
      in
      (* Step 4. If they match, we have found an alias. *)
      if PulseBasicInterface.AbstractValue.equal canonical_rep_to_match current_var_canonical_rep
      then (

        match Var.get_pvar stack_var with
        | Some pvar ->
            (stack_var, Exp.Lvar pvar) :: acc
        | None ->
            acc )
      else acc )
    astate []

(** Given a set of "seed" pointers, finds all variables that are aliased through simple
    assignments (e.g., `p = q`). This is a "syntactic" alias analysis that builds a graph
    of assignments and finds the transitive closure. It complements the semantic analysis. *)
let find_syntactic_aliases proc_desc (initial_ptrs : Exp.t list) : Exp.t list =
  (* Step 1: Build a map from temporary identifiers to the program variables they were loaded from. *)
  let ident_map =
    Procdesc.fold_instrs proc_desc ~init:Ident.Map.empty ~f:(fun map _node instr ->
        match instr with
        | Sil.Load {id; e= Exp.Lvar pvar; _} ->
            Ident.Map.add id pvar map
        | _ ->
            map )
  in
  (*
    Step 2: Build a graph of alias relationships, correctly handling both
    direct assignments (pvar1 = pvar2) and assignments through a temp (pvar1 = temp).
  *)
  let alias_graph =
    Procdesc.fold_instrs proc_desc ~init:Pvar.Map.empty ~f:(fun graph _node instr ->
        let add_edge p1 p2 g =
          let s1 = Pvar.Map.find_opt p1 g |> Option.value ~default:Pvar.Set.empty in
          let s2 = Pvar.Map.find_opt p2 g |> Option.value ~default:Pvar.Set.empty in
          g |> Pvar.Map.add p1 (Pvar.Set.add p2 s1) |> Pvar.Map.add p2 (Pvar.Set.add p1 s2)
        in
        match instr with
        | Sil.Store {e1= Exp.Lvar pvar_dest; e2= Exp.Lvar pvar_src; _} ->
            add_edge pvar_dest pvar_src graph
        | Sil.Store {e1= Exp.Lvar pvar_dest; e2= Exp.Var ident; _} -> (
          match Ident.Map.find_opt ident ident_map with
          | Some pvar_src ->
              add_edge pvar_dest pvar_src graph
          | None ->
              graph )
        | _ ->
            graph )
  in
  (* Step 3: Find the transitive closure (all connected aliases) for the initial pointers. *)
  let initial_pvars =
    List.filter_map initial_ptrs ~f:(function Exp.Lvar pvar -> Some pvar | _ -> None)
  in
  let rec find_all_connected worklist seen =
    match worklist with
    | [] ->
        seen
    | pvar :: rest ->
        let neighbors =
          Pvar.Map.find_opt pvar alias_graph |> Option.value ~default:Pvar.Set.empty
        in
        let new_worklist =
          Pvar.Set.fold
            (fun neighbor acc -> if Pvar.Set.mem neighbor seen then acc else neighbor :: acc)
            neighbors []
        in
        find_all_connected (List.rev_append new_worklist rest) (Pvar.Set.add pvar seen)
  in
  let all_aliased_pvars = find_all_connected initial_pvars Pvar.Set.empty in
  Pvar.Set.elements all_aliased_pvars |> List.map ~f:(fun pvar -> Exp.Lvar pvar) 


(** {4. transformation Strategy Planners} *)

(** {4a. The REPLACE Strategy Planner} *)

(** Checks if a pointer and all its aliases are "local" to the current function.
    A pointer is considered non-local if it's a global, a return value, or is passed as an
    argument to another function. This is a conservative (sound but incomplete) heuristic.
    It trades off a few missed opportunities for `REPLACE` transformations for speed and safety,
    as proving non-escape with 100% precision is a hard problem. *)
let is_local ~proc_desc ~(bug : 'payload bug_info) (all_aliases: Exp.t list) =
  let ptr_exp_str = Format.asprintf "%a" Exp.pp bug.ptr_expr in
  L.d_printfln "[transformation-debug] is_local: Checking alias set starting with %s" ptr_exp_str;

  let var_is_local =
    match bug.ptr_var with
    | None -> false
    | Some v ->
        let is_not_captured = not (Procdesc.is_captured_var proc_desc v) in
        let is_not_global = not (Var.is_global v) in
        let is_not_return = not (Var.is_return v) in
        is_not_captured && is_not_global && is_not_return
  in

  if not var_is_local then (
    L.d_printfln "[transformation-debug] is_local: Variable properties failed.";
    false )
  else

    let has_call_usage =
      Procdesc.fold_nodes proc_desc ~init:false ~f:(fun acc node ->
          if acc then true (* Early exit *)
          else
            let instrs = Procdesc.Node.get_instrs node in

            (* Step 1. In this node, find all temp IDs that are loaded with one of the aliased pointers. *)
            let idents_holding_aliases =
              Instrs.fold instrs ~init:Ident.Map.empty ~f:(fun map instr ->
                  match instr with
                  | Sil.Load {id; e= Exp.Lvar pvar; _} ->
                      if List.exists all_aliases ~f:(fun alias_exp -> Exp.equal (Exp.Lvar pvar) alias_exp) then
                        Ident.Map.add id (Exp.Lvar pvar) map
                      else map
                  | _ -> map )
            in
            if Ident.Map.is_empty idents_holding_aliases then false
            else
              (* Step 2. Now check if any of those IDs are used in a call instruction in this same node. *)
              Instrs.exists instrs ~f:(fun instr ->
                  match instr with
                  | Sil.Call (_, _, args, _, _) ->
                      List.exists args ~f:(fun (arg_exp, _) ->
                          match arg_exp with
                          | Exp.Var id -> Ident.Map.mem id idents_holding_aliases
                          | _ -> false )
                  | _ -> false ) )
    in
    L.d_printfln "[transformation-debug] is_local: has_call_usage=%b" has_call_usage;
    not has_call_usage


(** For a given pointer, finds the last definition site (a `Store` instruction) that
    dominates the crash site. This is the correct and most minimal location to apply a `REPLACE` transformation. *)
 
(*Helper for find_last_def_site*)    
let compute_dereference_slice pdesc ptr_exp =
  let deref_nodes = ref Procdesc.NodeSet.empty in
  Procdesc.iter_nodes
    (fun node ->
      let instrs = Procdesc.Node.get_instrs node in
      (* Step 1. ormatind all temporary variables (idents) that are loaded with the value of the pointer *)
      let idents_holding_pointer_value =
        Instrs.fold instrs ~init:Ident.Set.empty ~f:(fun acc instr ->
            match instr with
            | Sil.Load {id; e; _} when Exp.equal e ptr_exp ->
                Ident.Set.add id acc
            | _ ->
                acc )
      in
      (*Step 2. If we found any such temps, check if they are used as an address in a later instruction in THIS SAME NODE. *)
      if not (Ident.Set.is_empty idents_holding_pointer_value) then
        Instrs.iter instrs ~f:(fun instr ->
            let address_exp_opt =
              match instr with
              | Sil.Load {e; _} ->
                  Some e
              | Sil.Store {e1; _} ->
                  Some e1
              | _ ->
                  None
            in
            match address_exp_opt with
            | Some (Exp.Var id) when Ident.Set.mem id idents_holding_pointer_value ->
                (* This is a dereference. The address is a temp that holds the pointer's value. *)
                deref_nodes := Procdesc.NodeSet.add node !deref_nodes
            | _ ->
                () ) )
    pdesc ;
  Procdesc.NodeSet.elements !deref_nodes |> List.sort ~compare:Procdesc.Node.compare

let find_last_def_site ~proc_desc ~ptr_var =
  let ptr_pvar_str = Pvar.to_string ptr_var in
  L.d_printfln "[transformation-debug] find_last_def_site: Searching for definition of %s" ptr_pvar_str;

  (* Step 1. Find the actual node where the dereference happens to use as the anchor. *)
  let crashing_node_opt =
    compute_dereference_slice proc_desc (Exp.Lvar ptr_var) |> List.hd
  in
  match crashing_node_opt with
  | None ->
      L.d_printfln "[transformation-debug] find_last_def_site: Could not find the crashing node!";
      None
  | Some crashing_node ->
      L.d_printfln "[transformation-debug] find_last_def_site: Found crashing node %a" Procdesc.Node.pp
        crashing_node;
      
      (* Step 2. Build the dominator tree to check for correct ordering. *)
      let idom = GDoms.compute_idom proc_desc (Procdesc.get_start_node proc_desc) in
      let dominates def_node use_node =
        let rec is_dominated_by_rec current_node =
          if Procdesc.Node.equal current_node def_node then true
          else
            let dominator = idom current_node in
            if Procdesc.Node.equal dominator current_node then false (* Reached root of dominator tree *)
            else is_dominated_by_rec dominator
        in
        is_dominated_by_rec use_node
      in
      
      (* Step 3. Find all nodes that contain a definition of the variable. *)
      let is_def_instr instr =
        match (instr : Sil.instr) with
        | Store {e1=Exp.Lvar pvar; _} when Pvar.equal pvar ptr_var -> true
        | _ -> false
      in
      let all_def_nodes =
        Procdesc.fold_nodes proc_desc ~init:[] ~f:(fun acc node ->
            if Instrs.exists (Procdesc.Node.get_instrs node) ~f:is_def_instr then node :: acc
            else acc )
      in
      L.d_printfln "[transformation-debug] find_last_def_site: Found %d total definition nodes: [%a]"
        (List.length all_def_nodes) (Pp.seq ~sep:", " Procdesc.Node.pp) all_def_nodes;

      (* Step 4. Filter for valid sites: the definition must dominate the crash. *)
      let valid_sites =
        List.filter all_def_nodes ~f:(fun node ->
            let is_dominator = dominates node crashing_node in
            L.d_printfln
              "[transformation-debug] find_last_def_site: Candidate node %a. Dominates crash site? %b"
              Procdesc.Node.pp node is_dominator;
            is_dominator )
      in
      L.d_printfln "[transformation-debug] find_last_def_site: Found %d valid sites that dominate the crash."
        (List.length valid_sites);
      
      (* Step 5. Of the valid dominators, pick the one that is "closest" to the crash site.
         This is the one that is dominated by all the others. *)
      let result =
        List.max_elt valid_sites ~compare:(fun n1 n2 ->
            if dominates n1 n2 then -1 else if dominates n2 n1 then 1 else 0 )
      in
      ( match result with
      | Some n ->
          L.d_printfln "[transformation-debug] find_last_def_site: Selected best site: %a" Procdesc.Node.pp n
      | None ->
          L.d_printfln "[transformation-debug] find_last_def_site: No suitable definition site found." );
      result

(** Searches the current abstract state for a local variable that is a suitable "reuse" candidate.
    A candidate is viable if it has a compatible type and is non-null at the crash point.
    This logic is complex as it must correctly query Pulse's abstract state, distinguishing between
    a pointer's address and the value it holds to determine if it points to allocated, initialized memory. *)
let find_reuse_candidate proc_desc astate (pvar_to_fix, pvar_typ) =
  let locals = Procdesc.get_locals proc_desc in
  let proc_name = Procdesc.get_proc_name proc_desc in

  (*
    Step 1: Create a set of all local variables that are potential candidates.
    This is more efficient than iterating through the list repeatedly.
  *)
  let local_pvar_candidates =
    List.fold locals ~init:Pvar.Set.empty ~f:(fun acc (attrs : ProcAttributes.var_data) ->
        if Typ.equal attrs.typ pvar_typ then
          let pvar = Pvar.mk attrs.name proc_name in
          if Pvar.equal pvar pvar_to_fix then acc else Pvar.Set.add pvar acc
        else acc )
  in
  L.d_printfln "[transformation-reuse-debug] >> Identified %d potential reuse candidates of the correct type."
    (Pvar.Set.cardinal local_pvar_candidates);


  (*
    Step 2: Iterate through the stack (the analysis's ground truth) and find the first
    variable that is in the candidate set and is non-null.
  *)
  L.d_printfln "[transformation-reuse] >> Searching for a viable local variable by iterating through the abstract stack...";
  AbductiveDomain.Stack.fold
    (fun var vo found_opt ->
      if Option.is_some found_opt then found_opt
      else
        match Var.get_pvar var with
        | None ->
            found_opt (* Not a program variable, skip *)
        | Some pvar_in_stack when Pvar.Set.mem pvar_in_stack local_pvar_candidates -> (
            (* This variable from the stack is one of the local candidates. Now check it. *)
            L.d_printfln "[transformation-reuse-debug] >> Found candidate '%a' in stack. Checking its status..."
              (Pvar.pp Pp.text) pvar_in_stack;
            let addr, history = (ValueOrigin.value vo, ValueOrigin  .hist vo) in
            L.d_printfln "[transformation-reuse-debug]    - Addr: %a, History: %a"
                AbstractValue.pp addr ValueHistory.pp history;

            let path_condition = astate.AbductiveDomain.path_condition in
            let has_allocated_cell =
              AbductiveDomain.find_post_cell_opt addr astate |> Option.is_some
            in
            let is_not_null = not (PulseFormula.is_known_zero path_condition addr) in

            if has_allocated_cell && is_not_null then (
              L.d_printfln "[transformation-reuse-debug]   + SUCCESS: Candidate '%a' is allocated and not_null. Selecting it."
                (Pvar.pp Pp.text) pvar_in_stack;
              Some {reused_pvar= pvar_in_stack} )
            else (
              L.d_printfln
                "[transformation-reuse-debug]    - FAILED: Candidate '%a' check failed: has_cell=%b, is_not_null=%b. Continuing search."
                (Pvar.pp Pp.text) pvar_in_stack has_allocated_cell is_not_null;
              found_opt ) )
        | Some pvar_in_stack ->
            (* It's a pvar, but not one we're looking for *)
            L.d_printfln "[transformation-reuse-debug]    - Found pvar '%a' in stack, but it's not a candidate. Skipping."
                (Pvar.pp Pp.text) pvar_in_stack;
            found_opt
      )
    astate None

(** The main planner for the REPLACE strategy. If the pointer is local, this function finds the
    definition site and generates a `Replace` plan, including searching for a reuse candidate. *)

(*Helper that gets the type*)
let get_pvar_type proc_desc pvar =
  let locals = Procdesc.get_locals proc_desc in
  List.find_map locals ~f:(fun (var_data: ProcAttributes.var_data) ->
    if Mangled.equal var_data.name (Pvar.get_name pvar) then Some var_data.typ else None
  )

let plan_replace_transformation proc_desc (bug : 'payload bug_info) (all_aliases : Exp.t list) : transformation_plan list =
  let open IOption.Let_syntax in
  let plan_opt =
    let* ptr_var = bug.ptr_var in
    let* pvar = Var.get_pvar ptr_var in
    let* def_site = find_last_def_site ~proc_desc ~ptr_var:pvar in
    let+ pvar_typ = get_pvar_type proc_desc pvar in
    (*
      The `all_aliases` list is now included in the final plan record.
      This makes the plan's data complete and available for the reporter.
    *)
    
    L.d_printfln "[transformation-reuse] >> Searching for a viable local variable to reuse...";
    let reuse_candidate_opt =
      find_reuse_candidate proc_desc bug.astate (pvar, pvar_typ)
    in
    (* Calculate the metrics for the Replace strategy directly. *)
    let metrics =
      { (* Cost_Rep is 1 (one new definition site) + 0 (zero new heap cells). *)
        cost= 1
      ; total_aliases= List.length all_aliases }
    in
    (* Construct the final transformation_plan record with the metrics included. *)
    Replace
      { def_site_node= def_site
      ; pvar
      ; pvar_typ
      ; reuse_info= reuse_candidate_opt
      ; all_aliases
      ; metrics }
  in
  Option.to_list plan_opt


(** {4b. The SKIP Strategy Planner & Three-Stage Compaction} ---> Currently Monolith, can be separated later*)

(** Helper: Given the pointer Var.t that we recorded in bug.ptr_var, look up its
    current abstract address in the [astate]. *)
let get_ptr_address ~(astate: AbductiveDomain.t) (v: Var.t)
: AbstractValue.t option =
match AbductiveDomain.Stack.find_opt ~pre_or_post:`Post v astate with
| None ->
    None
| Some vo ->
    (* vo : PulseAbductiveDomain.Stack.value, i.e. a ValueOrigin.t_ over a needs_canon *)
    let raw_addr, _hist = PulseValueOrigin.addr_hist vo in
    Some raw_addr

(** The main planner for the SKIP/EVADE strategy. It orchestrates the three-stage compaction
    pipeline: generate -> filter -> merge. This process is what allows the tool
    to find a Pareto-optimal solution, balancing the number of guards with the number of
    unnecessarily guarded lines of code. *)

(** STAGE 1 of compaction. Generates an initial set of small, targeted `Skip` plans,
    typically one for each individual crash site. *)

(** STAGE 2 of compaction. Filters the candidate list to remove any plan whose scope is
    fully contained within another plan's scope. This eliminates redundant nested guards. *)

(** STAGE 3 of compaction. Iteratively merges adjacent or overlapping plans into a single, larger plan.
    This is a fixed-point algorithm that continues until no more merges are possible, reducing the
    total number of guards. The decision to merge is a heuristic that balances minimizing
    guard count against avoiding wrapping unrelated code with side-effects. *)
let plan_skip_or_evade_transformation proc_desc (bug : 'payload bug_info) all_ptrs_to_guard: transformation_plan list =
  let start = Procdesc.get_start_node proc_desc in
  let idom = GDoms.compute_idom proc_desc start in
  let compute_ipdom proc_desc =
    let exit_node = Procdesc.get_exit_node proc_desc in
    let reversed_graph_instance = PostDominators.ReversedCFG.from_pdesc proc_desc in
    PostDominators.compute_idom reversed_graph_instance exit_node
  in
  let ipdom_fun = lazy (compute_ipdom proc_desc) in
    
  (** Computes the Lowest Common Ancestor (LCA) of two nodes in a dominator tree. *)
  let lca x y=
    let rec collect_ancestors n acc =
      let acc' = Procdesc.NodeSet.add n acc in
      if Procdesc.Node.equal n start then acc' else collect_ancestors (idom n) acc'
    in
    let anc_x = collect_ancestors x Procdesc.NodeSet.empty in
    let rec climb m = if Procdesc.NodeSet.mem m anc_x then m else climb (idom m) in
    climb y
  in

  let rep_opt =
    match bug.ptr_var with
      | None -> bug.av_opt
      | Some v -> get_ptr_address ~astate:bug.astate v
  in
  let stack_aliases =
    match rep_opt with
      | None -> []
      | Some rep -> collect_stack_aliases bug.astate rep
  in
  
  L.d_printfln "[transformation-plan] ptr=%a, stack_aliases=%d" Exp.pp bug.ptr_expr (List.length stack_aliases);

  (* Step 1: UNIFY the slice for the ENTIRE alias set first. *)

  L.d_printfln "[transformation-log] >>> Starting plan_skip_or_evade_transformation for %a" Procname.pp
  (Procdesc.get_proc_name proc_desc) ;
  L.d_printfln "[transformation-log] Initial `all_ptrs_to_guard` list: [%a]" (Pp.seq ~sep:", " Exp.pp)
    all_ptrs_to_guard ;

  (* This is the version of the implementation that understands SIL's two-step dereference. *)
  let get_crash_nodes ptr_exp =
    L.d_printfln "\n[transformation-log] >> Running get_crash_nodes for pointer: %a" Exp.pp ptr_exp ;
  
    (* STAGE 1: Pre-computation.
       Find all temporary identifiers that can carry the null value by tracking its propagation
       through the procedure until a fixed point is reached. *)
   let compute_null_carrying_idents () =
    let rec find_tainted_idents_fixed_point current_tainted_idents =
      let newly_tainted_idents =
        (* The signature for fold_instrs includes the node, which we don't use. *)
        Procdesc.fold_instrs proc_desc ~init:Ident.Set.empty ~f:(fun acc _node instr ->
            match (instr : Sil.instr) with
            (* Taint can only be propagated by instructions that assign to a new identifier.
               In SIL for this purpose, that is primarily Sil.Load. *)
            | Load {id= dest_id; e= src_exp; _} -> (
              (* Recursive helper to check if the source expression is based on a tainted ident. *)
              let rec is_source_tainted e =
                match (e : Exp.t) with
                | Var id ->
                    Ident.Set.mem id current_tainted_idents
                | Lfield ({exp= base_exp}, _, _) ->
                    is_source_tainted base_exp
                | Lindex (base_exp, _) ->
                    is_source_tainted base_exp
                | Cast (_, base_exp) ->
                    is_source_tainted base_exp
                (* NEW: Handle pointer arithmetic expressions *)
                | BinOp (bop, e1, e2) -> (
                  match bop with
                  (* Taint propagates through pointer arithmetic. *)
                  | Binop.PlusPI | Binop.MinusPI ->
                      is_source_tainted e1 || is_source_tainted e2
                  | _ ->
                      false )
                | _ ->
                    false
              in
              if is_source_tainted src_exp then Ident.Set.add dest_id acc else acc )
            (* Other instructions like Store, Prune, Call etc. do not create new tainted temporaries
               in the way we are tracking here. *)
            | _ ->
                acc )
      in
      let all_tainted_idents = Ident.Set.union current_tainted_idents newly_tainted_idents in
      if Ident.Set.equal current_tainted_idents all_tainted_idents then (
        L.d_printfln "[transformation-log]    (Taint analysis fixed point reached)" ;
        all_tainted_idents )
      else find_tainted_idents_fixed_point all_tainted_idents
    in

    (* Initial taint: find the first temp(s) loaded from any expression ROOTED AT the pointer var.
      This is now recursive to handle fields, indices, etc. from the very start. *)
    let initial_idents =
    Procdesc.fold_instrs proc_desc ~init:Ident.Set.empty ~f:(fun acc _node instr ->
        match instr with
        | Sil.Load {id; e= src_exp; _} ->
            let rec is_rooted_at_ptr_exp e =
              match (e : Exp.t) with
              | e when Exp.equal e ptr_exp ->
                  true
              | Lfield ({exp= base_exp}, _, _) ->
                  is_rooted_at_ptr_exp base_exp
              | Lindex (base_exp, _) ->
                  is_rooted_at_ptr_exp base_exp
              | Cast (_, base_exp) ->
                  is_rooted_at_ptr_exp base_exp
              | _ ->
                  false
            in
            if is_rooted_at_ptr_exp src_exp then Ident.Set.add id acc else acc
        | _ ->
            acc )
    in
    L.d_printfln "[transformation-log]    (Taint analysis initial idents: {%a})"
      (Format.pp_print_list Ident.pp)
      (Ident.Set.elements initial_idents) ;
    find_tainted_idents_fixed_point initial_idents
    in
  
    let null_carrying_idents = compute_null_carrying_idents () in
    L.d_printfln "[transformation-log]    (Found %d total null-carrying idents: {%a})"
      (Ident.Set.cardinal null_carrying_idents)
      (Format.pp_print_list Ident.pp)
      (Ident.Set.elements null_carrying_idents) ;
  
    (* STAGE 2: Crash Site Detection.
       Walk the nodes again, but this time use the globally computed set of tainted idents
       to find dereferences. *)
    let result_nodes =
      Procdesc.fold_nodes proc_desc ~init:[] ~f:(fun acc node ->
          let instrs = Procdesc.Node.get_instrs node in
          let node_loc = Procdesc.Node.get_loc node in
          let rec is_base_of_dereference e =
            match (e : Exp.t) with
            | Var id ->
                Ident.Set.mem id null_carrying_idents
            | Lfield ({exp= base_exp}, _, _) | Lindex (base_exp, _) | Cast (_, base_exp) ->
                is_base_of_dereference base_exp
            | _ ->
                false
          in
          let has_dereference =
            Instrs.exists instrs ~f:(fun instr ->
                let is_deref, addr_exp_opt =
                  match instr with
                  | Sil.Load {e; _} ->
                      (is_base_of_dereference e, Some e)
                  | Sil.Store {e1; _} ->
                      (is_base_of_dereference e1, Some e1)
                  | _ ->
                      (false, None)
                in
                if is_deref then
                  L.d_printfln "[transformation-log]      !!! Found DEREFERENCE via expression: %a" Exp.pp
                    (Option.value_exn addr_exp_opt) ;
                is_deref )
          in
          if has_dereference then (
            L.d_printfln "[transformation-log]    >>> Node %a (C line %d) MARKED as a crash site."
              Procdesc.Node.pp node node_loc.line ;
            node :: acc )
          else acc )
    in
    L.d_printfln "[transformation-log] << Finished get_crash_nodes for %a. Found %d crash nodes."
      Exp.pp ptr_exp (List.length result_nodes) ;
    result_nodes
    in

  (*********************************************************************************)
  (* Stage 0: Cluster by Control-Flow Proximity                                  *)
  (*********************************************************************************)
  let ptr_to_crashes_map =
    List.map all_ptrs_to_guard ~f:(fun ptr -> (ptr, get_crash_nodes ptr))
    |> List.filter ~f:(fun (_, crashes) -> not (List.is_empty crashes))
  in

  L.d_printfln "\n[transformation-log] STEP 1.1: Mapped each pointer to itt crash sites." ;
  List.iter ptr_to_crashes_map ~f:(fun (ptr, nodes) ->
      let node_locs = List.map nodes ~f:(fun n -> (Procdesc.Node.get_loc n).line) in
      L.d_printfln "[transformation-log]   Pointer %a has %d crash site(s) at C file line(s): [%a]" Exp.pp
        ptr (List.length nodes) (Pp.seq ~sep:", " Int.pp) node_locs ) ;

  let lca_map =
    let lca_to_ptr_list =
      List.map ptr_to_crashes_map ~f:(fun (ptr, crashes) ->
          let lca_of_crashes =
            let first = List.hd_exn crashes in
            let rest = List.tl_exn crashes in
            List.fold rest ~init:first ~f:lca
          in
          (lca_of_crashes, ptr) )
    in
    List.fold lca_to_ptr_list ~init:Procdesc.NodeMap.empty ~f:(fun map (lca_node, ptr) ->
        let existing_ptrs =
          Procdesc.NodeMap.find_opt lca_node map |> Option.value ~default:[]
        in
        Procdesc.NodeMap.add lca_node (ptr :: existing_ptrs) map )
  in

  L.d_printfln "\n[transformation-log] STEP 1.2: Clustered pointers by the LCA of their crash sites." ;
  Procdesc.NodeMap.iter
    (fun lca_node ptrs_in_cluster ->
      let lca_loc = Procdesc.Node.get_loc lca_node in
      L.d_printfln
        "[transformation-log]   Cluster at LCA node %a (line %d) contains %d pointer(s): [%a]"
        Procdesc.Node.pp lca_node lca_loc.line (List.length ptrs_in_cluster)
        (Pp.seq ~sep:", " Exp.pp) ptrs_in_cluster )
    lca_map ;
  

  (* This helper correctly identifies the single node designated as the final crash site by the trace. *)
  let is_the_final_crash_site (node : Procdesc.Node.t) (trace : Trace.t) : bool =
      let node_loc = Procdesc.Node.get_loc node in
      let get_immediate_crash_location = function
        | Trace.Immediate {location; _} -> Some location
        | Trace.ViaCall {location; _} -> Some location 
      in
      match get_immediate_crash_location trace with
      | None -> false
      | Some final_crash_loc -> Location.equal node_loc final_crash_loc
  in
  
  (*********************************************************************************)
  (* Stage 1: Seed the Compaction Algorithm (Hybrid Approach)                    *)
  (*********************************************************************************)

  (** Pre-computes the complete set of temporary identifiers that are aliases of the given pointers.
    It performs a fixed-point analysis to track aliases as they are copied between variables. *)
  let get_all_alias_temps proc_desc (all_ptrs_to_guard : Exp.t list) : Ident.Set.t =
    let rec find_temps_fixed_point current_temps =
      let newly_found_temps =
        Procdesc.fold_instrs proc_desc ~init:Ident.Set.empty ~f:(fun acc _node instr ->
            match (instr : Sil.instr) with
            (* Case 1: A temp is loaded directly from a pointer pvar. *)
            | Load {id; e; _} when List.exists all_ptrs_to_guard ~f:(fun ptr -> Exp.equal e ptr) ->
                if Ident.Set.mem id current_temps then acc else Ident.Set.add id acc
            (* Case 2: A temp is loaded from another temp (alias propagation). *)
            | Load {id; e= Exp.Var src_id; _} when Ident.Set.mem src_id current_temps ->
                if Ident.Set.mem id current_temps then acc else Ident.Set.add id acc
            | _ ->
                acc )
      in
      if Ident.Set.is_empty newly_found_temps then current_temps
      else
        let all_temps = Ident.Set.union current_temps newly_found_temps in
        find_temps_fixed_point all_temps
    in
    find_temps_fixed_point Ident.Set.empty
  in

  (** A syntactic check that climbs the dominator tree to find a guarding Prune instruction.
    It uses a pre-computed set of all temporary aliases. *)
    let is_syntactically_guarded proc_desc idom (node : Procdesc.Node.t) (all_alias_temps : Ident.Set.t) : bool =
      let start_node = Procdesc.get_start_node proc_desc in
      L.d_printfln "[transformation-guard-check] Checking for guards for crash node %a (line %d)."
        Procdesc.Node.pp node (Procdesc.Node.get_loc node).line;
      L.d_printfln "[transformation-guard-check]    - Using pre-computed alias set: {%a}"
        (Format.pp_print_list Ident.pp)
        (Ident.Set.elements all_alias_temps);
    
      (* This is the heavily instrumented checker function. *)
      let is_non_null_check_of_alias (condition : Exp.t) : bool =
        L.d_printfln "[transformation-guard-check] --- Start Prune Check ---";
        L.d_printfln "[transformation-guard-check] Condition: `%a`" Exp.pp condition;

        let rec is_cast_of_null (e : Exp.t) : bool =
          match e with
          | e when Exp.is_null_literal e ->
              true
          | Exp.Cast (_, base_exp) ->
              is_cast_of_null base_exp
          | _ ->
              false
        in    
    
        (* Helper to robustly find a base variable, looking through casts. *)
        let rec get_base_ident (e : Exp.t) : Ident.t option =
          match e with
          | Exp.Var id ->
              Some id
          | Exp.Cast (_, base_exp) ->
              get_base_ident base_exp
          | _ ->
              None
        in
        let result =
          match condition with
          (* Case 1: if (ptr) *)
          | e -> (
            match get_base_ident e with
            | Some id when Ident.Set.mem id all_alias_temps ->
                L.d_printfln "[transformation-guard-check]   -> Matched simple guard: `if (%a)` is an alias." Ident.pp id;
                true
            | _ -> (
              (* Case 2: if (ptr != NULL) or if (NULL != ptr) *)
              match e with
              | Exp.BinOp (Binop.Ne, e1, e2) ->
                  L.d_printfln "[transformation-guard-check]   -> Found BinOp(Ne). Analyzing operands...";
                  let id1_opt = get_base_ident e1 in
                  let id2_opt = get_base_ident e2 in
                  (* Check Case A: (alias != NULL) *)
                  let is_e1_alias = Option.exists id1_opt ~f:(fun id -> Ident.Set.mem id all_alias_temps) in
                  let is_e2_null = is_cast_of_null e2 in
                  L.d_printfln "[transformation-guard-check]     - Checking (e1 != e2): Is e1 an alias? %b. Is e2 null? %b."
                  is_e1_alias is_e2_null;
                  if is_e1_alias && is_e2_null then true
                  else (
                    (* Check Case B: (NULL != alias) *)
                    let is_e2_alias = Option.exists id2_opt ~f:(fun id -> Ident.Set.mem id all_alias_temps) in
                    let is_e1_null = is_cast_of_null e1 in
                    L.d_printfln "[transformation-guard-check]     - Checking (e1 != e2): Is e2 an alias? %b. Is e1 null? %b."
                    is_e2_alias is_e1_null;
                    if is_e2_alias && is_e1_null then true else false
                  )
              | _ ->
                  false ) )
        in
        L.d_printfln "[transformation-guard-check] --- End Prune Check --- Result: %s"
          (if result then "MATCH" else "NO MATCH");
        result
      in
      let rec climb_dominators current_node =
        if Procdesc.Node.equal current_node start_node then (
          L.d_printfln "[transformation-guard-check] << Reached start node without finding a guard. Result: false.";
          false )
        else (
          L.d_printfln "[transformation-guard-check] >> Visiting dominator %a." Procdesc.Node.pp current_node;
          let instrs = Procdesc.Node.get_instrs current_node in
          let found_guard =
            Instrs.exists instrs ~f:(fun instr ->
                match instr with
                | Sil.Prune (condition, _, true, Sil.Ik_if) ->
                    L.d_printfln "[transformation-guard-check]    - Found Prune in this node." ;
                    let is_match = is_non_null_check_of_alias condition in
                    if is_match then
                      L.d_printfln "[transformation-guard-check]      - SUCCESS: This Prune is a valid guard."
                    else
                      L.d_printfln "[transformation-guard-check]      - INFO: This Prune does not match any known alias.";
                    is_match
                | _ ->
                    false )
          in
          if found_guard then (
            L.d_printfln "[transformation-guard-check] << Found a valid guard. Result: true.";
            true )
          else
            let parent_dominator = idom current_node in
            if Procdesc.Node.equal parent_dominator current_node then (
              L.d_printfln "[transformation-guard-check] << Parent is same as current. Stopping climb. Result: false.";
              false )
            else climb_dominators parent_dominator
        )
      in
      climb_dominators (idom node)
  in
  let total_aliases_in_proc = List.length all_ptrs_to_guard in
  let unified_crash_slice =
    match bug.diag_trace with
    | Trace.ViaCall {location= crash_loc; _} ->
        (* INTER-PROCEDURAL CASE: The crash is the call site itself. No syntactic search needed. *)
        L.d_printfln "[transformation-log]   Trace is ViaCall. The crash site is the call location.";
        List.filter (Procdesc.get_nodes proc_desc) ~f:(fun node ->
            Location.equal (Procdesc.Node.get_loc node) crash_loc )

    | Trace.Immediate _ ->
        (* INTRA-PROCEDURAL CASE: The crash is the union of all syntactic dereferences
            of all aliases, filtered to remove any non-crashing nodes. *)
        L.d_printfln "[transformation-log]   Trace is Immediate. Unifying all syntactic dereferences.";
        let all_syntactic_dereferences =
          List.concat_map all_ptrs_to_guard ~f:get_crash_nodes
        in

        (*Prune the list by removing dereferences that are already guarded. *)
        L.d_printfln "[transformation-log]   Pruning the slice by checking for existing semantic guards...";
        let all_alias_temps = get_all_alias_temps proc_desc all_ptrs_to_guard in
          L.d_printfln "[transformation-guard-check] Pre-computed all alias temps: {%a}"
          (Format.pp_print_list Ident.pp)
          (Ident.Set.elements all_alias_temps);
        let unguarded_syntactic_dereferences =
          List.filter all_syntactic_dereferences ~f:(fun node ->
            not (is_syntactically_guarded proc_desc idom node all_alias_temps)
          )
        in
        
        (* In the multi-alias case, the trace only blames one site. We must keep all
            syntactic sites for the other aliases. A simple union is the most robust approach. *)
        let final_crash_node =
          List.find all_syntactic_dereferences ~f:(fun node -> is_the_final_crash_site node bug.diag_trace)
        in
        List.dedup_and_sort ~compare:Procdesc.Node.compare
          (Option.to_list final_crash_node @ unguarded_syntactic_dereferences)
  in
  let true_slice_size = List.length unified_crash_slice in
  L.d_printfln "\n[transformation-log] STAGE 1.1: Found a unified slice of %d crash node(s)."
    (List.length unified_crash_slice);

  let candidate_plans =
    List.filter_map unified_crash_slice ~f:(fun crash_node ->
        let slice_for_this_node = [crash_node] in
        let start_node, end_node = find_minimal_scope slice_for_this_node ipdom_fun proc_desc lca idom in
        
        L.d_printfln "\n[transformation-log] STAGE 1.2: Generating candidate plan for single crash node at line %d..."
          (Procdesc.Node.get_loc crash_node).line;
        L.d_printfln "[transformation-log]   - Calculated minimal scope: start node %a (line %d), end node %a (line %d)"
            Procdesc.Node.pp start_node (Procdesc.Node.get_loc start_node).line
            Procdesc.Node.pp end_node (Procdesc.Node.get_loc end_node).line;

        if Procdesc.Node.equal start_node start then
          Some (IEvade {proc_start_node= start; pointer_expr= List.hd_exn all_ptrs_to_guard})
        else
          Some
            (ISkip
                { lca_node= start_node
                ; join_node= end_node
                ; pointer_exprs= all_ptrs_to_guard
                ; slice_nodes= [crash_node] } ) )
  in
  let initial_candidate_plans = List.length candidate_plans in
  (*********************************************************************************)
  (* Stage 2 & 3: Filter and Merge                             *)
  (*********************************************************************************)
  
  let is_strictly_contained_within scope1_raw scope2_raw =
    let start1, end1 = normalize_scope scope1_raw idom in
    let start2, end2 = normalize_scope scope2_raw idom in
    if Procdesc.Node.equal start1 start2 && Procdesc.Node.equal end1 end2 then false
    else
      is_dominated_by ~dominator:start1 ~node:start2 idom
      && is_post_dominated_by ~pdominator:end1 ~node:end2 ipdom_fun
  in
        
  let should_merge_scopes all_aliases scope1_raw scope2_raw =
    let s1_loc, e1_loc = ((Procdesc.Node.get_loc (fst scope1_raw)).line, (Procdesc.Node.get_loc (snd scope1_raw)).line) in
    let s2_loc, e2_loc = ((Procdesc.Node.get_loc (fst scope2_raw)).line, (Procdesc.Node.get_loc (snd scope2_raw)).line) in
    L.d_printfln "\n[transformation-merge-check] >> Checking if scopes [lines ~%d-%d] and [~%d-%d] should merge."
      (min s1_loc e1_loc) (max s1_loc e1_loc) (min s2_loc e2_loc) (max s2_loc e2_loc);

    let s1, e1 = normalize_scope scope1_raw idom in
    let s2, e2 = normalize_scope scope2_raw idom in

    (* Condition 1: Partial Overlap *)
    let partial_overlap =
      (is_dominated_by ~dominator:s1 ~node:s2 idom && is_post_dominated_by ~pdominator:e1 ~node:s2 ipdom_fun)
      || (is_dominated_by ~dominator:s2 ~node:s1 idom && is_post_dominated_by ~pdominator:e2 ~node:s1 ipdom_fun)
    in
    L.d_printfln "[transformation-merge-check]    - Partial overlap? %b" partial_overlap;

    (* Helper to find external side effects *)
    let has_external_side_effects (instr : Sil.instr) =
      match instr with
      | Prune _ | Metadata _ -> None
      | Load {e; _} | Store {e1= e; _} ->
        (* A load or store is an external side effect ONLY if the address `e`
            is NOT one of the pointers we are explicitly trying to guard.
            If it *is* one of the pointers, we want to skip. *)
        let is_aliased_access = List.exists all_aliases ~f:(fun alias -> Exp.equal e alias) in
        if is_aliased_access then
          (* Not an EXTERNAL side effect, it's part of the bug. Benign for merging purposes. *)
          Some instr
        else
          (* This is a memory access to an unrelated pointer. It's a side effect. *)
          None
      | Call (_, _, args, _, _) ->
        if List.exists args ~f:(fun (arg_exp, _) -> not (Exp.is_const arg_exp)) then Some instr else None
    in

    (* Helper to check if all nodes BETWEEN a start and end node are benign. *)
    let is_path_benign ~from_node ~to_node =
      L.d_printfln "[transformation-merge-check]      - Checking for benign path from node %a to node %a."
        Procdesc.Node.pp from_node Procdesc.Node.pp to_node;
      let all_proc_nodes = Procdesc.get_nodes proc_desc in
      let nodes_between =
        List.filter all_proc_nodes ~f:(fun n ->
          not (Procdesc.Node.equal n from_node) && not (Procdesc.Node.equal n to_node) &&
          is_dominated_by ~dominator:from_node ~node:n idom && is_post_dominated_by ~pdominator:to_node ~node:n ipdom_fun
        )
      in
      L.d_printfln "[transformation-merge-check]      - Found %d node(s) between the two scopes." (List.length nodes_between);
      
      (* Check if ANY of these intermediate nodes have a side effect. *)
      let offending_node_and_instr =
        List.find_map nodes_between ~f:(fun node ->
          let offending_instr_opt =
            Instrs.find_map (Procdesc.Node.get_instrs node) ~f:has_external_side_effects
          in
          match offending_instr_opt with
          | None -> None
          | Some instr -> Some (node, instr)
        )
      in

      match offending_node_and_instr with
      | Some (node, instr) ->
          L.d_printfln "[transformation-merge-check]      - Path NOT benign. Found external side-effect in node %a: %a"
            Procdesc.Node.pp node (Sil.pp_instr ~print_types:false Pp.text) instr;
          false
      | None ->
          L.d_printfln "[transformation-merge-check]      - Path is benign. No external side-effects found between scopes.";
          true
    in

    (* Condition 2: Principled Adjacency (Sequentiality). *)
    let are_sequential =
      L.d_printfln "[transformation-merge-check]    - Checking for sequentiality...";
      if is_dominated_by ~dominator:e1 ~node:s2 idom then
        is_path_benign ~from_node:e1 ~to_node:s2
      else if is_dominated_by ~dominator:e2 ~node:s1 idom then
        is_path_benign ~from_node:e2 ~to_node:s1
      else false
    in
    L.d_printfln "[transformation-merge-check]    - Are sequential? %b" are_sequential;

    let result = partial_overlap || are_sequential in
    L.d_printfln "[transformation-merge-check] << Should merge? %b" result;
    result
  in

  let merge_plans (plan1 : intermediate_plan) (plan2 : intermediate_plan) ipdom_fun : intermediate_plan =
    match (plan1, plan2) with
    | ( ISkip {lca_node= s1; join_node= e1; pointer_exprs= p1; slice_nodes= n1}
      , ISkip {lca_node= s2; join_node= e2; pointer_exprs= p2; slice_nodes= n2} ) ->
        let s1_loc, e1_loc = ((Procdesc.Node.get_loc s1).line, (Procdesc.Node.get_loc e1).line) in
        let s2_loc, e2_loc = ((Procdesc.Node.get_loc s2).line, (Procdesc.Node.get_loc e2).line) in
        L.d_printfln "\n[transformation-merge] >> Attempting to merge plan [lines %d-%d] with plan [lines %d-%d]"
          (min s1_loc e1_loc) (max s1_loc e1_loc) (min s2_loc e2_loc) (max s2_loc e2_loc);

        let new_slice = List.dedup_and_sort ~compare:Procdesc.Node.compare (n1 @ n2) in
        let new_pointers = List.dedup_and_sort ~compare:Exp.compare (p1 @ p2) in
        
        (*
          Step 1: Calculate the initial merged scope from the UNION of crash sites, not the old boundaries.
        *)
        let initial_lca = lca s1 s2 in

        (* The new join node is the one that is post-dominated by the other (i.e., the "latest" join). *)
        let new_join =
          L.d_printfln "[transformation-merge-join] -- Deciding join node between e1=%a (line %d) and e2=%a (line %d)"
            Procdesc.Node.pp e1 (Procdesc.Node.get_loc e1).line
            Procdesc.Node.pp e2 (Procdesc.Node.get_loc e2).line;

        let e1_postdoms_e2 = is_post_dominated_by ~pdominator:e1 ~node:e2 ipdom_fun in
        L.d_printfln "[transformation-merge-join]    - Does e1 post-dominate e2? %b" e1_postdoms_e2;

        let e2_postdoms_e1 = is_post_dominated_by ~pdominator:e2 ~node:e1 ipdom_fun in
        L.d_printfln "[transformation-merge-join]    - Does e2 post-dominate e1? %b" e2_postdoms_e1;

        if e1_postdoms_e2 then (
          L.d_printfln "[transformation-merge-join]    - Decision: e1 is the latest join. Using e1.";
          e1 )
        else if e2_postdoms_e1 then (
          L.d_printfln "[transformation-merge-join]    - Decision: e2 is the latest join. Using e2.";
          e2 )
          (*COULD BE A POTENTIAL PROBLEM*) 
        else (* Fallback: Parallel branches. The true join is the IPDOM of the LCPD. *)
        (
          let lcpd_node = lcpd (Lazy.force ipdom_fun) e1 e2 in
          L.d_printfln "[transformation-merge-join]    - Fallback: Nodes are in parallel branches." ;
          L.d_printfln "[transformation-merge-join]    - Earliest rejoin point (LCPD) is node %a (line %d)."
            Procdesc.Node.pp lcpd_node
            (Procdesc.Node.get_loc lcpd_node).line ;
          
          let ipdom = Lazy.force ipdom_fun in
          let final_join_node =
            try
              (* Attempt the potentially failing lookup. *)
              let node = ipdom lcpd_node in
              L.d_printfln
                "[transformation-merge-join]    - The true join is the IPDOM of the LCPD. Result is node %a (line %d)."
                Procdesc.Node.pp node (Procdesc.Node.get_loc node).line ;
              node
            with Stdlib.Not_found ->
              (* If the lookup fails, it's because lcpd_node is the exit node.
                 Safely fall back to using the lcpd_node itself. *)
              L.d_printfln
                "[transformation-merge-join-warning]    - Could not find IPDOM of the LCPD. This is expected if the rejoin point is the function exit. Using LCPD itself as the final join node." ;
              lcpd_node
          in
          final_join_node
        )
      in

      L.d_printfln "[transformation-merge]    - Initial merged scope from old boundaries: LCA node %a, Join node %a"
        Procdesc.Node.pp initial_lca Procdesc.Node.pp new_join;
      (*
        Step 2: The existing, correct data-flow-awareness logic now runs on a sound initial scope.
      *)
      let is_inside_scope node =
        is_dominated_by ~dominator:initial_lca ~node idom
        && is_post_dominated_by ~pdominator:new_join ~node ipdom_fun
      in
      let trapped_decls =
        Procdesc.fold_instrs proc_desc ~init:[] ~f:(fun acc node instr ->
          if is_inside_scope node then
            match instr with
            | Sil.Store {e1=Exp.Lvar pvar; _} when Pvar.is_local pvar ->
                (* Find the FIRST time this local is assigned. *)
                if not (List.exists acc ~f:(Pvar.equal pvar)) then (
                  L.d_printfln "[transformation-merge]    - Found trapped local variable declaration: %a in node %a"                           
                  (Pvar.pp Pp.text) pvar Procdesc.Node.pp node;
                  pvar :: acc
        ) else acc
            | _ -> acc
          else acc
        )
      in
      let earliest_decl_node =
        List.fold trapped_decls ~init:initial_lca ~f:(fun current_lca pvar ->
          let all_nodes = Procdesc.get_nodes proc_desc in
          let decl_node_opt =
            List.find all_nodes ~f:(fun node ->
              Instrs.exists (Procdesc.Node.get_instrs node) ~f:(function
                | Sil.Store {e1=Exp.Lvar p; _} -> Pvar.equal p pvar
                | _ -> false ) )
          in

          match decl_node_opt with
          | None ->
              L.d_printfln "[transformation-merge]    - WARNING: Could not find decl node for %a. This should not happen."
                (Pvar.pp Pp.text) pvar;
              current_lca
          | Some decl_node ->
              L.d_printfln "[transformation-merge]    - Declaration of %a is at node %a. Recalculating LCA."
                (Pvar.pp Pp.text) pvar Procdesc.Node.pp decl_node;
              lca current_lca decl_node
        )
      in
      let new_lca = earliest_decl_node in

      if not (Procdesc.Node.equal new_lca new_lca) then
        L.d_printfln "[transformation-merge]    - Scope expanded! New LCA is node %a (line %d) to include declarations."
          Procdesc.Node.pp new_lca (Procdesc.Node.get_loc new_lca).line;
      
      L.d_printfln "[transformation-merge] << Finished merge. Final scope: [%a -> %a]"
        Procdesc.Node.pp new_lca Procdesc.Node.pp new_join;

      ISkip {lca_node= new_lca; join_node= new_join; pointer_exprs= new_pointers; slice_nodes= new_slice}
  | _ -> plan1
  in

  L.d_printfln "\n[transformation-log] STEP 2: Filtering %d candidate plan(s)." (List.length candidate_plans);
  let filtered_plans =
    List.filter candidate_plans ~f:(fun current_plan ->
        let is_enveloped =
          List.exists candidate_plans ~f:(fun other_plan ->
              if phys_equal current_plan other_plan then false
              else
                match (current_plan, other_plan) with
                | ( ISkip {lca_node= s_curr; join_node= e_curr; _}
                  , ISkip {lca_node= s_other; join_node= e_other; _} ) ->
                    (* Pass scopes as two separate arguments *)
                    is_strictly_contained_within (s_other, e_other) (s_curr, e_curr)
                | _ ->
                    false )
        in
        if is_enveloped then L.d_printfln "[transformation-log]   Filtering one enveloped plan.";
        not is_enveloped )
  in

  L.d_printfln "\n[transformation-log] STEP 3: Merging %d filtered plan(s) using a fixed-point algorithm." (List.length filtered_plans);
  
  let final_intermediate_plans =
    let rec merge_fixed_point plans_to_merge =
      let rec find_and_merge_pair worklist acc =
        match worklist with
        | [] -> None (* No merge found in this pass *)
        | current_plan :: rest ->
            let found_merge =
              List.find_map rest ~f:(fun other_plan ->
                match (current_plan, other_plan) with
                | ( ISkip {lca_node= s1; join_node= e1; _}
                  , ISkip {lca_node= s2; join_node= e2; _} ) ->
                    if should_merge_scopes all_ptrs_to_guard (s1, e1) (s2, e2) then
                      let merged_plan = merge_plans current_plan other_plan ipdom_fun in
                      let remaining_plans = List.filter rest ~f:(fun p -> not (phys_equal p other_plan)) in
                      Some (merged_plan, acc @ remaining_plans)
                    else None
                | _ -> None
              )
            in
            match found_merge with
            | Some (new_plan, new_worklist) -> Some (new_plan :: new_worklist)
            | None -> find_and_merge_pair rest (current_plan :: acc)
      in

      match find_and_merge_pair plans_to_merge [] with
      | None ->
          (* BASE CASE: No merges possible in a full pass. *)
          L.d_printfln "[transformation-log]   - Fixed-point reached. No more merges possible.";
          plans_to_merge
      | Some new_list ->
          (* RECURSIVE STEP: A merge happened. Restart with the new list. *)
          L.d_printfln "[transformation-log]   - Merge successful. Restarting merge pass.";
          merge_fixed_point new_list
    in
    
    merge_fixed_point filtered_plans
  in
  
  L.d_printfln "\n[transformation-log] <<< Generated %d final plan(s)." (List.length final_intermediate_plans);

  let final_guard_count = List.length final_intermediate_plans in
  (* Final step: Map over the generated plans to compute and attach metrics. *)
  List.map final_intermediate_plans ~f:(fun iplan ->
    match iplan with
    | ISkip {lca_node; join_node; pointer_exprs; slice_nodes} ->
      let nodes_in_scope =
        (* Change: Call the new node-counting function. *)
        count_nodes_in_scope ~proc_desc ~idom ~ipdom_fun ~start_node:lca_node
          ~end_node:join_node
      in
      (* The rest of the logic remains the same, but the numbers will be different. *)
      let imprecision_cost = nodes_in_scope - List.length slice_nodes in
      let metrics =
        { total_aliases= total_aliases_in_proc
        ; true_slice_size
        ; initial_candidate_plans
        ; final_guard_count
        ; imprecision_cost
        ; nodes_in_scope }
      in
      Skip {lca_node; join_node; pointer_exprs; slice_nodes; metrics}
    | IEvade {proc_start_node; pointer_expr} ->
        (* Convert from intermediate Evade to final Evade *)
        Evade {proc_start_node; pointer_expr} )

  (* final_plans *)


(** {5. Main Entry Point & Reporting} *)

(** Helper to save a single transformation plan to a file. *)

let save_all_plans proc_desc plans =
  let proc_name = Procdesc.get_proc_name proc_desc in
  try
    L.d_printfln "[transformation-plan] Attempting to save plan.";
    let loc = Procdesc.get_loc proc_desc in
    let source_file_str = SourceFile.to_string loc.Location.file in

    (* Sanitize the filename to remove slashes and replace with a safe character.
       This creates a flat file structure which is simpler and more robust.
       e.g., "crypto/asn1/tasn_enc.c" becomes "crypto_asn1_tasn_enc.c" *)
    let sanitized_source_file = String.tr ~target:'/' ~replacement:'_' source_file_str in
    let filename = Format.asprintf "%s.json" sanitized_source_file in

    (* The output directory remains the same top-level one. *)
    let transformation_dir = Filename.concat Config.project_root "pulse-transformation" in
    let filepath = Filename.concat transformation_dir filename in

    (* Ensure the single output directory exists. mkdir_p is safer as it doesn't
       fail if the directory already exists. *)
    IUnix.mkdir_p transformation_dir;

    let plan_to_json plan =
      `Assoc
        [ ("procedure_name", `String (Procname.to_string proc_name))
        ; ("procedure_id", `String (Procname.to_unique_id proc_name))
        ; ("source_file", `String source_file_str) (* Also save the original source file path *)
        ; ( "plan_type"
          , match plan with
            | Skip _ -> `String "Skip"
            | Evade _ -> `String "Evade"
            | Replace _ -> `String "Replace"
            | NoPlanGenerated _ -> `String "NoPlanGenerated" )
        ; ( "details"
          , match plan with
          | Skip {lca_node; join_node; pointer_exprs; metrics; _} ->
            `Assoc
              [ ("start_node", `Int (Procdesc.Node.get_id lca_node :> int))
              ; ("end_node", `Int (Procdesc.Node.get_id join_node :> int))
              ; ("start_line", `Int (Procdesc.Node.get_loc lca_node).line)
              ; ("end_line", `Int (Procdesc.Node.get_loc join_node).line)
              ; ( "guard_with_pointer"
                , match pointer_exprs with
                  | [] ->
                      `String "unknown_pointer_due_to_empty_list"
                  | hd :: _ ->
                      `String (Format.asprintf "%a" Exp.pp hd) )
              ; ( "metrics"
                , `Assoc
                    [ ("cost_l_imprecision", `Int metrics.imprecision_cost)
                    ; ("cost_g_overhead_final", `Int metrics.final_guard_count)
                    ; ("nodes_in_scope", `Int metrics.nodes_in_scope)
                    ; ("true_slice_size", `Int metrics.true_slice_size)
                    ; ("initial_candidate_plans", `Int metrics.initial_candidate_plans)
                    ; ("total_aliases", `Int metrics.total_aliases) ] ) ]
            | Evade {proc_start_node; pointer_expr} ->
                `Assoc
                  [ ("start_node", `Int (Procdesc.Node.get_id proc_start_node :> int))
                  ; ("pointer_expr", `String (Format.asprintf "%a" Exp.pp pointer_expr)) ]
                  | Replace {def_site_node; pvar; pvar_typ; reuse_info; metrics; _} ->
                    `Assoc
                      [ ("def_site_node", `Int (Procdesc.Node.get_id def_site_node :> int))
                      ; ("def_site_line", `Int (Procdesc.Node.get_loc def_site_node).line)
                      ; ("target_pvar", `String (Pvar.to_string pvar))
                      ; ("pvar_type", `String (Typ.to_string pvar_typ))
                      ; ( "reuse_candidate"
                        , match reuse_info with
                          | None ->
                              `Null
                          | Some {reused_pvar} ->
                              `String (Pvar.to_string reused_pvar) )
                      ; ( "metrics"
                        , `Assoc
                            [ ("cost_rep_modification", `Int metrics.cost)
                            ; ("total_aliases", `Int metrics.total_aliases) ] ) ]
            | NoPlanGenerated {reason; npe_location; pointer_expr_str} ->
                `Assoc
                  [ ("reason", `String reason)
                  ; ("npe_file", `String (SourceFile.to_string npe_location.file))
                  ; ("npe_line", `Int npe_location.line)
                  ; ("original_pointer", `String pointer_expr_str) ] ) ]
    in
    let all_plans_json = `List (List.map plans ~f:plan_to_json) in
    let out_chan = Out_channel.create filepath in
    Yojson.Safe.pretty_to_channel out_chan all_plans_json;
    Out_channel.close out_chan;
    L.d_printfln "[transformation-plan] Saved %d repair plan(s) for %a to %s"
      (List.length plans) Procname.pp proc_name filepath
  with exn ->
    L.d_printfln "[transformation-plan] ERROR: Failed to save repair plans for %a. Exception: %s"
      Procname.pp proc_name (Exn.to_string exn)

(** A pure function that translates a `transformation_plan` record into a human-readable format for logging, and calls the save-plan helper *)
let report_transformation_plan proc_desc plan =
  let proc_name = Procdesc.get_proc_name proc_desc in
  (* let (_:unit) = *)
  match plan with
| Skip {lca_node; join_node; pointer_exprs; _} -> (
    (* --- START OF FIX 1A --- *)
    match pointer_exprs with
    | [] ->
        (* This case should ideally not happen, but we handle it defensively. *)
        L.d_printfln "[transformation-plan-warning] A SKIP plan was generated with an empty pointer list." ;
        L.d_printfln "[transformation-plan]--- PULSE TRANSFORMATION PLAN ---" ;
        L.d_printfln "[transformation-plan]STRATEGY: SKIP (malformed)"
    | guard_ptr_expr :: _ ->
        (* This is the normal, expected case. *)
        let line1 = (Procdesc.Node.get_loc lca_node).line in
        let line2 = (Procdesc.Node.get_loc join_node).line in
        let start_line = min line1 line2 in
        let end_line = max line1 line2 in
        L.d_printfln "[transformation-plan]--- PULSE TRANSFORMATION PLAN ---" ;
        L.d_printfln "[transformation-plan]PROCEDURE: %a" Procname.pp proc_name ;
        L.d_printfln "[transformation-plan]STRATEGY: SKIP" ;
        L.d_printfln "[transformation-plan]ACTION: Guard the code block from line ~%d to ~%d." start_line end_line ;
        L.d_printfln "[transformation-plan]        (Scope starts at node %d and ends at node %d)"
          (Procdesc.Node.get_id lca_node :> int)
          (Procdesc.Node.get_id join_node :> int) ;
        L.d_printfln "[transformation-plan]        with the condition: if (%a != NULL) { ... }" Exp.pp guard_ptr_expr ;
        L.d_printfln "[transformation-plan]        This guard protects pointers: [%a]"
          (Pp.seq ~sep:", " Exp.pp) pointer_exprs ;
        L.d_printfln "[transformation-plan]--------------------------" )

| Evade {proc_start_node; pointer_expr} ->
    L.d_printfln "[transformation-plan]--- PULSE TRANSFORMATION PLAN ---" ;
    L.d_printfln "[transformation-plan]PROCEDURE: %a" Procname.pp proc_name ;
    L.d_printfln "[transformation-plan]STRATEGY: EVADE" ;
    L.d_printfln "[transformation-plan]ACTION: At the start of the function (node %d), insert an early return." (Procdesc.Node.get_id proc_start_node :> int);
    L.d_printfln "[transformation-plan]        Insert logic: if (%a == NULL) return;" Exp.pp pointer_expr;
    L.d_printfln "[transformation-plan]--------------------------"
| Replace {def_site_node; pvar; pvar_typ; reuse_info} ->
    let def_line = (Procdesc.Node.get_loc def_site_node).line in
    L.d_printfln "[transformation-plan]--- PULSE TRANSFORMATION PLAN ---" ;
    L.d_printfln "[transformation-plan]PROCEDURE: %a" Procname.pp proc_name ;
    L.d_printfln "[transformation-plan]STRATEGY: REPLACE" ;
    L.d_printfln "[transformation-plan]TARGET POINTER: %a" (Pvar.pp Pp.text) pvar;

    (* Option 1: Always show the "assign-fresh" strategy *)
    L.d_printfln "[transformation-plan]OPTION 1 (Assign Fresh):" ;
    L.d_printfln "[transformation-plan]  ACTION: At definition site on line %d, modify the assignment." def_line;
    L.d_printfln "[transformation-plan]          (Definition site is node %d)" (Procdesc.Node.get_id def_site_node :> int);
    L.d_printfln "[transformation-plan]          Transform '%a = NULL;' to 'if (%a == NULL) { %a = &fresh_var; }'"
      (Pvar.pp Pp.text) pvar (Pvar.pp Pp.text) pvar (Pvar.pp Pp.text) pvar;
    L.d_printfln "[transformation-plan]          (where fresh_var has type: %a)" (Typ.pp_full Pp.text) pvar_typ;

    (* Option 2: Conditionally show the "reuse-existing" strategy *)
    ( match reuse_info with
    | None -> ()
    | Some {reused_pvar} ->
        L.d_printfln "[transformation-plan]OPTION 2 (Reuse Existing):" ;
        L.d_printfln "[transformation-plan]  ACTION: At definition site on line %d, modify the assignment." def_line;
        L.d_printfln "[transformation-plan]          Transform '%a = NULL;' to 'if (%a == NULL) { %a = %a; }'"
            (Pvar.pp Pp.text) pvar (Pvar.pp Pp.text) pvar
            (Pvar.pp Pp.text) pvar (Pvar.pp Pp.text) reused_pvar;
        L.d_printfln "[transformation-plan]          (Reusing non-null local variable '%a')" (Pvar.pp Pp.text) reused_pvar;
    ) 
| NoPlanGenerated {reason; npe_location; pointer_expr_str} ->
  L.d_printfln "[transformation-plan]--- PULSE TRANSFORMATION PLAN ---" ;
  L.d_printfln "[transformation-plan]PROCEDURE: %a" Procname.pp proc_name ;
  L.d_printfln "[transformation-plan]STRATEGY: NO PLAN GENERATED" ;
  L.d_printfln "[transformation-plan]REASON: %s" reason ;
  L.d_printfln "[transformation-plan]ORIGINAL NPE LOCATION: %a" Location.pp npe_location ;
  L.d_printfln "[transformation-plan]ORIGINAL POINTER: %s" pointer_expr_str ;
  L.d_printfln "[transformation-plan]--------------------------"
  (* in *)

  (* After logging to the console, also save the structured plan to a file. *)
  (* save_plan_to_file proc_desc plan *)


(** The top-level entry point called by the Pulse reporting engine.
    This function orchestrates the entire transformation planning process:
    1. It performs a comprehensive alias analysis (both semantic and syntactic).
    2. It dispatches to the appropriate planner (`plan_replace_transformation` or `plan_skip_or_evade_transformation`)
       based on the `is_local` check.
    3. It logs any generated plans to the console, ensuring not to report duplicates. *)

(* Helper to define equality between two plans for deduplication *)
let equal_transformation_plan p1 p2 =
  match (p1, p2) with
  | Skip r1, Skip r2 -> Procdesc.Node.equal r1.lca_node r2.lca_node
  | Evade r1, Evade r2 -> Procdesc.Node.equal r1.proc_start_node r2.proc_start_node
  | Replace r1, Replace r2 -> Procdesc.Node.equal r1.def_site_node r2.def_site_node
  | _, _ -> false

let plan_and_log_if_unique ~proc_desc ~(bug : 'payload bug_info) =
  clear_cache_if_new_proc (Procdesc.get_proc_name proc_desc);

  (*
    Step 1: Perform the complete alias analysis ONCE, at the top level.
  *)

  (* Step 1a. Get the initial abstract value for the bug *)
  let av_opt =
    match bug.ptr_var with
    | None ->
        bug.av_opt
    | Some v ->
        get_ptr_address ~astate:bug.astate v
  in

  (* Step 1b. Compute the full set of aliased pointers. *)
  let all_ptrs_to_guard =
    let stack_aliases =
      match av_opt with
      | None -> []
      | Some av -> collect_stack_aliases bug.astate av
    in
    let initial_ptr = (bug.ptr_var |> Option.value_map ~f:Var.to_exp ~default:bug.ptr_expr) in
    let semantic_alias_exps = List.map stack_aliases ~f:snd in
    let seed_pointers = List.dedup_and_sort ~compare:Exp.compare (initial_ptr :: semantic_alias_exps) in
    (* Call the now top-level syntactic alias collector. *)
    find_syntactic_aliases proc_desc seed_pointers
  in
  L.d_printfln "[transformation-plan] Found %d total pointers in alias set." (List.length all_ptrs_to_guard);
  if List.is_empty all_ptrs_to_guard then
    L.d_printfln
      "[transformation-warning] Alias analysis found no pointers to guard for procedure %a. Aborting plan generation for this bug."
      Procname.pp (Procdesc.get_proc_name proc_desc)
  else (
    (*
      Step 2: Now that we have the complete alias set, dispatch to the correct planner.
    *)
    (* let plans : transformation_plan list =
      if is_local ~proc_desc ~bug all_ptrs_to_guard then (
        let replace_plans = plan_replace_transformation proc_desc bug all_ptrs_to_guard in
        if not (List.is_empty replace_plans) then replace_plans
        else (
          L.d_printfln "[transformation-plan] REPLACE planning failed. Falling back to SKIP/EVADE.";
          plan_skip_or_evade_transformation proc_desc bug all_ptrs_to_guard ) )
      else
        plan_skip_or_evade_transformation proc_desc bug all_ptrs_to_guard
    in *)

  (* Step 2: Generate plans OR a "NoPlanGenerated" reason. *)
  let final_plans : transformation_plan list =
    if List.is_empty all_ptrs_to_guard then (
      (* SCENARIO 1: Alias analysis found no pointers. *)
      L.d_printfln
        "[transformation-warning] Alias analysis found no pointers to guard for procedure %a. Logging as NoPlanGenerated."
        Procname.pp (Procdesc.get_proc_name proc_desc) ;
      [ NoPlanGenerated
          { reason= "Alias analysis found no pointers to guard."
          ; npe_location= Trace.get_start_location bug.diag_trace
          ; pointer_expr_str= Format.asprintf "%a" Exp.pp bug.ptr_expr } ] )
    else (
      (* Alias analysis succeeded, now run the actual planners. *)
      let generated_plans =
        if is_local ~proc_desc ~bug all_ptrs_to_guard then (
          let replace_plans = plan_replace_transformation proc_desc bug all_ptrs_to_guard in
          if not (List.is_empty replace_plans) then replace_plans
          else (
            L.d_printfln "[transformation-plan] REPLACE planning failed. Falling back to SKIP/EVADE." ;
            plan_skip_or_evade_transformation proc_desc bug all_ptrs_to_guard ) )
        else plan_skip_or_evade_transformation proc_desc bug all_ptrs_to_guard
      in

      if List.is_empty generated_plans then (
        (* SCENARIO 2: Planners ran but produced no plans (e.g., all sites guarded). *)
        L.d_printfln
          "[transformation-warning] Planners generated ZERO plans for procedure %a. Logging as NoPlanGenerated."
          Procname.pp (Procdesc.get_proc_name proc_desc) ;
        [ NoPlanGenerated
            { reason= "All potential crash sites were found to be already syntactically guarded."
            ; npe_location= Trace.get_start_location bug.diag_trace
            ; pointer_expr_str= Format.asprintf "%a" Exp.pp bug.ptr_expr } ] )
      else (* Success! We have one or more valid repair plans. *)
        generated_plans
    )
  in
    
    (* The rest of the function iterates through the generated list of plans. *)
    List.iter final_plans ~f:(fun plan ->
      if not (List.mem !logged_transformations_cache plan ~equal:equal_transformation_plan) then (
        L.d_printfln "[transformation] Found new unique plan.";
        report_transformation_plan proc_desc plan;
        logged_transformations_cache := plan :: !logged_transformations_cache
      )
    )
  )