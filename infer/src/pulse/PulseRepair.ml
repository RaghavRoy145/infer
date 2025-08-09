open! IStd
open Graph
open PulseBasicInterface
open PulseDomainInterface

module L = Logging
module CFG = ProcCfg.Normal

(* Use ocamlgraph's dominators functor to get the dominators *)
module GDoms = Dominator.Make (ProcCfg.MakeOcamlGraph (CFG))
(* bring in a set for Procdesc.Node.t *)
module NodeSet = Stdlib.Set.Make(struct
  type t = Procdesc.Node.t
  let compare = Procdesc.Node.compare
end)

module PostDominators = struct
  (* 1. Use the Exceptional CFG. Its type `t` will be a tuple. *)
  module ReversedCFG = ProcCfg.Backward (ProcCfg.Exceptional)

  (* 2. Adapt to the OcamlGraph interface. *)
  module ReversedOcamlGraph = ProcCfg.MakeOcamlGraph (ReversedCFG)

  (*
    3. Build the final adapter for the Dominators functor.
       THIS IS THE CRITICAL CHANGE. We now define the graph type `t` to be the
       actual tuple type from the exceptional graph.
  *)
  module DominatorGraph :
    Dominator.G with type t = ReversedOcamlGraph.t and type V.t = Procdesc.Node.t = struct
    (* The graph type `t` IS the tuple from ReversedOcamlGraph. *)
    type t = ReversedOcamlGraph.t
    module V = ReversedOcamlGraph.V

    (* These functions already correctly expect the tuple type. *)
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

  (* 4. Create the analysis module. It is now guaranteed to be consistent. *)
  module D = Dominator.Make (DominatorGraph)

  (* 5. Expose the compute function. *)
  let compute_idom = D.compute_idom
end

type 'payload bug_info = {
  ptr_expr   : Exp.t;
  ptr_var    : Var.t option;
  diag_trace : Trace.t;
  err_node   : Procdesc.Node.t;
  astate     : AbductiveDomain.t;
  analysis: ('payload) InterproceduralAnalysis.t;
  av_opt: AbstractValue.t option;
}

(** A simple “reanalyze this proc and return true if no bug” callback *)
type reanalyze = Procdesc.t -> bool

let node_uses_ptr (ptr:Exp.t) (node:Procdesc.Node.t) : bool =
  let instrs = Procdesc.Node.get_instrs node in
  Instrs.exists instrs ~f:(fun instr ->
    List.exists (Sil.exps_of_instr instr) ~f:(fun e ->
      Exp.equal (Exp.ignore_cast e) (Exp.ignore_cast ptr)))

let compute_dereference_slice pdesc ptr_exp =
  let deref_nodes = ref Procdesc.NodeSet.empty in
  Procdesc.iter_nodes
    (fun node ->
      let instrs = Procdesc.Node.get_instrs node in
      (* 1. ormatind all temporary variables (idents) that are loaded with the value of our pointer *)
      let idents_holding_pointer_value =
        Instrs.fold instrs ~init:Ident.Set.empty ~f:(fun acc instr ->
            match instr with
            | Sil.Load {id; e; _} when Exp.equal e ptr_exp ->
                Ident.Set.add id acc
            | _ ->
                acc )
      in
      (* 2. If we found any such temps, check if they are used as an address in a later instruction in THIS SAME NODE. *)
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
                (* This is a dereference. The address is a temp that holds our pointer's value. *)
                deref_nodes := Procdesc.NodeSet.add node !deref_nodes
            | _ ->
                () ) )
    pdesc ;
  Procdesc.NodeSet.elements !deref_nodes |> List.sort ~compare:Procdesc.Node.compare

(* 

let insert_skip_or_evade_guard pdesc ~guard_node ~ptr =
  (* Helper for detailed node logging *)
  let pp_node_summary_log title node =
    L.d_printfln "[repair-debug] %s: Node %a (preds: [%a], succs: [%a])" title Procdesc.Node.pp
      node
      (Pp.seq ~sep:", " Procdesc.Node.pp)
      (Procdesc.Node.get_preds node |> List.sort ~compare:Procdesc.Node.compare)
      (Pp.seq ~sep:", " Procdesc.Node.pp)
      (Procdesc.Node.get_succs node |> List.sort ~compare:Procdesc.Node.compare)
  in
  let loc = Procdesc.Node.get_loc guard_node in
  let pdesc_start_node = Procdesc.get_start_node pdesc in
  if Procdesc.Node.equal guard_node pdesc_start_node then (
    (* ... Evade logic ... *)
    L.d_printfln "[repair]: Applying EVADE pattern." ;
    true )
  else (
    L.d_printfln "[repair]: Applying final SKIP pattern for node %a." Procdesc.Node.pp guard_node ;
    let original_preds = Procdesc.Node.get_preds guard_node in
    if List.is_empty original_preds then (
      L.d_printfln "[repair]: Cannot guard a node with no predecessors. Aborting." ;
      false )
    else (
      (* --- BEFORE --- *)
      L.d_printfln "[repair-debug] --- STATE BEFORE REWIRING ---" ;
      pp_node_summary_log "[repair] TARGET (to be bypassed)" guard_node ;
      List.iteri original_preds ~f:(fun i p -> pp_node_summary_log (Printf.sprintf "[repair] PRED-%d" i) p) ;

      (* 1. Create a NEW node that contains the original, guarded instructions. *)
      let original_instrs_list =
        Procdesc.Node.get_instrs guard_node |> Instrs.get_underlying_not_reversed |> Array.to_list
      in
      let safe_node =
        Procdesc.create_node pdesc loc (Procdesc.Node.get_kind guard_node) original_instrs_list
      in
      
      (* 2. Create the rest of the diamond structure. *)
      let if_head_node =
        Procdesc.create_node pdesc loc (Skip_node "PulseRepair If-Head") []
      in
      let then_prune_node =
        Procdesc.create_node pdesc loc
          (Prune_node (true, Sil.Ik_if, PruneNodeKind_TrueBranch))
          [Sil.Prune (Exp.ne ptr Exp.null, loc, true, Sil.Ik_if)]
      in
      let else_prune_node =
        Procdesc.create_node pdesc loc
          (Prune_node (false, Sil.Ik_if, PruneNodeKind_FalseBranch))
          [Sil.Prune (Exp.eq ptr Exp.null, loc, false, Sil.Ik_if)]
      in
      let join_node = Procdesc.create_node pdesc loc Join_node [] in
      
      (* 3. Get original destinations and wire the new structure. *)
      let original_succs = Procdesc.Node.get_succs guard_node in
      let original_exn_succs = Procdesc.Node.get_exn guard_node in
      Procdesc.node_set_succs pdesc if_head_node ~normal:[then_prune_node; else_prune_node] ~exn:[] ;
      Procdesc.node_set_succs pdesc then_prune_node ~normal:[safe_node] ~exn:[] ;
      Procdesc.node_set_succs pdesc safe_node ~normal:[join_node] ~exn:original_exn_succs ;
      Procdesc.node_set_succs pdesc else_prune_node ~normal:[join_node] ~exn:[] ;
      Procdesc.node_set_succs pdesc join_node ~normal:original_succs ~exn:original_exn_succs ;
      
      (* 4. Redirect all incoming edges from the original predecessors to our new 'if_head_node'. *)
      List.iter original_preds ~f:(fun pred_node ->
          let normal_succs = Procdesc.Node.get_succs pred_node in
          let exn_succs = Procdesc.Node.get_exn pred_node in
          let new_normal_succs =
            List.map normal_succs ~f:(fun succ ->
                if Procdesc.Node.equal succ guard_node then if_head_node else succ )
          in
          let new_exn_succs =
            List.map exn_succs ~f:(fun succ ->
                if Procdesc.Node.equal succ guard_node then if_head_node else succ )
          in
          Procdesc.node_set_succs pdesc pred_node ~normal:new_normal_succs ~exn:new_exn_succs ) ;
      
      (* 5. DO NOT REMOVE the original node. It is now unreachable (dead code), which is safe. *)
      
      (* --- AFTER --- *)
      L.d_printfln "[repair-debug] --- STATE AFTER REWIRING ---" ;
      List.iteri original_preds ~f:(fun i p -> pp_node_summary_log (Printf.sprintf "[repair] PRED-%d" i) p) ;
      pp_node_summary_log "[repair] NEW IF-HEAD" if_head_node ;
      pp_node_summary_log "[repair] SAFE-NODE (replaces target)" safe_node ;
      pp_node_summary_log "[repair] NEW JOIN" join_node ;
      
      true )) *)

let verify_and_commit reanalyze pdesc =
  if reanalyze pdesc then true else false

(** 1. Stack aliases: normalize each local’s addr before comparing to [rep]. *)
let collect_stack_aliases
    (astate: AbductiveDomain.t)
    (rep_raw: AbstractValue.t)
  : (Var.t * Exp.t) list =
  (* 1. Canonicalize the abstract value of the pointer we are looking for. *)
  let canonical_rep_to_match =
    let canon_v = AbductiveDomain.CanonValue.canon' astate rep_raw in
    AbductiveDomain.CanonValue.downcast canon_v
  in
  (* 2. Fold over the ENTIRE abstract stack. *)
  AbductiveDomain.Stack.fold
    (fun stack_var value_origin acc ->

      let stack_av, _ = ValueOrigin.addr_hist value_origin in
      (* 3. For each variable on the stack, get its canonical representative. *)
      let current_var_canonical_rep =
        let canon_v = AbductiveDomain.CanonValue.canon' astate stack_av in
        AbductiveDomain.CanonValue.downcast canon_v
      in
      (* 4. If they match, we have found an alias. *)
      if PulseBasicInterface.AbstractValue.equal canonical_rep_to_match current_var_canonical_rep
      then (

        match Var.get_pvar stack_var with
        | Some pvar ->
            (stack_var, Exp.Lvar pvar) :: acc
        | None ->
            acc )
      else acc )
    astate []

(** Collect all heap aliases of [rep_raw] by walking the post‐heap graph. *)
let collect_heap_aliases
    (astate: AbductiveDomain.t)
    (rep_raw: AbstractValue.t)
  : AbstractValue.t list =
  (* Build a Seq.t of one element *)
  let seed_seq : AbstractValue.t Seq.t = Seq.cons rep_raw Seq.empty in
  (* reachable_addresses_from returns a AbstractValue.Set.t *)
  let raw_set : AbstractValue.Set.t =
    AbductiveDomain.reachable_addresses_from
      ~edge_filter:(fun _ -> true)
      seed_seq astate `Post
  in
  (* Convert the set to a list *)
  let raw_list : AbstractValue.t list = AbstractValue.Set.elements raw_set in
  (* Canonicalize and downcast each, then dedupe *)
  raw_list
  |> List.map ~f:(fun av_raw ->
       let can = AbductiveDomain.CanonValue.canon' astate av_raw in
       AbductiveDomain.CanonValue.downcast can )
  |> List.dedup_and_sort ~compare:AbstractValue.compare

(** Given the pointer Var.t that we recorded in bug.ptr_var, look up its
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

let is_dereference_of ~ptr instr =
  match (instr : Sil.instr) with
  | Load {e; _} when Exp.equal e ptr ->
      true
  | Store {e1; _} when Exp.equal e1 ptr ->
      true
  | _ ->
      false


let node_dereferences_ptr ptr node =
  Instrs.exists (Procdesc.Node.get_instrs node) ~f:(is_dereference_of ~ptr)    
  
(* let apply_skip_repair ~proc_desc ~(bug : 'payload bug_info) ~reanalyze =
  let pname = Procdesc.get_proc_name proc_desc in
  let loc = Procdesc.Node.get_loc bug.err_node in
  let start = Procdesc.get_start_node proc_desc in
  let idom = GDoms.compute_idom proc_desc start in

  let lca x y =
    let rec collect_ancestors n acc =
      let acc = Procdesc.NodeSet.add n acc in
      if Procdesc.Node.equal n start then acc else collect_ancestors (idom n) acc
    in
    let anc_x = collect_ancestors x Procdesc.NodeSet.empty in
    let rec climb m = if Procdesc.NodeSet.mem m anc_x then m else climb (idom m) in
    climb y
  in

  (* Re-instate the original logic for finding the pointer's own abstract value. *)
  let rep_opt =
    match bug.ptr_var with
    | None ->
        bug.av_opt
    | Some v -> (
      match AbductiveDomain.Stack.find_opt ~pre_or_post:`Post v bug.astate with
      | None ->
          None
      | Some vo ->
          let addr_raw, _hist = PulseValueOrigin.addr_hist vo in
          Some addr_raw )
  in
  let stack_aliases =
    match rep_opt with
    | None ->
        []
    | Some rep ->
        collect_stack_aliases ~proc:proc_desc bug.astate rep
  in
  Logging.d_printfln "[repair %a:%a] ptr=%a  stack_aliases=%d" Procname.pp pname Location.pp loc
    Exp.pp bug.ptr_expr (List.length stack_aliases) ;
  
  let all_ptrs_to_guard =
    let initial_ptr = (bug.ptr_var |> Option.value_map ~f:Var.to_exp ~default:bug.ptr_expr) in
    let alias_exps = List.map stack_aliases ~f:snd in
    List.dedup_and_sort ~compare:Exp.compare (initial_ptr :: alias_exps)
  in

  let lca_map =
    let lca_to_ptr_list =
      List.filter_map all_ptrs_to_guard ~f:(fun ptr_exp ->
          
      (* *** THIS IS THE FINAL, CORRECT SLICE LOGIC *** *)
      let slice =
        Procdesc.fold_nodes proc_desc ~init:Procdesc.NodeSet.empty ~f:(fun acc node ->
            let instrs = Procdesc.Node.get_instrs node in
            
            (* 1. Find all temporary variables (idents) loaded with our pointer's value in this node. *)
            let idents_holding_pointer =
              Instrs.fold instrs ~init:Ident.Set.empty ~f:(fun acc' instr ->
                  match instr with
                  | Sil.Load {id; e; _} when Exp.equal e ptr_exp -> Ident.Set.add id acc'
                  | _ -> acc' )
            in
            
            (* 2. A node is part of the slice if it contains an instruction that USES the pointer
               in a dangerous way, either directly or via a temporary variable. *)
            let node_has_usage =
              Instrs.exists instrs ~f:(fun instr ->
                  match instr with
                  (* Direct dereference of a temporary: *tmp *)
                  | Sil.Load {e=Exp.Var id; _}
                  | Sil.Store {e1=Exp.Var id; _} ->
                      Ident.Set.mem id idents_holding_pointer
                  
                  (* Call using the pointer, either directly or via a temporary *)
                  | Sil.Call (_, _, args, _, _) ->
                      List.exists args ~f:(fun (arg, _) ->
                          if Exp.equal arg ptr_exp then true (* Direct use: foo(p) *)
                          else
                            match arg with
                            | Exp.Var id -> Ident.Set.mem id idents_holding_pointer (* Indirect use: foo(tmp) *)
                            | _ -> false )
                  | _ -> false )
            in
            if node_has_usage then Procdesc.NodeSet.add node acc else acc )
        |> Procdesc.NodeSet.elements
      in
      let sanitized_slice =
        List.filter slice ~f:(fun node ->
            Procdesc.Node.equal node start || not (List.is_empty (Procdesc.Node.get_preds node)) )
      in
      match sanitized_slice with
      | [] -> None
      | first_node :: rest_nodes ->
          let lca_node = List.fold rest_nodes ~init:first_node ~f:lca in
          Logging.d_printfln "[repair] alias %a has %d sites in slice, guard at node %a"
            Exp.pp ptr_exp (List.length sanitized_slice) Procdesc.Node.pp lca_node ;
          Some (lca_node, ptr_exp) )
  in
  List.fold lca_to_ptr_list ~init:Procdesc.NodeMap.empty ~f:(fun map (key, data) ->
    let existing_data = Procdesc.NodeMap.find_opt key map |> Option.value ~default:[] in
    Procdesc.NodeMap.add key (data :: existing_data) map )
  in
  let repairs_applied =
    (* Use `bindings` to get a list of (key, value) pairs from the map *)
    Procdesc.NodeMap.bindings lca_map
    |> List.map ~f:(fun (guard_node, ptr_exps) ->
            (* If multiple aliases share an LCA, just use the first one for the guard condition. *)
            let ptr_for_guard = List.hd_exn ptr_exps in
            (* Use the smarter guard insertion logic *)
            insert_skip_or_evade_guard proc_desc ~guard_node ~ptr:ptr_for_guard )
  in
  (* ... your logging code ... *)
  if List.exists repairs_applied ~f:Fn.id then (
    Logging.d_printfln "[repair] At least one guard inserted, re-verifying..." ;

    let dump_guard_instrs guard_node =
      let instrs = Procdesc.Node.get_instrs guard_node in
      Instrs.iter instrs ~f:(fun instr ->
        match instr with
        | Sil.Prune _ ->
            Logging.d_printfln
              "[repair][guard] node %a:  %a"
              Procdesc.Node.pp guard_node
              (Sil.pp_instr ~print_types:false Pp.text)
              instr
        | _ ->
            () )
    in
    Logging.d_printfln "[repair] final SIL-CFG for %a:" Procname.pp (Procdesc.get_proc_name proc_desc) ;
    List.iter (Procdesc.get_nodes proc_desc) ~f:(fun node ->
      dump_guard_instrs node);

    if verify_and_commit reanalyze proc_desc then (
      Logging.d_printfln "[repair] Verification successful, dropping error." ;
      true )
    else (
      Logging.d_printfln "[repair] Verification FAILED, keeping original error." ;
      false ) )
  else (
    Logging.d_printfln "[repair] No guards could be inserted." ;
    false ) *)
  
      
let is_provably_local ~proc_desc ~(bug : 'payload bug_info) (all_aliases: Exp.t list) =
  let ptr_exp_str = Format.asprintf "%a" Exp.pp bug.ptr_expr in
  L.d_printfln "[repair-debug] is_provably_local: Checking alias set starting with %s" ptr_exp_str;

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
    L.d_printfln "[repair-debug] is_provably_local: Variable properties failed.";
    false )
  else
    (*
      This is the corrected check. We now iterate over NODES, not just instructions,
      so we have the context needed to link temp IDs to pointers.
    *)
    let has_call_usage =
      Procdesc.fold_nodes proc_desc ~init:false ~f:(fun acc node ->
          if acc then true (* Early exit *)
          else
            let instrs = Procdesc.Node.get_instrs node in

            (* 1. In this node, find all temp IDs that are loaded with one of our aliased pointers. *)
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
              (* 2. Now check if any of those IDs are used in a call instruction in this same node. *)
              Instrs.exists instrs ~f:(fun instr ->
                  match instr with
                  | Sil.Call (_, _, args, _, _) ->
                      List.exists args ~f:(fun (arg_exp, _) ->
                          match arg_exp with
                          | Exp.Var id -> Ident.Map.mem id idents_holding_aliases
                          | _ -> false )
                  | _ -> false ) )
    in
    L.d_printfln "[repair-debug] is_provably_local: has_call_usage=%b" has_call_usage;
    not has_call_usage

        

(* Helper 1: Find the last instruction that assigns to the pointer before a given node. *)
let find_last_def_site ~proc_desc ~ptr_var =
  let ptr_pvar_str = Pvar.to_string ptr_var in
  L.d_printfln "[repair-debug] find_last_def_site: Searching for definition of %s" ptr_pvar_str;

  (* 1. Find the actual node where the dereference happens to use as our anchor. *)
  let crashing_node_opt =
    compute_dereference_slice proc_desc (Exp.Lvar ptr_var) |> List.hd
  in
  match crashing_node_opt with
  | None ->
      L.d_printfln "[repair-debug] find_last_def_site: Could not find the crashing node!";
      None
  | Some crashing_node ->
      L.d_printfln "[repair-debug] find_last_def_site: Found crashing node %a" Procdesc.Node.pp
        crashing_node;
      
      (* 2. Build the dominator tree to check for correct ordering. *)
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
      
      (* 3. Find all nodes that contain a definition of our variable. *)
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
      L.d_printfln "[repair-debug] find_last_def_site: Found %d total definition nodes: [%a]"
        (List.length all_def_nodes) (Pp.seq ~sep:", " Procdesc.Node.pp) all_def_nodes;

      (* 4. Filter for valid sites: the definition must dominate the crash. *)
      let valid_sites =
        List.filter all_def_nodes ~f:(fun node ->
            let is_dominator = dominates node crashing_node in
            L.d_printfln
              "[repair-debug] find_last_def_site: Candidate node %a. Dominates crash site? %b"
              Procdesc.Node.pp node is_dominator;
            is_dominator )
      in
      L.d_printfln "[repair-debug] find_last_def_site: Found %d valid sites that dominate the crash."
        (List.length valid_sites);
      
      (* 5. Of the valid dominators, pick the one that is "closest" to the crash site.
         This is the one that is dominated by all the others. *)
      let result =
        List.max_elt valid_sites ~compare:(fun n1 n2 ->
            if dominates n1 n2 then -1 else if dominates n2 n1 then 1 else 0 )
      in
      ( match result with
      | Some n ->
          L.d_printfln "[repair-debug] find_last_def_site: Selected best site: %a" Procdesc.Node.pp n
      | None ->
          L.d_printfln "[repair-debug] find_last_def_site: No suitable definition site found." );
      result

(* Helper 2: Insert the rebinding logic for the "fresh allocation" case. *)
(* let insert_rebind_fresh proc_desc ~def_node ~ptr_pvar =
  let loc = Procdesc.Node.get_loc def_node in
  let pname = Procdesc.get_proc_name proc_desc in
  
  (* 1. Create a new stack variable to hold our safe, default-initialized value. *)
  let new_pvar_name = Mangled.from_string ("pulsex_fresh_" ^ Pvar.get_simplified_name ptr_pvar) in
  let new_pvar = Pvar.mk new_pvar_name pname in
  let ptr_typ =
    (Procdesc.get_locals proc_desc |> List.find ~f:(fun v -> Mangled.equal v.ProcAttributes.name (Pvar.get_name ptr_pvar)))
    |> Option.value_map ~f:(fun v -> v.ProcAttributes.typ) ~default:(Typ.mk Tvoid)
  in
  let new_var_data =
    { ProcAttributes.name= new_pvar_name
    ; typ= ptr_typ
    ; modify_in_block= false
    ; is_constexpr= false
    ; is_declared_unused= false
    (* Add the missing fields with default values *)
    ; is_structured_binding= false
    ; has_cleanup_attribute= false
    ; tmp_id= None }
  in
  Procdesc.append_locals proc_desc [new_var_data] ;
  
  (* 2. Create the SIL instructions for: if (p == NULL) { p = &new_var; } *)
  let fresh_var_exp = Exp.Lvar new_pvar in
  let ptr_exp = Exp.Lvar ptr_pvar in
  
  let prune_instr = Sil.Prune (Exp.eq ptr_exp Exp.null, loc, true, Sil.Ik_if) in
  let rebind_instr = Sil.Store {e1=ptr_exp; typ=ptr_typ; e2=fresh_var_exp; loc} in

  (* 3. Prepend these instructions to the definition node. *)
  Procdesc.Node.prepend_instrs def_node [rebind_instr; prune_instr] ;
  true

(* The main function for the Replace strategy. *)
let apply_replace_repair ~proc_desc ~bug ~reanalyze =
  match bug.ptr_var with
  | None -> false
  | Some v -> (
    match Var.get_pvar v with
    | None -> false
    | Some ptr_pvar -> (
      match find_last_def_site ~proc_desc ~ptr_var:ptr_pvar with
      | None ->
          L.d_printfln "[repair] REPLACE: Could not find definition site for %a. Aborting." Var.pp v;
          false
      | Some def_node ->
          L.d_printfln "[repair] REPLACE: Found definition site for %a at node %a." Var.pp v
            Procdesc.Node.pp def_node;
          if insert_rebind_fresh proc_desc ~def_node ~ptr_pvar then (
            L.d_printfln "[repair] REPLACE: Insertion successful. Re-verifying...";
            let verified = verify_and_commit reanalyze proc_desc in
            if not verified then
              L.d_printfln "[repair] REPLACE: Verification FAILED (as expected without multi-stage pipeline).";
            verified )
          else false ) ) *)
(* 
let try_repair ~proc_desc ~(bug : 'payload bug_info) ~reanalyze =
  if is_provably_local ~proc_desc ~bug then (
    L.d_printfln "[repair] Pointer %a is local. Attempting REPLACE repair." Exp.pp bug.ptr_expr ;
    if apply_replace_repair ~proc_desc ~bug ~reanalyze then true
    else (
      L.d_printfln "[repair] REPLACE failed. Falling back to SKIP repair." ;
      apply_skip_repair ~proc_desc ~bug ~reanalyze ) )
  else (
    L.d_printfln "[repair] Pointer %a is not local. Applying SKIP repair." Exp.pp bug.ptr_expr ;
    apply_skip_repair ~proc_desc ~bug ~reanalyze 
  ) *)
type reuse_candidate = {
    reused_pvar: Pvar.t; (* The variable to reuse, e.g., 'q' *)
  }
type repair_plan =
| Skip of {
    lca_node : Procdesc.Node.t;
    join_node : Procdesc.Node.t; (* Add this field *)
    pointer_exprs : Exp.t list;
    slice_nodes : Procdesc.Node.t list;
  }
| Evade of {
    proc_start_node: Procdesc.Node.t;
    pointer_expr: Exp.t;
  }
  | Replace of
      { def_site_node: Procdesc.Node.t
      ; pvar: Pvar.t
      ; pvar_typ: Typ.t
      ; reuse_info: reuse_candidate option
      ; all_aliases: Exp.t list (* Add this field *) }

let logged_repairs_cache : repair_plan list ref = ref []
let last_proc_name = ref (Procname.from_string_c_fun "")
(* This function clears the cache when we start a new procedure *)
let clear_cache_if_new_proc (current_proc_name : Procname.t) =
  if not (Procname.equal !last_proc_name current_proc_name) then (
    L.d_printfln "[repair] New procedure %a, clearing repair cache." Procname.pp current_proc_name;
    (* Just reset the list to empty *)
    logged_repairs_cache := [];
    last_proc_name := current_proc_name
  )

let report_repair_plan proc_desc plan =
  let proc_name = Procdesc.get_proc_name proc_desc in
  match plan with
  | Skip {lca_node; join_node; pointer_exprs; _} ->
      let guard_ptr_expr = List.hd_exn pointer_exprs in
      (* Get the line numbers from the calculated scope boundaries. *)
      let line1 = (Procdesc.Node.get_loc lca_node).line in
      let line2 = (Procdesc.Node.get_loc join_node).line in
      let start_line = min line1 line2 in
      let end_line = max line1 line2 in

      L.d_printfln "[repair-plan]--- PULSE REPAIR PLAN ---" ;
      L.d_printfln "[repair-plan]PROCEDURE: %a" Procname.pp proc_name ;
      L.d_printfln "[repair-plan]STRATEGY: SKIP" ;
      L.d_printfln "[repair-plan]ACTION: Guard the code block from line ~%d to ~%d."
        start_line end_line;
      L.d_printfln "[repair-plan]        (Scope starts at node %d and ends at node %d)"
        (Procdesc.Node.get_id lca_node :> int) (Procdesc.Node.get_id join_node :> int);
      L.d_printfln "[repair-plan]        with the condition: if (%a != NULL) { ... }" Exp.pp guard_ptr_expr;
      L.d_printfln "[repair-plan]        This guard protects pointers: [%a]" (Pp.seq ~sep:", " Exp.pp) pointer_exprs;
      L.d_printfln "[repair-plan]--------------------------"

| Evade {proc_start_node; pointer_expr} ->
    L.d_printfln "[repair-plan]--- PULSE REPAIR PLAN ---" ;
    L.d_printfln "[repair-plan]PROCEDURE: %a" Procname.pp proc_name ;
    L.d_printfln "[repair-plan]STRATEGY: EVADE" ;
    L.d_printfln "[repair-plan]ACTION: At the start of the function (node %d), insert an early return." (Procdesc.Node.get_id proc_start_node :> int);
    L.d_printfln "[repair-plan]        Insert logic: if (%a == NULL) return;" Exp.pp pointer_expr;
    L.d_printfln "[repair-plan]--------------------------"
| Replace {def_site_node; pvar; pvar_typ; reuse_info} ->
    let def_line = (Procdesc.Node.get_loc def_site_node).line in
    L.d_printfln "[repair-plan]--- PULSE REPAIR PLAN ---" ;
    L.d_printfln "[repair-plan]PROCEDURE: %a" Procname.pp proc_name ;
    L.d_printfln "[repair-plan]STRATEGY: REPLACE" ;
    L.d_printfln "[repair-plan]TARGET POINTER: %a" (Pvar.pp Pp.text) pvar;

    (* Option 1: Always show the "assign-fresh" strategy *)
    L.d_printfln "[repair-plan]OPTION 1 (Assign Fresh):" ;
    L.d_printfln "[repair-plan]  ACTION: At definition site on line %d, modify the assignment." def_line;
    L.d_printfln "[repair-plan]          (Definition site is node %d)" (Procdesc.Node.get_id def_site_node :> int);
    L.d_printfln "[repair-plan]          Transform '%a = NULL;' to 'if (%a == NULL) { %a = &fresh_var; }'"
      (Pvar.pp Pp.text) pvar (Pvar.pp Pp.text) pvar (Pvar.pp Pp.text) pvar;
    L.d_printfln "[repair-plan]          (where fresh_var has type: %a)" (Typ.pp_full Pp.text) pvar_typ;

    (* Option 2: Conditionally show the "reuse-existing" strategy *)
    ( match reuse_info with
    | None -> ()
    | Some {reused_pvar} ->
        L.d_printfln "[repair-plan]OPTION 2 (Reuse Existing):" ;
        L.d_printfln "[repair-plan]  ACTION: At definition site on line %d, modify the assignment." def_line;
        L.d_printfln "[repair-plan]          Transform '%a = NULL;' to 'if (%a == NULL) { %a = %a; }'"
            (Pvar.pp Pp.text) pvar (Pvar.pp Pp.text) pvar
            (Pvar.pp Pp.text) pvar (Pvar.pp Pp.text) reused_pvar;
        L.d_printfln "[repair-plan]          (Reusing provably non-null local variable '%a')" (Pvar.pp Pp.text) reused_pvar;
    ) ;
    L.d_printfln "[repair-plan]--------------------------"

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
  (* Step 3: Find the transitive closure (all connected aliases) for our initial pointers. *)
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

let plan_skip_or_evade_repair proc_desc (bug : 'payload bug_info) all_ptrs_to_guard: repair_plan list =
  (* let pname = Procdesc.get_proc_name proc_desc in *)
  let start = Procdesc.get_start_node proc_desc in
  let idom = GDoms.compute_idom proc_desc start in
  let compute_ipdom proc_desc =
    let exit_node = Procdesc.get_exit_node proc_desc in
    (*
      `from_pdesc` from the Exceptional CFG view creates the required tuple
      of `(Procdesc.t * exceptional_edge_map)`. This is the graph instance.
    *)
    let reversed_graph_instance = PostDominators.ReversedCFG.from_pdesc proc_desc in
    PostDominators.compute_idom reversed_graph_instance exit_node
  in
  let ipdom_fun = lazy (compute_ipdom proc_desc) in


  let lca x y =
    let rec collect_ancestors n acc =
      let acc' = Procdesc.NodeSet.add n acc in
      if Procdesc.Node.equal n start then acc' else collect_ancestors (idom n) acc'
    in
    let anc_x = collect_ancestors x Procdesc.NodeSet.empty in
    let rec climb m = if Procdesc.NodeSet.mem m anc_x then m else climb (idom m) in
    climb y
  in

  (* Checks if `node` is dominated by `dominator`. *)
  let is_dominated_by ~dominator ~node =
    let rec climb current =
      if Procdesc.Node.equal current dominator then true
      else
        (*
          We wrap the call to `idom` in a try-with block. If the node `current`
          is not in the dominator tree (e.g., it's in dead code), this will
          prevent the crash and correctly stop the climb.
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
  in


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
  
  L.d_printfln "[repair-plan] ptr=%a, stack_aliases=%d" Exp.pp bug.ptr_expr (List.length stack_aliases);

    (* Step 1: UNIFY the slice for the ENTIRE alias set first. *)

  L.d_printfln "[repair-log] >>> Starting plan_skip_or_evade_repair for %a" Procname.pp
  (Procdesc.get_proc_name proc_desc) ;
  L.d_printfln "[repair-log] Initial `all_ptrs_to_guard` list: [%a]" (Pp.seq ~sep:", " Exp.pp)
    all_ptrs_to_guard ;

  (* This is the new, correct implementation that understands SIL's two-step dereference. *)
  let get_proven_crash_nodes ptr_exp =
    L.d_printfln "\n[repair-log] >> Running get_proven_crash_nodes for pointer: %a" Exp.pp ptr_exp ;
    let result_nodes =
      Procdesc.fold_nodes proc_desc ~init:[] ~f:(fun acc node ->
          let instrs = Procdesc.Node.get_instrs node in
          let node_loc = Procdesc.Node.get_loc node in
          (* L.d_printfln "[repair-log]    Scanning Node %a (C line %d)..." Procdesc.Node.pp node
            node_loc.line ; *)

          (* Step 1: Find all temporary identifiers that hold the value of our pointer. *)
          let idents_holding_pointer_value =
            Instrs.fold instrs ~init:Ident.Set.empty ~f:(fun idents_acc instr ->
                match instr with
                | Sil.Load {id; e; _} when Exp.equal e ptr_exp ->
                    L.d_printfln "[repair-log]      Found temp ident %a loading our pointer." Ident.pp
                      id ;
                    Ident.Set.add id idents_acc
                | _ ->
                    idents_acc )
          in

          (* If we didn't load the pointer in this node, it can't be dereferenced here. *)
          if Ident.Set.is_empty idents_holding_pointer_value then acc
          else (
            (* Step 2: Now, find where those identifiers are used as addresses. THIS is the dereference. *)
            let has_dereference =
              Instrs.exists instrs ~f:(fun instr ->
                  match instr with
                  (* Dereference READ: x = *p (translated as x = Load(id)) *)
                  | Sil.Load {e= Exp.Var id; _}
                    when Ident.Set.mem id idents_holding_pointer_value ->
                      L.d_printfln "[repair-log]      !!! Found DEREFERENCE (Load) of temp ident %a."
                        Ident.pp id ;
                      true
                  (* Dereference WRITE: *p = x (translated as Store(id, x)) *)
                  | Sil.Store {e1= Exp.Var id; _}
                    when Ident.Set.mem id idents_holding_pointer_value ->
                      L.d_printfln "[repair-log]      !!! Found DEREFERENCE (Store) of temp ident %a."
                        Ident.pp id ;
                      true
                  | _ ->
                      false )
            in
            if has_dereference then (
              L.d_printfln "[repair-log]    >>> Node %a (C line %d) MARKED as a crash site."
                Procdesc.Node.pp node node_loc.line ;
              node :: acc )
            else acc ) )
    in
    L.d_printfln "[repair-log] << Finished get_proven_crash_nodes for %a. Found %d crash nodes."
      Exp.pp ptr_exp (List.length result_nodes) ;
    result_nodes
  in
  (*********************************************************************************)
  (* Stage 1: Cluster by Control-Flow Proximity                                  *)
  (*********************************************************************************)
  let ptr_to_crashes_map =
    List.map all_ptrs_to_guard ~f:(fun ptr -> (ptr, get_proven_crash_nodes ptr))
    |> List.filter ~f:(fun (_, crashes) -> not (List.is_empty crashes))
  in

  L.d_printfln "\n[repair-log] STEP 1.1: Mapped each pointer to its proven crash sites." ;
  List.iter ptr_to_crashes_map ~f:(fun (ptr, nodes) ->
      let node_locs = List.map nodes ~f:(fun n -> (Procdesc.Node.get_loc n).line) in
      L.d_printfln "[repair-log]   Pointer %a has %d crash site(s) at C file line(s): [%a]" Exp.pp
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

  L.d_printfln "\n[repair-log] STEP 1.2: Clustered pointers by the LCA of their crash sites." ;
  Procdesc.NodeMap.iter
    (fun lca_node ptrs_in_cluster ->
      let lca_loc = Procdesc.Node.get_loc lca_node in
      L.d_printfln
        "[repair-log]   Cluster at LCA node %a (line %d) contains %d pointer(s): [%a]"
        Procdesc.Node.pp lca_node lca_loc.line (List.length ptrs_in_cluster)
        (Pp.seq ~sep:", " Exp.pp) ptrs_in_cluster )
    lca_map ;
  

  (* This helper correctly identifies the single node designated as the final crash site by the trace. *)
  let is_the_final_crash_site (node : Procdesc.Node.t) (trace : Trace.t) : bool =
      let node_loc = Procdesc.Node.get_loc node in
      let get_immediate_crash_location = function
        | Trace.Immediate {location; _} -> Some location
        | Trace.ViaCall {location; _} -> Some location (* Corrected based on your structure *)
      in
      match get_immediate_crash_location trace with
      | None -> false
      | Some final_crash_loc -> Location.equal node_loc final_crash_loc
  in
  
  (*********************************************************************************)
  (* Stage 1: Seed the Compaction Algorithm (Hybrid Approach)                    *)
  (*********************************************************************************)

  let unified_crash_slice =
    match bug.diag_trace with
    | Trace.ViaCall {location= crash_loc; _} ->
        (* INTER-PROCEDURAL CASE: The crash is the call site itself. No syntactic search needed. *)
        L.d_printfln "[repair-log]   Trace is ViaCall. The crash site is the call location.";
        List.filter (Procdesc.get_nodes proc_desc) ~f:(fun node ->
            Location.equal (Procdesc.Node.get_loc node) crash_loc )

    | Trace.Immediate _ ->
        (* INTRA-PROCEDURAL CASE: The crash is the union of all syntactic dereferences
            of all aliases, filtered to remove any non-crashing nodes. *)
        L.d_printfln "[repair-log]   Trace is Immediate. Unifying all syntactic dereferences.";
        let all_syntactic_dereferences =
          List.concat_map all_ptrs_to_guard ~f:get_proven_crash_nodes
        in
        (* In the multi-alias case, the trace only blames one site. We must keep all
            syntactic sites for the other aliases. A simple union is the most robust approach. *)
        let final_crash_node =
          List.find all_syntactic_dereferences ~f:(fun node -> is_the_final_crash_site node bug.diag_trace)
        in
        List.dedup_and_sort ~compare:Procdesc.Node.compare
          (Option.to_list final_crash_node @ all_syntactic_dereferences)
  in
  
  L.d_printfln "\n[repair-log] STAGE 1.1: Found a unified slice of %d proven crash node(s)."
    (List.length unified_crash_slice);


  (* Step 4: Generate a separate, minimal repair plan for each cluster found in the map *)
    let is_post_dominated_by ~pdominator ~node ipdom_fun =
      let ipdom_fun = Lazy.force ipdom_fun in
      let rec climb current =
        if Procdesc.Node.equal current pdominator then true
        else
          let parent = try ipdom_fun current with _ -> current in
          if Procdesc.Node.equal parent current then false else climb parent
      in
      climb node
    in

    let find_minimal_scope (slice : Procdesc.Node.t list) ipdom_fun =
      let slice_locs = List.map slice ~f:(fun n -> (Procdesc.Node.get_loc n).line) in
      L.d_printfln "[repair-scope] >> find_minimal_scope for slice with %d node(s) at C lines: [%a]"
        (List.length slice) (Pp.seq ~sep:", " Int.pp) slice_locs;

      let lca_of_slice, lcpd_of_slice =
        match slice with
        | [] ->
            L.d_printfln "[repair-scope]    - Case: Empty slice. Returning procedure boundaries.";
            (Procdesc.get_start_node proc_desc, Procdesc.get_exit_node proc_desc)
        | first :: rest ->
            L.d_printfln "[repair-scope]    - Case: Non-empty slice. Calculating overall LCA and LCPD.";
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
                       is_dominated_by ~dominator:then_branch_start ~node:slice_node ) ->
                L.d_printfln "[repair-scope]    - Adjusting start node from Prune node.";
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
                  (* let ipdom = Lazy.force ipdom_fun in *)

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

      L.d_printfln "[repair-scope] << Returning final scope: start node %a (line %d), end node %a (line %d)"
        Procdesc.Node.pp start_node (Procdesc.Node.get_loc start_node).line
        Procdesc.Node.pp end_node (Procdesc.Node.get_loc end_node).line;

      (start_node, end_node)
    in
    (* This new helper guarantees that the first element of the pair is the dominator. *)
    let normalize_scope (node1, node2) =
      if is_dominated_by ~dominator:node1 ~node:node2 then (node1, node2) else (node2, node1)
    in

    let is_strictly_contained_within scope1_raw scope2_raw =
      let start1, end1 = normalize_scope scope1_raw in
      let start2, end2 = normalize_scope scope2_raw in
      if Procdesc.Node.equal start1 start2 && Procdesc.Node.equal end1 end2 then false
      else
        is_dominated_by ~dominator:start1 ~node:start2
        && is_post_dominated_by ~pdominator:end1 ~node:end2 ipdom_fun
    in
          
    let should_merge_scopes all_aliases scope1_raw scope2_raw =
      let s1_loc, e1_loc = ((Procdesc.Node.get_loc (fst scope1_raw)).line, (Procdesc.Node.get_loc (snd scope1_raw)).line) in
      let s2_loc, e2_loc = ((Procdesc.Node.get_loc (fst scope2_raw)).line, (Procdesc.Node.get_loc (snd scope2_raw)).line) in
      L.d_printfln "\n[repair-merge-check] >> Checking if scopes [lines ~%d-%d] and [~%d-%d] should merge."
        (min s1_loc e1_loc) (max s1_loc e1_loc) (min s2_loc e2_loc) (max s2_loc e2_loc);

      let s1, e1 = normalize_scope scope1_raw in
      let s2, e2 = normalize_scope scope2_raw in

      (* Condition 1: Partial Overlap *)
      let partial_overlap =
        (is_dominated_by ~dominator:s1 ~node:s2 && is_post_dominated_by ~pdominator:e1 ~node:s2 ipdom_fun)
        || (is_dominated_by ~dominator:s2 ~node:s1 && is_post_dominated_by ~pdominator:e2 ~node:s1 ipdom_fun)
      in
      L.d_printfln "[repair-merge-check]    - Partial overlap? %b" partial_overlap;

      (* Helper to find external side effects *)
      let has_external_side_effects (instr : Sil.instr) =
        match instr with
        (* | Prune _ | Metadata _ -> None | Load _ -> None *)
        | Prune _ | Metadata _ -> None
        | Load {e; _} | Store {e1= e; _} ->
          (* A load or store is an external side effect ONLY if the address `e`
             is NOT one of the pointers we are explicitly trying to guard.
             If it *is* one of our pointers, it's part of the buggy behavior we want to skip. *)
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
        L.d_printfln "[repair-merge-check]      - Checking for benign path from node %a to node %a."
          Procdesc.Node.pp from_node Procdesc.Node.pp to_node;
        let all_proc_nodes = Procdesc.get_nodes proc_desc in
        let nodes_between =
          List.filter all_proc_nodes ~f:(fun n ->
            not (Procdesc.Node.equal n from_node) && not (Procdesc.Node.equal n to_node) &&
            is_dominated_by ~dominator:from_node ~node:n && is_post_dominated_by ~pdominator:to_node ~node:n ipdom_fun
          )
        in
        L.d_printfln "[repair-merge-check]      - Found %d node(s) between the two scopes." (List.length nodes_between);
        
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
            L.d_printfln "[repair-merge-check]      - Path NOT benign. Found external side-effect in node %a: %a"
              Procdesc.Node.pp node (Sil.pp_instr ~print_types:false Pp.text) instr;
            false
        | None ->
            L.d_printfln "[repair-merge-check]      - Path is benign. No external side-effects found between scopes.";
            true
      in

      (* Condition 2: Principled Adjacency (Sequentiality). *)
      let are_sequential =
        L.d_printfln "[repair-merge-check]    - Checking for sequentiality...";
        if is_dominated_by ~dominator:e1 ~node:s2 then
          is_path_benign ~from_node:e1 ~to_node:s2
        else if is_dominated_by ~dominator:e2 ~node:s1 then
          is_path_benign ~from_node:e2 ~to_node:s1
        else false
      in
      L.d_printfln "[repair-merge-check]    - Are sequential? %b" are_sequential;

      let result = partial_overlap || are_sequential in
      L.d_printfln "[repair-merge-check] << Should merge? %b" result;
      result
    in

  let merge_plans (plan1 : repair_plan) (plan2 : repair_plan) ipdom_fun : repair_plan =
    match (plan1, plan2) with
    | ( Skip {lca_node=s1; join_node=e1; pointer_exprs=p1; slice_nodes=n1}
      , Skip {lca_node=s2; join_node=e2; pointer_exprs=p2; slice_nodes=n2} ) ->
        let s1_loc, e1_loc = ((Procdesc.Node.get_loc s1).line, (Procdesc.Node.get_loc e1).line) in
        let s2_loc, e2_loc = ((Procdesc.Node.get_loc s2).line, (Procdesc.Node.get_loc e2).line) in
        L.d_printfln "\n[repair-merge] >> Attempting to merge plan [lines %d-%d] with plan [lines %d-%d]"
          (min s1_loc e1_loc) (max s1_loc e1_loc) (min s2_loc e2_loc) (max s2_loc e2_loc);

        let new_slice = List.dedup_and_sort ~compare:Procdesc.Node.compare (n1 @ n2) in
        let new_pointers = List.dedup_and_sort ~compare:Exp.compare (p1 @ p2) in
        
        (*
          Step 1: Calculate the initial merged scope from the UNION of crash sites, not the old boundaries.
        *)
        let initial_lca = lca s1 s2 in

        (* The new join node is the one that is post-dominated by the other (i.e., the "latest" join). *)
        let new_join =
          L.d_printfln "[repair-merge-join] -- Deciding join node between e1=%a (line %d) and e2=%a (line %d)"
            Procdesc.Node.pp e1 (Procdesc.Node.get_loc e1).line
            Procdesc.Node.pp e2 (Procdesc.Node.get_loc e2).line;

          let e1_postdoms_e2 = is_post_dominated_by ~pdominator:e1 ~node:e2 ipdom_fun in
          L.d_printfln "[repair-merge-join]    - Does e1 post-dominate e2? %b" e1_postdoms_e2;

          let e2_postdoms_e1 = is_post_dominated_by ~pdominator:e2 ~node:e1 ipdom_fun in
          L.d_printfln "[repair-merge-join]    - Does e2 post-dominate e1? %b" e2_postdoms_e1;

          if e1_postdoms_e2 then (
            L.d_printfln "[repair-merge-join]    - Decision: e1 is the latest join. Using e1.";
            e1 )
          else if e2_postdoms_e1 then (
            L.d_printfln "[repair-merge-join]    - Decision: e2 is the latest join. Using e2.";
            e2 )
            (*COULD BE A POTENTIAL PROBLEM*) 
          else (* Fallback: Parallel branches. The true join is the IPDOM of the LCPD. *)
          (
            let lcpd_node = lcpd (Lazy.force ipdom_fun) e1 e2 in
            L.d_printfln "[repair-merge-join]    - Fallback: Nodes are in parallel branches." ;
            L.d_printfln "[repair-merge-join]    - Earliest rejoin point (LCPD) is node %a (line %d)."
              Procdesc.Node.pp lcpd_node
              (Procdesc.Node.get_loc lcpd_node).line ;
            
            let ipdom = Lazy.force ipdom_fun in
            let final_join_node = ipdom lcpd_node in

            L.d_printfln
              "[repair-merge-join]    - The true join is the IPDOM of the LCPD. Result is node %a (line %d)."
              Procdesc.Node.pp final_join_node
              (Procdesc.Node.get_loc final_join_node).line ;
            final_join_node
          )
        in

        L.d_printfln "[repair-merge]    - Initial merged scope from old boundaries: LCA node %a, Join node %a"
          Procdesc.Node.pp initial_lca Procdesc.Node.pp new_join;
        (*
          Step 2: The existing, correct data-flow-awareness logic now runs on a sound initial scope.
        *)
        let is_inside_scope node =
          is_dominated_by ~dominator:initial_lca ~node
          && is_post_dominated_by ~pdominator:new_join ~node ipdom_fun
        in
        let trapped_decls =
          Procdesc.fold_instrs proc_desc ~init:[] ~f:(fun acc node instr ->
            if is_inside_scope node then
              match instr with
              | Sil.Store {e1=Exp.Lvar pvar; _} when Pvar.is_local pvar ->
                  (* Find the FIRST time this local is assigned. *)
                  if not (List.exists acc ~f:(Pvar.equal pvar)) then (
                    L.d_printfln "[repair-merge]    - Found trapped local variable declaration: %a in node %a"                           
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
                L.d_printfln "[repair-merge]    - WARNING: Could not find decl node for %a. This should not happen."
                  (Pvar.pp Pp.text) pvar;
                current_lca
            | Some decl_node ->
                L.d_printfln "[repair-merge]    - Declaration of %a is at node %a. Recalculating LCA."
                  (Pvar.pp Pp.text) pvar Procdesc.Node.pp decl_node;
                lca current_lca decl_node
          )
        in
        let new_lca = earliest_decl_node in

        if not (Procdesc.Node.equal new_lca new_lca) then
          L.d_printfln "[repair-merge]    - Scope expanded! New LCA is node %a (line %d) to include declarations."
            Procdesc.Node.pp new_lca (Procdesc.Node.get_loc new_lca).line;
        
        L.d_printfln "[repair-merge] << Finished merge. Final scope: [%a -> %a]"
          Procdesc.Node.pp new_lca Procdesc.Node.pp new_join;

        Skip {lca_node=new_lca; join_node=new_join; pointer_exprs=new_pointers; slice_nodes=new_slice}
    | _ -> plan1
        in

    let candidate_plans =
      List.filter_map unified_crash_slice ~f:(fun crash_node ->
          let slice_for_this_node = [crash_node] in
          let start_node, end_node = find_minimal_scope slice_for_this_node ipdom_fun in
          
          L.d_printfln "\n[repair-log] STAGE 1.2: Generating candidate plan for single crash node at line %d..."
            (Procdesc.Node.get_loc crash_node).line;
          L.d_printfln "[repair-log]   - Calculated minimal scope: start node %a (line %d), end node %a (line %d)"
              Procdesc.Node.pp start_node (Procdesc.Node.get_loc start_node).line
              Procdesc.Node.pp end_node (Procdesc.Node.get_loc end_node).line;
  
          if Procdesc.Node.equal start_node start then
            Some (Evade {proc_start_node= start; pointer_expr= List.hd_exn all_ptrs_to_guard})
          else
            Some
              (Skip
                  { lca_node= start_node
                  ; join_node= end_node
                  ; pointer_exprs= all_ptrs_to_guard
                  ; slice_nodes= slice_for_this_node } ) )
    in
  (*********************************************************************************)
  (* Stage 2 & 3: Filter and Merge                             *)
  (*********************************************************************************)
  L.d_printfln "\n[repair-log] STEP 2: Filtering %d candidate plan(s)." (List.length candidate_plans);
  let filtered_plans =
    List.filter candidate_plans ~f:(fun current_plan ->
        let is_enveloped =
          List.exists candidate_plans ~f:(fun other_plan ->
              if phys_equal current_plan other_plan then false
              else
                match (current_plan, other_plan) with
                | ( Skip {lca_node= s_curr; join_node= e_curr; _}
                  , Skip {lca_node= s_other; join_node= e_other; _} ) ->
                    (* CORRECTED CALL: Pass scopes as two separate arguments *)
                    is_strictly_contained_within (s_other, e_other) (s_curr, e_curr)
                | _ ->
                    false )
        in
        if is_enveloped then L.d_printfln "[repair-log]   Filtering one enveloped plan.";
        not is_enveloped )
  in

  L.d_printfln "\n[repair-log] STEP 3: Merging %d filtered plan(s) using a fixed-point algorithm." (List.length filtered_plans);
  
  let final_plans =
    let rec merge_fixed_point plans_to_merge =
      let rec find_and_merge_pair worklist acc =
        match worklist with
        | [] -> None (* No merge found in this pass *)
        | current_plan :: rest ->
            let found_merge =
              List.find_map rest ~f:(fun other_plan ->
                match (current_plan, other_plan) with
                | (Skip {lca_node=s1; join_node=e1; _}, Skip {lca_node=s2; join_node=e2; _}) ->
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
          L.d_printfln "[repair-log]   - Fixed-point reached. No more merges possible.";
          plans_to_merge
      | Some new_list ->
          (* RECURSIVE STEP: A merge happened. Restart with the new list. *)
          L.d_printfln "[repair-log]   - Merge successful. Restarting merge pass.";
          merge_fixed_point new_list
    in
    
    merge_fixed_point filtered_plans
  in
  
  L.d_printfln "\n[repair-log] <<< Generated %d final plan(s)." (List.length final_plans);
  final_plans

let get_pvar_type proc_desc pvar =
  let locals = Procdesc.get_locals proc_desc in
  List.find_map locals ~f:(fun (var_data: ProcAttributes.var_data) ->
    if Mangled.equal var_data.name (Pvar.get_name pvar) then Some var_data.typ else None
  )

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
  L.d_printfln "[repair-reuse-debug] >> Identified %d potential reuse candidates of the correct type."
    (Pvar.Set.cardinal local_pvar_candidates);


  (*
    Step 2: Iterate through the stack (the analysis's ground truth) and find the first
    variable that is in our candidate set and is provably non-null.
  *)
  L.d_printfln "[repair-reuse] >> Searching for a viable local variable by iterating through the abstract stack...";
  AbductiveDomain.Stack.fold
    (fun var vo found_opt ->
      if Option.is_some found_opt then found_opt
      else
        match Var.get_pvar var with
        | None ->
            found_opt (* Not a program variable, skip *)
        | Some pvar_in_stack when Pvar.Set.mem pvar_in_stack local_pvar_candidates -> (
            (* This variable from the stack is one of our local candidates. Now check it. *)
            L.d_printfln "[repair-reuse-debug] >> Found candidate '%a' in stack. Checking its status..."
              (Pvar.pp Pp.text) pvar_in_stack;
            let addr, history = (ValueOrigin.value vo, ValueOrigin  .hist vo) in
            L.d_printfln "[repair-reuse-debug]    - Addr: %a, History: %a"
                AbstractValue.pp addr ValueHistory.pp history;

            let path_condition = astate.AbductiveDomain.path_condition in
            let has_allocated_cell =
              AbductiveDomain.find_post_cell_opt addr astate |> Option.is_some
            in
            let is_not_null = not (PulseFormula.is_known_zero path_condition addr) in

            if has_allocated_cell && is_not_null then (
              L.d_printfln "[repair-reuse-debug]   + SUCCESS: Candidate '%a' is allocated and not_null. Selecting it."
                (Pvar.pp Pp.text) pvar_in_stack;
              Some {reused_pvar= pvar_in_stack} )
            else (
              L.d_printfln
                "[repair-reuse-debug]    - FAILED: Candidate '%a' check failed: has_cell=%b, is_not_null=%b. Continuing search."
                (Pvar.pp Pp.text) pvar_in_stack has_allocated_cell is_not_null;
              found_opt ) )
        | Some pvar_in_stack ->
            (* It's a pvar, but not one we're looking for *)
            L.d_printfln "[repair-reuse-debug]    - Found pvar '%a' in stack, but it's not a candidate. Skipping."
                (Pvar.pp Pp.text) pvar_in_stack;
            found_opt
      )
    astate None
(** This function performs the analysis part of `apply_replace_repair` *)
let plan_replace_repair proc_desc (bug : 'payload bug_info) (all_aliases : Exp.t list) : repair_plan list =

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
    
    L.d_printfln "[repair-reuse] >> Searching for a viable local variable to reuse...";
    let reuse_candidate_opt =
      find_reuse_candidate proc_desc bug.astate (pvar, pvar_typ)
    in
    Replace {def_site_node= def_site; pvar; pvar_typ; reuse_info= reuse_candidate_opt; all_aliases}
  in
  Option.to_list plan_opt

(* Helper to define equality between two plans for deduplication *)
let equal_repair_plan p1 p2 =
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

  (* 1a. Get the initial abstract value for the bug. This is the correct logic you already had. *)
  let av_opt =
    match bug.ptr_var with
    | None ->
        bug.av_opt
    | Some v ->
        get_ptr_address ~astate:bug.astate v
  in

  (* 1b. Compute the full set of aliased pointers. *)
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
  L.d_printfln "[repair-plan] Found %d total pointers in alias set." (List.length all_ptrs_to_guard);

  (*
    Step 2: Now that we have the complete alias set, dispatch to the correct planner.
  *)
  let plans : repair_plan list =
    if is_provably_local ~proc_desc ~bug all_ptrs_to_guard then (
      let replace_plans = plan_replace_repair proc_desc bug all_ptrs_to_guard in
      if not (List.is_empty replace_plans) then replace_plans
      else (
        L.d_printfln "[repair-plan] REPLACE planning failed. Falling back to SKIP/EVADE.";
        plan_skip_or_evade_repair proc_desc bug all_ptrs_to_guard ) )
    else
      plan_skip_or_evade_repair proc_desc bug all_ptrs_to_guard
  in
  
  (* The rest of the function iterates through the generated list of plans. *)
  List.iter plans ~f:(fun plan ->
    if not (List.mem !logged_repairs_cache plan ~equal:equal_repair_plan) then (
      L.d_printfln "[repair] Found new unique plan.";
      report_repair_plan proc_desc plan;
      logged_repairs_cache := plan :: !logged_repairs_cache
    )
  )
      