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

    (*
      Now, we fix our manual functions to also expect the tuple.
      We destructure the tuple `g` to get the `pdesc` we need.
    *)
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
      (*
        FIX #2 & #3: The value is a `ValueOrigin.t`. We must deconstruct it
        to get the abstract value (`stack_av`).
      *)
      let stack_av, _ = ValueOrigin.addr_hist value_origin in
      (* 3. For each variable on the stack, get its canonical representative. *)
      let current_var_canonical_rep =
        let canon_v = AbductiveDomain.CanonValue.canon' astate stack_av in
        AbductiveDomain.CanonValue.downcast canon_v
      in
      (* 4. If they match, we have found an alias. *)
      if PulseBasicInterface.AbstractValue.equal canonical_rep_to_match current_var_canonical_rep
      then (
        (*
          FIX #4: `Var.get_pvar` returns an option. We must handle the `None`
          case where a stack variable is not a program variable.
        *)
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
  
let is_provably_local ~proc_desc ~(bug : 'payload bug_info) =
  let ptr_exp_str = Format.asprintf "%a" Exp.pp bug.ptr_expr in
  L.d_printfln "[repair-debug] is_provably_local: Checking var %s" ptr_exp_str;
  let result =
    match bug.ptr_var with
    | None -> false
    | Some v ->
        let ptr_exp = Var.to_exp v in
        let has_call_usage =
          Procdesc.fold_nodes proc_desc ~init:false ~f:(fun acc node ->
              if acc then true (* already found escape *)
              else
                let instrs = Procdesc.Node.get_instrs node in
                (* 1. Find all temporary variables that are loaded with our pointer's value. *)
                let idents_holding_pointer =
                  Instrs.fold instrs ~init:Ident.Set.empty ~f:(fun acc' instr ->
                      match instr with
                      | Sil.Load {id; e; _} when Exp.equal e ptr_exp ->
                          Ident.Set.add id acc'
                      | _ -> acc' )
                in
                if Ident.Set.is_empty idents_holding_pointer then false
                else
                  (* 2. Check if any of these temps are used as an argument in a call. *)
                  Instrs.exists instrs ~f:(fun instr ->
                      match instr with
                      | Sil.Call (_, _, args, _, _) ->
                          List.exists args ~f:(fun (arg_exp, _) ->
                              match arg_exp with
                              | Exp.Var id ->
                                  Ident.Set.mem id idents_holding_pointer
                              | _ -> false )
                      | _ -> false ) )
        in
        let is_not_captured = not (Procdesc.is_captured_var proc_desc v) in
        let is_not_global = not (Var.is_global v) in
        let is_not_return = not (Var.is_return v) in

        L.d_printfln
          "[repair-debug] is_provably_local: has_call_usage=%b, is_not_captured=%b, is_not_global=%b, is_not_return=%b"
          has_call_usage is_not_captured is_not_global is_not_return;

        (not has_call_usage) && is_not_captured && is_not_global && is_not_return
  in
  L.d_printfln "[repair-debug] is_provably_local: Final result for %s is %b" ptr_exp_str result;
  result

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
| Replace of {
    def_site_node: Procdesc.Node.t;
    pvar: Pvar.t;
    pvar_typ: Typ.t;
  }

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
  | Skip {lca_node; pointer_exprs; slice_nodes} ->
      let guard_ptr_expr = List.hd_exn pointer_exprs in
      let line_nums = List.map slice_nodes ~f:(fun n -> (Procdesc.Node.get_loc n).line) in
      let min_line = List.min_elt line_nums ~compare:Int.compare |> Option.value ~default:0 in
      let max_line = List.max_elt line_nums ~compare:Int.compare |> Option.value ~default:0 in
      L.d_printfln "[repair-plan]--- PULSE REPAIR PLAN ---" ;
      L.d_printfln "[repair-plan]PROCEDURE: %a" Procname.pp proc_name ;
      L.d_printfln "[repair-plan]STRATEGY: SKIP" ;
      L.d_printfln "[repair-plan]ACTION: Guard the code block from line ~%d to ~%d at node %d (LCA)."
        min_line max_line (Procdesc.Node.get_id lca_node :> int) ;
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
| Replace {def_site_node; pvar; pvar_typ} ->
    L.d_printfln "[repair-plan]--- PULSE REPAIR PLAN ---" ;
    L.d_printfln "[repair-plan]PROCEDURE: %a" Procname.pp proc_name ;
    L.d_printfln "[repair-plan]STRATEGY: REPLACE" ;
    L.d_printfln "[repair-plan]TARGET POINTER: %a" (Pvar.pp Pp.text) pvar;
    L.d_printfln "[repair-plan]ACTION: At definition site node %d, modify the assignment." (Procdesc.Node.get_id def_site_node :> int) ;
    L.d_printfln "[repair-plan]        Transform '%a = NULL;' to 'if (%a == NULL) { %a = &fresh_var; }'"
      (Pvar.pp Pp.text) pvar (Pvar.pp Pp.text) pvar (Pvar.pp Pp.text) pvar;
    L.d_printfln "[repair-plan]        (where fresh_var has type: %a)" (Typ.pp_full Pp.text) pvar_typ;
    L.d_printfln "[repair-plan]--------------------------"

(** This is a powerful helper. Given a trace and the top-level procedure it started from,
    it finds the final dereference location and checks if THAT dereference is guarded in its
    own function. *)
(* let is_dereference_guarded_in_callee (top_pdesc: Procdesc.t) (trace: Trace.t) : bool =
  let rec find_guarded_deref_in_trace (current_pdesc: Procdesc.t) (trace: Trace.t) =
    match trace with
    | Immediate {location; _} ->
        let node_opt =
          List.find (Procdesc.get_nodes current_pdesc) ~f:(fun n -> Location.equal (Procdesc.Node.get_loc n) location)
        in
        ( match node_opt with
          | None -> false
          | Some node ->
              List.exists (Procdesc.Node.get_preds node) ~f:(fun pred_node ->
                match Procdesc.Node.get_kind pred_node with
                | Prune_node (true, _, _) -> true
                | _ -> false ) )
    | ViaCall {f; in_call; _} ->
        let callee_pdesc_opt =
          match (f: CallEvent.t) with
          | Call pname | ModelName pname | SkippedKnownCall pname -> Procdesc.load pname
          | _ -> None
        in
        match callee_pdesc_opt with
        | None -> false
        | Some callee_pdesc -> find_guarded_deref_in_trace callee_pdesc in_call
  in
  (* Start the traversal from the top-level procedure that was passed in. *)
  find_guarded_deref_in_trace top_pdesc trace *)

(*
  For a given bug trace, finds the location of the call in the *current*
  procedure that is the entry point to the crashing trace.
*)
(* let get_top_level_call_location (trace : Trace.t) : Location.t option =
  match trace with
  | Immediate {location; _} ->
      (* This is an intra-procedural crash. The top-level location is the crash itself. *)
      Some location
  | ViaCall {location; _} ->
      (* This is an inter-procedural crash. The location of the ViaCall is exactly
         what we need—it's the call site in the current function. *)
      Some location *)

let plan_skip_or_evade_repair proc_desc (bug : 'payload bug_info) : repair_plan list =
  (* let pname = Procdesc.get_proc_name proc_desc in *)
  let start = Procdesc.get_start_node proc_desc in
  let idom = GDoms.compute_idom proc_desc start in

  let lca x y =
    let rec collect_ancestors n acc =
      let acc' = Procdesc.NodeSet.add n acc in
      if Procdesc.Node.equal n start then acc' else collect_ancestors (idom n) acc'
    in
    let anc_x = collect_ancestors x Procdesc.NodeSet.empty in
    let rec climb m = if Procdesc.NodeSet.mem m anc_x then m else climb (idom m) in
    climb y
  in

(* Checks if a dereference is already protected by a non-null check. *)
  let is_guarded_by_preds (node: Procdesc.Node.t) (guarded_idents: Ident.Set.t) (ptr_exp: Exp.t) =
    List.exists (Procdesc.Node.get_preds node) ~f:(fun pred_node ->
      match Procdesc.Node.get_kind pred_node with
      | Prune_node (true, _, _) ->
          Instrs.exists (Procdesc.Node.get_instrs pred_node) ~f:(fun instr ->
            match instr with
            | Sil.Prune (cond, _, _, _) ->
                (* This is the only case we care about. Check the condition. *)
                if Exp.equal cond ptr_exp || Exp.equal cond (Exp.ne ptr_exp Exp.null) then 
                  true
                else (
                  match cond with
                  | Exp.Var id -> Ident.Set.mem id guarded_idents
                  | _ -> false
                )
            | _ -> false
          )
      | _ -> false
    )
  in

  (* Checks if `node` is dominated by `dominator`. *)
  let is_dominated_by ~dominator ~node =
    let rec climb current =
      if Procdesc.Node.equal current dominator then true
      else
        let parent = idom current in
        if Procdesc.Node.equal parent current then false else climb parent
    in
    climb node
  in

  let compute_ipdom proc_desc =
    let exit_node = Procdesc.get_exit_node proc_desc in
    (*
      `from_pdesc` from the Exceptional CFG view creates the required tuple
      of `(Procdesc.t * exceptional_edge_map)`. This is the graph instance.
    *)
    let reversed_graph_instance = PostDominators.ReversedCFG.from_pdesc proc_desc in
    PostDominators.compute_idom reversed_graph_instance exit_node
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

    (* This version correctly finds the final crash site and uses it to determine
     if the node in question is a safe, intermediate step on the trace. *)
  let is_semantically_safe_on_trace (node: Procdesc.Node.t) (trace: Trace.t) : bool =
    let node_loc = Procdesc.Node.get_loc node in

    (* Step 1: Find the location of the immediate, final crash. *)
    let rec get_immediate_crash_location = function
      | Trace.Immediate {location; _} -> Some location
      | Trace.ViaCall {in_call; _} -> get_immediate_crash_location in_call
    in
    let final_crash_loc_opt = get_immediate_crash_location trace in

    match final_crash_loc_opt with
    | None ->
        (* Should not happen on a valid bug trace, but as a safeguard,
            if we can't find the crash, we can't prove anything is safe. *)
        false
    | Some final_crash_loc ->
        (* A node is safe if it is NOT the final crash site.
            We can simply check if the node's location is the final one. *)
        if Location.equal node_loc final_crash_loc then
          (* This node IS the final crash site. It is NOT safe. *)
          false
        else
          (* This node is NOT the final crash site. Now we just need to confirm
              it actually appears somewhere on the trace to be considered a relevant
              (and therefore safe) intermediate step. *)
          let rec is_on_trace = function
            | Trace.Immediate {location; _} -> Location.equal node_loc location
            | Trace.ViaCall {location; in_call; _} ->
                Location.equal node_loc location || is_on_trace in_call
          in
          is_on_trace trace
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

  (* Performs a simple, syntactic scan of the procedure to find direct aliases.
  It takes a set of known pointer expressions and finds other variables that
  are assigned to or from them. It iterates until no new aliases are found. *)
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
  in

  let all_ptrs_to_guard =
    let initial_ptr = (bug.ptr_var |> Option.value_map ~f:Var.to_exp ~default:bug.ptr_expr) in
    (* First, get semantic aliases from the astate (for complex cases). *)
    let semantic_alias_exps = List.map stack_aliases ~f:snd in
    let known_ptrs = List.dedup_and_sort ~compare:Exp.compare (initial_ptr :: semantic_alias_exps) in
    (* Then, use the syntactic collector to find aliases defined after the crash point. *)
    find_syntactic_aliases proc_desc known_ptrs
  in
    
  let lca_map =
    let lca_to_ptr_list =
      List.filter_map all_ptrs_to_guard ~f:(fun ptr_exp ->

        let syntactic_slice =
          Procdesc.fold_nodes proc_desc ~init:Procdesc.NodeSet.empty ~f:(fun acc node ->
              let instrs = Procdesc.Node.get_instrs node in
              let idents_holding_pointer =
                Instrs.fold instrs ~init:Ident.Set.empty ~f:(fun acc' instr ->
                  match instr with
                  | Sil.Load {id; e; _} when Exp.equal e ptr_exp -> Ident.Set.add id acc'
                  | _ -> acc' )
              in
              let has_usage =
                Instrs.exists instrs ~f:(fun instr ->
                  match instr with
                  | Sil.Load {e=Exp.Var id; _} | Sil.Store {e1=Exp.Var id; _} ->
                      if Ident.Set.mem id idents_holding_pointer then
                        (* We must call is_guarded_by_preds here! *)
                        not (is_guarded_by_preds node idents_holding_pointer ptr_exp)
                      else false
                  | Sil.Load {e; _} when Exp.equal e ptr_exp ->
                      not (is_guarded_by_preds node Ident.Set.empty ptr_exp)
                  | Sil.Store {e1; _} -> (
                    match e1 with
                    | Exp.Lvar _ -> false
                    | _ ->
                        if Exp.equal e1 ptr_exp then
                          not (is_guarded_by_preds node Ident.Set.empty ptr_exp)
                        else false )
                  | Sil.Call (_, _, args, _, _) ->
                      let is_call_to_check =
                        List.exists args ~f:(fun (arg, _) ->
                          if Exp.equal arg ptr_exp then true
                          else match arg with Exp.Var id -> Ident.Set.mem id idents_holding_pointer | _ -> false )
                      in
                      if is_call_to_check then
                        not (is_guarded_by_preds node idents_holding_pointer ptr_exp)
                      else false
                  | _ -> false )
              in
              if has_usage then Procdesc.NodeSet.add node acc else acc )
          |> Procdesc.NodeSet.elements
        in


        (* 2. Now, we refine this list based on the type of bug trace. *)
        let semantic_slice =
          match bug.diag_trace with
          | Trace.ViaCall {location=crash_loc; _} ->
              (
                (*
                  INTER-PROCEDURAL CASE: Here, we do NOT need the syntactic_slice.
                  We know the exact location of the single problematic call site.
                  So, we find that one node directly for efficiency.
                *)
                L.d_printfln "[repair-plan] Inter-procedural crash. Targeting call site at %a"
                  Location.pp crash_loc;
                List.filter (Procdesc.get_nodes proc_desc) ~f:(fun node ->
                    Location.equal (Procdesc.Node.get_loc node) crash_loc ) )
          | Trace.Immediate _ ->
              (
                (*
                  INTRA-PROCEDURAL CASE: Here, the syntactic_slice is CRITICAL.
                  It gives us the list of candidate nodes that might be crashing.
                  We then filter THIS LIST to get the final set of nodes to guard.
                  This is much more efficient than re-scanning all nodes.
                *)
                L.d_printfln "[repair-plan] Intra-procedural crash. Vetting syntactic slice.";
                List.filter syntactic_slice ~f:(fun node ->
                    (* Keep the node if it's not semantically safe (i.e., it's a real crash) *)
                    not (is_semantically_safe_on_trace node bug.diag_trace) ) )
        in
      let final_slice_for_this_ptr = semantic_slice in

      (* Step 2: Find the LCA for this pointer's individual slice. *)
      match final_slice_for_this_ptr with
      | [] -> None
      | first :: rest ->
          let lca_node = List.fold rest ~init:first ~f:lca in
          let adjusted_lca_node =
            match Procdesc.Node.get_kind lca_node with
            | Prune_node _ -> (
                match Procdesc.Node.get_succs lca_node with
                | [then_branch_start] ->
                    if List.for_all final_slice_for_this_ptr ~f:(fun slice_node -> is_dominated_by ~dominator:then_branch_start ~node:slice_node) then (
                      L.d_printfln "[repair-plan] Adjusting LCA from Prune node %a to successor %a"
                        Procdesc.Node.pp lca_node Procdesc.Node.pp then_branch_start;
                      then_branch_start )
                    else lca_node
                | _ -> lca_node )
            | _ -> lca_node
          in
          L.d_printfln "[repair-plan] alias %a has slice of size %d, final guard at node %a"
            Exp.pp ptr_exp (List.length final_slice_for_this_ptr) Procdesc.Node.pp adjusted_lca_node;
          Some (adjusted_lca_node, (ptr_exp, final_slice_for_this_ptr)) )
      in
      (* Step 3: Group the pointers and their slices by their common LCA key. This forms the clusters. *)
      List.fold lca_to_ptr_list ~init:Procdesc.NodeMap.empty
      ~f:(fun map (lca_node, (ptr_exp, slice)) ->
        let existing_pointers, existing_slice =
          Procdesc.NodeMap.find_opt lca_node map |> Option.value ~default:([], [])
        in
        let new_slice = List.rev_append slice existing_slice in
        Procdesc.NodeMap.add lca_node (ptr_exp :: existing_pointers, new_slice) map )
      in

    (* Step 4: Generate a separate, minimal repair plan for each cluster found in the map *)
      let ipdom_fun = lazy (compute_ipdom proc_desc) in

      let find_correct_scope (slice : Procdesc.Node.t list) =
        let ipdom_fun = Lazy.force ipdom_fun in
        (* Helper to find the immediate dominator of a node. *)
        let idom_fun = idom in
      
        (* For a given node, climb the dominator tree to find the nearest enclosing Prune node (if/loop condition). *)
        let get_enclosing_prune_opt node =
          let rec climb current =
            if Procdesc.Node.equal current start then None
            else
              let parent = idom_fun current in
              match Procdesc.Node.get_kind parent with Prune_node _ -> Some parent | _ -> climb parent
          in
          climb node
        in
        (*
          Find the highest "common" prune node that encloses the entire slice.
          We do this by finding the enclosing prune for the LCA of the slice.
        *)
        let lca_of_slice =
          let first = List.hd_exn slice in
          let rest = List.tl_exn slice in
          List.fold rest ~init:first ~f:lca
        in
        match get_enclosing_prune_opt lca_of_slice with
        | Some prune_node ->
            (*
              The slice is inside a control structure. The scope is the structure itself.
              Start Node: The Prune node (the `if` condition).
              End Node: The immediate post-dominator of the Prune node (the "join" node after the `if`).
            *)
            (prune_node, ipdom_fun prune_node)
        | None ->
            (*
              The slice is not in a common control structure. The scope is simply the
              LCA of the slice and the post-dominator (LCPD) of the slice.
            *)
            let lcpd_of_slice =
              let first = List.hd_exn slice in
              let rest = List.tl_exn slice in
              List.fold rest ~init:first ~f:(lcpd ipdom_fun)
            in
            (lca_of_slice, lcpd_of_slice)
          in
      Procdesc.NodeMap.bindings lca_map
      |> List.map ~f:(fun (_, (pointer_exprs, slice_nodes)) ->
        let unique_slice = List.dedup_and_sort ~compare:Procdesc.Node.compare slice_nodes in
        if List.is_empty unique_slice then None
        else
          let start_node, end_node =
            (* Call the new, correct scope-finding logic on the cluster's unified slice. *)
            find_correct_scope unique_slice
          in
          if Procdesc.Node.equal start_node start then
            Some (Evade {proc_start_node = start_node; pointer_expr = List.hd_exn pointer_exprs})
          else
            ( L.d_printfln "[repair-plan] Found cluster with %d pointers. Scope: START=%a, END=%a"
                (List.length pointer_exprs) Procdesc.Node.pp start_node Procdesc.Node.pp end_node;
              Some
                (Skip {lca_node = start_node; join_node = end_node; pointer_exprs; slice_nodes= unique_slice}) ) )
    |> List.filter_map ~f:Fn.id (* To remove the None values from empty slices *)

let get_pvar_type proc_desc pvar =
  let locals = Procdesc.get_locals proc_desc in
  List.find_map locals ~f:(fun (var_data: ProcAttributes.var_data) ->
    if Mangled.equal var_data.name (Pvar.get_name pvar) then Some var_data.typ else None
  )

(** This function performs the analysis part of `apply_replace_repair` *)
let plan_replace_repair proc_desc (bug : 'payload bug_info) : repair_plan list =
  let open IOption.Let_syntax in
  let plan_opt =
    let* ptr_var = bug.ptr_var in
    let* pvar = Var.get_pvar ptr_var in
    let* def_site = find_last_def_site ~proc_desc ~ptr_var:pvar in
    let+ pvar_typ = get_pvar_type proc_desc pvar in
    Replace {def_site_node= def_site; pvar; pvar_typ}
  in
  Option.to_list plan_opt

(* Helper to define equality between two plans for deduplication *)
let equal_repair_plan p1 p2 =
  match (p1, p2) with
  | Skip r1, Skip r2 -> Procdesc.Node.equal r1.lca_node r2.lca_node
  | Evade r1, Evade r2 -> Procdesc.Node.equal r1.proc_start_node r2.proc_start_node
  | Replace r1, Replace r2 -> Procdesc.Node.equal r1.def_site_node r2.def_site_node
  | _, _ -> false

(* let compare_repair_plan p1 p2 =
  match (p1, p2) with
  | Skip r1, Skip r2 -> Procdesc.Node.compare r1.lca_node r2.lca_node
  | Evade r1, Evade r2 -> Procdesc.Node.compare r1.proc_start_node r2.proc_start_node
  | Replace r1, Replace r2 -> Procdesc.Node.compare r1.def_site_node r2.def_site_node
  (* Define an arbitrary but consistent order for different kinds of plans. *)
  | Skip _, _ -> -1
  | _, Skip _ -> 1
  | Evade _, _ -> -1
  | _, Evade _ -> 1 *)

(** Performs a reverse lookup to find the program variable in a given procedure
that corresponds to a given abstract value. *)
(* let find_pvar_for_abstract_value ~proc_desc ~astate (av_target: AbstractValue.t) : Pvar.t option =

  let local_names =
    List.map (Procdesc.get_locals proc_desc) ~f:(fun (var_data: ProcAttributes.var_data) -> var_data.name)
  in
  let formal_names =
    List.map (Procdesc.get_formals proc_desc) ~f:(fun (name, _typ, _annot) -> name)
  in
  let all_var_names = local_names @ formal_names in
  
  let p_name = Procdesc.get_proc_name proc_desc in
  List.find_map all_var_names ~f:(fun var_name ->
    let pvar = Pvar.mk var_name p_name in
    match AbductiveDomain.Stack.find_opt ~pre_or_post:`Post (Var.of_pvar pvar) astate with
    | None -> None
    | Some vo ->
        let av_actual, _history = PulseValueOrigin.addr_hist vo in
        if AbstractValue.equal av_target av_actual then Some pvar else None
  ) *)

(* let rec get_final_callee_pdesc_loc (current_pdesc: Procdesc.t) (trace: Trace.t) : (Procdesc.t * Location.t) =
  match trace with
  | Immediate {location; _} ->
      (* Base case: The trace ends here. The location is in the current procedure. *)
      (current_pdesc, location)
  | ViaCall {f; in_call; _} ->
      (* Recursive step: The trace continues inside a callee. *)
      let callee_proc_name_opt =
        match (f : CallEvent.t) with
        | Call proc_name | ModelName proc_name | SkippedKnownCall proc_name ->
            (* These cases all provide a procname we can try to load. *)
            Some proc_name
        | Model _ | SkippedUnknownCall _ ->
            (* These cases do not have a procname we can load. Stop traversal. *)
            None
      in
      match callee_proc_name_opt with
      | None ->
          (* This can happen for calls to function pointers or other indirect calls.
              It's safest to stop here and use the current context. *)
          (current_pdesc, Trace.get_outer_location trace)
      | Some callee_proc_name ->
          (* We found the name of the callee. Now we must load its proc_desc. *)
          match Procdesc.load callee_proc_name with
          | None ->
              (* This is rare, but could happen if the callee's source is not available.
                  Safest to stop here. *)
              L.d_printfln "[repair] Could not load proc_desc for %a" Procname.pp callee_proc_name;
              (current_pdesc, Trace.get_outer_location trace)
          | Some callee_pdesc ->
              (* SUCCESS: We have the callee's procedure. Recurse into the rest of the trace. *)
              get_final_callee_pdesc_loc callee_pdesc in_call *)

let plan_and_log_if_unique ~proc_desc ~(bug : 'payload bug_info) =
  clear_cache_if_new_proc (Procdesc.get_proc_name proc_desc);
  
  (* `plans` is now correctly a list, preserving your multi-LCA design. *)
  let plans : repair_plan list =
    if is_provably_local ~proc_desc ~bug then (
      let replace_plans = plan_replace_repair proc_desc bug in
      if not (List.is_empty replace_plans) then
        replace_plans
      else (
        L.d_printfln "[repair-plan] REPLACE planning failed. Falling back to SKIP/EVADE.";
        plan_skip_or_evade_repair proc_desc bug
      )
    ) else (
      plan_skip_or_evade_repair proc_desc bug
    )
  in
  
  (* The rest of the function iterates through the generated list of plans. *)
  List.iter plans ~f:(fun plan ->
    if not (List.mem !logged_repairs_cache plan ~equal:equal_repair_plan) then (
      L.d_printfln "[repair] Found new unique plan.";
      report_repair_plan proc_desc plan;
      logged_repairs_cache := plan :: !logged_repairs_cache
    )
  )
      