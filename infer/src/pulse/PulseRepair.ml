open! IStd
open Graph
module L = Logging
module CFG = ProcCfg.Normal

(* Use ocamlgraph's dominators functor to get the dominators *)
module GDoms = Dominator.Make (ProcCfg.MakeOcamlGraph (CFG))
(* bring in a set for Procdesc.Node.t *)
module NodeSet = Stdlib.Set.Make(struct
  type t = Procdesc.Node.t
  let compare = Procdesc.Node.compare
end)

(* let idom = GDoms.compute_idom proc_desc (ProcCfg.Normal.start_node proc_desc) *)

type 'payload bug_info = {
  ptr_expr   : Exp.t;
  ptr_var    : Var.t option;
  diag_trace : PulseTrace.t;
  err_node   : Procdesc.Node.t;
  astate     : PulseAbductiveDomain.t;
  analysis: ('payload) InterproceduralAnalysis.t;
  av_opt: PulseAbstractValue.t option;
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
      (* 1. Find all temporary variables (idents) that are loaded with the value of our pointer *)
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
      
      true ))

let verify_and_commit reanalyze pdesc =
  if reanalyze pdesc then true else false

(** 1. Stack aliases: normalize each local’s addr before comparing to [rep]. *)
let collect_stack_aliases
    ~(proc: Procdesc.t)
    (astate: PulseAbductiveDomain.t)
    (rep_raw: PulseAbstractValue.t)
  : (Var.t * Exp.t) list =
  let acc = ref [] in
  let pname = Procdesc.get_proc_name proc in
  (* compute the canonical representative of rep_raw, then downcast back *)
  let rep_can = PulseAbductiveDomain.CanonValue.canon' astate rep_raw in
  let rep = PulseAbductiveDomain.CanonValue.downcast rep_can in
  Procdesc.get_locals proc
  |> List.iter ~f:(fun var_data ->
       let pvar = Pvar.mk var_data.ProcAttributes.name pname in
       let v = Var.of_pvar pvar in
       match PulseAbductiveDomain.Stack.find_opt ~pre_or_post:`Post v astate with
       | None -> ()
       | Some vo ->
           let addr_raw, _hist = PulseValueOrigin.addr_hist vo in
           (* canonicalize and downcast *)
           let addr_can = PulseAbductiveDomain.CanonValue.canon' astate addr_raw in
           let addr = PulseAbductiveDomain.CanonValue.downcast addr_can in
           if PulseAbstractValue.equal rep addr then
             acc := (v, Exp.Lvar pvar) :: !acc
     ) ;
  !acc

(** Collect all heap aliases of [rep_raw] by walking the post‐heap graph. *)
let collect_heap_aliases
    (astate: PulseAbductiveDomain.t)
    (rep_raw: PulseAbstractValue.t)
  : PulseAbstractValue.t list =
  (* Build a Seq.t of one element *)
  let seed_seq : PulseAbstractValue.t Seq.t = Seq.cons rep_raw Seq.empty in
  (* reachable_addresses_from returns a PulseAbstractValue.Set.t *)
  let raw_set : PulseAbstractValue.Set.t =
    PulseAbductiveDomain.reachable_addresses_from
      ~edge_filter:(fun _ -> true)
      seed_seq astate `Post
  in
  (* Convert the set to a list *)
  let raw_list : PulseAbstractValue.t list = PulseAbstractValue.Set.elements raw_set in
  (* Canonicalize and downcast each, then dedupe *)
  raw_list
  |> List.map ~f:(fun av_raw ->
       let can = PulseAbductiveDomain.CanonValue.canon' astate av_raw in
       PulseAbductiveDomain.CanonValue.downcast can )
  |> List.dedup_and_sort ~compare:PulseAbstractValue.compare

(** Given the pointer Var.t that we recorded in bug.ptr_var, look up its
    current abstract address in the [astate]. *)
let get_ptr_address ~(astate: PulseAbductiveDomain.t) (v: Var.t)
  : PulseAbstractValue.t option =
  match PulseAbductiveDomain.Stack.find_opt ~pre_or_post:`Post v astate with
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
  
let apply_skip_repair ~proc_desc ~(bug : 'payload bug_info) ~reanalyze =
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
      match PulseAbductiveDomain.Stack.find_opt ~pre_or_post:`Post v bug.astate with
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
    false )
  
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
let insert_rebind_fresh proc_desc ~def_node ~ptr_pvar =
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
          else false ) )

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
  )