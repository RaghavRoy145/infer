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

type bug_info = {
  ptr_expr   : Exp.t;
  ptr_var    : Var.t option;
  diag_trace : PulseTrace.t;
  err_node   : Procdesc.Node.t;
  astate     : PulseAbductiveDomain.t;
}

(** A simple “reanalyze this proc and return true if no bug” callback *)
type reanalyze = Procdesc.t -> bool

(* let rec lca idom x y =
  if Procdesc.Node.equal x y then x
  else
    let dx = GDoms.idom idom x in
    let dy = GDoms.idom idom y in
    match (dx, dy) with
    | Some dx, Some dy when Procdesc.Node.equal dx dy -> dx
    | Some dx, Some _ -> lca idom dx y
    | Some dx, None -> dx
    | None, Some dy -> dy
    | None, None -> x  fallback to x if neither has an idom *)

let node_uses_ptr (ptr:Exp.t) (node:Procdesc.Node.t) : bool =
  let instrs = Procdesc.Node.get_instrs node in
  Instrs.exists instrs ~f:(fun instr ->
    List.exists (Sil.exps_of_instr instr) ~f:(fun e ->
      Exp.equal (Exp.ignore_cast e) (Exp.ignore_cast ptr)))

let compute_slice (pdesc:Procdesc.t) (ptr:Exp.t) : Procdesc.Node.t list =
  Procdesc.fold_nodes pdesc ~init:[] ~f:(fun acc n ->
    if node_uses_ptr ptr n then n :: acc else acc)
  |> List.rev

let insert_guard_block (pdesc:Procdesc.t) ~guard_node ~ptr ~covered =
  (* … append instrs … *)
  ignore covered;
  let loc = Procdesc.Node.get_loc guard_node in
  let cond = Exp.ne ptr Exp.null in
  (* Create then-/else-branches *)
  let then_node =
    Procdesc.create_node pdesc loc
      (Procdesc.Node.Prune_node (true, Sil.Ik_if, Procdesc.Node.PruneNodeKind_TrueBranch)) []
  in
  let else_node =
    Procdesc.create_node pdesc loc
      (Procdesc.Node.Prune_node (false, Sil.Ik_if, Procdesc.Node.PruneNodeKind_FalseBranch)) []
  in

  List.iter covered ~f:(fun n ->
    Logging.d_printfln "[repair]  covering node %a (%a)"
      Procdesc.Node.pp n Location.pp (Procdesc.Node.get_loc n)) ;
  let loc = Procdesc.Node.get_loc guard_node in
  Logging.d_printfln "[repair] inserting guard at %a, covering %d nodes"
    Location.pp loc (List.length covered) ;
  (* … create then_node & else_node … *)
  Logging.d_printfln "[repair]  then_node %a, else_node %a"
    Procdesc.Node.pp then_node Procdesc.Node.pp else_node ;

  Procdesc.Node.append_instrs then_node [Sil.Prune (cond, loc, true, Sil.Ik_if)];
  Procdesc.Node.append_instrs else_node [Sil.Prune (cond, loc, false, Sil.Ik_if)];
  (* Rewire edges *)
  let old_succs = Procdesc.Node.get_succs guard_node in
  Procdesc.node_set_succs pdesc guard_node ~normal:[then_node; else_node] ~exn:[];
  Procdesc.node_set_succs pdesc then_node ~normal:old_succs ~exn:[];
  let exit = Procdesc.get_exit_node pdesc in
  Procdesc.node_set_succs pdesc else_node ~normal:[exit] ~exn:[];
  Logging.d_printfln "[repair] Inserted guard at %a" Location.pp loc;
  true

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

let try_repair ~proc_desc ~bug ~reanalyze =
  let pname = Procdesc.get_proc_name proc_desc in
  let loc   = Procdesc.Node.get_loc bug.err_node in

  (* 0. build the dominator function idom *)
  let start = CFG.start_node proc_desc in
  let idom = GDoms.compute_idom proc_desc start in

  (* helper: “does x dominate y (reflexively)?” *)
  (* let dominates x y =
    GDoms.idom_to_dom idom x y || Procdesc.Node.equal x y
  in *)

  (* helper: LCA of two nodes via repeated lifting *)
  (* let rec lca u v =
    if Procdesc.Node.equal u v then u
    else if dominates u v
    then lca u      (idom v)
    else       lca (idom u) v
  in *)

  (* 1. recover the raw abstract value for pointer if any *)
  let rep_opt =
    match bug.ptr_var with
    | None -> None
    | Some v ->
      PulseAbductiveDomain.Stack.find_opt ~pre_or_post:`Post v bug.astate
      |> Option.map ~f:PulseValueOrigin.addr_hist
      |> Option.map ~f:fst
  in

  (* 2. logging alias counts *)
  let stack_aliases, heap_aliases =
    match rep_opt with
    | None -> 0, 0
    | Some rep ->
      let sa = collect_stack_aliases ~proc:proc_desc bug.astate rep in
      let ha = collect_heap_aliases      bug.astate rep     in
      List.length sa, List.length ha
  in
  Logging.d_printfln
    "[repair %a:%a] ptr=%a  stack_aliases=%d  heap_aliases=%d"
    Procname.pp pname Location.pp loc
    Exp.pp bug.ptr_expr
    stack_aliases heap_aliases;

  (* 3. build the list of pointer‐expressions to guard (original + aliases) *)
  let alias_exps =
    match rep_opt with
    | None -> []
    | Some rep ->
      let stack_exps = collect_stack_aliases ~proc:proc_desc bug.astate rep |> List.map ~f:snd in
      let heap_exps  = collect_heap_aliases  bug.astate rep |> List.map ~f:(fun _ -> bug.ptr_expr) in
      stack_exps @ heap_exps
  in

  (* 4. for each distinct alias, compute its slice and its minimal‐LCA *)
  let lca x y =
    (* collect all ancestors of x down to start *)
    let rec collect_ancestors n acc =
      let acc = NodeSet.add n acc in
      if Procdesc.Node.equal n start then acc else collect_ancestors (idom n) acc
    in
    let anc_x = collect_ancestors x NodeSet.empty in
    (* walk y up until you hit one of x’s ancestors *)
    let rec climb m =
      if NodeSet.mem m anc_x then m else climb (idom m)
    in
    climb y
  in
  
  let lca_nodes =
    let all_ptrs = bug.ptr_expr :: alias_exps in
    all_ptrs
    |> List.filter_map ~f:(fun ptr_exp ->
         let slice = compute_slice proc_desc ptr_exp in
         match slice with
         | [] ->
             Logging.d_printfln "[repair] no slice for %a, skipping" Exp.pp ptr_exp;
             None
         | first :: rest ->
             (* now fold with our two‑argument [lca] *)
             let guard = List.fold rest ~init:first ~f:lca in
             Logging.d_printfln
               "[repair] alias %a covers %d nodes, guard at %a"
               Exp.pp ptr_exp (List.length slice) Procdesc.Node.pp guard;
             Some guard)
    |> List.dedup_and_sort ~compare:Procdesc.Node.compare
  in

  (* 5. insert one guard per unique LCA, require them *all* to succeed *)
  let ok =
    List.for_all lca_nodes ~f:(fun guard_node ->
      insert_guard_block proc_desc ~guard_node ~ptr:bug.ptr_expr ~covered:[guard_node])
  in
  (* Logging.d_printfln "[repair] final CFG for %a:" Procname.pp pname ;
  List.iter (Procdesc.get_nodes proc_desc) ~f:(fun node ->
    let loc = Procdesc.Node.get_loc node in
    Logging.d_printfln "[repair]  node %a @[%a@]" Procdesc.Node.pp node Location.pp loc;

    Procdesc.get_nodes proc_desc
    |> List.iter ~f:(fun node ->
        let instrs = Procdesc.Node.get_instrs node in
        Logging.d_printfln "[repair] Node %a\n%a"
          Procdesc.Node.pp node
          (Instrs.pp ~print_types:false Pp.text) instrs ));  *)

  (* --- dump every nod its SIL instrs for post‑repair debugging --- *)
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

  (* 6. only actually commit (and drop the original report) if every guard went in cleanly *)
  if ok && verify_and_commit reanalyze proc_desc then (
    Logging.d_printfln "[repair] all %d guards committed, dropping error" (List.length lca_nodes) ;
    true )
  else (
    Logging.d_printfln "[repair] guard insertion failed ⇒ keeping error" ;
    false );

      

(* let try_repair ~proc ~bug ~reanalyze =
  (* let open PulseAbductiveDomain in *)
  let pname = Procdesc.get_proc_name proc in
  let loc   = Procdesc.Node.get_loc bug.err_node in

  (* Recover the raw abstract value “rep” for collect_* callers *)
  let rep_opt =
    match bug.ptr_var with
    | Some v -> get_ptr_address ~astate:bug.astate v
    | None -> None
  in

  let stack_aliases, heap_aliases =
    match rep_opt with
    | Some rep ->
        ( List.length (collect_stack_aliases ~proc bug.astate rep)
        , List.length (collect_heap_aliases  bug.astate rep) )
    | None ->
        (* fallback, no concrete abstract value to chase *)
        (0, 0)
  in

  Logging.d_printfln
    "🔧[repair %a:%a] ptr=%a  stack_aliases=%d  heap_aliases=%d"
    Procname.pp pname Location.pp loc
    Exp.pp bug.ptr_expr
    stack_aliases heap_aliases
  ;

  (* 1. Direct‐use slice *)
  (* let slice_direct = compute_slice proc bug.ptr_expr in *)

  (* 2. Extract the “raw” abstract value from the *live* domain state *)
  let rep_opt : PulseAbstractValue.t option =
    match bug.ptr_var with
    | None -> None
    | Some v ->
        match PulseAbductiveDomain.Stack.find_opt ~pre_or_post:`Post v bug.astate with
        | None -> None
        | Some vo ->
            let addr_raw, _ = PulseValueOrigin.addr_hist vo in
            Some addr_raw
  in

  (* 3. Build alias expressions *)
  (* let alias_exps : Exp.t list =
    match rep_opt with
    | None -> []
    | Some rep_raw ->
        let stack_exps =
          collect_stack_aliases ~proc bug.astate rep_raw |> List.map ~f:snd
        in
        let heap_exps =
          collect_heap_aliases bug.astate rep_raw
          |> List.map ~f:(fun _ -> bug.ptr_expr)
        in
        stack_exps @ heap_exps
  in *)

  (* 4. Union all slices *)
  (* let slice_all =
    let alias_slices = List.map alias_exps ~f:(compute_slice proc) in
    List.concat (slice_direct :: alias_slices)
    |> List.dedup_and_sort ~compare:Procdesc.Node.compare
  in  *)

  (* 5. Guard or give up *)
  (* match slice_all with
  | [] -> false
  | nodes ->
      let lca = List.hd_exn nodes in
      insert_guard_block proc ~guard_node:lca ~ptr:bug.ptr_expr ~covered:nodes
      && verify_and_commit reanalyze proc *)
    (* 4. Instead of one big guard, insert one per alias *)
    (* let any_guard = *)
      (* collect the “pointer expressions” to guard: the original ptr_expr plus
         any stack/heap aliases, all as Exp.t *)
      let all_aliases =
        bug.ptr_expr
        :: ( match rep_opt with
           | None -> []
           | Some rep_raw ->
               let stack_exps =
                 collect_stack_aliases ~proc bug.astate rep_raw
                 |> List.map ~f:snd
               in
               let heap_exps =
                 collect_heap_aliases bug.astate rep_raw
                 |> List.map ~f:(fun _ -> bug.ptr_expr)
               in
               stack_exps @ heap_exps )
      in
      (* for each alias, compute its slice and install a guard at the slice’s root *)
      (* List.exists all_aliases ~f:(fun alias_exp ->
        let slice = compute_slice proc alias_exp in
        match slice with
        | [] ->
            (* no uses of this alias, nothing to guard *)
            false
        | nodes ->
            (* pick a guard_node (e.g. the first node in the slice) *)
            let guard_node = List.hd_exn nodes in
            Logging.d_printfln
              "[repair] inserting guard for %a at node %a covering %d uses"
              Exp.pp alias_exp Procdesc.Node.pp guard_node (List.length nodes) ;
            insert_guard_block proc ~guard_node ~ptr:alias_exp ~covered:nodes )
    in *)
    (* 4. For each alias, pick the LCA of all its slice nodes *)
    let any_guard =
      List.exists all_aliases ~f:(fun alias_exp ->
        let slice = compute_slice proc alias_exp in
        match slice with
        | [] -> false
        | first :: rest ->
          (* fold rest into an LCA of the whole set *)
          let guard_node =
            List.fold rest ~init:first ~f:(fun acc n -> lca idom acc n)
          in
          Logging.d_printfln
            "[repair] inserting guard for %a at LCA node %a covering %d uses"
            Exp.pp alias_exp Procdesc.Node.pp guard_node (List.length slice) ;
          insert_guard_block proc ~guard_node ~ptr:alias_exp ~covered:slice )
        in
    (* 5. If any guard was inserted, verify & commit; otherwise give up *)
    any_guard && verify_and_commit reanalyze proc
 *)
