module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module RP = ResourcePredicates
module RET = ResourceTypes
module GBT = GenBaseTypes
module GTC = GenTypeConstraints
module SymSet = Set.Make (Sym)
module SymMap = Map.Make (Sym)

type modeSignature =
  { iargs : (Sym.t * GBT.t) list;
    oargs : (Sym.t * GBT.t) list
  }
[@@deriving eq, ord]

module ModeSet = Set.Make (struct
    type t = modeSignature

    let compare = compare_modeSignature
  end)

type t =
  { modes : ModeSet.t;
    ret : BT.t option
  }
[@@deriving eq, ord]

type context = t SymMap.t [@@deriving eq, ord]

(* let inter
  ({ iargs = iargs1; oargs = oargs1 } : modeSignature)
  ({ iargs = iargs2; oargs = oargs2 } : modeSignature)
  : modeSignature option
  =
  if
    not
      (SymSet.equal
         (SymSet.of_list (List.map fst iargs1))
         (SymSet.of_list (List.map fst iargs2))
       && SymSet.equal
            (SymSet.of_list (List.map fst oargs1))
            (SymSet.of_list (List.map fst oargs2)))
  then
    None
  else (
    let compare (x1, _) (x2, _) = Sym.compare x1 x2 in
    let aux acc (x1, gbt1) (x2, gbt2) =
      assert (Sym.equal x1 x2);
      let gbt = GBT.inter gbt1 gbt2 in
      (x1, gbt) :: acc
    in
    let iargs =
      List.fold_left2 aux [] (List.sort compare iargs1) (List.sort compare iargs2)
    in
    let oargs =
      List.fold_left2 aux [] (List.sort compare oargs1) (List.sort compare oargs2)
    in
    Some { iargs; oargs }) *)

module ModeInference = struct
  let ( let@ ) g f = List.flatten (List.map f g)

  let return x = [ x ]

  let rec infer_lat
    (preds : Mucore.T.resource_predicates)
    (ctx : context)
    (fsym : Sym.t)
    (lat : 'a LAT.t)
    : ModeSet.t
    =
    let update (p : Sym.t) (gtc : GTC.t) (args : (Sym.t * GBT.t) list) =
      match List.assoc_opt Sym.equal p args with
      | Some (y, y_bt, y_gtc) ->
        let y_gtc' = GTC.inter gtc y_gtc in
        let args' = List.filter (fun (y', _) -> not (Sym.equal y y')) args in
        (p, (y, y_bt, y_gtc')) :: args'
      | None -> args
    in
    match lat with
    | Define ((x, it), _info, lat') ->
      infer_lat preds ctx fsym (LAT.subst IT.subst (IT.make_subst [ (x, it) ]) lat')
    | Resource ((_, (P { name = Owned (ty, _); pointer; iargs = _ }, _bt)), (loc, _), lat')
      ->
      let modes =
        let@ { iargs; oargs } =
          List.of_seq (ModeSet.to_seq (infer_lat preds ctx fsym lat'))
        in
        match pointer with
        | IT (Sym p, _, _) ->
          let gtc = GTC.alloc_ (IT.sizeOf_ ty loc) in
          return { iargs = update p gtc iargs; oargs = update p gtc oargs }
        | IT (ArrayShift { base = IT (Sym p, _, _); ct; index }, _, loc') ->
          let size =
            IT.add_ (IT.sizeOf_ ty loc, IT.mul_ (index, IT.sizeOf_ ct loc') loc') loc
          in
          let gtc = GTC.alloc_ size in
          return { iargs = update p gtc iargs; oargs = update p gtc oargs }
        | _ -> return { iargs; oargs }
      in
      ModeSet.of_list modes
    | Resource
        ((_, (P { name = PName fsym; pointer; iargs = arg_its' }, _bt)), _info, lat') ->
      let modes =
        let@ modes = List.of_seq (ModeSet.to_seq (infer_lat preds ctx fsym lat')) in
        let pred = List.assoc Sym.equal fsym preds in
        let arg_syms = pred.pointer :: fst (List.split pred.iargs) in
        let arg_its = pointer :: arg_its' in
        let args = List.combine arg_syms arg_its in
        let { oargs = f_oargs; iargs = _ } =
          (* Ideally should do some overload finding thing *)
          ModeSet.choose (SymMap.find fsym ctx).modes
        in
        return
          (args
           |> List.filter (fun (x, _) -> List.mem_assoc Sym.equal x f_oargs)
           |> List.map snd
           |> List.fold_left
                (fun { iargs; oargs } it ->
                  let vars = IT.free_vars it in
                  let iargs = List.filter (fun (x, _) -> not (SymSet.mem x vars)) iargs in
                  let oargs = List.filter (fun (x, _) -> SymSet.mem x vars) oargs in
                  { iargs; oargs })
                modes)
      in
      ModeSet.of_list modes
    | Resource
        ( ( _,
            ( Q
                { name = PName fsym;
                  pointer = _;
                  q = _;
                  q_loc = _;
                  step = _;
                  permission = _;
                  iargs = arg_its
                },
              _bt ) ),
          _info,
          lat' ) ->
      let modes =
        let@ modes = List.of_seq (ModeSet.to_seq (infer_lat preds ctx fsym lat')) in
        let pred = List.assoc Sym.equal fsym preds in
        let arg_syms = fst (List.split pred.iargs) in
        let args = List.combine arg_syms arg_its in
        let { oargs = f_oargs; iargs = f_iargs } =
          ModeSet.choose (SymMap.find fsym ctx).modes
        in
        if not (List.mem_assoc Sym.equal pred.pointer f_iargs) then
          failwith "Pointer must allow input mode for `each`"
        else
          return
            (args
             |> List.filter (fun (x, _) -> List.mem_assoc Sym.equal x f_oargs)
             |> List.map snd
             |> List.fold_left
                  (fun { iargs; oargs } it ->
                    let vars = IT.free_vars it in
                    let iargs =
                      List.filter (fun (x, _) -> not (SymSet.mem x vars)) iargs
                    in
                    let oargs = List.filter (fun (x, _) -> SymSet.mem x vars) oargs in
                    { iargs; oargs })
                  modes)
      in
      ModeSet.of_list modes
    | Resource
        ( ( _,
            ( Q
                { name = Owned (_, _);
                  pointer = _;
                  q = _;
                  q_loc = _;
                  step = _;
                  permission = _;
                  iargs = _
                },
              _bt ) ),
          _info,
          lat' ) ->
      (* Could improve allocation estimation, but does not affect soundness *)
      infer_lat preds ctx fsym lat'
    | Constraint (lc, _info, lat') ->
      let modes =
        let@ { iargs; oargs } =
          List.of_seq (ModeSet.to_seq (infer_lat preds ctx fsym lat'))
        in
        let iargs =
          SymSet.fold
            (fun x iargs' -> update x (GTC.of_lc lc) iargs')
            (LC.free_vars lc)
            iargs
        in
        let oargs =
          SymSet.fold
            (fun x oargs' -> update x (GTC.of_lc lc) oargs')
            (LC.free_vars lc)
            oargs
        in
        return { iargs; oargs }
      in
      ModeSet.of_list modes
    | I _ -> (SymMap.find fsym ctx).modes


  let infer_clause
    (preds : Mucore.T.resource_predicates)
    (ctx : context)
    (fsym : Sym.t)
    (cl : RP.clause)
    : ModeSet.t
    =
    let here = Locations.other __FUNCTION__ in
    infer_lat preds ctx fsym (Constraint (T cl.guard, (here, None), cl.packing_ft))


  let infer_clauses
    (preds : Mucore.T.resource_predicates)
    (ctx : context)
    (fsym : Sym.t)
    (cls : RP.clause list)
    : ModeSet.t
    =
    match cls with
    | cl :: _ :: _cls' ->
      let modes =
        let@ { iargs = _; oargs = _ } =
          List.of_seq (ModeSet.to_seq (infer_clause preds ctx fsym cl))
        in
        failwith "todo: actually requires thinking"
      in
      ModeSet.of_list modes
    | [ cl ] -> infer_clause preds ctx fsym cl
    | [] -> failwith ("unreachable @ " ^ __LOC__)


  let infer_pred
    (preds : Mucore.T.resource_predicates)
    (ctx : context)
    (fsym : Sym.t)
    (pd : ResourcePredicates.definition)
    : ModeSet.t
    =
    infer_clauses preds ctx fsym (Option.get pd.clauses)


  let infer_preds (prog5 : unit Mucore.mu_file) : context =
    (* Build context *)
    let build_context (f : Sym.t -> RP.definition -> ModeSet.t) : context =
      prog5.mu_resource_predicates
      |> List.map (fun (fsym, pd) -> (fsym, { modes = f fsym pd; ret = Some pd.oarg_bt }))
      |> List.to_seq
      |> SymMap.of_seq
    in
    (* Perform one pass *)
    let aux (ctx : context) : context =
      build_context (infer_pred prog5.mu_resource_predicates ctx)
    in
    (* Chaotic iteration *)
    let rec loop (ctx : context) : context =
      let old_ctx = ctx in
      let new_ctx = aux ctx in
      if equal_context old_ctx new_ctx then new_ctx else loop new_ctx
    in
    (* Start out with all arguments possible as inputs *)
    let ctx =
      build_context (fun _fsym pd ->
        let args = (pd.pointer, BT.Loc ()) :: pd.iargs in
        ModeSet.singleton { iargs = List.map_snd GBT.of_bt args; oargs = [] })
    in
    (* Run *)
    loop ctx


  let infer_specs (prog5 : unit Mucore.mu_file) : context =
    prog5
    |> Core_to_mucore.collect_instrumentation
    |> fst
    |> List.filter_map
         (fun (inst : Core_to_mucore.instrumentation) : (Sym.t * t) option ->
            let open Option in
            let@ at = inst.internal in
            let rec at_aux (at : 'a AT.t) : (Sym.t * GBT.t) list =
              match at with
              | Computational ((x, bt), _, at') -> (x, GBT.of_bt bt) :: at_aux at'
              | L _ -> []
            in
            return
              ( inst.fn,
                { modes = ModeSet.singleton { iargs = []; oargs = at_aux at };
                  ret = None
                } ))
    |> List.to_seq
    |> SymMap.of_seq


  let infer (prog5 : unit Mucore.mu_file) : context =
    SymMap.union
      (fun fsym _modes1 _modes2 ->
        failwith ("multiple definitions of " ^ Sym.pp_string fsym))
      (infer_preds prog5)
      (infer_specs prog5)
end

let infer = ModeInference.infer
