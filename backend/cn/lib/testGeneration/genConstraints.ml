module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module LAT = LogicalArgumentTypes

type t =
  | Alloc of
      { pointer : Sym.t;
        size : IT.t
      }
  | Ownership of
      { pointer : Sym.t;
        x : Sym.t;
        ty : Sctypes.t
      }
  | Logical of LC.t list
  | Predicate of
      { name : Sym.t;
        iargs : (Sym.t * BT.t) list;
        oarg : Sym.t * BT.t
      }
[@@deriving eq, ord]

let add_indirection (it : IT.t) : Sym.t * t option =
  match IT.is_sym it with
  | Some (x, _) -> (x, None)
  | None ->
    let here = Locations.other __FUNCTION__ in
    let sym, it' = IT.fresh (IT.bt it) here in
    (sym, Some (Logical [ T (IT.eq_ (it, it') here) ]))

(* let rec of_lat (lat : 'a LAT.t) : t list =
  match lat with
  | Define ((x, it), (loc, _), lat') ->
    let gcs = of_lat lat' in
    let gc = Logical [ T (IT.eq_ (IT.sym_ (x, IT.bt it, loc), it) loc) ] in
    gc :: gcs
  | Resource ((x, (P { name = Owned (ty, _); pointer; iargs = _ }, _bt)), (loc, _), lat')
    ->
    let gcs = of_lat lat' in
    (match pointer with
     | IT (Sym p, _, _) ->
       Ownership { pointer = p; x; ty }
       :: Alloc { pointer = p; size = IT.sizeOf_ ty loc }
       :: gcs
     | IT (ArrayShift { base = IT (Sym p, _, _); ct; index }, _, loc') ->
       let size =
         IT.add_ (IT.sizeOf_ ty loc, IT.mul_ (index, IT.sizeOf_ ct loc') loc') loc
       in
       Ownership { pointer = p; x; ty } :: Alloc { pointer = p; size } :: gcs
     | it ->
       let y, oc = add_indirection it in
       Logical [ T (IT.eq_ (it, IT.sym_ (y, IT.bt it, IT.loc it)) loc) ]
       :: Ownership { pointer = y; x; ty }
       :: Alloc { pointer = y; size = IT.sizeOf_ ty loc }
       :: (Option.to_list oc @ gcs))
  | Resource ((x, (P { name = PName name; pointer; iargs = _ }, _bt)), (loc, _), lat') ->
    let gcs = of_lat lat' in
    (* Evaluate possible modes *)
    let iargs, cs =
      List.fold_left
        (fun (syms, cs) it ->
          let sym, oc = add_indirection it in
          (sym :: syms, match oc with Some c -> c :: cs | None -> cs))
        ([], [])
        (it :: its)
    in
    let pred = List.assoc Sym.equal name prog5.mu_resource_predicates in
    let iargs = List.combine iargs (BT.Loc :: List.map snd pred.iargs) in
    let oarg = (x, pred.oarg_bt) in
    Predicate { name; iargs; oarg } :: gcs
  | Constraint (lc, _info, lat') ->
    let gcs = of_lat lat' in
    let gc = Logical [ lc ] in
    gc :: gcs
  | I _ -> []
  | _ -> failwith __FUNCTION__ *)
