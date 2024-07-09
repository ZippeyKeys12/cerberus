(* module AT = ArgumentTypes

   module LS = LogicalSorts
   module LC = LogicalConstraints
   module LAT = LogicalArgumentTypes
*)
module BT = BaseTypes
module IT = IndexTerms
module SymMap = IT.SymMap
module RP = ResourcePredicates
module RET = ResourceTypes
module LAT = LogicalArgumentTypes
module CF = Cerb_frontend
open CF
open Mucore

let weak_sym_equal s1 s2 =
  String.equal (Pp_symbol.to_string_pretty s1) (Pp_symbol.to_string_pretty s2)
;;

type arg_map = BT.t SymMap.t

let expect_equal_types _ bt1 bt2 =
  if BT.equal bt1 bt2 then Some bt1 else failwith "contradictory types"
;;

let rec free_vars (tm : 'a IT.term) : arg_map =
  match tm with
  | IT (Sym x, bt, _) -> SymMap.singleton x bt
  | IT (tm_, _, _) ->
    (match tm_ with
     | Const _ -> SymMap.empty
     | Sym _ -> failwith "unreachable"
     | Unop (_uop, t1) -> free_vars t1
     | Binop (_bop, t1, t2) -> free_vars_list [ t1; t2 ]
     | ITE (t1, t2, t3) -> free_vars_list [ t1; t2; t3 ]
     | EachI ((_, (s, _), _), t) -> SymMap.remove s (free_vars t)
     | Tuple ts -> free_vars_list ts
     | NthTuple (_, t) -> free_vars t
     | Struct (_tag, members) -> free_vars_list (List.map snd members)
     | StructMember (t, _member) -> free_vars t
     | StructUpdate ((t1, _member), t2) -> free_vars_list [ t1; t2 ]
     | Record members -> free_vars_list (List.map snd members)
     | RecordMember (t, _member) -> free_vars t
     | RecordUpdate ((t1, _member), t2) -> free_vars_list [ t1; t2 ]
     | Cast (_cbt, t) -> free_vars t
     | MemberShift (t, _tag, _id) -> free_vars t
     | ArrayShift { base; ct = _; index } -> free_vars_list [ base; index ]
     | CopyAllocId { addr; loc } -> free_vars_list [ addr; loc ]
     | SizeOf _t -> SymMap.empty
     | OffsetOf (_tag, _member) -> SymMap.empty
     | Nil _bt -> SymMap.empty
     | Cons (t1, t2) -> free_vars_list [ t1; t2 ]
     | Head t -> free_vars t
     | Tail t -> free_vars t
     | NthList (i, xs, d) -> free_vars_list [ i; xs; d ]
     | ArrayToList (arr, i, len) -> free_vars_list [ arr; i; len ]
     | Representable (_sct, t) -> free_vars t
     | Good (_sct, t) -> free_vars t
     | WrapI (_ity, t) -> free_vars t
     | Aligned { t; align } -> free_vars_list [ t; align ]
     | MapConst (_bt, t) -> free_vars t
     | MapSet (t1, t2, t3) -> free_vars_list [ t1; t2; t3 ]
     | MapGet (t1, t2) -> free_vars_list [ t1; t2 ]
     | MapDef ((s, _bt), t) -> SymMap.remove s (free_vars t)
     | Apply (_pred, ts) -> free_vars_list ts
     | Let ((nm, t1), t2) ->
       SymMap.union expect_equal_types (free_vars t1) (SymMap.remove nm (free_vars t2))
     | Match (e, cases) ->
       let rec aux acc = function
         | [] -> acc
         | (pat, body) :: cases ->
           let bound = List.map fst (IT.bound_by_pattern pat) in
           let more =
             List.fold_left (fun sm x -> SymMap.remove x sm) (free_vars body) bound
           in
           aux (SymMap.union expect_equal_types more acc) cases
       in
       aux (free_vars e) cases
     | Constructor (_s, args) -> free_vars_list (List.map snd args))

and free_vars_list : 'a IT.term list -> arg_map =
  fun xs ->
  List.fold_left
    (fun sm t -> SymMap.union expect_equal_types sm (free_vars t))
    SymMap.empty
    xs
;;

let get_lower_bound ((x, bt) : Sym.sym * BT.t) (tm : IT.t) : IT.t =
  let min =
    match bt with
    | Bits (sign, sz) -> fst (BT.bits_range (sign, sz))
    | _ -> failwith "unsupported type for `each`"
  in
  let rec aux (tm : IT.t) : IT.t option =
    match tm with
    | IT (Binop (EQ, IT (Sym x', _, _), tm2), _, _)
    | IT (Binop (EQ, tm2, IT (Sym x', _, _)), _, _) ->
      if weak_sym_equal x x' then Some tm2 else None
    | IT (Binop (LE, tm', IT (Sym x', _, _)), _, _) when weak_sym_equal x x' -> Some tm'
    | IT (Binop (LT, tm', IT (Sym x', _, _)), _, _) when weak_sym_equal x x' ->
      Some
        (IT
           ( Binop (Add, tm', IT.num_lit_ Z.one bt Cerb_location.unknown)
           , bt
           , Cerb_location.unknown ))
    | IT (Binop (And, tm1, tm2), _, _) ->
      (match aux tm1, aux tm2 with
       | None, None -> None
       | None, tm' | tm', None -> tm'
       | Some tm1, Some tm2 ->
         Some (IT (Binop (Max, tm1, tm2), bt, Cerb_location.unknown)))
    | IT (Binop (Or, tm1, tm2), _, _) ->
      (match aux tm1, aux tm2 with
       | None, None | None, _ | _, None -> None
       | Some tm1, Some tm2 ->
         Some (IT (Binop (Min, tm1, tm2), bt, Cerb_location.unknown)))
    | _ -> None
  in
  aux tm |> Option.value ~default:(IT.num_lit_ min bt Cerb_location.unknown)
;;

let get_upper_bound ((x, bt) : Sym.sym * BT.t) (tm : IT.t) : IT.t =
  let max =
    match bt with
    | Bits (sign, sz) -> snd (BT.bits_range (sign, sz))
    | _ -> failwith "unsupported type for `each`"
  in
  let rec aux (tm : IT.t) : IT.t option =
    match tm with
    | IT (Binop (EQ, IT (Sym x', _, _), tm2), _, _)
    | IT (Binop (EQ, tm2, IT (Sym x', _, _)), _, _) ->
      if weak_sym_equal x x' then Some tm2 else None
    | IT (Binop (LE, IT (Sym x', _, _), tm'), _, _) when weak_sym_equal x x' -> Some tm'
    | IT (Binop (LT, IT (Sym x', _, _), tm'), _, _) when weak_sym_equal x x' ->
      Some
        (IT
           ( Binop (Sub, tm', IT.num_lit_ Z.one bt Cerb_location.unknown)
           , bt
           , Cerb_location.unknown ))
    | IT (Binop (And, tm1, tm2), _, _) ->
      (match aux tm1, aux tm2 with
       | None, None -> None
       | None, tm' | tm', None -> tm'
       | Some tm1, Some tm2 ->
         Some (IT (Binop (Min, tm1, tm2), bt, Cerb_location.unknown)))
    | IT (Binop (Or, tm1, tm2), _, _) ->
      (match aux tm1, aux tm2 with
       | None, None | None, _ | _, None -> None
       | Some tm1, Some tm2 ->
         Some (IT (Binop (Max, tm1, tm2), bt, Cerb_location.unknown)))
    | _ -> None
  in
  aux tm |> Option.value ~default:(IT.num_lit_ max bt Cerb_location.unknown)
;;

(* let reduce_exclusive ((x, bt) : Sym.sym * BT.t) (tm : IT.t) : IT.t = *)

let eliminate_each_in_resource_predicates (rps : Mucore.T.resource_predicates)
  : Mucore.T.resource_predicates
  =
  rps
;;

let eliminate_each_in_qpredicate_type
  (prog5 : unit Mucore.mu_file)
  (qt : RET.qpredicate_type)
  : (Sym.sym * RP.definition) * RET.predicate_type
  =
  let pred_name = Sym.fresh () in
  let i_sym, i_bt = qt.q in
  let iargs_bts =
    List.fold_left
      (SymMap.union expect_equal_types)
      (SymMap.singleton i_sym i_bt)
      (List.map free_vars (qt.pointer :: qt.step :: qt.permission :: qt.iargs))
    |> SymMap.filter (fun x_sym _ ->
      List.find_opt (weak_sym_equal x_sym) [ i_sym ] |> Option.is_none)
    |> SymMap.to_seq
    |> List.of_seq
  in
  let iargs_with (i : IT.t) : IT.t list =
    i
    :: List.map (fun (x_sym, bt) -> IT.sym_ (x_sym, bt, Cerb_location.unknown)) iargs_bts
  in
  let predicate : RP.definition =
    let offset_ct =
      match qt.step with
      | IT (Cast (_, IT (SizeOf ct, _, _)), _, _) -> ct
      | _ -> failwith "unreachable"
    in
    let upper_bound = get_upper_bound qt.q qt.permission in
    let i = IT.sym_ (i_sym, i_bt, Cerb_location.unknown) in
    let p_sym, _ = IT.fresh BT.Loc Cerb_location.unknown in
    let v_bt =
      match qt.name with
      | RET.Owned (ct, _) -> Memory.bt_of_sct ct
      | RET.PName name ->
        (List.assoc weak_sym_equal name prog5.mu_resource_predicates).oarg_bt
    in
    let v_sym, v = IT.fresh v_bt Cerb_location.unknown in
    let oarg_bt = BT.Map (i_bt, v_bt) in
    let r_sym, r = IT.fresh oarg_bt Cerb_location.unknown in
    let resource (lat : 'a LAT.t) : 'a LAT.t =
      LAT.Resource
        ( ( v_sym
          , ( P
                { name = qt.name
                ; pointer =
                    IT.arrayShift_
                      ~base:qt.pointer
                      ~index:i
                      offset_ct
                      Cerb_location.unknown
                ; iargs = qt.iargs
                }
            , v_bt ) )
        , (Cerb_location.unknown, None)
        , lat )
    in
    let recursive_call (lat : 'a LAT.t) : 'a LAT.t =
      LAT.Resource
        ( ( r_sym
          , ( P
                { name = PName pred_name
                ; pointer = IT.null_ Cerb_location.unknown
                ; iargs =
                    iargs_with
                      (IT.add_
                         (i, IT.num_lit_ Z.one i_bt Cerb_location.unknown)
                         Cerb_location.unknown)
                }
            , oarg_bt ) )
        , (Cerb_location.unknown, None)
        , lat )
    in
    let add_kv (map : IT.t) : IT.t = IT.map_set_ map (i, v) Cerb_location.unknown in
    (*
       predicate <oarg_bt> <pname>(pointer <p>, <iargs>) {
      if (x >= <upper_bound>) {
        take <V> = 
      }
    }
    *)
    { loc = Cerb_location.unknown
    ; pointer = p_sym
    ; iargs = (i_sym, i_bt) :: iargs_bts
    ; oarg_bt
    ; clauses =
        Some
          [ { loc = Cerb_location.unknown
            ; guard = IT.lt_ (upper_bound, i) Cerb_location.unknown
            ; packing_ft =
                LAT.I
                  (IT.const_map_
                     i_bt
                     (IT.default_ v_bt Cerb_location.unknown)
                     Cerb_location.unknown)
            }
          ; { loc = Cerb_location.unknown
            ; guard = IT.eq_ (upper_bound, i) Cerb_location.unknown
            ; packing_ft =
                LAT.I
                  (add_kv
                     (IT.const_map_
                        i_bt
                        (IT.default_ v_bt Cerb_location.unknown)
                        Cerb_location.unknown))
                |> resource
            }
            (* ; { loc = Cerb_location.unknown
            ; guard = IT.not_ qt.permission Cerb_location.unknown
            ; packing_ft = LAT.I r |> recursive_call
            } *)
          ; { loc = Cerb_location.unknown
            ; guard = IT.bool_ true Cerb_location.unknown
            ; packing_ft = LAT.I (add_kv r) |> recursive_call |> resource
            }
          ]
    }
  in
  let pt : RET.predicate_type =
    let lower_bound = get_lower_bound qt.q qt.permission in
    { name = PName pred_name
    ; pointer = IT.null_ Cerb_location.unknown
    ; iargs = iargs_with lower_bound
    }
  in
  (pred_name, predicate), pt
;;

let rec eliminate_each_in_arguments_l
  (prog5 : unit Mucore.mu_file)
  (args_l : _ mu_arguments_l)
  : (Sym.sym * RP.definition) list * _ mu_arguments_l
  =
  match args_l with
  | M_Define ((x, it), info, l) ->
    let preds, l = eliminate_each_in_arguments_l prog5 l in
    preds, M_Define ((x, it), info, l)
  | M_Resource ((x, (P pt, bt)), info, l) ->
    let preds, l = eliminate_each_in_arguments_l prog5 l in
    preds, M_Resource ((x, (P pt, bt)), info, l)
  | M_Resource ((x, (Q qt, bt)), info, l) ->
    let pred, pt = eliminate_each_in_qpredicate_type prog5 qt in
    let preds, l = eliminate_each_in_arguments_l prog5 l in
    pred :: preds, M_Resource ((x, (P pt, bt)), info, l)
  | M_Constraint (lc, info, l) ->
    let preds, l = eliminate_each_in_arguments_l prog5 l in
    preds, M_Constraint (lc, info, l)
  | M_I i -> [], M_I i
;;

let rec eliminate_each_in_arguments
  (prog5 : unit Mucore.mu_file)
  (args_and_body : _ mu_arguments)
  : (Sym.sym * RP.definition) list * _ mu_arguments
  =
  match args_and_body with
  | M_Computational (bound, info, a) ->
    let preds, a = eliminate_each_in_arguments prog5 a in
    preds, M_Computational (bound, info, a)
  | M_L l ->
    let preds, l = eliminate_each_in_arguments_l prog5 l in
    preds, M_L l
;;

let eliminate_each (prog5 : unit Mucore.mu_file) : unit Mucore.mu_file =
  let rpreds = ref prog5.mu_resource_predicates in
  let mu_funs =
    Pmap.map
      (fun decl ->
        match decl with
        | M_Proc (fn_loc, args_and_body, trusted, spec) ->
          let preds, args_and_body = eliminate_each_in_arguments prog5 args_and_body in
          rpreds := preds @ !rpreds;
          M_Proc (fn_loc, args_and_body, trusted, spec)
        | M_ProcDecl _ -> decl)
      prog5.mu_funs
  in
  let mu_resource_predicates = eliminate_each_in_resource_predicates !rpreds in
  { prog5 with mu_funs; mu_resource_predicates }
;;
