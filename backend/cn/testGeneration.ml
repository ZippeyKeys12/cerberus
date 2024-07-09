module AT = ArgumentTypes
module BT = BaseTypes
module RP = ResourcePredicates
module IT = IndexTerms
module LS = LogicalSorts
module RET = ResourceTypes
module LC = LogicalConstraints
module LAT = LogicalArgumentTypes
module CF = Cerb_frontend
open CF
open EachElimination

let weak_sym_equal s1 s2 =
  String.equal (Pp_symbol.to_string_pretty s1) (Pp_symbol.to_string_pretty s2)
;;

let string_of_ctype (ty : Ctype.ctype) : string =
  Cerb_colour.do_colour := false;
  let tmp = String_ail.string_of_ctype ~is_human:true Ctype.no_qualifiers ty ^ " " in
  Cerb_colour.do_colour := true;
  tmp
;;

type cn_value =
  | CNVal_null
  | CNVal_integer of Z.t
  | CNVal_bits of (BT.sign * int) * Z.t
  | CNVal_bool of bool
  | CNVal_unit
  | CNVal_struct of (string * (Ctype.ctype * cn_value)) list
  | CNVal_constr of Sym.sym * (string * cn_value) list

(* let rec string_of_value (v : cn_value) : string =
  match v with
  | CNVal_null -> "NULL"
  | CNVal_bits ((Signed, bits), n) when bits <= 16 -> Int64.to_string (Z.to_int64 n)
  | CNVal_bits ((Unsigned, bits), n) when bits <= 16 ->
    Int64.to_string (Z.to_int64 n) ^ "U"
  | CNVal_bits ((Signed, bits), n) when bits <= 32 -> Int64.to_string (Z.to_int64 n) ^ "L"
  | CNVal_bits ((Unsigned, bits), n) when bits <= 32 -> string_of_int (Z.to_int n) ^ "UL"
  | CNVal_bits ((Signed, bits), n) when bits <= 64 ->
    Int64.to_string (Z.to_int64 n) ^ "LL"
  | CNVal_bits ((Unsigned, bits), n) when bits <= 64 ->
    Int64.to_string (Z.to_int64 n) ^ "ULL"
  | CNVal_struct ms ->
    "{ "
    ^ String.concat
        ", "
        (List.map
           (fun (x, (ty, v)) ->
             "." ^ x ^ ": " ^ string_of_ctype ty ^ " = " ^ string_of_value v)
           ms)
    ^ "}"
  | CNVal_bool b -> string_of_bool b
  | CNVal_integer n -> Int64.to_string (Z.to_int64 n)
  | CNVal_constr (_, ms) ->
    "{ "
    ^ String.concat ", " (List.map (fun (x, v) -> x ^ " = " ^ string_of_value v) ms)
    ^ "}"
  | CNVal_unit -> "()"
  | CNVal_bits _ -> failwith "unreachable (Generator.string_of_value)"
;; *)

type variables = (Symbol.sym * (Ctype.ctype * IT.t)) list

let string_of_variables (vars : variables) : string =
  "{ "
  ^ String.concat
      "; "
      (List.map
         (fun (x, (ty, e)) ->
           Pp_symbol.to_string_pretty x
           ^ " -> ("
           ^ string_of_ctype ty
           ^ ", "
           ^ Pp_utils.to_plain_pretty_string (IT.pp e)
           ^ ")")
         vars)
  ^ " }"
;;

type locations = (IT.t * Symbol.sym) list

let string_of_locations (locs : locations) : string =
  "{ "
  ^ String.concat
      "; "
      (List.map
         (fun (e, x) ->
           "(*"
           ^ Pp_utils.to_plain_pretty_string (IT.pp e)
           ^ ") -> "
           ^ Pp_symbol.to_string_pretty x)
         locs)
  ^ " }"
;;

type members = (Symbol.sym * (string * (Ctype.ctype * Symbol.sym)) list) list

let string_of_members (ms : members) : string =
  "{ "
  ^ String.concat
      "; "
      (List.map
         (fun (x, ms) ->
           Pp_symbol.to_string_pretty x
           ^ " -> {"
           ^ String.concat
               ", "
               (List.map
                  (fun (y, (ty, z)) ->
                    "."
                    ^ y
                    ^ ": "
                    ^ string_of_ctype ty
                    ^ " = "
                    ^ Pp_symbol.to_string_pretty z)
                  ms))
         ms)
  ^ " }"
;;

type constraints = IT.t list

let string_of_constraints (cs : constraints) : string =
  "{ "
  ^ String.concat "; " (List.map (fun e -> Pp_utils.to_plain_pretty_string (IT.pp e)) cs)
  ^ " }"
;;

type goal = variables * members * locations * constraints

let string_of_goal ((vars, ms, locs, cs) : goal) : string =
  "Vars: "
  ^ string_of_variables vars
  ^ "\n"
  ^ "Ms: "
  ^ string_of_members ms
  ^ "\n"
  ^ "Locs: "
  ^ string_of_locations locs
  ^ "\n"
  ^ "Cs: "
  ^ string_of_constraints cs
  ^ "\n"
;;

let sub_sym_clause (x : Sym.sym) (v : IT.t) (e : RP.clause) : RP.clause =
  { loc = e.loc
  ; guard = IT.subst (IT.make_subst [ x, v ]) e.guard
  ; packing_ft = LAT.subst IT.subst (IT.make_subst [ x, v ]) e.packing_ft
  }
;;

let add_to_vars_ms
  (sigma : GenTypes.genTypeCategory AilSyntax.sigma)
  (sym : Symbol.sym)
  (ty : Ctype.ctype)
  (vars : variables)
  (ms : members)
  : variables * members
  =
  match ty with
  | Ctype (_, Struct n) ->
    (match List.assoc weak_sym_equal n sigma.tag_definitions with
     | _, _, StructDef (membs, _) ->
       let f (Symbol.Identifier (_, id), (_, _, _, ty)) =
         let sym' = Symbol.fresh () in
         ( ( sym'
           , ( ty
             , IT.IT
                 ( Sym sym'
                 , BT.of_sct
                     AilTypesAux.is_signed_ity
                     Memory.size_of_integer_type
                     (Sctypes.of_ctype_unsafe Cerb_location.unknown ty)
                 , Cerb_location.unknown ) ) )
         , (id, (ty, sym')) )
       in
       let vars', member_data = List.split (List.map f membs) in
       ( (( sym
          , ( ty
            , IT.IT
                ( Sym sym
                , BT.of_sct
                    AilTypesAux.is_signed_ity
                    Memory.size_of_integer_type
                    (Sctypes.of_ctype_unsafe Cerb_location.unknown ty)
                , Cerb_location.unknown ) ) )
          :: vars)
         @ vars'
       , (sym, member_data) :: ms )
     | _ -> failwith ("No struct '" ^ Pp_symbol.to_string_pretty n ^ "' defined"))
  | _ ->
    ( ( sym
      , ( ty
        , IT.fresh_named
            (BT.of_sct
               AilTypesAux.is_signed_ity
               Memory.size_of_integer_type
               (Sctypes.of_ctype_unsafe Cerb_location.unknown ty))
            (Pp_symbol.to_string_pretty sym)
            Cerb_location.unknown
          |> snd ) )
      :: vars
    , ms )
;;

let ( >>= ) (x : 'a list) (f : 'a -> 'b list) : 'b list = List.flatten (List.map f x)
let return (x : 'a) : 'a list = [ x ]

let sym_term (x : Sym.sym) (ty : Ctype.ctype) : IT.t =
  IT.IT
    ( Sym x
    , BT.of_sct
        AilTypesAux.is_signed_ity
        Memory.size_of_integer_type
        (Sctypes.of_ctype_unsafe Cerb_location.unknown ty)
    , Cerb_location.unknown )
;;

let collect_lc (vars : variables) (ms : members) (lc : LC.t)
  : (variables * members * locations * constraints) list
  =
  match lc with
  | T it -> return (vars, ms, [], [ it ])
  | Forall _ -> failwith "`each` not supported"
;;

let rec collect_clauses
  (max_depth : int)
  (sigma : _ AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (vars : variables)
  (ms : members)
  (cs : RP.clause list)
  : (IT.t * variables * members * locations * constraints) list
  =
  match cs with
  | c :: cs' ->
    let rest =
      List.map
        (fun (v, vars, ms, locs, cs) ->
          ( v
          , vars
          , ms
          , locs
          , IT.IT (Unop (Not, c.guard), BT.Bool, Cerb_location.unknown) :: cs ))
        (collect_clauses max_depth sigma prog5 vars ms cs')
    in
    collect_lat_it max_depth sigma prog5 vars ms c.packing_ft
    >>= fun (v, vars, ms, locs, cs) -> (v, vars, ms, locs, c.guard :: cs) :: rest
  | [] -> []

and collect_ret
  (max_depth : int)
  (sigma : _ AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (vars : variables)
  (ms : members)
  (ret : RET.t)
  : (IT.t * variables * members * locations * constraints) list
  =
  match ret with
  | P { name = Owned (ty, _); pointer; iargs = [] } ->
    let sym = Symbol.fresh () in
    let ty = Sctypes.to_ctype ty in
    let vars, ms = add_to_vars_ms sigma sym ty vars ms in
    return (sym_term sym ty, vars, ms, [ pointer, sym ], [])
  | P { name = Owned (_, _); _ } -> failwith "Incorrect number of arguments for `Owned`"
  | P { name = PName psym; pointer; iargs } ->
    if max_depth <= 0
    then []
    else (
      let pred = List.assoc weak_sym_equal psym prog5.mu_resource_predicates in
      let args = List.combine (List.map fst pred.iargs) iargs in
      let clauses =
        Option.get pred.clauses
        |> List.map (sub_sym_clause pred.pointer pointer)
        |> List.map (List.fold_right (fun (x, v) acc -> sub_sym_clause x v acc) args)
      in
      collect_clauses (max_depth - 1) sigma prog5 vars ms clauses)
  | Q _ -> failwith "`each` not supported"

and collect_lat_it
  (max_depth : int)
  (sigma : _ AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (vars : variables)
  (ms : members)
  (lat : IT.t LAT.t)
  : (IT.t * variables * members * locations * constraints) list
  =
  let lat_subst x v e =
    LAT.subst IT.subst (IT.make_subst [ x, v ]) e
  in
  match lat with
  | Define ((x, tm), _, lat') ->
    collect_lat_it max_depth sigma prog5 vars ms (lat_subst x tm lat')
  | Resource ((x, (ret, _)), _, lat') ->
    collect_ret max_depth sigma prog5 vars ms ret
    >>= fun (v, vars, ms, locs, cs) ->
    collect_lat_it max_depth sigma prog5 vars ms (lat_subst x v lat')
    >>= fun (v', vars, ms, locs', cs') -> return (v', vars, ms, locs @ locs', cs @ cs')
  | Constraint (lc, _, lat') ->
    collect_lc vars ms lc
    >>= fun (vars, ms, locs, cs) ->
    collect_lat_it max_depth sigma prog5 vars ms lat'
    >>= fun (v, vars, ms, locs', cs') -> return (v, vars, ms, locs @ locs', cs @ cs')
  | I it -> return (it, vars, ms, [], [])
;;

let rec collect_lat
  (max_depth : int)
  (sigma : _ AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (vars : variables)
  (ms : members)
  (lat : unit LAT.t)
  : (variables * members * locations * constraints) list
  =
  let lat_subst x v e = LAT.subst (fun _ x -> x) (IT.make_subst [ x, v ]) e in
  match lat with
  | Define ((x, tm), _, lat') ->
    collect_lat max_depth sigma prog5 vars ms (lat_subst x tm lat')
  | Resource ((x, (ret, _)), _, lat') ->
    collect_ret max_depth sigma prog5 vars ms ret
    >>= fun (v, vars, ms, locs, cs) ->
    collect_lat max_depth sigma prog5 vars ms (lat_subst x v lat')
    >>= fun (vars, ms, locs', cs') -> return (vars, ms, locs @ locs', cs @ cs')
  | Constraint (lc, _, lat') ->
    collect_lc vars ms lc
    >>= fun (vars, ms, locs, cs) ->
    collect_lat max_depth sigma prog5 vars ms lat'
    >>= fun (vars, ms, locs', cs') -> return (vars, ms, locs @ locs', cs @ cs')
  | I _ -> return (vars, ms, [], [])
;;

let sub_sym_variables (x : Symbol.sym) (v : IT.t) (vars : variables) : variables =
  List.map (fun (x', (ty, e)) -> x', (ty, IT.subst (IT.make_subst [ x, v ]) e)) vars
;;

let sub_sym_locations (x : Symbol.sym) (v : IT.t) (locs : locations) : locations =
  List.map (fun (e, y) -> IT.subst (IT.make_subst [ x, v ]) e, y) locs
;;

let sub_sym_constraints (x : Symbol.sym) (v : IT.t) (cs : constraints) : constraints =
  List.map (fun e -> IT.subst (IT.make_subst [ x, v ]) e) cs
;;

let sub_sym_goal (x : Symbol.sym) (v : IT.t) ((vars, ms, locs, cs) : goal) : goal =
  sub_sym_variables x v vars, ms, sub_sym_locations x v locs, sub_sym_constraints x v cs
;;

let rec inline_constants' (g : goal) (iter : constraints) : goal =
  match iter with
  | IT (Binop (EQ, IT (Const c, bt, loc), IT (Sym x, _, _)), _, _) :: iter'
  | IT (Binop (EQ, IT (Sym x, _, _), IT (Const c, bt, loc)), _, _) :: iter' ->
    let g = sub_sym_goal x (IT (Const c, bt, loc)) g in
    inline_constants' g iter'
  | _ :: iter' -> inline_constants' g iter'
  | [] -> g
;;

let inline_constants (g : goal) : goal =
  let _, _, _, cs = g in
  inline_constants' g cs
;;

let rec eval_term_ (t : BT.t IT.term_) : cn_value =
  match t with
  | Const c ->
    (match c with
     | Null -> CNVal_null
     | Z n -> CNVal_integer n
     | Bits ((sign, bits), n) -> CNVal_bits ((sign, bits), n)
     | Bool b -> CNVal_bool b
     | Unit -> CNVal_unit
     | _ -> failwith "unsupported Const")
  | Sym x -> failwith ("free variable " ^ Pp_symbol.to_string_pretty x)
  | Unop (Not, it) ->
    (match eval_term it with
     | CNVal_bool b -> CNVal_bool (not b)
     | _ -> failwith "unsupported Not")
  | Unop (Negate, it) ->
    (match eval_term it with
     | CNVal_integer n -> CNVal_integer (Z.neg n)
     | CNVal_bits ((sign, bits), n) -> CNVal_bits ((sign, bits), Z.neg n)
     | _ -> failwith "unsupported Negate")
  | Binop (And, it1, it2) ->
    (match eval_term it1, eval_term it2 with
     | CNVal_bool b1, CNVal_bool b2 -> CNVal_bool (b1 && b2)
     | _ -> failwith "unsupported And")
  | Binop (Or, it1, it2) ->
    (match eval_term it1, eval_term it2 with
     | CNVal_bool b1, CNVal_bool b2 -> CNVal_bool (b1 || b2)
     | _ -> failwith "unsupported Or")
  | Binop (Implies, it1, it2) ->
    (match eval_term it1, eval_term it2 with
     | CNVal_bool b1, CNVal_bool b2 -> CNVal_bool ((not b1) || b2)
     | _ -> failwith "unsupported Impl")
  | Binop (Add, it1, it2) ->
    (match eval_term it1, eval_term it2 with
     | CNVal_integer n1, CNVal_integer n2 -> CNVal_integer (Z.add n1 n2)
     | CNVal_bits ((sign1, bits1), n1), CNVal_bits ((sign2, bits2), n2)
       when Stdlib.( = ) sign1 sign2 && bits1 = bits2 ->
       CNVal_bits ((sign1, bits1), Z.add n1 n2)
     | _ -> failwith "unsupported Add")
  | Binop (Sub, it1, it2) ->
    (match eval_term it1, eval_term it2 with
     | CNVal_integer n1, CNVal_integer n2 -> CNVal_integer (Z.sub n1 n2)
     | CNVal_bits ((sign1, bits1), n1), CNVal_bits ((sign2, bits2), n2)
       when Stdlib.( = ) sign1 sign2 && bits1 = bits2 ->
       CNVal_bits ((sign1, bits1), Z.sub n1 n2)
     | _ -> failwith "unsupported Sub")
  | Binop (Mul, it1, it2) | Binop (MulNoSMT, it1, it2) ->
    (match eval_term it1, eval_term it2 with
     | CNVal_integer n1, CNVal_integer n2 -> CNVal_integer (Z.mul n1 n2)
     | CNVal_bits ((sign1, bits1), n1), CNVal_bits ((sign2, bits2), n2)
       when Stdlib.( = ) sign1 sign2 && bits1 = bits2 ->
       CNVal_bits ((sign1, bits1), Z.mul n1 n2)
     | _ -> failwith "unsupported Mul")
  | Binop (Div, it1, it2) | Binop (DivNoSMT, it1, it2) ->
    (match eval_term it1, eval_term it2 with
     | CNVal_integer n1, CNVal_integer n2 -> CNVal_integer (Z.div n1 n2)
     | CNVal_bits ((sign1, bits1), n1), CNVal_bits ((sign2, bits2), n2)
       when Stdlib.( = ) sign1 sign2 && bits1 = bits2 ->
       CNVal_bits ((sign1, bits1), Z.div n1 n2)
     | _ -> failwith "unsupported Div")
  | Binop (Rem, it1, it2) | Binop (RemNoSMT, it1, it2) ->
    (match eval_term it1, eval_term it2 with
     | CNVal_integer n1, CNVal_integer n2 -> CNVal_integer (Z.rem n1 n2)
     | CNVal_bits ((sign1, bits1), n1), CNVal_bits ((sign2, bits2), n2)
       when Stdlib.( = ) sign1 sign2 && bits1 = bits2 ->
       CNVal_bits ((sign1, bits1), Z.rem n1 n2)
     | _ -> failwith "unsupported Rem")
  | Binop (LT, it1, it2) | Binop (LTPointer, it1, it2) ->
    (match eval_term it1, eval_term it2 with
     | CNVal_integer n1, CNVal_integer n2 -> CNVal_bool (Z.lt n1 n2)
     | CNVal_bits ((sign1, bits1), n1), CNVal_bits ((sign2, bits2), n2)
       when Stdlib.( = ) sign1 sign2 && bits1 = bits2 -> CNVal_bool (Z.lt n1 n2)
     | _ -> failwith "unsupported LT")
  | Binop (LE, it1, it2) | Binop (LEPointer, it1, it2) ->
    (match eval_term it1, eval_term it2 with
     | CNVal_integer n1, CNVal_integer n2 -> CNVal_bool (Z.leq n1 n2)
     | CNVal_bits ((sign1, bits1), n1), CNVal_bits ((sign2, bits2), n2)
       when Stdlib.( = ) sign1 sign2 && bits1 = bits2 -> CNVal_bool (Z.leq n1 n2)
     | _ -> failwith "unsupported LE")
  | Binop (Min, it1, it2) ->
    (match eval_term it1, eval_term it2 with
     | CNVal_integer n1, CNVal_integer n2 -> CNVal_integer (Z.min n1 n2)
     | CNVal_bits ((sign1, bits1), n1), CNVal_bits ((sign2, bits2), n2)
       when Stdlib.( = ) sign1 sign2 && bits1 = bits2 ->
       CNVal_bits ((sign1, bits1), Z.min n1 n2)
     | _ -> failwith "unsupported Min")
  | Binop (Max, it1, it2) ->
    (match eval_term it1, eval_term it2 with
     | CNVal_integer n1, CNVal_integer n2 -> CNVal_integer (Z.max n1 n2)
     | CNVal_bits ((sign1, bits1), n1), CNVal_bits ((sign2, bits2), n2)
       when Stdlib.( = ) sign1 sign2 && bits1 = bits2 ->
       CNVal_bits ((sign1, bits1), Z.max n1 n2)
     | _ -> failwith "unsupported Max")
  | Binop (EQ, it1, it2) ->
    (match eval_term it1, eval_term it2 with
     | CNVal_null, CNVal_null | CNVal_unit, CNVal_unit -> CNVal_bool true
     | CNVal_integer n1, CNVal_integer n2 -> CNVal_bool (Z.equal n1 n2)
     | CNVal_bits ((sign1, bits1), n1), CNVal_bits ((sign2, bits2), n2)
       when Stdlib.( = ) sign1 sign2 && bits1 = bits2 -> CNVal_bool (Z.equal n1 n2)
     | CNVal_bool b1, CNVal_bool b2 -> CNVal_bool (Bool.equal b1 b2)
     | _ -> failwith "unsupported EQ")
  | ITE (it1, it2, it3) ->
    (match eval_term it1 with
     | CNVal_bool b -> if b then eval_term it2 else eval_term it3
     | _ -> failwith "unsupported ITE")
  (* | Struct (x, yits) ->
     CNVal_struct
     (List.map
     (fun (y, it) ->
     let (Sym.Identifier (_, y)) = y in
     y, eval_term it)
     yits) *)
  | StructMember (it', x) ->
    (match eval_term it' with
     | CNVal_struct ms ->
       let (Sym.Identifier (_, x)) = x in
       List.assoc String.equal x ms |> snd
     | _ -> failwith "unsupported StructMember")
  | Constructor (x, yits) ->
    CNVal_constr
      ( x
      , List.map
          (fun (y, it) ->
            let (Sym.Identifier (_, y)) = y in
            y, eval_term it)
          yits )
  | SizeOf ty ->
    CNVal_bits
      ( (Unsigned, Memory.size_of_ctype Sctypes.(Integer Size_t))
      , Z.of_int (Memory.size_of_ctype ty) )
  | Let ((x, it1), it2) -> eval_term (IT.subst (IT.make_subst [ x, it1 ]) it2)
  (* *)
  | Unop (BWCLZNoSMT, _) -> failwith "todo: add support for Unop BWCLZNoSMT"
  | Unop (BWCTZNoSMT, _) -> failwith "todo: add support for Unop BWCTZNoSMT"
  | Unop (BWFFSNoSMT, _) -> failwith "todo: add support for Unop BWFFSNoSMT"
  | Binop (Exp, _, _) -> failwith "todo: add support for Binop Exp"
  | Binop (ExpNoSMT, _, _) -> failwith "todo: add support for Binop ExpNoSMT"
  | Binop (Mod, _, _) -> failwith "todo: add support for Binop Mod"
  | Binop (ModNoSMT, _, _) -> failwith "todo: add support for Binop ModNoSMT"
  | Binop (XORNoSMT, _, _) -> failwith "todo: add support for Binop XORNoSMT"
  | Binop (BWAndNoSMT, _, _) -> failwith "todo: add support for Binop BWAndNoSMT"
  | Binop (BWOrNoSMT, _, _) -> failwith "todo: add support for Binop BWOrNoSMT"
  | Binop (ShiftLeft, _, _) -> failwith "todo: add support for Binop ShiftLeft"
  | Binop (ShiftRight, _, _) -> failwith "todo: add support for Binop ShiftRight"
  | Binop (SetUnion, _, _) -> failwith "todo: add support for Binop SetUnion"
  | Binop (SetIntersection, _, _) ->
    failwith "todo: add support for Binop SetIntersection"
  | Binop (SetDifference, _, _) -> failwith "todo: add support for Binop SetDifference"
  | Binop (SetMember, _, _) -> failwith "todo: add support for Binop SetMember"
  | Binop (Subset, _, _) -> failwith "todo: add support for Binop Subset"
  | EachI _ -> failwith "todo: add support for EachI"
  | Tuple _ -> failwith "todo: add support for Tuple"
  | NthTuple _ -> failwith "todo: add support for NthTuple"
  | Struct _ -> failwith "todo: add support for Struct"
  | StructUpdate _ -> failwith "todo: add support for StructUpdate"
  | Record _ -> failwith "todo: add support for Record"
  | RecordMember _ -> failwith "todo: add support for RecordMember"
  | RecordUpdate _ -> failwith "todo: add support for RecordUpdate"
  | MemberShift _ -> failwith "todo: add support for MemberShift"
  | ArrayShift _ -> failwith "todo: add support for ArrayShift"
  | CopyAllocId _ -> failwith "todo: add support for CopyAllocId"
  | OffsetOf _ -> failwith "todo: add support for OffsetOf"
  | Nil _ -> failwith "todo: add support for Nil"
  | Cons _ -> failwith "todo: add support for Cons"
  | Head _ -> failwith "todo: add support for Head"
  | Tail _ -> failwith "todo: add support for Tail"
  | NthList _ -> failwith "todo: add support for NthList"
  | ArrayToList _ -> failwith "todo: add support for ArrayToList"
  | Representable _ -> failwith "todo: add support for Representable"
  | Good _ -> CNVal_bool true
  | Aligned _ -> failwith "todo: add support for Aligned"
  | WrapI _ -> failwith "todo: add support for WrapI"
  | MapConst _ -> failwith "todo: add support for MapConst"
  | MapSet _ -> failwith "todo: add support for MapSet"
  | MapGet _ -> failwith "todo: add support for MapGet"
  | MapDef _ -> failwith "todo: add support for MapDef"
  | Apply _ -> failwith "todo: add support for Apply"
  | Match _ -> failwith "todo: add support for Match"
  | Cast _ -> failwith "todo: add support for Cast"

and eval_term (it : IT.t) : cn_value =
  let (IT (it, _, _)) = it in
  eval_term_ it
;;

let rec remove_tautologies ((vars, ms, locs, cs) : goal) : goal =
  match cs with
  | IT (Binop (EQ, IT (Sym x, _, _), IT (Sym y, _, _)), _, _) :: cs
    when weak_sym_equal x y -> remove_tautologies (vars, ms, locs, cs)
  | c :: cs ->
    (try
       let v = eval_term c in
       if Stdlib.( = ) v (CNVal_bool true)
       then remove_tautologies (vars, ms, locs, cs)
       else failwith "Inconsistent constraints"
     with
     | Not_found | Failure _ ->
       let vars, ms, locs, cs = remove_tautologies (vars, ms, locs, cs) in
       vars, ms, locs, c :: cs)
  | [] -> vars, ms, locs, cs
;;

let rec cnf_ (e : BT.t IT.term_) : BT.t IT.term_ =
  match e with
  (* Double negation elimination *)
  | Unop (Not, IT (Unop (Not, IT (e, _, _)), _, _)) -> e
  (* Flip inequalities *)
  | Unop (Not, IT (Binop (LT, e1, e2), _, _)) -> Binop (LE, e2, e1)
  | Unop (Not, IT (Binop (LE, e1, e2), _, _)) -> Binop (LT, e2, e1)
  (* De Morgan's Law *)
  | Unop (Not, IT (Binop (And, e1, e2), info, loc)) ->
    Binop (Or, IT (Unop (Not, cnf e1), info, loc), IT (Unop (Not, cnf e2), info, loc))
  | Unop (Not, IT (Binop (Or, e1, e2), info, loc)) ->
    Binop (And, IT (Unop (Not, cnf e1), info, loc), IT (Unop (Not, cnf e2), info, loc))
  (* Distribute disjunction *)
  | Binop (Or, e1, IT (Binop (And, e2, e3), info, loc))
  | Binop (Or, IT (Binop (And, e2, e3), info, loc), e1) ->
    Binop (And, IT (Binop (Or, e1, e2), info, loc), IT (Binop (Or, e1, e3), info, loc))
  | _ -> e

and cnf (e : IT.t) : IT.t =
  let (IT (e, info, loc)) = e in
  IT (cnf_ e, info, loc)
;;

let rec inline_aliasing' (g : goal) (iter : constraints) : goal =
  match iter with
  | IT (Binop (EQ, IT (Sym x, info_x, loc_x), IT (Sym y, _, _)), info_y, loc_y) :: iter'
    ->
    let vars, _, _, _ = g in
    let g =
      match List.assoc weak_sym_equal x vars with
      | _, IT (Sym x', _, _) when weak_sym_equal x x' ->
        sub_sym_goal x (IT (Sym y, info_y, loc_y)) g
      | _ -> sub_sym_goal y (IT (Sym x, info_x, loc_x)) g
    in
    inline_aliasing' g iter'
  | _ :: iter' -> inline_aliasing' g iter'
  | [] -> g
;;

let inline_aliasing (g : goal) : goal =
  let _, _, _, cs = g in
  inline_aliasing' g cs
;;

let rec remove_nonnull_for_locs ((vars, ms, locs, cs) : goal) : goal =
  match cs with
  | IT (Unop (Not, IT (Binop (EQ, e, IT (Const Null, _, _)), _, _)), _, _) :: cs
    when List.assoc_opt Stdlib.( = ) e locs |> Option.is_some ->
    remove_nonnull_for_locs (vars, ms, locs, cs)
  | IT (Unop (Not, IT (Binop (EQ, IT (Const Null, _, _), e), _, _)), _, _) :: cs
    when List.assoc_opt Stdlib.( = ) e locs |> Option.is_some ->
    remove_nonnull_for_locs (vars, ms, locs, cs)
  | c :: cs ->
    let vars, ms, locs, cs = remove_nonnull_for_locs (vars, ms, locs, cs) in
    vars, ms, locs, c :: cs
  | [] -> vars, ms, locs, []
;;

let rec indirect_members_expr_ (ms : members) (e : BT.t IT.term_) : BT.t IT.term_ =
  match e with
  | StructMember (IT (Sym x, _, _), Symbol.Identifier (_, y)) ->
    let new_sym = List.assoc weak_sym_equal x ms |> List.assoc String.equal y |> snd in
    Sym new_sym
  | Unop (op, e') -> Unop (op, indirect_members_expr ms e')
  | Binop (op, e1, e2) ->
    Binop (op, indirect_members_expr ms e1, indirect_members_expr ms e2)
  | ITE (e_if, e_then, e_else) ->
    ITE
      ( indirect_members_expr ms e_if
      , indirect_members_expr ms e_then
      , indirect_members_expr ms e_else )
  | EachI ((min, (x', bt), max), e') ->
    EachI ((min, (x', bt), max), indirect_members_expr ms e')
  | Tuple es -> Tuple (List.map (indirect_members_expr ms) es)
  | NthTuple (i, e') -> NthTuple (i, indirect_members_expr ms e')
  | Struct (x', xes) ->
    Struct (x', List.map (fun (x', e') -> x', indirect_members_expr ms e') xes)
  | StructMember (e', x') -> StructMember (indirect_members_expr ms e', x')
  | StructUpdate ((e', x'), e'') ->
    StructUpdate ((indirect_members_expr ms e', x'), indirect_members_expr ms e'')
  | Record xes -> Record (List.map (fun (x', e') -> x', indirect_members_expr ms e') xes)
  | RecordMember (e', x') -> RecordMember (indirect_members_expr ms e', x')
  | RecordUpdate ((e', x'), e'') ->
    RecordUpdate ((indirect_members_expr ms e', x'), indirect_members_expr ms e'')
  | Constructor (x', xes) ->
    Constructor (x', List.map (fun (x', e') -> x', indirect_members_expr ms e') xes)
  | MemberShift (e', x', x'') -> MemberShift (indirect_members_expr ms e', x', x'')
  | ArrayShift { base; ct; index } ->
    ArrayShift
      { base = indirect_members_expr ms base; ct; index = indirect_members_expr ms index }
  | CopyAllocId { addr; loc } ->
    CopyAllocId
      { addr = indirect_members_expr ms addr; loc = indirect_members_expr ms loc }
  | Cons (e1, e2) -> Cons (indirect_members_expr ms e1, indirect_members_expr ms e2)
  | Head e' -> Head (indirect_members_expr ms e')
  | Tail e' -> Tail (indirect_members_expr ms e')
  | NthList (e1, e2, e3) ->
    NthList
      ( indirect_members_expr ms e1
      , indirect_members_expr ms e2
      , indirect_members_expr ms e3 )
  | ArrayToList (e1, e2, e3) ->
    ArrayToList
      ( indirect_members_expr ms e1
      , indirect_members_expr ms e2
      , indirect_members_expr ms e3 )
  | Representable (ty, e') -> Representable (ty, indirect_members_expr ms e')
  | Good (ty, e') -> Good (ty, indirect_members_expr ms e')
  | Aligned { t; align } ->
    Aligned { t = indirect_members_expr ms t; align = indirect_members_expr ms align }
  | WrapI (ty, e') -> WrapI (ty, indirect_members_expr ms e')
  | MapConst (bt, e') -> MapConst (bt, indirect_members_expr ms e')
  | MapSet (e1, e2, e3) ->
    MapSet
      ( indirect_members_expr ms e1
      , indirect_members_expr ms e2
      , indirect_members_expr ms e3 )
  | MapGet (e1, e2) -> MapGet (indirect_members_expr ms e1, indirect_members_expr ms e2)
  | MapDef (xbt, e') -> MapDef (xbt, indirect_members_expr ms e')
  | Apply (x', es) -> Apply (x', List.map (indirect_members_expr ms) es)
  | Let ((x', e1), e2) ->
    Let ((x', indirect_members_expr ms e1), indirect_members_expr ms e2)
  | Match (e', pes) ->
    Match
      ( indirect_members_expr ms e'
      , List.map (fun (p, e') -> p, indirect_members_expr ms e') pes )
  | Cast (bt, e') -> Cast (bt, indirect_members_expr ms e')
  | Sym _ | Const _ | SizeOf _ | OffsetOf _ | Nil _ -> e

and indirect_members_expr (ms : members) (e : IT.t) : IT.t =
  let (IT (e, info, loc)) = e in
  IT (indirect_members_expr_ ms e, info, loc)
;;

let indirect_members ((vars, ms, locs, cs) : goal) : goal =
  ( List.map (fun (x, (ty, e)) -> x, (ty, indirect_members_expr ms e)) vars
  , ms
  , List.map (fun (e, x) -> indirect_members_expr ms e, x) locs
  , List.map (fun e -> indirect_members_expr ms e) cs )
;;

let listify_constraints (cs : constraints) : constraints =
  let rec loop (c : IT.t) : constraints =
    match c with
    | IT (Binop (And, e1, e2), _, _) -> loop e1 @ loop e2
    | _ -> [ c ]
  in
  List.map loop cs |> List.flatten
;;

let simplify (g : goal) : goal =
  let g = indirect_members g in
  let vars, ms, locs, cs = g in
  let g = vars, ms, locs, List.map cnf cs in
  let g = remove_nonnull_for_locs g in
  let rec loop (g : goal) : goal =
    let og = g in
    let g = inline_constants g in
    let g = inline_aliasing g in
    let vars, ms, locs, cs = remove_tautologies g in
    let cs = listify_constraints cs in
    let g = vars, ms, locs, cs in
    if Stdlib.( <> ) og g then loop g else g
  in
  loop g
;;

type gen =
  | Arbitrary of Ctype.ctype
  | Return of Ctype.ctype * IT.t
  | Filter of Sym.sym * Ctype.ctype * IT.t * gen
  | Map of Sym.sym * Ctype.ctype * IT.t * gen
  | Alloc of Ctype.ctype * Sym.sym
  | Struct of Ctype.ctype * (string * Sym.sym) list

let rec string_of_gen (g : gen) : string =
  match g with
  | Arbitrary ty -> "arbitrary<" ^ string_of_ctype ty ^ ">"
  | Return (ty, e) ->
    "return<"
    ^ string_of_ctype ty
    ^ ">("
    ^ Pp_utils.to_plain_pretty_string (IT.pp e)
    ^ ")"
  | Filter (x, ty, e, g') ->
    "filter("
    ^ "|"
    ^ Pp_symbol.to_string_pretty x
    ^ ": "
    ^ string_of_ctype ty
    ^ "| "
    ^ Pp_utils.to_plain_pretty_string (IT.pp e)
    ^ ", "
    ^ string_of_gen g'
    ^ ")"
  | Map (x, ty, e, g') ->
    "map("
    ^ "|"
    ^ Pp_symbol.to_string_pretty x
    ^ ": "
    ^ string_of_ctype ty
    ^ "| "
    ^ Pp_utils.to_plain_pretty_string (IT.pp e)
    ^ ", "
    ^ string_of_gen g'
    ^ ")"
  | Alloc (ty, x) ->
    "alloc<" ^ string_of_ctype ty ^ ">(" ^ Pp_symbol.to_string_pretty x ^ ")"
  | Struct (ty, ms) ->
    "struct<"
    ^ string_of_ctype ty
    ^ ">("
    ^ String.concat
        ", "
        (List.map (fun (x, g') -> "." ^ x ^ ": " ^ Pp_symbol.to_string_pretty g') ms)
    ^ ")"
;;

type gen_context = (Symbol.sym * gen) list

let string_of_gen_context (gtx : gen_context) : string =
  "{ "
  ^ String.concat
      "; "
      (List.map
         (fun (x, g) ->
           "\"" ^ Pp_symbol.to_string_pretty x ^ "\" <- \"" ^ string_of_gen g ^ "\"")
         gtx)
  ^ " }"
;;

let filter_gen (x : Symbol.sym) (ty : Ctype.ctype) (cs : constraints) : gen =
  match cs with
  | c :: cs' ->
    Filter
      ( x
      , ty
      , List.fold_left
          (fun acc c' -> IT.IT (Binop (And, acc, c'), BT.Bool, Cerb_location.unknown))
          c
          cs'
      , Arbitrary ty )
  | [] -> Arbitrary ty
;;

let compile_gen (x : Symbol.sym) (ty : Ctype.ctype) (e : IT.t) (cs : constraints) : gen =
  match e with
  | IT (Sym x', _, _) when weak_sym_equal x x' -> filter_gen x ty cs
  | _ -> Return (ty, e)
;;

let rec compile_singles'
  (gtx : gen_context)
  (locs : locations)
  (cs : constraints)
  (iter : variables)
  : gen_context * variables
  =
  let get_loc x =
    List.find_map
      (fun (e, y) ->
        if weak_sym_equal x y
        then (
          match e with
          | IT.IT (Sym z, _, _) -> Some z
          | _ -> None)
        else None)
      locs
  in
  match iter with
  | (x, (ty, e)) :: iter' ->
    let var_in_gtx y =
      List.find_opt (fun (z, _) -> weak_sym_equal y z) gtx |> Option.is_some
    in
    let relevant_cs =
      List.filter
        (fun c ->
          List.exists
            (weak_sym_equal x)
            (c |> IT.free_vars |> IT.SymSet.to_seq |> List.of_seq))
        cs
    in
    let no_free_vars =
      List.for_all
        (fun c ->
          List.for_all
            (fun y -> weak_sym_equal x y || var_in_gtx y)
            (c |> IT.free_vars |> IT.SymSet.to_seq |> List.of_seq))
        relevant_cs
    in
    if no_free_vars
    then (
      let gen = compile_gen x ty e relevant_cs in
      let gen_loc = Alloc (Ctype.Ctype ([], Pointer (Ctype.no_qualifiers, ty)), x) in
      match get_loc x with
      | Some x_loc -> compile_singles' ((x_loc, gen_loc) :: (x, gen) :: gtx) locs cs iter'
      | None -> compile_singles' ((x, gen) :: gtx) locs cs iter')
    else (
      let gtx, iter' = compile_singles' gtx locs cs iter' in
      gtx, (x, (ty, e)) :: iter')
  | [] -> gtx, iter
;;

let rec compile_singles
  (gtx : gen_context)
  (vars : variables)
  (locs : locations)
  (cs : constraints)
  : gen_context
  =
  let gtx, vars = compile_singles' gtx locs cs vars in
  if List.non_empty vars then compile_singles gtx vars locs cs else gtx
;;

let rec compile_structs'
  (gtx : gen_context)
  (vars : variables)
  (ms : members)
  (locs : locations)
  : gen_context * members
  =
  let get_loc x =
    List.find_map
      (fun (e, y) ->
        if weak_sym_equal x y
        then (
          match e with
          | IT.IT (Sym z, _, _) -> Some z
          | _ -> None)
        else None)
      locs
  in
  match ms with
  | (x, syms) :: ms' ->
    let gtx, ms' = compile_structs' gtx vars ms' locs in
    let free_vars =
      not
        (List.for_all
           (fun (_, (_, sym)) -> List.assoc_opt weak_sym_equal sym gtx |> Option.is_some)
           syms)
    in
    if free_vars
    then gtx, (x, syms) :: ms'
    else (
      let _, (ty, _) = List.find (fun (y, _) -> weak_sym_equal x y) vars in
      let mems = List.map (fun (id, (_, sym)) -> id, sym) syms in
      match get_loc x with
      | Some loc ->
        let gen = Struct (ty, mems) in
        let gen_loc = Alloc (Ctype.Ctype ([], Pointer (Ctype.no_qualifiers, ty)), x) in
        (loc, gen_loc) :: (x, gen) :: gtx, ms'
      | None -> (x, Struct (ty, mems)) :: gtx, ms')
  | [] -> gtx, []
;;

let rec compile_structs
  (gtx : gen_context)
  (vars : variables)
  (ms : members)
  (locs : locations)
  : gen_context
  =
  let gtx, ms = compile_structs' gtx vars ms locs in
  if List.non_empty ms then compile_structs gtx vars ms locs else gtx
;;

let compile ((vars, ms, locs, cs) : goal) : gen_context =
  (* Not a location *)
  let vars' =
    List.filter
      (fun (x, _) ->
        List.for_all
          (fun (e, _) ->
            match e with
            | IT.IT (Sym y, _, _) -> not (weak_sym_equal x y)
            | _ -> true)
          locs)
      vars
  in
  (* Not a struct *)
  let vars' =
    List.filter
      (fun (x, _) -> List.for_all (fun (y, _) -> not (weak_sym_equal x y)) ms)
      vars'
  in
  let gtx = compile_singles [] vars' locs cs in
  compile_structs gtx vars ms locs |> List.rev
;;

type test_framework =
  | GTest
  | Catch2

let rec codify_it_ (e : BT.t IT.term_) : string =
  match e with
  | Const Null -> "nullptr"
  | Const (Bits ((Signed, bits), n)) when bits <= 16 -> Int64.to_string (Z.to_int64 n)
  | Const (Bits ((Unsigned, bits), n)) when bits <= 16 ->
    Int64.to_string (Z.to_int64 n) ^ "U"
  | Const (Bits ((Signed, bits), n)) when bits <= 32 ->
    Int64.to_string (Z.to_int64 n) ^ "L"
  | Const (Bits ((Unsigned, bits), n)) when bits <= 32 ->
    string_of_int (Z.to_int n) ^ "UL"
  | Const (Bits ((Signed, bits), n)) when bits <= 64 ->
    Int64.to_string (Z.to_int64 n) ^ "LL"
  | Const (Bits ((Unsigned, bits), n)) when bits <= 64 ->
    Int64.to_string (Z.to_int64 n) ^ "ULL"
  | Const (Bool b) -> string_of_bool b
  | Sym x -> Sym.pp_string x
  | Unop (Not, e') -> "(!" ^ codify_it e' ^ ")"
  | Unop (Negate, e') -> "(-" ^ codify_it e' ^ ")"
  | Binop (And, e1, e2) -> "(" ^ codify_it e1 ^ " && " ^ codify_it e2 ^ ")"
  | Binop (Or, e1, e2) -> codify_it e1 ^ " || " ^ codify_it e2 ^ ")"
  | Binop (Implies, e1, e2) -> "((!" ^ codify_it e1 ^ ") || " ^ codify_it e2 ^ ")"
  | Binop (Add, e1, e2) -> "(" ^ codify_it e1 ^ " + " ^ codify_it e2 ^ ")"
  | Binop (Sub, e1, e2) -> "(" ^ codify_it e1 ^ " - " ^ codify_it e2 ^ ")"
  | Binop (Mul, e1, e2) | Binop (MulNoSMT, e1, e2) ->
    "(" ^ codify_it e1 ^ " * " ^ codify_it e2 ^ ")"
  | Binop (Div, e1, e2) | Binop (DivNoSMT, e1, e2) ->
    "(" ^ codify_it e1 ^ " / " ^ codify_it e2 ^ ")"
  | Binop (XORNoSMT, e1, e2) -> "(" ^ codify_it e1 ^ " ^ " ^ codify_it e2 ^ ")"
  | Binop (BWAndNoSMT, e1, e2) -> "(" ^ codify_it e1 ^ " & " ^ codify_it e2 ^ ")"
  | Binop (BWOrNoSMT, e1, e2) -> "(" ^ codify_it e1 ^ " | " ^ codify_it e2 ^ ")"
  | Binop (ShiftLeft, e1, e2) -> "(" ^ codify_it e1 ^ " << " ^ codify_it e2 ^ ")"
  | Binop (ShiftRight, e1, e2) -> "(" ^ codify_it e1 ^ " >> " ^ codify_it e2 ^ ")"
  | Binop (LT, e1, e2) | Binop (LTPointer, e1, e2) ->
    "(" ^ codify_it e1 ^ " < " ^ codify_it e2 ^ ")"
  | Binop (LE, e1, e2) | Binop (LEPointer, e1, e2) ->
    "(" ^ codify_it e1 ^ " <= " ^ codify_it e2 ^ ")"
  | Binop (EQ, e1, e2) -> "(" ^ codify_it e1 ^ " == " ^ codify_it e2 ^ ")"
  (* *)
  | _ -> failwith "unsupported operation"

and codify_it (e : IT.t) : string =
  let (IT (e, _, _)) = e in
  codify_it_ e
;;

let rec codify_gen' (g : gen) : string =
  match g with
  | Arbitrary ty -> "rc::gen::arbitrary<" ^ string_of_ctype ty ^ ">()"
  | Return (ty, e) -> "rc::gen::just<" ^ string_of_ctype ty ^ ">(" ^ codify_it e ^ ")"
  | Filter (x', ty, e, g') ->
    let gen = codify_gen' g' in
    "rc::gen::suchThat("
    ^ gen
    ^ ", [=]("
    ^ string_of_ctype ty
    ^ " "
    ^ Pp_symbol.to_string_pretty x'
    ^ "){ return "
    ^ codify_it e
    ^ "; })"
  | Map (x', ty, e, g') ->
    let gen = codify_gen' g' in
    "rc::gen::map("
    ^ gen
    ^ ", [=]("
    ^ string_of_ctype ty
    ^ " "
    ^ Pp_symbol.to_string_pretty x'
    ^ "){ return "
    ^ codify_it e
    ^ "; })"
  | Alloc (ty, x) ->
    "rc::gen::just<" ^ string_of_ctype ty ^ ">(&" ^ Pp_symbol.to_string_pretty x ^ ")"
  | Struct (ty, ms) ->
    "rc::gen::just<"
    ^ string_of_ctype ty
    ^ ">({ "
    ^ String.concat
        ", "
        (List.map (fun (x, y) -> "." ^ x ^ " = " ^ Pp_symbol.to_string_pretty y) ms)
    ^ "})"
;;

(* let get_gen_ty (g : gen) : Ctype.ctype =
   match g with
   | Arbitrary ty
   | Return (ty, _)
   | Filter (_, ty, _, _)
   | Map (_, ty, _, _)
   | Alloc (ty, _)
   | Struct (ty, _) -> ty
   ;; *)

let codify_gen (x : Sym.sym) (g : gen) : string =
  "/* "
  ^ string_of_gen g
  ^ " */\n"
  ^ "auto "
  ^ Pp_symbol.to_string_pretty x
  ^ " = *"
  ^ codify_gen' g
  ^ ";\n"
;;

let rec codify_gen_context (gtx : gen_context) : string =
  match gtx with
  | (x, g) :: gtx' -> codify_gen x g ^ codify_gen_context gtx'
  | [] -> ""
;;

let codify_pbt_header
  (tf : test_framework)
  (suite : string)
  (test : string)
  (oc : out_channel)
  : unit
  =
  match tf with
  | GTest ->
    output_string
      oc
      ("\nRC_GTEST_PROP(Test" ^ String.capitalize_ascii suite ^ ", " ^ test ^ ", ()){\n")
  | Catch2 ->
    output_string
      oc
      ("\nTEST_CASE(\""
       ^ test
       ^ "\"){\n\trc::prop(\"["
       ^ String.lowercase_ascii suite
       ^ "]\"), [](){\n")
;;

let codify_pbt
  (tf : test_framework)
  (instrumentation : Core_to_mucore.instrumentation)
  (args : (Symbol.sym * Ctype.ctype) list)
  (index : int)
  (oc : out_channel)
  (gtx : gen_context)
  : unit
  =
  codify_pbt_header
    tf
    (Pp_symbol.to_string_pretty instrumentation.fn)
    ("Test" ^ string_of_int index)
    oc;
  output_string oc (codify_gen_context gtx);
  output_string oc (Pp_symbol.to_string_pretty instrumentation.fn);
  output_string oc "(";
  output_string
    oc
    (args |> List.map fst |> List.map Pp_symbol.to_string_pretty |> String.concat ", ");
  output_string oc ");\n";
  match tf with
  | GTest -> output_string oc "}\n\n"
  | Catch2 -> output_string oc "})}\n"
;;

let get_args (sigma : _ AilSyntax.sigma) (fun_name : Sym.sym)
  : (Sym.sym * Ctype.ctype) list
  =
  let lookup_fn (x, _) = weak_sym_equal x fun_name in
  let fn_decl = List.filter lookup_fn sigma.declarations in
  let fn_def = List.filter lookup_fn sigma.function_definitions in
  let arg_types, arg_syms =
    match fn_decl, fn_def with
    | ( (_, (_, _, Decl_function (_, _, arg_types, _, _, _))) :: _
      , (_, (_, _, _, arg_syms, _)) :: _ ) ->
      let arg_types = List.map (fun (_, ctype, _) -> ctype) arg_types in
      arg_types, arg_syms
    | _ -> [], []
  in
  List.combine arg_syms arg_types
;;

let rec get_lat_from_at (at : _ AT.t) : _ LAT.t =
  match at with
  | AT.Computational (_, _, at') -> get_lat_from_at at'
  | AT.L lat -> lat
;;

let generate_pbt
  (max_depth : int)
  (sigma : _ AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (tf : test_framework)
  (oc : out_channel)
  (instrumentation : Core_to_mucore.instrumentation)
  : unit
  =
  let args = get_args sigma instrumentation.fn in
  let vars, ms =
    List.fold_left
      (fun (vars, ms) (x, ty) -> add_to_vars_ms sigma x ty vars ms)
      ([], [])
      args
  in
  output_string oc ("/* Begin:\n" ^ string_of_goal (vars, ms, [], []) ^ "*/\n\n");
  let lat =
    Option.get instrumentation.internal |> get_lat_from_at |> LAT.map (fun _ -> ())
  in
  List.iteri
    (fun i g ->
      output_string oc ("/* Collected:\n" ^ string_of_goal g ^ "*/\n\n");
      let g = simplify g in
      output_string oc ("/* Simplified:\n" ^ string_of_goal g ^ "*/\n\n");
      let gtx = compile g in
      output_string oc ("/* Compiled: " ^ string_of_gen_context gtx ^ "*/\n");
      codify_pbt tf instrumentation args i oc gtx)
    (collect_lat max_depth sigma prog5 vars ms lat)
;;

let main
  (output_dir : string)
  (filename : string)
  (max_depth : int)
  (sigma : _ AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (tf : test_framework)
  : unit
  =
  let prog5 = eliminate_each prog5 in
  let instrumentation_list, _symbol_table =
    Core_to_mucore.collect_instrumentation prog5
  in
  let instrumentation_list =
    instrumentation_list
    |> List.filter (fun (inst : Core_to_mucore.instrumentation) ->
      match Cerb_location.get_filename inst.fn_loc with
      | Some filename' -> String.equal filename filename'
      | None -> false)
  in
  let oc = Stdlib.open_out (output_dir ^ "test_" ^ Filename.basename filename ^ ".cpp") in
  List.iter (generate_pbt max_depth sigma prog5 tf oc) instrumentation_list
;;
