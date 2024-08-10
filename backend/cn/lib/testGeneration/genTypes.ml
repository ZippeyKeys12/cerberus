module BT = BaseTypes
module LC = LogicalConstraints

type base_type =
  | Unit
  | Bool
  | Integer
  | Bits of BT.sign * int
  | Real
  | Alloc_id
  | Loc of base_type
  | CType
  | Struct of Sym.t
  | Datatype of Sym.t
  | Record of member_types
  | Map of base_type * base_type
  | List of base_type
  | Tuple of base_type list
  | Set of base_type
[@@deriving eq, ord]

and member_types = (Id.t * base_type) list

let rec of_bt (bt : BT.t) : base_type =
  match bt with
  | Unit -> Unit
  | Bool -> Bool
  | Integer -> Integer
  | Bits (sgn, sz) -> Bits (sgn, sz)
  | Real -> Real
  | Alloc_id -> Alloc_id
  | Loc -> Loc Unit
  | CType -> CType
  | Struct tag -> Struct tag
  | Datatype constr -> Datatype constr
  | Record tys -> Record (List.map (fun (x, bt) -> (x, of_bt bt)) tys)
  | Map (ty_key, ty_value) -> Map (of_bt ty_key, of_bt ty_value)
  | List bt' -> List (of_bt bt')
  | Tuple bts -> Tuple (List.map of_bt bts)
  | Set bt' -> Set (of_bt bt')


let rec of_sct = function
  | Sctypes.Void -> Unit
  | Integer ity ->
    Bits
      ( (if Memory.is_signed_integer_type ity then Signed else Unsigned),
        Memory.size_of_integer_type ity * 8 )
  | Array (sct, _) -> Map (of_sct Sctypes.(Integer (Unsigned Intptr_t)), of_sct sct)
  | Pointer ty -> Loc (of_sct ty)
  | Struct tag -> Struct tag
  | Function _ -> Cerb_debug.error "todo: function types"


let rec pp_base_type =
  let open Pp in
  function
  | Unit -> !^"void"
  | Bool -> !^"bool"
  | Integer -> !^"integer"
  | Bits (Signed, n) -> !^("i" ^ string_of_int n)
  | Bits (Unsigned, n) -> !^("u" ^ string_of_int n)
  | Real -> !^"real"
  | Loc gt -> !^"pointer" ^^ angles (pp_base_type gt)
  | Alloc_id -> !^"alloc_id"
  | CType -> !^"ctype"
  | Struct sym -> !^"struct" ^^^ Sym.pp sym
  | Datatype sym -> !^"datatype" ^^^ Sym.pp sym
  | Record members ->
    braces (flow_map comma (fun (s, bt) -> pp_base_type bt ^^^ Id.pp s) members)
  | Map (agt, rgt) -> !^"map" ^^ angles (pp_base_type agt ^^ comma ^^^ pp_base_type rgt)
  | List gt -> !^"list" ^^ angles (pp_base_type gt)
  | Tuple nbts -> !^"tuple" ^^ angles (flow_map comma pp_base_type nbts)
  | Set t -> !^"set" ^^ angles (pp_base_type t)


type refined_type = Sctypes.t * (Sym.t * LC.t list list)

let pp_refined_type ((ty, (x, lcss)) : refined_type) : Pp.document =
  let open Pp in
  let intersect lcs =
    match lcs with
    | _ :: _ ->
      group
        (parens
           (nest 2 (separate_map (space ^^ ampersand ^^ ampersand ^^ break 1) LC.pp lcs)))
    | [] -> string "true"
  in
  let union lcss =
    match lcss with
    | _ :: _ :: _ ->
      group
        (break 1
         ^^ nest 2 (separate_map (space ^^ bar ^^ bar ^^ break 1) intersect lcss)
         ^^ break 1)
    | [ lcs ] -> intersect lcs
    | [] -> string "true"
  in
  match lcss with
  | _ :: _ ->
    lbrace
    ^^ space
    ^^ Sym.pp x
    ^^ colon
    ^^ space
    ^^ Sctypes.pp ty
    ^^ space
    ^^ bar
    ^^ space
    ^^ union lcss
  | [] -> Sctypes.pp ty


type gen_type =
  { args : refined_type list;
    rets : refined_type list
  }

let pp_gen_type ({ args; rets } : gen_type) : Pp.document =
  let open Pp in
  let args = parens (group (separate_map (comma ^^ break 1) pp_refined_type args)) in
  let rets = parens (group (separate_map (comma ^^ break 1) pp_refined_type rets)) in
  infix_arrow args rets


type t = gen_type

let pp = pp_gen_type
