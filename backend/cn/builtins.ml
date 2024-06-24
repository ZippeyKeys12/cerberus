module SBT = SurfaceBaseTypes
open Resultat
open Effectful.Make(Resultat)
open TypeErrors
open IndexTerms



(* builtin function symbols *)
let mk_arg0 mk args loc = match args with
  | [] -> return (mk loc)
  | _ :: _ as xs -> fail {loc; msg = Number_arguments {has = List.Old.length xs; expect = 0}}

let mk_arg1 mk args loc = match args with
  | [x] -> return (mk x loc)
  | xs -> fail {loc; msg = Number_arguments {has = List.Old.length xs; expect = 1}}

let mk_arg2_err mk args loc = match args with
  | [x; y] -> mk (x, y) loc
  | xs -> fail {loc; msg = Number_arguments {has = List.Old.length xs; expect = 2}}

let mk_arg2 mk = mk_arg2_err (fun tup loc-> return (mk tup loc))

let mk_arg3_err mk args loc = match args with
  | [x; y; z] -> mk (x, y, z) loc
  | xs -> fail {loc; msg = Number_arguments {has = List.Old.length xs; expect = 3}}

let mk_arg3 mk = mk_arg3_err (fun tup loc -> return (mk tup loc))


let mk_arg5 mk args loc = match args with
  | [a;b;c;d;e] -> return (mk (a,b,c,d,e) loc)
  | xs -> fail {loc; msg = Number_arguments {has = List.Old.length xs; expect = 5}}


let min_bits_def (sign, n) =
  let (num, letter) = match sign with
    | BT.Unsigned -> (Z.zero, "u")
    | Signed -> (Z.(neg @@ shift_left one (Int.sub n 1)), "i") in
  let name = "MIN" ^ letter ^ Int.to_string n in
  (name, Sym.fresh_named name, mk_arg0 (fun loc ->
        IT.sterm_of_term @@ num_lit_ num (BT.Bits (sign, n)) loc))

let max_bits_def (sign, n) =
  let (num, letter) = match sign with
    | BT.Unsigned -> (Z.(shift_left one n - one), "u")
    | Signed -> (Z.(shift_left one (Int.sub n 1) - one), "i") in
  let name = "MAX" ^ letter ^ Int.to_string n in
  (name, Sym.fresh_named name, mk_arg0 (fun loc ->
       IT.sterm_of_term @@ num_lit_ num (BT.Bits (sign, n)) loc))

let mul_uf_def = ("mul_uf", Sym.fresh_named "mul_uf", mk_arg2 mul_no_smt_)
let div_uf_def = ("div_uf", Sym.fresh_named "div_uf", mk_arg2 div_no_smt_)
let power_uf_def = ("power_uf", Sym.fresh_named "power_uf", mk_arg2 exp_no_smt_)
let rem_uf_def = ("rem_uf", Sym.fresh_named "rem_uf", mk_arg2 rem_no_smt_)
let mod_uf_def = ("mod_uf", Sym.fresh_named "mod_uf", mk_arg2 mod_no_smt_)
let xor_uf_def = ("xor_uf", Sym.fresh_named "xor_uf", mk_arg2 (arith_binop XORNoSMT))
let bw_and_uf_def = ("bw_and_uf", Sym.fresh_named "bw_and_uf", mk_arg2 (arith_binop BWAndNoSMT))
let bw_or_uf_def = ("bw_or_uf", Sym.fresh_named "bw_or_uf", mk_arg2 (arith_binop BWOrNoSMT))

let bw_clz_uf_def = ("bw_clz_uf", Sym.fresh_named "bw_clz_uf", mk_arg1 (arith_unop BWCLZNoSMT))
let bw_ctz_uf_def = ("bw_ctz_uf", Sym.fresh_named "bw_ctz_uf", mk_arg1 (arith_unop BWCTZNoSMT))
let bw_ffs_uf_def = ("bw_ffs_uf", Sym.fresh_named "bw_ffs_uf", mk_arg1 (arith_unop BWFFSNoSMT))

let shift_left_def = ("shift_left", Sym.fresh_named "shift_left", mk_arg2 (arith_binop ShiftLeft))
let shift_right_def = ("shift_right",
    Sym.fresh_named "shift_right", mk_arg2 (arith_binop ShiftRight))

let power_def = ("power", Sym.fresh_named "power", mk_arg2 exp_)
let rem_def = ("rem", Sym.fresh_named "rem", mk_arg2 rem_)
let mod_def = ("mod", Sym.fresh_named "mod", mk_arg2 mod_)

let not_def = ("not", Sym.fresh_named "not", mk_arg1 not_)

let nth_list_def = ("nth_list", Sym.fresh_named "nth_list", mk_arg3 nthList_)

let array_to_list_def =
  ("array_to_list", Sym.fresh_named "array_to_list", mk_arg3_err
  (fun (arr, i, len) loc -> match SBT.is_map_bt (IT.bt arr) with
    | None ->
      let reason = "map/array operation" in
      let expected = "map/array" in
      fail {loc; msg = Illtyped_it {it = IT.pp arr; has = SBT.pp (IT.bt arr); expected; reason}}
    | Some (_, bt) -> return (array_to_list_ (arr, i, len) bt loc)
  ))

let in_loc_list_def =
  ("in_loc_list", Sym.fresh_named "in_loc_list",
    mk_arg2_err (fun tup loc -> return (IT.mk_in_loc_list tup loc)))


let cellpointer_def =
  ("cellPointer",
   Sym.fresh_named "cellPointer",
   mk_arg5 (fun (base, step, starti, endi, p) loc ->
       let base = IT.term_of_sterm base in
       let step = IT.term_of_sterm step in
       let starti = IT.term_of_sterm starti in
       let endi = IT.term_of_sterm endi in
       let p = IT.term_of_sterm p in
       IT.sterm_of_term (IT.cellPointer_ ~base ~step ~starti ~endi ~p loc)
     )
  )

let is_null_def =
  ("is_null",
   Sym.fresh_named "is_null",
   mk_arg1 (fun p loc' ->
       IT.sterm_of_term IT.(eq_ (IT.term_of_sterm p, null_ loc') loc')
     )
  )

let ptr_eq_def =
    ("ptr_eq",
        Sym.fresh_named "ptr_eq",
        mk_arg2 (fun (p1, p2) loc' ->
       IT.(sterm_of_term @@ eq_ (term_of_sterm p1, term_of_sterm p2) loc')
     )
   )

let prov_eq_def =
    ("prov_eq",
       Sym.fresh_named "prov_eq",
        mk_arg2 (fun (p1, p2) loc' ->
          IT.(sterm_of_term @@ eq_ (
             pointerToAllocIdCast_ (term_of_sterm p1) loc',
             pointerToAllocIdCast_ (term_of_sterm p2) loc'
          ) loc')
       )
   )

let addr_eq_def =
    ("addr_eq",
       Sym.fresh_named "addr_eq",
        mk_arg2 (fun (p1, p2) loc' ->
          IT.(sterm_of_term @@ eq_ (
             pointerToIntegerCast_ (term_of_sterm p1) loc',
             pointerToIntegerCast_ (term_of_sterm p2) loc'
          ) loc')
       )
   )

let max_min_bits =
  let sizes = [8; 16; 32; 64] in
  let signs = [BT.Unsigned; Signed] in
  List.Old.fold_left
    (fun acc sign ->
      List.Old.fold_left
        (fun acc size -> max_bits_def (sign, size) :: min_bits_def (sign, size) :: acc)
        acc
        sizes)
    []
    signs


let builtin_funs = max_min_bits @ [

  mul_uf_def;
  div_uf_def;
  power_uf_def;
  rem_uf_def;
  mod_uf_def;
  xor_uf_def;
  bw_and_uf_def;
  bw_or_uf_def;

  bw_clz_uf_def;
  bw_ctz_uf_def;
  bw_ffs_uf_def;

  shift_left_def;
  shift_right_def;

  power_def;
  rem_def;
  mod_def;

  not_def;

  nth_list_def;
  array_to_list_def;
  in_loc_list_def;

  cellpointer_def;
  is_null_def;
  prov_eq_def;
  ptr_eq_def;
  addr_eq_def;
]

let apply_builtin_funs fsym args loc =
  match List.Old.find_opt (fun (_, fsym', _) -> Sym.equal fsym fsym') builtin_funs with
  | None -> return None
  | Some (_, _, mk) ->
    let@ t = mk args loc in
    return (Some t)

let cn_builtin_fun_names =
  List.map ~f:(fun (str,sym,_) -> (str, sym)) builtin_funs
