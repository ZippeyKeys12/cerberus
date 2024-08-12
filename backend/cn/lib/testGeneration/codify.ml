module BT = BaseTypes
module IT = IndexTerms
module CF = Cerb_frontend
open Dsl

type test_framework = GTest

module type TF_Codify = sig
  val codify_test_includes : unit -> Pp.document

  val codify_pbt : Pp.document -> Pp.document -> Pp.document -> Pp.document
end

module GTest_Codify = struct
  let codify_test_includes () : Pp.document =
    let open Pp in
    string "#include <gtest/gtest.h>"
    ^^ hardline
    ^^ string "#include <rapidcheck/gtest.h>"


  let codify_pbt (suite : Pp.document) (test_name : Pp.document) (body : Pp.document)
    : Pp.document
    =
    let open Pp in
    string "RC_GTEST_PROP"
    ^^ parens
         (string (String.capitalize_ascii (Pp.plain ~width:90 suite))
          ^^ comma
          ^^ space
          ^^ test_name
          ^^ comma
          ^^ space
          ^^ parens empty)
    ^^ space
    ^^ braces (nest 2 (break 1 ^^ body) ^^ break 1)
end

let codify_function_signature
  (sigma : _ CF.AilSyntax.sigma)
  (instrumentation : Core_to_mucore.instrumentation)
  : Pp.document
  =
  let lookup_fn (fsym, _) = Sym.equal fsym instrumentation.fn in
  let fsym, (_, _, fdecl) = List.nth (List.filter lookup_fn sigma.declarations) 0 in
  CF.Pp_ail.pp_function_prototype fsym fdecl


let codify_declarations
  (sigma : _ CF.AilSyntax.sigma)
  (inst_list : Core_to_mucore.instrumentation list)
  : Pp.document
  =
  let open Pp in
  separate_map
    (ifflat (blank 1) (twice hardline))
    (fun tag_def ->
      string "extern"
      ^^ space
      ^^ dquotes (string "C")
      ^^ space
      ^^ CF.Pp_ail.pp_tag_definition tag_def)
    sigma.tag_definitions
  ^^ separate_map
       (ifflat (blank 1) (twice hardline))
       (fun inst ->
         string "extern"
         ^^ space
         ^^ dquotes (string "C")
         ^^ space
         ^^ codify_function_signature sigma inst)
       inst_list


let rec codify_base_type (gbt : GT.base_type) : Pp.document =
  let open Pp in
  match gbt with
  | Unit -> Sctypes.pp Void
  | Bool -> string "boolean"
  | Integer -> failwith "todo: integer"
  | Bits (sgn, sz) ->
    let ibty =
      (CF.Ocaml_implementation.get ()).type_alias_map.intN_t_alias sz |> Option.get
    in
    let ity =
      match sgn with Signed -> CF.Ctype.Signed ibty | Unsigned -> CF.Ctype.Unsigned ibty
    in
    CF.Pp_ail.pp_integerType ity
  | Loc gbt' -> codify_base_type gbt' ^^ star
  | Struct tag -> string "struct" ^^ space ^^ Sym.pp tag
  | Map (gbt_key, gbt_value) ->
    string "std::map"
    ^^ angles (codify_base_type gbt_key ^^ comma ^^ space ^^ codify_base_type gbt_value)
  | List gbt' -> string "std::list" ^^ angles (codify_base_type gbt')
  | Tuple gbts ->
    string "std::tuple" ^^ angles (separate_map (comma ^^ space) codify_base_type gbts)
  | _ -> failwith ("unsupported (" ^ __LOC__ ^ ")")


let rec codify_it_ (e : BT.t IT.term_) : Pp.document option =
  let open Pp in
  let exception Unsupported_codify_it in
  try
    Some
      (parens
         (match e with
          | Const Null -> string "nullptr"
          | Const (Bits ((Signed, bits), n)) when bits <= 16 ->
            string (Int64.to_string (Z.to_int64 n))
          | Const (Bits ((Unsigned, bits), n)) when bits <= 16 ->
            string (Int64.to_string (Z.to_int64 n)) ^^ string "U"
          | Const (Bits ((Signed, bits), n)) when bits <= 32 ->
            string (Int64.to_string (Z.to_int64 n)) ^^ string "L"
          | Const (Bits ((Unsigned, bits), n)) when bits <= 32 ->
            string (Int64.to_string (Z.to_int64 n)) ^^ string "UL"
          | Const (Bits ((Signed, bits), n)) when bits <= 64 ->
            string (Int64.to_string (Z.to_int64 n)) ^^ string "LL"
          | Const (Bits ((Unsigned, bits), n)) when bits <= 64 ->
            string (Int64.to_string (Z.to_int64 n)) ^^ string "ULL"
          | Const (Bool b) -> bool b
          | Sym x -> Sym.pp x
          | Unop (Not, e') -> bang ^^ codify_it e'
          | Unop (Negate, e') -> minus ^^ codify_it e'
          | Binop (And, e1, e2) ->
            codify_it e1 ^^ space ^^ twice ampersand ^^ space ^^ codify_it e2
          | Binop (Or, e1, e2) ->
            codify_it e1 ^^ space ^^ twice bar ^^ space ^^ codify_it e2
          | Binop (Implies, e1, e2) ->
            parens (bang ^^ codify_it e1) ^^ space ^^ twice bar ^^ space ^^ codify_it e2
          | Binop (Add, e1, e2) -> codify_it e1 ^^ space ^^ plus ^^ space ^^ codify_it e2
          | Binop (Sub, e1, e2) -> codify_it e1 ^^ space ^^ minus ^^ space ^^ codify_it e2
          | Binop (Mul, e1, e2) | Binop (MulNoSMT, e1, e2) ->
            codify_it e1 ^^ space ^^ star ^^ space ^^ codify_it e2
          | Binop (Div, e1, e2) | Binop (DivNoSMT, e1, e2) ->
            codify_it e1 ^^ space ^^ slash ^^ space ^^ codify_it e2
          | Binop (XORNoSMT, e1, e2) ->
            codify_it e1 ^^ space ^^ string "^" ^^ space ^^ codify_it e2
          | Binop (BW_And, e1, e2) ->
            codify_it e1 ^^ space ^^ ampersand ^^ space ^^ codify_it e2
          | Binop (BWOrNoSMT, e1, e2) ->
            codify_it e1 ^^ space ^^ bar ^^ space ^^ codify_it e2
          | Binop (ShiftLeft, e1, e2) ->
            codify_it e1 ^^ space ^^ twice (langle ()) ^^ space ^^ codify_it e2
          | Binop (ShiftRight, e1, e2) ->
            codify_it e1 ^^ space ^^ twice (rangle ()) ^^ space ^^ codify_it e2
          | Binop (LT, e1, e2) | Binop (LTPointer, e1, e2) ->
            codify_it e1 ^^ space ^^ langle () ^^ space ^^ codify_it e2
          | Binop (LE, e1, e2) | Binop (LEPointer, e1, e2) ->
            codify_it e1 ^^ space ^^ langle () ^^ equals ^^ space ^^ codify_it e2
          | Binop (EQ, e1, e2) ->
            codify_it e1 ^^ space ^^ twice equals ^^ space ^^ codify_it e2
          | Binop (Mod, e1, e2) ->
            codify_it e1 ^^ space ^^ percent ^^ space ^^ codify_it e2
          | ITE (e1, e2, e3) ->
            codify_it e1
            ^^ break 1
            ^^ string "?"
            ^^ break 1
            ^^ codify_it e2
            ^^ space
            ^^ colon
            ^^ space
            ^^ codify_it e3
          | ArrayShift { base; ct = _; index } ->
            parens
              (parens (string "uintptr_t") ^^ codify_it base ^^ plus ^^ codify_it index)
          | Tuple its ->
            string "std::make_tuple"
            ^^ parens (separate_map (comma ^^ break 1) codify_it its)
          (* *)
          | _ -> raise Unsupported_codify_it))
  with
  | Unsupported_codify_it -> None


and codify_it (e : IT.t) : Pp.document =
  let (IT (e_, _, _)) = e in
  match codify_it_ e_ with
  | Some str -> str
  | None ->
    failwith ("unsupported operation " ^ CF.Pp_utils.to_plain_pretty_string (IT.pp e))


let rec codify_gen_term (gt : gen_term) : Pp.document =
  let open Pp in
  match gt with
  | GT (gbt, Arbitrary) ->
    string "rc::gen::arbitrary" ^^ angles (codify_base_type gbt) ^^ parens empty
  | GT (gbt, Just it) ->
    string "rc::gen::just" ^^ angles (codify_base_type gbt) ^^ parens (codify_it it)
  | GT (gbt, Alloc it) ->
    let sym = Sym.fresh () in
    let gbt, gbt' =
      match gbt with
      | Loc gbt ->
        let gbt = match gbt with Unit -> GT.of_bt Memory.size_bt | _ -> gbt in
        (GT.Loc gbt, gbt)
      | _ -> failwith "invalid"
    in
    string "rc::gen::map"
    ^^ parens
         (nest
            2
            (break 0
             ^^ codify_gen_term (GT (GT.of_bt Memory.size_bt, Just it))
             ^^ comma
             ^^ break 1
             ^^ brackets equals
             ^^ parens (codify_base_type (GT.of_bt Memory.size_bt) ^^ space ^^ Sym.pp sym)
             ^^ braces
                  (nest
                     2
                     (break 1
                      ^^ string "auto *p = "
                      ^^ parens (codify_base_type gbt)
                      ^^ string "malloc"
                      ^^ parens
                           (Sym.pp sym
                            ^^ space
                            ^^ star
                            ^^ space
                            ^^ string "sizeof"
                            ^^ parens (codify_base_type gbt'))
                      ^^ semi
                      ^^ break 1
                      ^^ string "*p ="
                      ^^ space
                      ^^ Sym.pp sym
                      ^^ semi
                      ^^ break 1
                      ^^ string "return"
                      ^^ space
                      ^^ char 'p'
                      ^^ semi)
                   ^^ break 1))
          ^^ break 0)
  | GT (_, Call (fsym, its)) ->
    Sym.pp fsym ^^ parens (separate_map (comma ^^ break 1) codify_it its)


let rec codify_gen (g : gen) : Pp.document =
  let open Pp in
  let debug_comment doc =
    if !Cerb_debug.debug_level > 0 then
      enclose (string "/* ") (string " */") doc ^^ hardline
    else
      empty
  in
  match g with
  | Asgn ((it_addr, gt), it_val, g') ->
    star
    ^^ parens (codify_base_type gt)
    ^^ parens (codify_it it_addr)
    ^^ space
    ^^ equals
    ^^ space
    ^^ codify_it it_val
    ^^ semi
    ^^ break 1
    ^^ string "auto "
    ^^
    let sym = Sym.fresh () in
    Sym.pp sym
    ^^ string " = (char *)\"generator\";"
    ^^ break 1
    ^^ string "cn_assume_ownership"
    ^^ parens
         (separate
            (comma ^^ space)
            [ string "(void*)" ^^ codify_it it_addr;
              string "sizeof" ^^ parens (codify_base_type gt);
              Sym.pp sym
            ])
    ^^ semi
    ^^ break 1
    ^^ codify_gen g'
  | Let ([ x ], gt, g') ->
    debug_comment (pp_gen_term gt)
    ^^ string "auto"
    ^^ space
    ^^ (match gt with GT (Tuple _, _) -> brackets (Sym.pp x) | _ -> Sym.pp x)
    ^^ string " = *"
    ^^ codify_gen_term gt
    ^^ semi
    ^^ break 1
    ^^ codify_gen g'
  | Let (xs, gt, g') ->
    string "auto"
    ^^ space
    ^^ brackets (separate_map (comma ^^ space) (fun x -> x |> Sym.pp) xs)
    ^^ space
    ^^ string "= *"
    ^^ codify_gen_term gt
    ^^ semi
    ^^ break 1
    ^^ codify_gen g'
  | Return it -> string "return" ^^ space ^^ codify_it it ^^ semi
  | Assert (lcs, g') ->
    concat_map (fun lc -> debug_comment (string "assert" ^^ parens (LC.pp lc))) lcs
    ^^ string "// todo: assert"
    ^^ hardline
    ^^ codify_gen g'
  | ITE (it_cond, g_then, g_else) ->
    debug_comment (string "if" ^^ space ^^ IT.pp it_cond)
    ^^ string "if ("
    ^^ codify_it it_cond
    ^^ string ")"
    ^^ space
    ^^ braces (nest 2 (break 1 ^^ codify_gen g_then) ^^ break 1)
    ^^ space
    ^^ string "else"
    ^^ braces (nest 2 (break 1 ^^ codify_gen g_else) ^^ break 1)


let codify_gen_def ({ name; iargs; oargs; body; _ } : gen_def) : Pp.document =
  let open Pp in
  string "std::tuple"
  ^^ angles (separate_map (comma ^^ space) codify_base_type oargs)
  ^^ space
  ^^ Sym.pp name
  ^^ parens
       (separate_map
          (comma ^^ space)
          (fun (x, gbt) -> codify_base_type gbt ^^ space ^^ Sym.pp x)
          iargs)
  ^^ space
  ^^ braces (nest 2 (break 1 ^^ (body |> Option.get |> codify_gen)) ^^ break 1)


let rec codify_gen_context (gtx : gen_context) : Pp.document =
  let open Pp in
  match gtx with
  | (x, g) :: gtx' ->
    assert (x == g.name);
    codify_gen_def g ^^ break 1 ^^ codify_gen_context gtx'
  | [] -> empty


let codify_generators
  (sigma : _ CF.AilSyntax.sigma)
  (inst_list : Core_to_mucore.instrumentation list)
  (gtx : gen_context)
  : Pp.document
  =
  let open Pp in
  separate_map
    hardline
    string
    [ "#include <cstdlib>";
      "#include <cstdint>";
      "#include <tuple>";
      "#include <rapidcheck.h>"
    ]
  ^^ twice hardline
  ^^ string "extern"
  ^^ space
  ^^ dquotes (char 'C')
  ^^ space
  ^^ string
       "void cn_assume_ownership(void *generic_c_ptr, unsigned long size, char *fun);"
  ^^ break 1
  ^^ codify_declarations sigma inst_list
  ^^ twice hardline
  ^^ string "namespace cn"
  ^^ space
  ^^ braces
       (nest
          2
          (break 1
           ^^ string "namespace gen"
           ^^ braces (nest 2 (break 1 ^^ codify_gen_context gtx) ^^ break 1))
        ^^ break 1)
  ^^ hardline


module Impl (C : TF_Codify) = struct
  let codify_test_includes (gen_filename : string) =
    let open Pp in
    string "#include"
    ^^ space
    ^^ dquotes (string gen_filename)
    ^^ hardline
    ^^ C.codify_test_includes ()
    ^^ twice hardline
    ^^ string "extern \"C\" void initialise_ownership_ghost_state(void);"
    ^^ hardline
    ^^ string "extern \"C\" void initialise_ghost_stack_depth(void);"
    ^^ twice hardline
    ^^ string "extern \"C\" void ghost_stack_depth_incr(void);"
    ^^ hardline
    ^^ string "extern \"C\" void ghost_stack_depth_decr(void);"
    ^^ twice hardline
    ^^ string
         "extern \"C\" void c_add_local_to_ghost_state(uintptr_t ptr_to_local, size_t \
          size);"
    ^^ hardline
    ^^ string
         "extern \"C\" void c_remove_local_from_ghost_state(uintptr_t ptr_to_local, \
          size_t size);"


  let codify_pbt
    (sigma : _ CF.AilSyntax.sigma)
    (instrumentation : Core_to_mucore.instrumentation)
    : Pp.document
    =
    let args : (Sym.sym * Sctypes.t) list =
      let lookup_fn (x, _) = Sym.equal x instrumentation.fn in
      let fn_decl = List.filter lookup_fn sigma.declarations in
      let fn_def = List.filter lookup_fn sigma.function_definitions in
      let arg_types, arg_syms =
        match (fn_decl, fn_def) with
        | ( (_, (_, _, Decl_function (_, _, arg_types, _, _, _))) :: _,
            (_, (_, _, _, arg_syms, _)) :: _ ) ->
          let arg_types =
            List.map (fun (_, ctype, _) -> Option.get (Sctypes.of_ctype ctype)) arg_types
          in
          (arg_types, arg_syms)
        | _ -> ([], [])
      in
      List.combine arg_syms arg_types
    in
    let open Pp in
    C.codify_pbt
      (Sym.pp instrumentation.fn)
      (string "RandomTests")
      (string "initialise_ownership_ghost_state();"
       ^^ break 1
       ^^ string "initialise_ghost_stack_depth();"
       ^^ break 1
       ^^ string "ghost_stack_depth_incr();"
       ^^ twice hardline
       ^^ string "auto"
       ^^ space
       ^^ brackets (separate_map (comma ^^ break 1) (fun (x, _) -> Sym.pp x) args)
       ^^ space
       ^^ equals
       ^^ space
       ^^ string "cn::gen::"
       ^^ Sym.pp instrumentation.fn
       ^^ parens empty
       ^^ semi
       ^^ twice hardline
       ^^ separate_map
            (semi ^^ break 1)
            (fun (x, ty) ->
              string "c_add_local_to_ghost_state((uintptr_t) &"
              ^^ Sym.pp x
              ^^ string ", sizeof("
              ^^ CF.Pp_ail.pp_ctype CF.Ctype.no_qualifiers (Sctypes.to_ctype ty)
              ^^ string "))")
            args
       ^^ semi
       ^^ twice hardline
       ^^ Sym.pp instrumentation.fn
       ^^ parens
            (separate_map
               (comma ^^ break 1)
               (fun (x, ty) ->
                 parens (CF.Pp_ail.pp_ctype CF.Ctype.no_qualifiers (Sctypes.to_ctype ty))
                 ^^ Sym.pp x)
               args)
       ^^ semi
       ^^ twice hardline
       ^^ separate_map
            (semi ^^ break 1)
            (fun (x, ty) ->
              string "c_remove_local_from_ghost_state((uintptr_t) &"
              ^^ Sym.pp x
              ^^ string ", sizeof("
              ^^ CF.Pp_ail.pp_ctype CF.Ctype.no_qualifiers (Sctypes.to_ctype ty)
              ^^ string "))")
            args
       ^^ semi
          (* ^^ break 1
             ^^ string "ghost_stack_depth_decr();" *))


  let codify_tests
    (sigma : _ CF.AilSyntax.sigma)
    (inst_list : Core_to_mucore.instrumentation list)
    (gen_filename : string)
    : Pp.document
    =
    let open Pp in
    codify_test_includes gen_filename
    ^^ twice hardline
    ^^ separate_map (twice hardline) (codify_pbt sigma) inst_list
    ^^ hardline


  let codify_file
    (output_dir : string)
    ((gen_filename, generators) : string * Pp.document)
    ((test_filename, tests) : string * Pp.document)
    : unit
    =
    output_string
      (Stdlib.open_out (Filename.concat output_dir gen_filename))
      (Pp.plain ~width:90 generators);
    output_string
      (Stdlib.open_out (Filename.concat output_dir test_filename))
      (Pp.plain ~width:90 tests)


  let codify
    ~(output_dir : string)
    (sigma : _ CF.AilSyntax.sigma)
    (prog5 : unit Mucore.mu_file)
    (gtx : gen_context)
    : unit
    =
    let filenames =
      let module StrSet = Set.Make (String) in
      gtx
      |> List.map (fun (_, Dsl.{ filename; _ }) -> filename)
      |> StrSet.of_list
      |> StrSet.to_seq
      |> List.of_seq
    in
    let inst_list (filename : string) : Core_to_mucore.instrumentation list =
      let gtx =
        List.filter
          (fun (_, { filename = filename'; _ }) -> String.equal filename filename')
          gtx
      in
      prog5
      |> Core_to_mucore.collect_instrumentation
      |> fst
      |> List.filter (fun (inst : Core_to_mucore.instrumentation) ->
        gtx |> List.find_opt (fun (x, _) -> Sym.equal x inst.fn) |> Option.is_some)
    in
    List.iter
      (fun filename ->
        let inst_list = inst_list filename in
        let gen_filename =
          "gen_" ^ (filename |> Filename.basename |> Filename.chop_extension) ^ ".hpp"
        in
        let test_filename =
          "test_" ^ (filename |> Filename.basename |> Filename.chop_extension) ^ ".cpp"
        in
        codify_file
          output_dir
          (gen_filename, codify_generators sigma inst_list gtx)
          (test_filename, codify_tests sigma inst_list gen_filename))
      filenames
end

let codify
  ~(output_dir : string)
  (tf : test_framework)
  (sigma : _ CF.AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (gtx : gen_context)
  : unit
  =
  match tf with
  | GTest ->
    let open Impl (GTest_Codify) in
    codify ~output_dir sigma prog5 gtx
