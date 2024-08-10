module BT = BaseTypes
module IT = IndexTerms
open Utils
module CF = Cerb_frontend
open Dsl

type test_framework = GTest

module type TF_Codify = sig
  val codify_header_files : out_channel -> unit

  val codify_header : string -> string -> string
end

module GTest_Codify = struct
  let codify_header_files (oc : out_channel) : unit =
    output_string oc "#include <gtest/gtest.h>\n";
    output_string oc "#include <rapidcheck/gtest.h>\n"


  let codify_header (suite : string) (test : string) : string =
    "RC_GTEST_PROP(Test" ^ String.capitalize_ascii suite ^ ", " ^ test ^ ", ())\n"
end

let rec codify_it_ (e : BT.t IT.term_) : string option =
  let exception Unsupported_codify_it in
  try
    Some
      (match e with
       | Const Null -> "nullptr"
       | Const (Bits ((Signed, bits), n)) when bits <= 16 ->
         Int64.to_string (Z.to_int64 n)
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
       | Sym x -> codify_sym x
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
       | Binop (BW_And, e1, e2) -> "(" ^ codify_it e1 ^ " & " ^ codify_it e2 ^ ")"
       | Binop (BWOrNoSMT, e1, e2) -> "(" ^ codify_it e1 ^ " | " ^ codify_it e2 ^ ")"
       | Binop (ShiftLeft, e1, e2) -> "(" ^ codify_it e1 ^ " << " ^ codify_it e2 ^ ")"
       | Binop (ShiftRight, e1, e2) -> "(" ^ codify_it e1 ^ " >> " ^ codify_it e2 ^ ")"
       | Binop (LT, e1, e2) | Binop (LTPointer, e1, e2) ->
         "(" ^ codify_it e1 ^ " < " ^ codify_it e2 ^ ")"
       | Binop (LE, e1, e2) | Binop (LEPointer, e1, e2) ->
         "(" ^ codify_it e1 ^ " <= " ^ codify_it e2 ^ ")"
       | Binop (EQ, e1, e2) -> "(" ^ codify_it e1 ^ " == " ^ codify_it e2 ^ ")"
       | Binop (Mod, e1, e2) -> "(" ^ codify_it e1 ^ " % " ^ codify_it e2 ^ ")"
       | ITE (e1, e2, e3) ->
         "(" ^ codify_it e1 ^ " ? " ^ codify_it e2 ^ " : " ^ codify_it e3 ^ ")"
       (* *)
       | _ -> raise Unsupported_codify_it)
  with
  | Unsupported_codify_it -> None


and codify_it (e : IT.t) : string =
  let (IT (e_, _, _)) = e in
  match codify_it_ e_ with
  | Some str -> str
  | None ->
    failwith ("unsupported operation " ^ CF.Pp_utils.to_plain_pretty_string (IT.pp e))


let codify_base_type (ty : GT.base_type) : string = GT.pp_base_type ty |> Pp.plain

let rec codify_gen_term (gt : gen_term) : string =
  (if !Cerb_debug.debug_level > 0 then
     "/* " ^ CF.Pp_utils.to_plain_string (pp_gen_term gt) ^ " */\n"
   else
     "")
  ^
  match gt with
  | GT (tys, Arbitrary) -> "rc::gen::arbitrary<" ^ codify_base_type tys ^ ">()"
  | GT (tys, Just it) ->
    "rc::gen::just<" ^ codify_base_type tys ^ ">(" ^ codify_it it ^ ")"
  | GT (tys, Alloc it) ->
    let sym = Sym.fresh () in
    let ty' = match tys with Loc ty -> ty | _ -> failwith "invalid" in
    "rc::gen::map("
    ^ codify_it it
    ^ ", [=]("
    ^ codify_base_type ty'
    ^ " "
    ^ codify_sym sym
    ^ "){ auto *p = ("
    ^ codify_base_type tys
    ^ ") malloc(sizeof("
    ^ codify_base_type ty'
    ^ ")); *p = "
    ^ codify_sym sym
    ^ "; })"
  | GT (_, Call (fsym, _gts)) -> Sym.pp_string fsym ^ failwith "todo"


let rec codify_gen (g : gen) : Pp.document =
  let open Pp in
  match g with
  | Asgn ((it_addr, gt), it_val, g') ->
    space
    ^^ star
    ^^ parens (string (codify_base_type gt))
    ^^ parens (IT.pp it_addr)
    ^^ space
    ^^ equals
    ^^ space
    ^^ string (codify_it it_val)
    ^^ semi
    ^^ break 1
    ^^ codify_gen g'
  | Let ([ x ], gt, g') ->
    string "auto "
    ^^ string (codify_sym x)
    ^^ string " = *"
    ^^ string (codify_gen_term gt)
    ^^ semi
    ^^ break 1
    ^^ codify_gen g'
  | Let (xs, gt, g') ->
    string "auto {"
    ^^ separate_map (comma ^^ space) (fun x -> x |> codify_sym |> string) xs
    ^^ string "} = *"
    ^^ string (codify_gen_term gt)
    ^^ semi
    ^^ break 1
    ^^ codify_gen g'
  | Return it -> string "return " ^^ string (codify_it it)
  | Assert _ -> failwith "todo: assert"
  | ITE (it_cond, g_then, g_else) ->
    string "if ("
    ^^ string (codify_it it_cond)
    ^^ string ") {"
    ^^ break 1
    ^^ codify_gen g_then
    ^^ break 1
    ^^ string "} else {"
    ^^ break 1
    ^^ codify_gen g_else
    ^^ break 1
    ^^ string "}"


let codify_gen_def (gd : gen_def) : Pp.document =
  let open Pp in
  let _ = gd.body |> Option.get |> codify_gen in
  string "todo: gen_def"


let rec codify_gen_context (gtx : gen_context) : Pp.document =
  let open Pp in
  match gtx with
  | (x, g) :: gtx' ->
    assert (x == g.name);
    codify_gen_def g ^^ codify_gen_context gtx'
  | [] -> empty


module Impl (C : TF_Codify) = struct
  open C

  let codify_function_signature
    (sigma : _ CF.AilSyntax.sigma)
    (instrumentation : Core_to_mucore.instrumentation)
    : string
    =
    let lookup_fn (x, _) = sym_codified_equal x instrumentation.fn in
    let fsym, (_, _, fdecl) = List.nth (List.filter lookup_fn sigma.declarations) 0 in
    CF.Pp_utils.to_plain_pretty_string (CF.Pp_ail.pp_function_prototype fsym fdecl)


  let codify_pbt
    (instrumentation : Core_to_mucore.instrumentation)
    (args : (Sym.sym * Sctypes.t) list)
    (index : int)
    (oc : out_channel)
    (gtx : gen_context)
    : unit
    =
    output_string
      oc
      (codify_header (codify_sym instrumentation.fn) ("Test" ^ string_of_int index));
    output_string oc "{\n";
    output_string oc (gtx |> codify_gen_context |> Pp.plain);
    output_string oc (codify_sym instrumentation.fn);
    output_string oc "(";
    output_string oc (args |> List.map fst |> List.map codify_sym |> String.concat ", ");
    output_string oc ");\n";
    output_string oc "}\n\n"


  let codify_prelude
    (sigma : _ CF.AilSyntax.sigma)
    (inst_list : Core_to_mucore.instrumentation list)
    (oc : out_channel)
    : unit
    =
    output_string oc "#include <cstdlib>\n";
    output_string oc "#include <cstdint>\n";
    output_string oc "#include <rapidcheck.h>\n";
    codify_header_files oc;
    output_string oc "\n";
    List.iter
      (fun d ->
        output_string oc "extern \"C\" ";
        output_string
          oc
          (CF.Pp_utils.to_plain_pretty_string (CF.Pp_ail.pp_tag_definition d));
        output_string oc "\n\n")
      sigma.tag_definitions;
    List.iter
      (fun inst ->
        output_string oc "extern \"C\" ";
        output_string oc (codify_function_signature sigma inst);
        output_string oc "\n\n")
      inst_list
end

let codify_prelude
  (tf : test_framework)
  (sigma : _ CF.AilSyntax.sigma)
  (inst_list : Core_to_mucore.instrumentation list)
  (oc : out_channel)
  : unit
  =
  match tf with
  | GTest ->
    let open Impl (GTest_Codify) in
    codify_prelude sigma inst_list oc


let codify_pbt
  (tf : test_framework)
  (instrumentation : Core_to_mucore.instrumentation)
  (args : (Sym.sym * Sctypes.t) list)
  (index : int)
  (oc : out_channel)
  (gtx : gen_context)
  : unit
  =
  match tf with
  | GTest ->
    let open Impl (GTest_Codify) in
    codify_pbt instrumentation args index oc gtx


type codify_result =
  { gens : Pp.document;
    tests : Pp.document
  }

type codify_context = (string * codify_result) list

type t = codify_context

let codify (tf : test_framework) (_ : gen_context) : t =
  codify_prelude tf (failwith "codify") (failwith "codify") (failwith "codify");
  []


let save ~(output_dir : string) (ctx : t) : unit =
  let aux ((filename, res) : string * codify_result) : unit =
    output_string
      (Stdlib.open_out
         (Filename.concat
            output_dir
            ("gen_" ^ (filename |> Filename.basename |> Filename.chop_extension) ^ ".h")))
      (Pp.plain res.gens);
    output_string
      (Stdlib.open_out
         (Filename.concat
            output_dir
            ("test_" ^ (filename |> Filename.basename |> Filename.chop_extension) ^ ".cpp")))
      (Pp.plain res.tests)
  in
  List.iter aux ctx
