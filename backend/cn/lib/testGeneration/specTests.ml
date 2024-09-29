module CF = Cerb_frontend
module A = CF.AilSyntax
module C = CF.Ctype
module CtA = Cn_internal_to_ail
module Utils = Executable_spec_utils
module BT = BaseTypes

let debug_log_file : out_channel option ref = ref None

let debug_log (str : string) : unit =
  match !debug_log_file with Some oc -> output_string oc str | None -> ()


let debug_stage (stage : string) (str : string) : unit =
  debug_log (stage ^ ":\n");
  debug_log (str ^ "\n\n")


let compile_generators
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (prog5 : unit Mucore.mu_file)
  (insts : Core_to_mucore.instrumentation list)
  =
  let ctx = GenCompile.compile prog5.mu_resource_predicates insts in
  debug_stage "Compile" (ctx |> GenDefinitions.pp_context |> Pp.plain ~width:80);
  let ctx = ctx |> GenNormalize.normalize prog5 in
  debug_stage "Normalize" (ctx |> GenDefinitions.pp_context |> Pp.plain ~width:80);
  let ctx = ctx |> GenDistribute.distribute in
  debug_stage "Distribute" (ctx |> GenDefinitions.pp_context |> Pp.plain ~width:80);
  let ctx = ctx |> GenOptimize.optimize in
  debug_stage "Optimize" (ctx |> GenDefinitions.pp_context |> Pp.plain ~width:80);
  let ctx = ctx |> GenRuntime.elaborate in
  debug_stage "Elaborated" (ctx |> GenRuntime.pp |> Pp.plain ~width:80);
  let doc = ctx |> GenCodeGen.compile sigma in
  debug_stage "CodeGen" (Pp.plain ~width:80 doc);
  doc


(* TODO:
   Per test:
   - Initialize everything
   - Call generators
   - Loop until `n` or failure
   - Return on failure? Exit on failure?
*)

let compile_tests
  (filename : string)
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (insts : Core_to_mucore.instrumentation list)
  : Pp.document
  =
  let _main_decl : A.sigma_declaration =
    ( Sym.fresh_named "main",
      ( Locations.other __LOC__,
        CF.Annot.Attrs [],
        Decl_function
          ( false,
            (C.no_qualifiers, CF.Ctype.signed_int),
            [ (C.no_qualifiers, CF.Ctype.signed_int, false);
              (C.no_qualifiers, CF.Ctype.pointer_to_char, false)
            ],
            false,
            false,
            false ) ) )
  in
  let declarations : A.sigma_declaration list =
    (* main_decl :: *)
    insts
    |> List.map (fun (inst : Core_to_mucore.instrumentation) ->
      (inst.fn, List.assoc Sym.equal inst.fn sigma.declarations))
  in
  let args : (Sym.t * (Sym.t * C.ctype) list) list =
    (* main_decl :: *)
    List.map
      (fun (inst : Core_to_mucore.instrumentation) ->
        ( inst.fn,
          let _, _, _, xs, _ = List.assoc Sym.equal inst.fn sigma.function_definitions in
          match List.assoc Sym.equal inst.fn declarations with
          | _, _, Decl_function (_, _, cts, _, _, _) ->
            List.combine xs (List.map (fun (_, ct, _) -> ct) cts)
          | _ -> failwith __LOC__ ))
      insts
  in
  let sigma' = { A.empty_sigma with declarations } in
  let convert_from ((x, ct) : Sym.t * C.ctype) =
    CF.Pp_ail.pp_expression
      (Utils.mk_expr
         (CtA.wrap_with_convert_from
            A.(
              AilEmemberofptr
                ( Utils.mk_expr (AilEident (Sym.fresh_named "res")),
                  Sym.Identifier (Locations.other __LOC__, Sym.pp_string x) ))
            (Memory.bt_of_sct (Sctypes.of_ctype_unsafe (Locations.other __LOC__) ct))))
  in
  let suite = List.hd (String.split_on_char '.' filename) in
  let open Pp in
  string "#include "
  ^^ dquotes (string filename)
  ^^ twice hardline
  ^^ CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, sigma')
  ^^ hardline
  ^^ concat_map
       (fun (inst : Core_to_mucore.instrumentation) ->
         string "CN_TEST_CASE"
         ^^ parens
              (separate
                 (comma ^^ space)
                 [ string suite;
                   Sym.pp inst.fn;
                   Pp.int 100;
                   separate_map
                     (comma ^^ space)
                     convert_from
                     (List.assoc Sym.equal inst.fn args)
                 ])
         ^^ twice hardline)
       insts
  ^^ string "int main"
  ^^ parens (string "int argc, char* argv[]")
  ^^ break 1
  ^^ braces
       (nest
          2
          (hardline
           ^^ concat_map
                (fun fn ->
                  string "cn_register_test_case"
                  ^^ parens
                       (separate
                          (comma ^^ space)
                          [ string "(char*)" ^^ dquotes (string suite);
                            string "(char*)" ^^ dquotes (Sym.pp fn);
                            separate_map
                              underscore
                              string
                              [ "&cn_test"; suite; Sym.pp_string fn ]
                          ])
                  ^^ semi
                  ^^ hardline)
                (List.map fst declarations)
           ^^ string "return cn_test_main(argc, argv);")
        ^^ hardline)
  ^^ hardline


let save (output_dir : string) (filename : string) (doc : Pp.document) : unit =
  let oc = Stdlib.open_out (Filename.concat output_dir filename) in
  output_string oc (Pp.plain ~width:80 doc)


let generate
  ~(output_dir : string)
  ~(filename : string)
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (prog5 : unit Mucore.mu_file)
  : unit
  =
  if !Cerb_debug.debug_level > 0 then
    debug_log_file
    := Some
         (let open Stdlib in
          open_out_gen
            [ Open_wronly; Open_creat; (* Open_append; *) Open_trunc; Open_text ]
            0o666
            "generatorCompilation.log");
  let insts =
    prog5
    |> Core_to_mucore.collect_instrumentation
    |> fst
    |> List.filter (fun (inst : Core_to_mucore.instrumentation) ->
      Option.is_some inst.internal)
    |> List.filter (fun (inst : Core_to_mucore.instrumentation) ->
      match List.assoc Sym.equal inst.fn sigma.declarations with
      | _, _, A.Decl_function (_, _, _, _, true, _) ->
        false (* exclude `inline` functions*)
      | _ -> true)
  in
  if List.is_empty insts then failwith "No testable functions";
  let filename_base = filename |> Filename.basename |> Filename.chop_extension in
  let generators_doc = compile_generators sigma prog5 insts in
  let generators_fn = filename_base ^ "_gen.h" in
  save output_dir generators_fn generators_doc;
  let tests_doc = compile_tests generators_fn sigma insts in
  save output_dir (filename_base ^ "_test.c") tests_doc;
  ()
