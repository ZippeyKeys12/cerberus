module CF = Cerb_frontend
module A = CF.AilSyntax

let debug_log_file : out_channel option ref = ref None

let debug_log (str : string) : unit =
  match !debug_log_file with Some oc -> output_string oc str | None -> ()


let debug_stage (stage : string) (str : string) : unit =
  debug_log (stage ^ ":\n");
  debug_log (str ^ "\n\n")


let compile_generators
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (prog5 : unit Mucore.mu_file)
  =
  let ctx = prog5 |> GenCompile.compile in
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

let compile_tests (filename : string) (prog5 : unit Mucore.mu_file) : Pp.document =
  let _insts =
    prog5
    |> Core_to_mucore.collect_instrumentation
    |> fst
    |> List.filter (fun (inst : Core_to_mucore.instrumentation) ->
      Option.is_some inst.internal)
  in
  let open Pp in
  string "#include "
  ^^ dquotes (string filename)
  ^^ twice hardline
  ^^ string "int main"
  ^^ parens (string "int argc, char* argv[]")
  ^^ break 1
  ^^ braces (string "return cn_test_main(argc, argv);")


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
  let filename_base = filename |> Filename.basename |> Filename.chop_extension in
  let generators_doc = compile_generators sigma prog5 in
  let generators_fn = filename_base ^ "_gen.h" in
  save output_dir generators_fn generators_doc;
  let tests_doc = compile_tests generators_fn prog5 in
  save output_dir (filename_base ^ "_test.c") tests_doc;
  ()
