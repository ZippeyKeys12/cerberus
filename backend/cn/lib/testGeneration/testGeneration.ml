let debug_log_file : out_channel option ref = ref None

let debug_log (str : string) : unit =
  match !debug_log_file with Some oc -> output_string oc str | None -> ()


let debug_stage (stage : string) (str : string) : unit =
  debug_log (stage ^ ":\n");
  debug_log (str ^ "\n\n")


let run
  ~output_dir
  ~filename
  ~max_unfolds:_
  (sigma : Cerb_frontend.GenTypes.genTypeCategory Cerb_frontend.AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  =
  if !Cerb_debug.debug_level > 0 then
    debug_log_file
    := Some
         (let open Stdlib in
          open_out_gen
            [ Open_wronly; Open_creat; (* Open_append; *) Open_trunc; Open_text ]
            0o666
            (Filename.concat output_dir "testGeneration.log"));
  Cerb_debug.begin_csv_timing ();
  if Option.is_some prog5.mu_main then
    failwith "Cannot test a file with a `main` function";
  debug_log ("Starting test generation for " ^ filename ^ "\n\n");
  let filename_base = filename |> Filename.basename |> Filename.chop_extension in
  let ctx = prog5 |> GenCompile.compile in
  debug_stage "Compile" (ctx |> GenDefinitions.pp_context |> Pp.plain ~width:80);
  let ctx = ctx |> GenNormalize.normalize prog5 in
  debug_stage "Normalize" (ctx |> GenDefinitions.pp_context |> Pp.plain ~width:80);
  let ctx = ctx |> GenDistribute.distribute in
  debug_stage "Distribute" (ctx |> GenDefinitions.pp_context |> Pp.plain ~width:80);
  let ctx = ctx |> GenOptimize.optimize in
  debug_stage "Optimize" (ctx |> GenDefinitions.pp_context |> Pp.plain ~width:80);
  let doc = ctx |> GenCodeGen.compile sigma in
  debug_stage "CodeGen" (Pp.plain ~width:80 doc);
  let oc = Stdlib.open_out (Filename.concat output_dir (filename_base ^ "_gen.h")) in
  output_string oc (Pp.plain ~width:80 doc)
