module Compile = GenCompile

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
  (_sigma : Cerb_frontend.GenTypes.genTypeCategory Cerb_frontend.AilSyntax.sigma)
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
  debug_log ("Starting test generation for " ^ filename ^ "\n\n");
  let ctx = prog5 |> Compile.compile in
  debug_stage "Compile" (ctx |> GenDefinitions.pp_context |> Pp.plain ~width:80)
