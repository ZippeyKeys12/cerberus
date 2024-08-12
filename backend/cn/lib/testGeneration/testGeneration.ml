(** Test Generation
    Generates RapidCheck tests for functions
    with CN specifications, where inputs are
    guaranteed to satisfy the CN precondition.
    **)

module AT = ArgumentTypes
module BT = BaseTypes
module RP = ResourcePredicates
module IT = IndexTerms
module LS = LogicalSorts
module RET = ResourceTypes
module LC = LogicalConstraints
module LAT = LogicalArgumentTypes
module CF = Cerb_frontend

type test_framework = Codify.test_framework

let test_frameworks = [ ("gtest", Codify.GTest) ]

let debug_log_file : out_channel option ref = ref None

let debug_log (str : string) : unit =
  match !debug_log_file with Some oc -> output_string oc str | None -> ()


let debug_stage (stage : string) (str : string) : unit =
  debug_log (stage ^ ":\n");
  debug_log (str ^ "\n\n")


let run
  ~(output_dir : string)
  ~(filename : string)
  ~(max_unfolds : int)
  (sigma : _ CF.AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (tf : Codify.test_framework)
  : unit
  =
  let _ = max_unfolds in
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
  let cs_ctx = Constraints.collect prog5 [ filename ] in
  debug_stage "Collect" (cs_ctx |> Constraints.pp_constraint_context |> Pp.plain ~width:90);
  let cs_ctx = Constraints.simplify cs_ctx in
  debug_stage
    "Simplify"
    (cs_ctx |> Constraints.pp_constraint_context |> Pp.plain ~width:90);
  let gtx = Dsl.compile cs_ctx in
  debug_stage "Compile" (gtx |> Dsl.pp_gen_context |> Pp.plain ~width:90);
  let gtx = Dsl.optimize gtx in
  debug_stage "Optimize" (gtx |> Dsl.pp_gen_context |> Pp.plain ~width:90);
  gtx |> Codify.codify ~output_dir tf sigma prog5;
  Cerb_debug.end_csv_timing "test generation";
  ()
