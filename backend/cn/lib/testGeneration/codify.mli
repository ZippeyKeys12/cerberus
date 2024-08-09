type test_framework = GTest

type codify_result =
  { gens : Pp.document;
    tests : Pp.document
  }

type codify_context = (string * codify_result) list

type t = codify_context

val codify : test_framework -> Dsl.gen_context -> t

val save : output_dir:string -> t -> unit
