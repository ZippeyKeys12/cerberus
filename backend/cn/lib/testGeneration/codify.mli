module CF = Cerb_frontend

type test_framework = GTest

val codify
  :  output_dir:string ->
  test_framework ->
  _ CF.AilSyntax.sigma ->
  unit Mucore.mu_file ->
  Dsl.gen_context ->
  unit
