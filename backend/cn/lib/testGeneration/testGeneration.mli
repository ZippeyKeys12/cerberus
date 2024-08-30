val run
  :  output_dir:string ->
  filename:string ->
  max_unfolds:int ->
  Cerb_frontend.GenTypes.genTypeCategory Cerb_frontend.AilSyntax.sigma ->
  unit Mucore.mu_file ->
  unit
