let run
  ~output_dir
  ~filename
  ~max_unfolds:_
  (sigma : Cerb_frontend.GenTypes.genTypeCategory Cerb_frontend.AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  : unit
  =
  if Option.is_some prog5.mu_main then
    failwith "Cannot test a file with a `main` function";
  SpecTests.generate ~output_dir ~filename sigma prog5
