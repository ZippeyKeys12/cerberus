module GT = GenTerms

let rec is_pure (gt : GT.t) : bool =
  let (GT (gt_, _, _)) = gt in
  match gt_ with
  | Arbitrary | Uniform _ -> true
  | Pick wgts -> wgts |> List.map snd |> List.for_all is_pure
  | Alloc _ -> false
  | Call _ -> false (* Could be less conservative... *)
  | Asgn _ -> false
  | Let (_, _, gt1, gt2) -> is_pure gt1 && is_pure gt2
  | Return _ -> true
  | Assert _ -> false
  | ITE (_, gt_then, gt_else) -> is_pure gt_then && is_pure gt_else
  | Map _ -> false
