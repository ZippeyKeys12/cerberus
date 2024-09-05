module IT = IndexTerms
module GT = GenTerms
module GD = GenDefinitions
module SymSet = Set.Make (Sym)

let inline_just_terms (gt : GT.t) : GT.t =
  let aux (gt : GT.t) : GT.t =
    let (GT (gt_, _, _)) = gt in
    match gt_ with
    | Let (_, x, GT (Return it, _, _), gt') ->
      let (IT (t_, _, _)) = it in
      (match t_ with
       (* Terms to inline *)
       | Const _ | Sym _ -> GT.subst (IT.make_subst [ (x, it) ]) gt'
       | _ -> gt)
    | _ -> gt
  in
  GT.map_gen_pre aux gt


let remove_unused (gt : GT.t) : GT.t =
  let aux (gt : GT.t) : GT.t =
    let (GT (gt_, _, _)) = gt in
    match gt_ with
    | Let (_, x, _, gt') when not (SymSet.mem x (GT.free_vars gt')) -> gt'
    | _ -> gt
  in
  GT.map_gen_post aux gt


let rec optimize_gen (gt : GT.t) : GT.t =
  let loop (gt : GT.t) : GT.t =
    let old_gt = gt in
    let new_gt = gt |> inline_just_terms in
    if GT.equal old_gt new_gt then new_gt else optimize_gen new_gt
  in
  gt |> remove_unused |> loop


let optimize_gen_def ({ name; iargs; oargs; body } : GD.t) : GD.t =
  { name; iargs; oargs; body = Option.map optimize_gen body }


let optimize (ctx : GD.context) : GD.context =
  List.map_snd (List.map_snd optimize_gen_def) ctx
