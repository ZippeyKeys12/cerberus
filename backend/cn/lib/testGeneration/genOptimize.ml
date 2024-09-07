module IT = IndexTerms
module GT = GenTerms
module GD = GenDefinitions
module SymSet = Set.Make (Sym)

type pass = GT.t -> GT.t

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


type config =
  { inline_just_terms : bool;
    remove_unused : bool
  }

let all_passes = { inline_just_terms = true; remove_unused = true }

let get_first_pass (cfg : config) : pass =
  [ (if cfg.remove_unused then Some remove_unused else None) ]
  |> List.map Option.to_list
  |> List.flatten
  |> List.fold_left (fun acc pass gt -> pass (acc gt)) (fun gt -> gt)


let get_repeating_pass (cfg : config) : pass =
  [ (if cfg.inline_just_terms then Some inline_just_terms else None) ]
  |> List.map Option.to_list
  |> List.flatten
  |> List.fold_left (fun acc pass gt -> pass (acc gt)) (fun gt -> gt)


let rec optimize_gen (cfg : config) (gt : GT.t) : GT.t =
  let first_pass = get_first_pass cfg in
  let repeating_pass = get_repeating_pass cfg in
  let loop (gt : GT.t) : GT.t =
    let old_gt = gt in
    let new_gt = repeating_pass gt in
    if GT.equal old_gt new_gt then new_gt else optimize_gen cfg new_gt
  in
  gt |> first_pass |> loop


let optimize_gen_def (cfg : config) ({ name; iargs; oargs; body } : GD.t) : GD.t =
  { name; iargs; oargs; body = Option.map (optimize_gen cfg) body }


let optimize ?(cfg : config = all_passes) (ctx : GD.context) : GD.context =
  List.map_snd (List.map_snd (optimize_gen_def cfg)) ctx
