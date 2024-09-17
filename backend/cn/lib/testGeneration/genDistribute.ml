module BT = BaseTypes
module IT = IndexTerms
module GT = GenTerms
module GD = GenDefinitions

let generated_size (bt : BT.t) : int = match bt with Datatype _ -> 100 | _ -> -1

let handle_arbitrary (gt : GT.t) : GT.t =
  let aux (gt : GT.t) : GT.t =
    let (GT (gt_, (pred, bt), loc)) = gt in
    let gt_ =
      match gt_ with
      | Arbitrary ->
        (match bt with
         | Map (_k_bt, _v_bt) -> failwith __LOC__
         | Loc () -> GT.Alloc (IT.num_lit_ Z.zero Memory.size_bt loc)
         | _ -> GT.Uniform (generated_size bt))
      | _ -> gt_
    in
    GT (gt_, (pred, bt), loc)
  in
  GT.map_gen_pre aux gt


let distribute_gen (gt : GT.t) : GT.t =
  let rec loop (gt : GT.t) : GT.t =
    let old_gt = gt in
    let new_gt = gt |> handle_arbitrary in
    if GT.equal old_gt new_gt then new_gt else loop new_gt
  in
  gt |> loop


let distribute_gen_def ({ name; iargs; oargs; body } : GD.t) : GD.t =
  { name; iargs; oargs; body = Option.map distribute_gen body }


let distribute (ctx : GD.context) : GD.context =
  List.map_snd (List.map_snd distribute_gen_def) ctx
