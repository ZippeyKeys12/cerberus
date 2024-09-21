module BT = BaseTypes
module IT = IndexTerms
module GT = GenTerms
module GD = GenDefinitions

(* let array_size : int = 20 *)

(* let weight_array_size (_gt : GT.t) : GT.t = failwith __LOC__ *)

let generated_size (bt : BT.t) : int = match bt with Datatype _ -> 100 | _ -> -1

let default_weights (gt : GT.t) : GT.t =
  let aux (gt : GT.t) : GT.t =
    let (GT (gt_, bt, loc)) = gt in
    let gt_ =
      match gt_ with
      | Arbitrary ->
        (match bt with
         | Map (_k_bt, _v_bt) -> failwith __LOC__
         | Loc () -> GT.Alloc (IT.num_lit_ Z.zero Memory.size_bt loc)
         | _ -> GT.Uniform (generated_size bt))
      | _ -> gt_
    in
    GT (gt_, bt, loc)
  in
  GT.map_gen_pre aux gt


let confirm_distribution (gt : GT.t) : GT.t =
  let rec aux (gt : GT.t) : Locations.t list =
    let (GT (gt_, _, loc)) = gt in
    match gt_ with
    | Arbitrary -> [ loc ]
    | Uniform _ | Alloc _ | Call _ | Return _ -> []
    | Pick wgts -> wgts |> List.map snd |> List.map aux |> List.flatten
    | Asgn (_, _, gt') | Assert (_, gt') | Map ((_, _, _), gt') -> aux gt'
    | Let (_, _, gt1, gt2) | ITE (_, gt1, gt2) ->
      [ gt1; gt2 ] |> List.map aux |> List.flatten
  in
  let failures = aux gt in
  if List.is_empty failures then
    gt
  else
    failwith
      Pp.(
        plain
          (string "Distribute failure: `arbitrary` still remaining at following locations"
           ^^ space
           ^^ brackets (separate_map (comma ^^ break 1) Locations.pp failures)))


let distribute_gen (gt : GT.t) : GT.t =
  (* let rec loop (gt : GT.t) : GT.t =
     let old_gt = gt in
     let new_gt = gt |> default_weights in
     if GT.equal old_gt new_gt then new_gt else loop new_gt
     in
     gt |> loop *)
  gt |> default_weights |> confirm_distribution


let distribute_gen_def ({ name; iargs; oargs; body } : GD.t) : GD.t =
  { name; iargs; oargs; body = Option.map distribute_gen body }


let distribute (ctx : GD.context) : GD.context =
  List.map_snd (List.map_snd distribute_gen_def) ctx
