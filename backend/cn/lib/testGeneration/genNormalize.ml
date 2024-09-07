module BT = BaseTypes
module IT = IndexTerms
module GT = GenTerms
module GD = GenDefinitions

(* Should not have any primitve generators of structs *)
let destruct_struct_arbitrary (prog5 : unit Mucore.mu_file) (gt : GT.t) : GT.t =
  let aux (gt : GT.t) : GT.t =
    let (GT (gt_, _, _)) = gt in
    match gt_ with
    | Let (backtracks, x, GT (Arbitrary sz, Struct tag, loc), gt') ->
      (match Pmap.find tag prog5.mu_tagDefs with
       | M_StructDef pieces ->
         let members =
           pieces
           |> List.filter_map (fun ({ member_or_padding; _ } : Memory.struct_piece) ->
             member_or_padding)
           |> List.map (fun (member, ct) -> (Sym.fresh (), (member, Memory.bt_of_sct ct)))
         in
         let gt_struct =
           GT.let_
             ( 0,
               ( x,
                 GT.return_
                   (IT.struct_
                      ( tag,
                        List.map
                          (fun (y, (member, bt)) -> (member, IT.sym_ (y, bt, loc)))
                          members )
                      loc)
                   loc ),
               gt' )
             loc
         in
         List.fold_left
           (fun gt'' (y, (_, bt)) ->
             GT.let_ (backtracks, (y, GT.arbitrary_ (bt, sz) loc), gt'') loc)
           gt_struct
           members
       | _ -> failwith ("no struct " ^ Sym.pp_string tag ^ " found"))
    | _ -> gt
  in
  GT.map_gen_pre aux gt


let normalize_gen (prog5 : unit Mucore.mu_file) (gt : GT.t) : GT.t =
  let rec loop (gt : GT.t) : GT.t =
    let old_gt = gt in
    let new_gt = gt |> destruct_struct_arbitrary prog5 in
    if GT.equal old_gt new_gt then new_gt else loop new_gt
  in
  gt |> loop


let normalize_gen_def (prog5 : unit Mucore.mu_file) ({ name; iargs; oargs; body } : GD.t)
  : GD.t
  =
  { name; iargs; oargs; body = Option.map (normalize_gen prog5) body }


let normalize (prog5 : unit Mucore.mu_file) (ctx : GD.context) : GD.context =
  List.map_snd (List.map_snd (normalize_gen_def prog5)) ctx
