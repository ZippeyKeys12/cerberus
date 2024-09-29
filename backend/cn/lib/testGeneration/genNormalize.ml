module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module GT = GenTerms
module GD = GenDefinitions
module SymMap = Map.Make (Sym)

let backtracks = 10

(* Should not have any primitve generators of structs *)
let destruct_struct_arbitrary (prog5 : unit Mucore.mu_file) (gt : GT.t) : GT.t =
  let aux (gt : GT.t) : GT.t =
    match gt with
    | GT (Arbitrary, Struct tag, loc) ->
      (match Pmap.find tag prog5.mu_tagDefs with
       | M_StructDef pieces ->
         let members =
           pieces
           |> List.filter_map (fun ({ member_or_padding; _ } : Memory.struct_piece) ->
             member_or_padding)
           |> List.map (fun (member, ct) -> (Sym.fresh (), (member, ct)))
         in
         let gt_struct =
           GT.return_
             (IT.struct_
                ( tag,
                  List.map
                    (fun (y, (member, ct)) ->
                      (member, IT.sym_ (y, Memory.bt_of_sct ct, loc)))
                    members )
                loc)
             loc
         in
         List.fold_left
           (fun gt'' (y, (_, ct)) ->
             let gt_arb =
               match ct with
               | Sctypes.Array (ct', Some len) ->
                 let sym = Sym.fresh () in
                 let bt = BT.Bits (Unsigned, 64) in
                 GT.map_
                   ( ( sym,
                       bt,
                       IT.and2_
                         ( IT.le_ (IT.num_lit_ Z.zero bt loc, IT.sym_ (sym, bt, loc)) loc,
                           IT.lt_
                             (IT.sym_ (sym, bt, loc), IT.num_lit_ (Z.of_int len) bt loc)
                             loc )
                         loc ),
                     GT.arbitrary_ (Memory.bt_of_sct ct') loc )
                   loc
               | Array (_, None) -> failwith __LOC__
               | _ -> GT.arbitrary_ (Memory.bt_of_sct ct) loc
             in
             GT.let_ (backtracks, (y, gt_arb), gt'') loc)
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
