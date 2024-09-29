module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module GT = GenTerms
module GD = GenDefinitions
module SymMap = Map.Make (Sym)

(* let array_size : int = 20 *)

(* let weight_array_size (_gt : GT.t) : GT.t = failwith __LOC__ *)

let generated_size (bt : BT.t) : int = match bt with Datatype _ -> 100 | _ -> 100

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


let rec implicit_contraints (gt : GT.t) : GT.t =
  let infer_size_it (it : IT.t) : (Sym.t * IT.t) option =
    let (IT (it_, _, loc)) = it in
    match it_ with
    | ArrayShift { base = IT (Sym p_sym, _, _); ct; index = it_offset } ->
      Some (p_sym, IT.mul_ (IT.sizeOf_ ct loc, IT.cast_ Memory.size_bt it_offset loc) loc)
    | Binop (Add, IT (Sym p_sym, _, _), it_offset) -> Some (p_sym, it_offset)
    | Sym p_sym -> Some (p_sym, IT.num_lit_ Z.zero Memory.size_bt loc)
    | _ -> None
  in
  let names = ref SymMap.empty in
  let rec aux (gt : GT.t) : GT.t =
    let (GT (gt_, _, here)) = gt in
    match gt_ with
    | Arbitrary | Uniform _ | Alloc _ | Call _ | Return _ -> gt
    | Pick wgts -> GT.pick_ (List.map_snd aux wgts) here
    | Asgn ((it_addr, sct), it_val, gt') ->
      let gt = GT.asgn_ ((it_addr, sct), it_val, aux gt') here in
      Option.value
        ~default:gt
        (let open Option in
         let@ psym, it_offset = infer_size_it it_addr in
         let@ it_q = SymMap.find_opt psym !names in
         let loc = Locations.other __LOC__ in
         let it_size = IT.add_ (it_offset, IT.sizeOf_ sct loc) loc in
         return
           (GT.assert_
              (LC.T (IT.gt_ (it_q, IT.cast_ (IT.bt it_q) it_size loc) loc), gt)
              loc))
    | Let (backtracks, x, (GT (Alloc it, _, here') as gt_inner), gt') ->
      (match IT.is_sym it with
       | Some (y, bt) ->
         names := SymMap.add x (IT.sym_ (y, bt, here')) !names;
         GT.let_ (backtracks, (x, implicit_contraints gt_inner), aux gt') here
       | None ->
         let y = Sym.fresh () in
         names := SymMap.add x (IT.sym_ (y, IT.bt it, here')) !names;
         let loc = Locations.other __LOC__ in
         GT.let_
           ( backtracks,
             (y, GT.arbitrary_ (IT.bt it) loc),
             GT.let_ (0, (x, GT.alloc_ (IT.sym_ (y, IT.bt it, loc)) loc), aux gt') here )
           loc)
    | Let (backtracks, x, gt_inner, gt') ->
      GT.let_ (backtracks, (x, aux gt_inner), aux gt') here
    | Assert (lc, gt') -> GT.assert_ (lc, aux gt') here
    | ITE (it_if, gt_then, gt_else) -> GT.ite_ (it_if, aux gt_then, aux gt_else) here
    | Map ((i, i_bt, it_perm), gt') -> GT.map_ ((i, i_bt, it_perm), aux gt') here
  in
  aux gt


let distribute_gen (gt : GT.t) : GT.t =
  gt |> default_weights |> implicit_contraints |> default_weights |> confirm_distribution


let distribute_gen_def ({ name; iargs; oargs; body } : GD.t) : GD.t =
  { name; iargs; oargs; body = Option.map distribute_gen body }


let distribute (ctx : GD.context) : GD.context =
  List.map_snd (List.map_snd distribute_gen_def) ctx
