module IT = IndexTerms
module LC = LogicalConstraints
module GT = GenTerms
module SymSet = Set.Make (Sym)
module SymMap = Map.Make (Sym)

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


let get_single_uses ?(pure : bool = false) (gt : GT.t) : SymSet.t =
  let union =
    SymMap.union (fun _ oa ob ->
      Some
        (let open Option in
         let@ a = oa in
         let@ b = ob in
         return (a + b)))
  in
  let it_value : int option = if pure then Some 1 else None in
  let aux_it (it : IT.t) : int option SymMap.t =
    it
    |> IT.free_vars
    |> SymSet.to_seq
    |> Seq.map (fun x -> (x, it_value))
    |> SymMap.of_seq
  in
  let aux_lc (lc : LC.t) : int option SymMap.t =
    lc
    |> LC.free_vars
    |> SymSet.to_seq
    |> Seq.map (fun x -> (x, it_value))
    |> SymMap.of_seq
  in
  let rec aux (gt : GT.t) : int option SymMap.t =
    let (GT (gt_, _, _)) = gt in
    match gt_ with
    | Arbitrary | Uniform _ -> SymMap.empty
    | Pick wgts ->
      wgts |> List.map snd |> List.map aux |> List.fold_left union SymMap.empty
    | Alloc it | Return it -> aux_it it
    | Call (_, iargs) ->
      iargs |> List.map snd |> List.map aux_it |> List.fold_left union SymMap.empty
    | Asgn ((it_addr, _), it_val, gt') ->
      aux gt' :: List.map aux_it [ it_addr; it_val ] |> List.fold_left union SymMap.empty
    | Let (_, x, gt1, gt2) -> SymMap.remove x (union (aux gt1) (aux gt2))
    | Assert (lc, gt') -> union (aux gt') (aux_lc lc)
    | ITE (it_if, gt_then, gt_else) ->
      aux_it it_if :: List.map aux [ gt_then; gt_else ]
      |> List.fold_left union SymMap.empty
    | Map ((i, _, it_perm), gt') ->
      union
        (aux_it it_perm)
        (gt' |> aux |> SymMap.remove i |> SymMap.map (Option.map (Int.add 1)))
  in
  aux gt
  |> SymMap.filter (fun _ -> Option.equal Int.equal (Some 1))
  |> SymMap.bindings
  |> List.map fst
  |> SymSet.of_list
