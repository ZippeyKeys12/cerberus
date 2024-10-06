module CF = Cerb_frontend
module IT = IndexTerms
module LC = LogicalConstraints
module GT = GenTerms
module GD = GenDefinitions
module GA = GenAnalysis
module SymSet = Set.Make (Sym)
module SymMap = Map.Make (Sym)
module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

type opt_pass =
  { name : string;
    transform : GT.t -> GT.t
  }

(** This pass performs various inlinings *)
module Inline = struct
  (** This pass inlines generators that just return a constant or symbol *)
  module Returns = struct
    let name = "inline_return"

    let transform (gt : GT.t) : GT.t =
      let aux (gt : GT.t) : GT.t =
        let (GT (gt_, _, here)) = gt in
        match gt_ with
        | Let (_, x, GT (Return it, _, loc_ret), gt') ->
          let (IT (t_, _, _)) = it in
          (match t_ with
           (* Terms to inline *)
           | Const _ | Sym _ -> GT.subst (IT.make_subst [ (x, it) ]) gt'
           (* Otherwise, at least avoid pointless backtracking *)
           | _ -> GT.let_ (0, (x, GT.return_ it loc_ret), gt') here)
        | _ -> gt
      in
      GT.map_gen_pre aux gt


    let pass = { name; transform }
  end

  (* This pass inlines *)
  module SingleUse = struct
    module IndexTerms = struct
      let name = "inline_single_use_pure"

      let transform (_gt : GT.t) : GT.t = failwith __LOC__
      (* let aux (gt : GT.t) : GT.t =
         let (GT (gt_, _, _)) = gt in
         match gt_ with
         | Let (_, x, GT (Return it, _, _), gt') ->
         let single_uses = GA.get_single_uses ~pure:true gt' in
         if SymSet.mem x single_uses then
         GT.subst (IT.make_subst [ (x, it) ]) gt'
         else
         gt
         | _ -> gt
         in
         GT.map_gen_pre aux gt *)

      let pass = { name; transform }
    end

    module GenTerms = struct
      let name = "inline_single_use_gen"

      let subst (x : Sym.t) (gt_repl : GT.t) (gt : GT.t) : GT.t =
        let aux (gt : GT.t) : GT.t =
          let (GT (gt_, _, _)) = gt in
          match gt_ with
          | Return (IT (Sym y, _, _)) when Sym.equal x y -> gt_repl
          | _ -> gt
        in
        GT.map_gen_post aux gt


      let of_symset (s : SymSet.t) : bool SymMap.t =
        s |> SymSet.to_seq |> Seq.map (fun x -> (x, false)) |> SymMap.of_seq


      let union = SymMap.union (fun _ a b -> Some (not (a || b)))

      let rec transform_aux (gt : GT.t) : GT.t * bool SymMap.t =
        let (GT (gt_, _, loc)) = gt in
        match gt_ with
        | Arbitrary | Uniform _ -> (gt, SymMap.empty)
        | Pick wgts ->
          let wgts, only_ret =
            wgts
            |> List.map_snd transform_aux
            |> List.map (fun (a, (b, c)) -> ((a, b), c))
            |> List.split
          in
          (GT.pick_ wgts loc, List.fold_left union SymMap.empty only_ret)
        | Alloc it -> (gt, it |> IT.free_vars |> of_symset)
        | Call (_fsym, xits) ->
          ( gt,
            xits
            |> List.map snd
            |> List.map IT.free_vars
            |> List.map of_symset
            |> List.fold_left union SymMap.empty )
        | Asgn ((it_addr, sct), it_val, gt') ->
          let only_ret =
            [ it_addr; it_val ]
            |> List.map IT.free_vars
            |> List.map of_symset
            |> List.fold_left union SymMap.empty
          in
          let gt', only_ret' = transform_aux gt' in
          (GT.asgn_ ((it_addr, sct), it_val, gt') loc, union only_ret only_ret')
        | Let (backtracks, x, gt_inner, gt') ->
          let gt', only_ret = transform_aux gt' in
          let only_ret = SymMap.remove x only_ret in
          if Option.equal Bool.equal (SymMap.find_opt x only_ret) (Some true) then
            (subst x gt_inner gt', only_ret)
          else (
            let gt_inner, only_ret' = transform_aux gt_inner in
            (GT.let_ (backtracks, (x, gt_inner), gt') loc, union only_ret only_ret'))
        | Return it ->
          ( gt,
            (match IT.is_sym it with
             | Some (x, _bt) -> SymMap.singleton x true
             | None -> it |> IT.free_vars |> of_symset) )
        | Assert (lc, gt') ->
          let only_ret = lc |> LC.free_vars |> of_symset in
          let gt', only_ret' = transform_aux gt' in
          (GT.assert_ (lc, gt') loc, union only_ret only_ret')
        | ITE (it_if, gt_then, gt_else) ->
          let only_ret = it_if |> IT.free_vars |> of_symset in
          let gt_then, only_ret' = transform_aux gt_then in
          let gt_else, only_ret'' = transform_aux gt_else in
          ( GT.ite_ (it_if, gt_then, gt_else) loc,
            [ only_ret; only_ret'; only_ret'' ] |> List.fold_left union SymMap.empty )
        | Map ((i, i_bt, it_perm), gt_inner) ->
          let only_ret = it_perm |> IT.free_vars |> SymSet.remove i |> of_symset in
          let gt_inner, only_ret' = transform_aux gt_inner in
          let only_ret' = only_ret' |> SymMap.remove i |> SymMap.map (fun _ -> false) in
          (GT.map_ ((i, i_bt, it_perm), gt_inner) loc, union only_ret only_ret')


      let transform (gt : GT.t) : GT.t = fst (transform_aux gt)

      let pass = { name; transform }
    end

    let passes = [ (* IndexTerms.pass; *) GenTerms.pass ]
  end

  let passes = Returns.pass :: SingleUse.passes
end

(** This pass ... *)
module Reordering = struct end

(** This pass ... *)
module Specialization = struct end

(** This pass ... *)
(* module InferAllocationSize = struct
  let name = "infer_alloc_size"

  let infer_size_it (x : Sym.t) (it : IT.t) : IT.t option =
    let (IT (it_, _, loc)) = it in
    match it_ with
    | ArrayShift { base = IT (Sym p_sym, _, _); ct; index = it_offset }
      when Sym.equal x p_sym ->
      Some (IT.mul_ (IT.sizeOf_ ct loc, IT.cast_ Memory.size_bt it_offset loc) loc)
    | Binop (Add, IT (Sym p_sym, _, _), it_offset) when Sym.equal x p_sym ->
      Some it_offset
    | Sym p_sym when Sym.equal x p_sym -> Some (IT.num_lit_ Z.zero Memory.size_bt loc)
    | _ -> None


  let rec infer_size (x : Sym.t) (gt : GT.t) : IT.t option =
    let (GT (gt_, _, _)) = gt in
    let here = Locations.other __LOC__ in
    match gt_ with
    | Arbitrary | Uniform _ | Alloc _ | Call _ -> None
    | Pick wgts ->
      wgts
      |> List.map snd
      |> List.map (infer_size x)
      |> List.fold_left
           (fun oa ob ->
             match (oa, ob) with
             | Some a, Some b -> Some (IT.max_ (a, b) here)
             | Some a, _ | _, Some a -> Some a
             | None, None -> None)
           None
    | Let (_, x, gt_inner, gt') ->
      

  let transform (gt : GT.t) : GT.t = failwith __LOC__
end *)

(** This pass ... *)
module LazyPruning = struct end

(** This pass ... *)
module Fusion = struct
  (** This pass ... *)
  module Recursive = struct end

  (** This pass ... *)
  module Iterative = struct end
end

(** This pass uses [Simplify] to rewrite [IndexTerms.t] *)
module TermSimplification = struct
  let name = "simplify_term"

  let transform (gt : GT.t) : GT.t =
    let simp_it (it : IT.t) : IT.t =
      Simplify.IndexTerms.simp (Simplify.default Global.empty) it
    in
    let simp_lc (lc : LC.t) : LC.t =
      Simplify.LogicalConstraints.simp (Simplify.default Global.empty) lc
    in
    let aux (gt : GT.t) : GT.t =
      let (GT (gt_, bt, loc)) = gt in
      match gt_ with
      | Alloc it -> GT.alloc_ (simp_it it) loc
      | Call (fsym, iargs) -> GT.call_ (fsym, List.map_snd simp_it iargs) bt loc
      | Asgn ((it_addr, sct), it_val, gt') ->
        GT.asgn_ ((simp_it it_addr, sct), simp_it it_val, gt') loc
      | Return it -> GT.return_ (simp_it it) loc
      | Assert (lc, gt') -> GT.assert_ (simp_lc lc, gt') loc
      | Map ((i, i_bt, it_perm), gt') -> GT.map_ ((i, i_bt, simp_it it_perm), gt') loc
      | _ -> gt
    in
    GT.map_gen_pre aux gt


  let pass = { name; transform }
end

(** This pass ... *)
module ConstraintPropagation = struct end

(** This pass ... *)
module DraGen = struct end

(** This pass removes unused variables *)
module RemoveUnused = struct
  let name = "remove_unused"

  let transform (gt : GT.t) : GT.t =
    let aux (gt : GT.t) : GT.t =
      let (GT (gt_, _, _)) = gt in
      match gt_ with
      | Let (_, x, gt1, gt2) when GA.is_pure gt1 && not (SymSet.mem x (GT.free_vars gt2))
        ->
        gt2
      | _ -> gt
    in
    GT.map_gen_post aux gt


  let passes = [ { name; transform } ]
end

let all_passes = Inline.passes @ RemoveUnused.passes @ [ TermSimplification.pass ]

let optimize_gen (passes : StringSet.t) (gt : GT.t) : GT.t =
  let passes =
    all_passes
    |> List.filter_map (fun { name; transform } ->
      if StringSet.mem name passes then Some transform else None)
  in
  let opt (gt : GT.t) : GT.t = List.fold_left (fun gt pass -> pass gt) gt passes in
  let rec aux (gt : GT.t) (fuel : int) : GT.t =
    if fuel <= 0 then
      gt
    else (
      let old_gt = gt in
      let new_gt = opt gt in
      if GT.equal old_gt new_gt then new_gt else aux new_gt (fuel - 1))
  in
  aux gt 5


let optimize_gen_def (passes : StringSet.t) ({ name; iargs; oargs; body } : GD.t) : GD.t =
  { name; iargs; oargs; body = Option.map (optimize_gen passes) body }


let optimize ?(passes : StringSet.t option = None) (ctx : GD.context) : GD.context =
  let default = all_passes |> List.map (fun p -> p.name) |> StringSet.of_list in
  let passes = Option.value ~default passes in
  List.map_snd (List.map_snd (optimize_gen_def passes)) ctx
