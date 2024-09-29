module IT = IndexTerms
module LC = LogicalConstraints
module GT = GenTerms
module GD = GenDefinitions
module GA = GenAnalysis
module SymSet = Set.Make (Sym)
module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

type opt_pass =
  { name : string;
    transform : GT.t -> GT.t
  }

(** This pass ... *)
module Inline = struct
  (** This pass ... *)
  module Returns = struct
    let name = "inline_return"

    let transform (gt : GT.t) : GT.t =
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


    let pass = { name; transform }
  end

  (** This pass ... *)
  module SingleUse = struct
    let name = "inline_single_use"

    let transform (gt : GT.t) : GT.t =
      let single_uses = GA.get_single_uses ~pure:true gt in
      let aux (gt : GT.t) : GT.t =
        let (GT (gt_, _, _)) = gt in
        match gt_ with
        | Let (_, x, GT (Return it, _, _), gt') ->
          if SymSet.mem x single_uses then
            GT.subst (IT.make_subst [ (x, it) ]) gt'
          else
            gt
        | _ -> gt
      in
      GT.map_gen_pre aux gt


    let pass = { name; transform }
  end

  let passes = [ SingleUse.pass ]
end

(** This pass ... *)
module Reordering = struct end

(** This pass ... *)
module Specialization = struct end

(** This pass ... *)
module BetterAllocations = struct end

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
