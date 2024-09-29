module IT = IndexTerms
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

module InlineReturns = struct
  let name = "inline_returns"

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

module Reordering = struct end

module Specialization = struct end

module LazyPruning = struct end

module Fusion = struct
  module Recursive = struct end

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

module ConstraintPropagation = struct end

module DraGen = struct end

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


  let pass = { name; transform }
end

let all_passes = [ InlineReturns.pass; RemoveUnused.pass ]

let optimize_gen (passes : StringSet.t) (gt : GT.t) : GT.t =
  all_passes
  |> List.filter_map (fun { name; transform } ->
    if StringSet.mem name passes then Some transform else None)
  |> List.fold_left (fun gt pass -> pass gt) gt


let optimize_gen_def (passes : StringSet.t) ({ name; iargs; oargs; body } : GD.t) : GD.t =
  { name; iargs; oargs; body = Option.map (optimize_gen passes) body }


let optimize ?(passes : StringSet.t option = None) (ctx : GD.context) : GD.context =
  let default = all_passes |> List.map (fun p -> p.name) |> StringSet.of_list in
  let passes = Option.value ~default passes in
  List.map_snd (List.map_snd (optimize_gen_def passes)) ctx
