module IT = IndexTerms
module LC = LogicalConstraints
module GC = GenConstraints

type t =
  { alloc : IT.t option;
    logical : LC.t list
  }
[@@deriving eq, ord]

let pp ({ alloc; logical } : t) : Pp.document =
  let open Pp in
  let doc_alloc = alloc |> Option.map IT.pp |> Option.value ~default:empty in
  let doc_logical = separate_map (break 1 ^^ twice ampersand ^^ space) LC.pp logical in
  doc_alloc
  ^^ (if Option.is_some alloc then break 1 ^^ twice ampersand ^^ space else empty)
  ^^ doc_logical


let true_ = { alloc = None; logical = [] }

let alloc_ (size : IT.t) = { alloc = Some size; logical = [] }

let is_true ({ alloc; logical } : t) : bool =
  Option.is_none alloc && List.is_empty logical


let of_lc (lc : LC.t) : t = { alloc = None; logical = [ lc ] }

let of_gc (gc : GC.t) : t option =
  match gc with
  | Alloc { pointer = _; size } -> Some { alloc = Some size; logical = [] }
  | Logical lcs -> Some { alloc = None; logical = lcs }
  | Ownership _ | Predicate _ -> None


let inter
  ({ alloc = alloc1; logical = lcs1 } : t)
  ({ alloc = alloc2; logical = lcs2 } : t)
  : t
  =
  let logical = lcs1 @ lcs2 in
  match (alloc1, alloc2) with
  | Some it1, Some it2 ->
    let here = Locations.other __FUNCTION__ in
    let alloc = Some (IT.max_ (it1, it2) here) in
    { alloc; logical }
  | Some it, None | None, Some it ->
    let alloc = Some it in
    { alloc; logical }
  | None, None -> { alloc = None; logical }


let of_gcs (gcs : GC.t list) : t option =
  List.fold_left
    (fun acc gc ->
      let open Option in
      let@ acc in
      let@ gtc = of_gc gc in
      return (inter acc gtc))
    (Some true_)
    gcs


let subst (su : [ `Term of IT.t | `Rename of Sym.t ] Subst.t) ({ alloc; logical } : t) : t
  =
  let alloc = Option.map (IT.subst su) alloc in
  let logical = List.map (LC.subst su) logical in
  { alloc; logical }
