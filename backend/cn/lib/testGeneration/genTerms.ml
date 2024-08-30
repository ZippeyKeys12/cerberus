module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module CF = Cerb_frontend
module GBT = GenBaseTypes
module SymMap = Map.Make (Sym)
module SymSet = Set.Make (Sym)

type t_ =
  | Uniform of BT.t * int (** Generate uniform values *)
  | Pick of (int * t) list
  (** Pick among a list of options, weighted by the provided [int]s *)
  | Alloc of IT.t (** Allocate an array of a length [IT.t]  and return its address *)
  | Call of Sym.t * (Sym.t * IT.t) list
  (** Call a defined generator according to a [Sym.t] with arguments [IT.t list] *)
  | Asgn of (IT.t * Sctypes.t) * IT.t * t
  (** Claim ownership and assign a value to a memory location *)
  | Let of int * Sym.t * t * t (** Monadic bind *)
  | Return of IT.t (** Monadic return *)
  | Assert of LC.t list * t (** Assert some [LC.t] are true, backtracking otherwise *)
  | ITE of IT.t * t * t (** If-then-else *)
  | Map of (Sym.t * BT.t * IT.t) * t
[@@deriving eq, ord]

and t = GT of t_ * BT.t * (Locations.t[@equal fun _ _ -> true] [@compare fun _ _ -> 0])
[@@deriving eq, ord]

(* Accessors *)

let basetype (GT (_, bt, _)) = bt

let bt = basetype

let loc (GT (_, _, loc)) = loc

(* Smart constructors *)

let uniform_ ((bt, sz) : BT.t * int) (loc : Locations.t) : t =
  GT (Uniform (bt, sz), bt, loc)


let pick_ (wgts : (int * t) list) (loc : Locations.t) : t =
  match wgts with
  | (_, gt) :: wgts' ->
    let bt =
      List.fold_left
        (fun bt (_, gt) ->
          assert (BT.equal bt (basetype gt));
          bt)
        (basetype gt)
        wgts'
    in
    GT (Pick wgts, bt, loc)
  | [] -> failwith "unreachable"


let alloc_ (it : IT.t) loc : t = GT (Alloc it, BT.Loc, loc)

let call_ (fsym, xits) bt loc : t = GT (Call (fsym, xits), bt, loc)

let asgn_ ((it_addr, ct), it_val, gt') loc =
  GT (Asgn ((it_addr, ct), it_val, gt'), basetype gt', loc)


let let_ ((retries, (x, gt1), gt2) : int * (Sym.t * t) * t) (loc : Locations.t) : t =
  GT (Let (retries, x, gt1, gt2), basetype gt2, loc)


let return_ (it : IT.t) (loc : Locations.t) : t = GT (Return it, IT.bt it, loc)

let assert_ ((lcs, gt') : LC.t list * t) (loc : Locations.t) : t =
  GT (Assert (lcs, gt'), basetype gt', loc)


let ite_ ((it_if, gt_then, gt_else) : IT.t * t * t) loc : t =
  let bt = basetype gt_then in
  assert (BT.equal bt (basetype gt_else));
  GT (ITE (it_if, gt_then, gt_else), bt, loc)


(* Constructor-checking functions *)

let is_uniform_ (gt_ : t_) : bool = match gt_ with Uniform _ -> true | _ -> false

let is_uniform (gt : t) : bool =
  let (GT (gt_, _, _)) = gt in
  is_uniform_ gt_


let is_pick_ (gt_ : t_) : bool = match gt_ with Pick _ -> true | _ -> false

let is_pick (gt : t) : bool =
  let (GT (gt_, _, _)) = gt in
  is_pick_ gt_


let is_alloc_ (gt_ : t_) : bool = match gt_ with Alloc _ -> true | _ -> false

let is_alloc (gt : t) : bool =
  let (GT (gt_, _, _)) = gt in
  is_alloc_ gt_


let is_call_ (gt_ : t_) : bool = match gt_ with Call _ -> true | _ -> false

let is_call (gt : t) : bool =
  let (GT (gt_, _, _)) = gt in
  is_call_ gt_


let is_asgn_ (gt_ : t_) : bool = match gt_ with Asgn _ -> true | _ -> false

let is_asgn (gt : t) : bool =
  let (GT (gt_, _, _)) = gt in
  is_asgn_ gt_


let is_let_ (gt_ : t_) : bool = match gt_ with Let _ -> true | _ -> false

let is_let (gt : t) : bool =
  let (GT (gt_, _, _)) = gt in
  is_let_ gt_


let is_return_ (gt_ : t_) : bool = match gt_ with Return _ -> true | _ -> false

let is_return (gt : t) : bool =
  let (GT (gt_, _, _)) = gt in
  is_return_ gt_


let is_assert_ (gt_ : t_) : bool = match gt_ with Assert _ -> true | _ -> false

let is_assert (gt : t) : bool =
  let (GT (gt_, _, _)) = gt in
  is_assert_ gt_


let is_ite_ (gt_ : t_) : bool = match gt_ with ITE _ -> true | _ -> false

let is_ite (gt : t) : bool =
  let (GT (gt_, _, _)) = gt in
  is_ite_ gt_


let rec pp (gt : t) : Pp.document =
  let open Pp in
  match gt with
  | GT (Uniform (bt, sz), bt', _here) ->
    assert (BT.equal bt bt');
    string "uniform" ^^ angles (BT.pp bt) ^^ parens (int sz)
  | GT (Pick wgts, _bt, _here) ->
    string "pick"
    ^^ parens
         (brackets
            (separate_map
               (semi ^^ break 1)
               (fun (w, gt) ->
                 parens (int w ^^ comma ^^ braces (nest 2 (break 1 ^^ pp gt))))
               wgts))
  | GT (Alloc it, _bt, _here) -> string "alloc" ^^ parens (IT.pp it)
  | GT (Call (fsym, xits), _bt, _here) ->
    Sym.pp fsym
    ^^ parens
         (nest
            2
            (separate_map
               (comma ^^ break 1)
               (fun (x, it) -> Sym.pp x ^^ colon ^^ space ^^ IT.pp it)
               xits))
  | GT (Asgn ((it_addr, ty), it_val, gt'), _bt, _here) ->
    Sctypes.pp ty
    ^^ space
    ^^ IT.pp it_addr
    ^^ space
    ^^ string ":="
    ^^ space
    ^^ IT.pp it_val
    ^^ semi
    ^^ break 1
    ^^ pp gt'
  | GT (Let (tries, x, gt1, gt2), _bt, _here) ->
    string "let"
    ^^ (if tries <> 0 then parens (int tries) else empty)
    ^^ (if is_return gt1 then empty else star)
    ^^ space
    ^^ Sym.pp x
    ^^ space
    ^^ equals
    ^^ space
    ^^ pp gt1
    ^^ semi
    ^^ break 1
    ^^ pp gt2
  | GT (Return it, _bt, _here) -> string "return" ^^ space ^^ IT.pp it
  | GT (Assert (lcs, gt'), _bt, _here) ->
    string "assert"
    ^^ parens (nest 2 (break 1 ^^ separate_map (comma ^^ break 1) LC.pp lcs) ^^ break 1)
    ^^ semi
    ^^ break 1
    ^^ pp gt'
  | GT (ITE (it_if, gt_then, gt_else), _bt, _here) ->
    string "if"
    ^^ space
    ^^ parens (IT.pp it_if)
    ^^ space
    ^^ braces (nest 2 (break 1 ^^ pp gt_then) ^^ break 1)
    ^^ space
    ^^ string "else"
    ^^ space
    ^^ braces (nest 2 (break 1 ^^ pp gt_else) ^^ break 1)
  | GT (Map ((i, bt, permission), gt'), _bt, _here) ->
    string "map"
    ^^ space
    ^^ parens (BT.pp bt ^^ space ^^ Sym.pp i ^^ semi ^^ space ^^ IT.pp permission)
    ^^ braces (nest 2 (break 1 ^^ pp gt') ^^ break 1)


let rec subst_ (su : [ `Term of IT.typed | `Rename of Sym.t ] Subst.t) (gt_ : t_) : t_ =
  match gt_ with
  | Uniform (ty, sz) -> Uniform (ty, sz)
  | Pick wgts -> Pick (List.map_snd (subst su) wgts)
  | Alloc it -> Alloc (IT.subst su it)
  | Call (fsym, xits) -> Call (fsym, List.map_snd (IT.subst su) xits)
  | Asgn ((it_addr, gbt), it_val, g') ->
    Asgn ((IT.subst su it_addr, gbt), IT.subst su it_val, subst su g')
  | Let (tries, x, gt1, gt2) ->
    let x, gt2 = suitably_alpha_rename_gen su.relevant x gt2 in
    Let (tries, x, subst su gt1, subst su gt2)
  | Return it -> Return (IT.subst su it)
  | Assert (lcs, gt') -> Assert (List.map (LC.subst su) lcs, subst su gt')
  | ITE (it, gt_then, gt_else) -> ITE (IT.subst su it, subst su gt_then, subst su gt_else)
  | Map ((i, bt, permission), gt') ->
    let i', permission = IT.suitably_alpha_rename su.relevant i permission in
    let gt' = subst (IT.make_rename ~from:i ~to_:i') gt' in
    Map ((i', bt, IT.subst su permission), subst su gt')


and subst (su : [ `Term of IT.typed | `Rename of Sym.t ] Subst.t) (gt : t) : t =
  let (GT (gt_, bt, here)) = gt in
  GT (subst_ su gt_, bt, here)


and alpha_rename_gen x gt =
  let x' = Sym.fresh_same x in
  (x', subst (IT.make_rename ~from:x ~to_:x') gt)


and suitably_alpha_rename_gen syms x gt =
  if SymSet.mem x syms then
    alpha_rename_gen x gt
  else
    (x, gt)


let rec map_gen_pre (f : t -> t) (g : t) : t =
  let (GT (gt_, bt, here)) = f g in
  let gt_ =
    match gt_ with
    | Uniform (ty, sz) -> Uniform (ty, sz)
    | Pick wgts -> Pick (List.map_snd (map_gen_pre f) wgts)
    | Alloc it -> Alloc it
    | Call (fsym, its) -> Call (fsym, its)
    | Asgn ((it_addr, gt), it_val, g') -> Asgn ((it_addr, gt), it_val, map_gen_pre f g')
    | Let (tries, x, gt, g') -> Let (tries, x, gt, map_gen_pre f g')
    | Return it -> Return it
    | Assert (lcs, g') -> Assert (lcs, map_gen_pre f g')
    | ITE (it, g_then, g_else) -> ITE (it, map_gen_pre f g_then, map_gen_pre f g_else)
    | Map ((i, bt, permission), gt') -> Map ((i, bt, permission), map_gen_pre f gt')
  in
  GT (gt_, bt, here)


let rec map_gen_post (f : t -> t) (g : t) : t =
  let (GT (gt_, bt, here)) = g in
  let gt_ =
    match gt_ with
    | Uniform (ty, sz) -> Uniform (ty, sz)
    | Pick wgts -> Pick (List.map_snd (map_gen_post f) wgts)
    | Alloc it -> Alloc it
    | Call (fsym, its) -> Call (fsym, its)
    | Asgn ((it_addr, gt), it_val, g') -> Asgn ((it_addr, gt), it_val, map_gen_post f g')
    | Let (tries, x, gt, g') -> Let (tries, x, gt, map_gen_post f g')
    | Return it -> Return it
    | Assert (lcs, g') -> Assert (lcs, map_gen_post f g')
    | ITE (it, g_then, g_else) -> ITE (it, map_gen_post f g_then, map_gen_post f g_else)
    | Map ((i, bt, permission), gt') -> Map ((i, bt, permission), map_gen_post f gt')
  in
  f (GT (gt_, bt, here))


type definition =
  { filename : string;
    name : Sym.t;
    iargs : (Sym.t * GBT.t) list;
    oargs : GBT.t list;
    body : t option
  }
