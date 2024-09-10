module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module CF = Cerb_frontend
module GBT = GenBaseTypes
module SymMap = Map.Make (Sym)
module SymSet = Set.Make (Sym)

type t_ =
  | Arbitrary (** Generate arbitrary values *)
  | Uniform of int (** Generate uniform values *)
  | Pick of (int * t) list
  (** Pick among a list of options, weighted by the provided [int]s *)
  | Alloc of IT.t (** Allocate an array of a length [IT.t]  and return its address *)
  | Call of Sym.t * (Sym.t * IT.t) list
  (** Call a defined generator according to a [Sym.t] with arguments [IT.t list] *)
  | Asgn of (IT.t * Sctypes.t) * IT.t * t
  (** Claim ownership and assign a value to a memory location *)
  | Let of int * Sym.t * t * t (** Monadic bind *)
  | Return of IT.t (** Monadic return *)
  | Assert of LC.t * t (** Assert some [LC.t] are true, backtracking otherwise *)
  | ITE of IT.t * t * t (** If-then-else *)
  | Map of (Sym.t * BT.t * (IT.t * IT.t) * IT.t) * t
[@@deriving eq, ord]

and t = GT of t_ * BT.t * (Locations.t[@equal fun _ _ -> true] [@compare fun _ _ -> 0])
[@@deriving eq, ord]

(* Accessors *)

let term (GT (gt_, _, _)) = gt_

let basetype (GT (_, bt, _)) = bt

let bt = basetype

let loc (GT (_, _, loc)) = loc

(* Smart constructors *)

let arbitrary_ (bt : BT.t) (loc : Locations.t) : t = GT (Arbitrary, bt, loc)

let uniform_ ((bt, sz) : BT.t * int) (loc : Locations.t) : t = GT (Uniform sz, bt, loc)

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

let assert_ ((lc, gt') : LC.t * t) (loc : Locations.t) : t =
  GT (Assert (lc, gt'), basetype gt', loc)


let ite_ ((it_if, gt_then, gt_else) : IT.t * t * t) loc : t =
  let bt = basetype gt_then in
  assert (BT.equal bt (basetype gt_else));
  GT (ITE (it_if, gt_then, gt_else), bt, loc)


let map_
  (((i, i_bt, its_range, it_perm), gt_inner) :
    (Sym.t * BT.t * (IT.t * IT.t) option * IT.t) * t)
  loc
  : t
  =
  let it_min, it_max =
    match its_range with
    | Some (it_min, it_max) -> (it_min, it_max)
    | None ->
      let min, max = BT.is_bits_bt i_bt |> Option.get |> BT.bits_range in
      (IT.num_lit_ min i_bt loc, IT.num_lit_ max i_bt loc)
  in
  GT
    ( Map ((i, i_bt, (it_min, it_max), it_perm), gt_inner),
      BT.make_map_bt i_bt (basetype gt_inner),
      loc )


(* Constructor-checking functions *)
let is_arbitrary_ (gt_ : t_) : bool = match gt_ with Arbitrary -> true | _ -> false

let is_arbitrary (gt : t) : bool =
  let (GT (gt_, _, _)) = gt in
  is_arbitrary_ gt_


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
  | GT (Arbitrary, bt, _here) -> string "arbitrary" ^^ angles (BT.pp bt) ^^ parens empty
  | GT (Uniform sz, bt, _here) -> string "uniform" ^^ angles (BT.pp bt) ^^ parens (int sz)
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
    ^^ nest 2 (break 1 ^^ pp gt1)
    ^^ semi
    ^^ break 1
    ^^ pp gt2
  | GT (Return it, _bt, _here) -> string "return" ^^ space ^^ IT.pp it
  | GT (Assert (lc, gt'), _bt, _here) ->
    string "assert"
    ^^ parens (nest 2 (break 1 ^^ LC.pp lc) ^^ break 1)
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
  | GT (Map ((i, i_bt, (it_min, it_max), it_perm), gt'), _bt, here) ->
    let it_i = IT.sym_ (i, i_bt, here) in
    let it_perm' =
      IT.and_ [ IT.lt_ (it_min, it_i) here; IT.lt_ (it_i, it_max) here; it_perm ] here
    in
    string "map"
    ^^ space
    ^^ parens (BT.pp i_bt ^^ space ^^ Sym.pp i ^^ semi ^^ space ^^ IT.pp it_perm')
    ^^ braces (nest 2 (break 1 ^^ pp gt') ^^ break 1)


let rec subst_ (su : [ `Term of IT.typed | `Rename of Sym.t ] Subst.t) (gt_ : t_) : t_ =
  match gt_ with
  | Arbitrary -> Arbitrary
  | Uniform sz -> Uniform sz
  | Pick wgts -> Pick (List.map_snd (subst su) wgts)
  | Alloc it -> Alloc (IT.subst su it)
  | Call (fsym, xits) -> Call (fsym, List.map_snd (IT.subst su) xits)
  | Asgn ((it_addr, gbt), it_val, g') ->
    Asgn ((IT.subst su it_addr, gbt), IT.subst su it_val, subst su g')
  | Let (tries, x, gt1, gt2) ->
    let x, gt2 = suitably_alpha_rename_gen su.relevant x gt2 in
    Let (tries, x, subst su gt1, subst su gt2)
  | Return it -> Return (IT.subst su it)
  | Assert (lc, gt') -> Assert (LC.subst su lc, subst su gt')
  | ITE (it, gt_then, gt_else) -> ITE (IT.subst su it, subst su gt_then, subst su gt_else)
  | Map ((i, bt, (it_min, it_max), it_perm), gt') ->
    let i', it_perm = IT.suitably_alpha_rename su.relevant i it_perm in
    let gt' = subst (IT.make_rename ~from:i ~to_:i') gt' in
    Map
      ( (i', bt, (IT.subst su it_min, IT.subst su it_max), IT.subst su it_perm),
        subst su gt' )


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


let rec free_vars_bts_ (gt_ : t_) : BT.t SymMap.t =
  match gt_ with
  | Arbitrary | Uniform _ -> SymMap.empty
  | Pick wgts -> free_vars_bts_list (List.map snd wgts)
  | Alloc it -> IT.free_vars_bts it
  | Call (_, xits) -> IT.free_vars_bts_list (List.map snd xits)
  | Asgn ((it_addr, _), it_val, gt') ->
    free_vars_bts_list
      [ return_ it_addr Locations.unknown; return_ it_val Locations.unknown; gt' ]
  | Let (_, x, gt1, gt2) ->
    SymMap.union
      (fun _ bt1 bt2 ->
        assert (BT.equal bt1 bt2);
        Some bt1)
      (free_vars_bts gt1)
      (SymMap.remove x (free_vars_bts gt2))
  | Return it -> IT.free_vars_bts it
  | Assert (lc, gt') ->
    (SymMap.union (fun _ bt1 bt2 ->
       assert (BT.equal bt1 bt2);
       Some bt1))
      (free_vars_bts gt')
      (LC.free_vars_bts lc)
  | ITE (it_if, gt_then, gt_else) ->
    free_vars_bts_list [ return_ it_if Locations.unknown; gt_then; gt_else ]
  | Map ((i, _bt, (it_min, it_max), it_perm), gt') ->
    (SymMap.union (fun _ bt1 bt2 ->
       assert (BT.equal bt1 bt2);
       Some bt1))
      (IT.free_vars_bts_list [ it_min; it_max ])
      (SymMap.remove i (free_vars_bts_list [ return_ it_perm Locations.unknown; gt' ]))


and free_vars_bts (GT (gt_, _, _) : t) : BT.t SymMap.t = free_vars_bts_ gt_

and free_vars_bts_list : t list -> BT.t SymMap.t =
  fun xs ->
  List.fold_left
    (fun ss t ->
      SymMap.union
        (fun _ bt1 bt2 ->
          assert (BT.equal bt1 bt2);
          Some bt1)
        ss
        (free_vars_bts t))
    SymMap.empty
    xs


let free_vars (gt : t) : SymSet.t =
  gt |> free_vars_bts |> SymMap.bindings |> List.map fst |> SymSet.of_list


let rec map_gen_pre (f : t -> t) (g : t) : t =
  let (GT (gt_, bt, here)) = f g in
  let gt_ =
    match gt_ with
    | Arbitrary -> Arbitrary
    | Uniform sz -> Uniform sz
    | Pick wgts -> Pick (List.map_snd (map_gen_pre f) wgts)
    | Alloc it -> Alloc it
    | Call (fsym, its) -> Call (fsym, its)
    | Asgn ((it_addr, gt), it_val, gt') -> Asgn ((it_addr, gt), it_val, map_gen_pre f gt')
    | Let (tries, x, gt, gt') -> Let (tries, x, map_gen_pre f gt, map_gen_pre f gt')
    | Return it -> Return it
    | Assert (lcs, gt') -> Assert (lcs, map_gen_pre f gt')
    | ITE (it, gt_then, gt_else) -> ITE (it, map_gen_pre f gt_then, map_gen_pre f gt_else)
    | Map ((i, bt, (it_min, it_max), it_perm), gt') ->
      Map ((i, bt, (it_min, it_max), it_perm), map_gen_pre f gt')
  in
  GT (gt_, bt, here)


let rec map_gen_post (f : t -> t) (g : t) : t =
  let (GT (gt_, bt, here)) = g in
  let gt_ =
    match gt_ with
    | Arbitrary -> Arbitrary
    | Uniform sz -> Uniform sz
    | Pick wgts -> Pick (List.map_snd (map_gen_post f) wgts)
    | Alloc it -> Alloc it
    | Call (fsym, its) -> Call (fsym, its)
    | Asgn ((it_addr, gt), it_val, gt') -> Asgn ((it_addr, gt), it_val, map_gen_post f gt')
    | Let (tries, x, gt, gt') -> Let (tries, x, map_gen_post f gt, map_gen_post f gt')
    | Return it -> Return it
    | Assert (lcs, gt') -> Assert (lcs, map_gen_post f gt')
    | ITE (it, gt_then, gt_else) ->
      ITE (it, map_gen_post f gt_then, map_gen_post f gt_else)
    | Map ((i, bt, (it_min, it_max), it_perm), gt') ->
      Map ((i, bt, (it_min, it_max), it_perm), map_gen_post f gt')
  in
  f (GT (gt_, bt, here))


type definition =
  { filename : string;
    name : Sym.t;
    iargs : (Sym.t * GBT.t) list;
    oargs : GBT.t list;
    body : t option
  }