module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module GC = GenConstraints
module GTC = GenTypeConstraints

type t = Sym.t * (Sym.t option * BT.t) * GTC.t [@@deriving eq, ord]

let pred ((_, (psym, _), _) : t) : Sym.t option = psym

let sym ((x, _, _) : t) : Sym.t = x

let bt ((_, (_, bt), _) : t) : BT.t = bt

let gtc ((_, _, gtc) : t) : GTC.t = gtc

let pp ((x, (psym, bt), gtc) : t) : Pp.document =
  let open Pp in
  if GTC.is_true gtc then
    BT.pp bt ^^ space ^^ at ^^ Option.pp Sym.pp psym
  else
    braces
      (Sym.pp x
       ^^ space
       ^^ colon
       ^^ space
       ^^ BT.pp bt
       ^^ space
       ^^ bar
       ^^ space
       ^^ GTC.pp gtc)
    ^^ space
    ^^ at
    ^^ Option.pp Sym.pp psym


let of_bt ?(pred_sym : Sym.t option = None) (bt : BT.t) : t =
  (Sym.fresh (), (pred_sym, bt), GTC.true_)

(* let inter ((x1, bt1, gtc1) : t) ((x2, bt2, gtc2) : t) : t =
   let gtc2 = GTC.subst (IT.make_rename ~from:x2 ~to_:x1) gtc2 in
   assert (BT.equal bt1 bt2);
   let gtc = GTC.inter gtc1 gtc2 in
   (x1, bt1, gtc) *)
