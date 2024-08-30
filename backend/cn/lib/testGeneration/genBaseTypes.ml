module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module GC = GenConstraints
module GTC = GenTypeConstraints

type t = Sym.t * BT.t * GTC.t [@@deriving eq, ord]

let pp ((x, bt, gtc) : t) : Pp.document =
  let open Pp in
  if GTC.is_true gtc then
    BT.pp bt
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


let of_bt (bt : BT.t) : t = (Sym.fresh (), bt, GTC.true_)

let inter ((x1, bt1, gtc1) : t) ((x2, bt2, gtc2) : t) : t =
  let gtc2 = GTC.subst (IT.make_rename ~from:x2 ~to_:x1) gtc2 in
  assert (BT.equal bt1 bt2);
  let gtc = GTC.inter gtc1 gtc2 in
  (x1, bt1, gtc)
