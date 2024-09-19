module CF = Cerb_frontend
module A = CF.AilSyntax
module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module GD = GenDefinitions

type term =
  | Uniform of
      { bt : BT.t;
        sz : int
      }
  | Pick of { choices : (int * term) list }
  | Alloc of { bytes : IT.t }
  | Call of
      { fsym : Sym.t;
        iargs : (Sym.t * Sym.t) list
      }
  | Asgn of
      { pointer : Sym.t;
        offset : IT.t;
        sct : Sctypes.t;
        value : IT.t;
        last_var : Sym.t;
        rest : term
      }
  | Let of
      { backtracks : int;
        x : Sym.t;
        x_bt : BT.t;
        value : term;
        rest : term
      }
  | Return of { value : IT.t }
  | Assert of
      { prop : LC.t;
        last_var : Sym.t;
        rest : term
      }
  | ITE of
      { bt : BT.t;
        cond : IT.t;
        t : term;
        f : term
      }
  | Map of
      { i : Sym.t;
        i_bt : BT.t;
        upper : IT.t;
        lower : IT.t;
        guard : IT.t;
        inner : term
      }
[@@deriving eq, ord]

type definition =
  { name : Sym.t;
    iargs : (Sym.t * BT.t) list;
    oargs : (Sym.t * BT.t) list;
    body : term option
  }
[@@deriving eq, ord]

type context = (A.ail_identifier * (A.ail_identifier list * definition) list) list

val elaborate : CF.GenTypes.genTypeCategory A.sigma -> GD.context -> context
