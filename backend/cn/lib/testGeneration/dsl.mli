module GT = GenTypes
module IT = IndexTerms
module LC = LogicalConstraints
module CF = Cerb_frontend

type gen_term_ =
  | Arbitrary
  | Just of IT.t
  | Alloc of IT.t
  | Call of Sym.t * IT.t list

and gen_term = GT of GT.base_type * gen_term_

val pp_gen_term : gen_term -> Pp.document

type gen =
  | Asgn of (IT.t * GT.base_type) * IT.t * gen
  | Let of Sym.t list * gen_term * gen
  | Return of IT.t
  | Assert of LC.t list * gen
  | ITE of IT.t * gen * gen

val pp_gen : gen -> Pp.document

type gen_def =
  { name : Sym.t;
    args : (Sym.t * GT.base_type) list;
    rets : GT.base_type list;
    body : gen option
  }

val pp_gen_def : gen_def -> Pp.document

type gen_context = (Sym.t * gen_def) list

val pp_gen_context : gen_context -> Pp.document

val compile : Constraints.t -> gen_context

val optimize : gen_context -> gen_context
