module BT = BaseTypes
module IT = IndexTerms
module RET = ResourceTypes
module LC = LogicalConstraints
module LAT = LogicalArgumentTypes
module CF = Cerb_frontend

type constraint_ =
  | Ownership of
      { pointer : Sym.t;
        x : Sym.t;
        ty : Sctypes.t
      }
  | Logical of LC.t
  | Predicate of
      { name : Sym.t;
        iargs : (Sym.t * BT.t) list;
        oarg : Sym.t * BT.t
      }

val pp_constraint : constraint_ -> Pp.document

type constraints = constraint_ list

val pp_constraints : constraints -> Pp.document

type clause =
  { guard : IT.t;
    cs : constraints;
    it : IT.t
  }

val pp_clause : clause -> Pp.document

type constraint_definition_ =
  | Pred of clause list
  | Spec of constraints

and constraint_definition =
  | CD of
      { fn : string; (** File this definition came from *)
        name : Sym.t;
        iargs : (Sym.t * BT.t) list;
        oarg : BT.t option;
        def : constraint_definition_
      }

val pp_constraint_definition : constraint_definition -> Pp.document

type constraint_context = (Sym.t * constraint_definition) list

val pp_constraint_context : constraint_context -> Pp.document

type t = constraint_context

val pp : t -> Pp.document

(** Collecting [constraints] for all specifications and predicates in [filename] *)
val collect : unit Mucore.mu_file -> string list -> t

val simplify : t -> t
