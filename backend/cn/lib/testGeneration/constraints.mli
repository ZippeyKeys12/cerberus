module BT = BaseTypes
module IT = IndexTerms
module RET = ResourceTypes
module LC = LogicalConstraints
module LAT = LogicalArgumentTypes
module CF = Cerb_frontend

type resource_constraint = Sym.t * RET.t

val pp_resource_constraint : resource_constraint -> Pp.document

type resource_constraints = resource_constraint list

val pp_resource_constraints : resource_constraints -> Pp.document

type logical_constraints = LC.t list

val pp_logical_constraints : logical_constraints -> Pp.document

type constraints = resource_constraints * logical_constraints

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
        oarg : BT.t;
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
