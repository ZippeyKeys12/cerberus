module AT = ArgumentTypes
module BT = BaseTypes
module RP = ResourcePredicates
module IT = IndexTerms
module LS = LogicalSorts
module RET = ResourceTypes
module LC = LogicalConstraints
module LAT = LogicalArgumentTypes
module CF = Cerb_frontend

type resource_constraint = Sym.t * RET.t

let pp_resource_constraint ((x, ret) : resource_constraint) : Pp.document =
  let open Pp in
  string "(" ^^ Sym.pp x ^^ string ", " ^^ RET.pp ret


type resource_constraints = resource_constraint list

let pp_resource_constraints (rcs : resource_constraints) : Pp.document =
  let open Pp in
  lbrace
  ^^ nest 2 (break 1 ^^ separate_map (semi ^^ break 1) pp_resource_constraint rcs)
  ^^ break 1
  ^^ rbrace


type logical_constraints = LC.t list

let pp_logical_constraints (lcs : logical_constraints) : Pp.document =
  let open Pp in
  lbrace
  ^^ nest 2 (break 1 ^^ separate_map (semi ^^ break 1) LC.pp lcs)
  ^^ break 1
  ^^ rbrace


type constraints = resource_constraints * logical_constraints

let pp_constraints ((rcs, lcs) : constraints) : Pp.document =
  let open Pp in
  string "Resource Constraints: "
  ^^ pp_resource_constraints rcs
  ^^ semi
  ^^ break 1
  ^^ string "Logical Constraints: "
  ^^ pp_logical_constraints lcs


type clause =
  { guard : IT.t;
    cs : constraints;
    it : IT.t
  }

let pp_clause ({ guard; cs; it } : clause) : Pp.document =
  let open Pp in
  string "guard"
  ^^ space
  ^^ equals
  ^^ space
  ^^ parens (IT.pp guard)
  ^^ semi
  ^^ break 1
  ^^ string "cs"
  ^^ space
  ^^ equals
  ^^ space
  ^^ braces (nest 2 (break 1 ^^ pp_constraints cs) ^^ break 1)
  ^^ semi
  ^^ break 1
  ^^ string "it"
  ^^ space
  ^^ equals
  ^^ space
  ^^ IT.pp it
  ^^ semi


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

let pp_constraint_definition (cs_def : constraint_definition) : Pp.document =
  let open Pp in
  match cs_def with
  | CD { fn; name; iargs = _; oarg = _; def = Pred cls } ->
    group
      (string "pred"
       ^^ lparen
       ^^ Sym.pp name
       ^^ comma
       ^^ space
       ^^ lbrace
       ^^ nest
            2
            (break 1
             ^^ separate_map
                  (semi ^^ break 1)
                  (fun cl -> braces (nest 2 (break 1 ^^ pp_clause cl) ^^ break 1))
                  cls)
       ^^ rbrace
       ^^ rparen
       ^^ break 1
       ^^ at
       ^^ space
       ^^ string fn)
  | CD { fn; name; iargs = _; oarg = _; def = Spec cs } ->
    group
      (string "spec"
       ^^ lparen
       ^^ Sym.pp name
       ^^ comma
       ^^ nest 2 (break 1 ^^ pp_constraints cs)
       ^^ rparen
       ^^ break 1
       ^^ at
       ^^ space
       ^^ string fn)


type constraint_context = (Sym.t * constraint_definition) list

let pp_constraint_context (cs_ctx : constraint_context) : Pp.document =
  let open Pp in
  group
    (lbrace
     ^^ break 1
     ^^ separate_map
          (semi ^^ break 1)
          (fun (x, cs_def) ->
            Sym.pp x
            ^^ space
            ^^ equals
            ^^ space
            ^^ pp_constraint_definition cs_def
            ^^ break 1
            ^^ rbrace)
          cs_ctx)


type t = constraint_context

let pp = pp_constraint_context

module Collect = struct
  let rec collect_clauses
    (filename : string)
    (prog5 : unit Mucore.mu_file)
    (cs_ctx : constraint_context)
    (lcs : logical_constraints)
    (cls : RP.clause list)
    : constraint_context * clause list
    =
    match cls with
    | cl :: cls' ->
      let cs_ctx, (it, cs) = collect_lat_it filename prog5 cs_ctx lcs cl.packing_ft in
      let cs_ctx, cls = collect_clauses filename prog5 cs_ctx lcs cls' in
      (cs_ctx, { guard = cl.guard; it; cs } :: cls)
    | [] -> (cs_ctx, [])


  and collect_ret
    (filename : string)
    (prog5 : unit Mucore.mu_file)
    (cs_ctx : constraint_context)
    (lcs : logical_constraints)
    (ret : RET.t)
    : constraint_context
    =
    match RET.predicate_name ret with
    | Owned _ -> cs_ctx
    | PName psym ->
      if List.exists (fun (psym', _) -> Sym.equal psym psym') cs_ctx then
        cs_ctx
      else (
        let pred = List.assoc Sym.equal psym prog5.mu_resource_predicates in
        let clauses = pred.clauses |> Option.get in
        let cs_ctx, rest =
          (* Add dummy definition for [psym] *)
          collect_clauses
            filename
            prog5
            (( psym,
               CD
                 { fn = filename;
                   name = psym;
                   iargs = pred.iargs;
                   oarg = pred.oarg_bt;
                   def = Pred []
                 } )
             :: cs_ctx)
            lcs
            clauses
        in
        (* Get rid of dummy definition *)
        let cs_ctx = List.filter (fun (psym', _) -> not (Sym.equal psym psym')) cs_ctx in
        ( psym,
          CD
            { fn = filename;
              name = psym;
              iargs = pred.iargs;
              oarg = pred.oarg_bt;
              def = Pred rest
            } )
        :: cs_ctx)


  and collect_lat_it
    (filename : string)
    (prog5 : unit Mucore.mu_file)
    (cs_ctx : constraint_context)
    (lcs : logical_constraints)
    (lat : IT.t LAT.t)
    : constraint_context * (IT.t * constraints)
    =
    let lat_subst x v e = LAT.subst IT.subst (IT.make_subst [ (x, v) ]) e in
    match lat with
    | Define ((x, tm), _, lat') ->
      collect_lat_it filename prog5 cs_ctx lcs (lat_subst x tm lat')
    | Resource ((x, (ret, _)), _, lat') ->
      let cs_ctx = collect_ret filename prog5 cs_ctx lcs ret in
      let cs_ctx, (v', (rcs, lcs)) = collect_lat_it filename prog5 cs_ctx lcs lat' in
      (cs_ctx, (v', ((x, ret) :: rcs, lcs)))
    | Constraint (lc, _, lat') ->
      let cs_ctx, (v, (rcs, lcs)) = collect_lat_it filename prog5 cs_ctx lcs lat' in
      (cs_ctx, (v, (rcs, lc :: lcs)))
    | I it -> (cs_ctx, (it, ([], [])))


  let rec collect_lat
    (filename : string)
    (prog5 : unit Mucore.mu_file)
    (cs_ctx : constraint_context)
    (lcs : logical_constraints)
    (lat : unit LAT.t)
    : constraint_context * constraints
    =
    let lat_subst x v e = LAT.subst (fun _ x -> x) (IT.make_subst [ (x, v) ]) e in
    match lat with
    | Define ((x, tm), _, lat') ->
      collect_lat filename prog5 cs_ctx lcs (lat_subst x tm lat')
    | Resource ((x, (ret, _)), _, lat') ->
      let cs_ctx = collect_ret filename prog5 cs_ctx lcs ret in
      let cs_ctx, (rcs, lcs) = collect_lat filename prog5 cs_ctx lcs lat' in
      (cs_ctx, ((x, ret) :: rcs, lcs))
    | Constraint (lc, _, lat') ->
      let cs_ctx, (rcs, lcs) = collect_lat filename prog5 cs_ctx lcs lat' in
      (cs_ctx, (rcs, lc :: lcs))
    | I _ -> (cs_ctx, ([], lcs))


  let rec collect_at
    (filename : string)
    (prog5 : unit Mucore.mu_file)
    (cs_ctx : constraint_context)
    (lcs : logical_constraints)
    (at : unit AT.t)
    : (Sym.t * BT.t) list * (constraint_context * constraints)
    =
    match at with
    | Computational ((x, bt), _, at') ->
      let ty_ctx, res = collect_at filename prog5 cs_ctx lcs at' in
      ((x, bt) :: ty_ctx, res)
    | L lat -> ([], collect_lat filename prog5 cs_ctx [] lat)


  let collect_spec
    (filename : string)
    (prog5 : unit Mucore.mu_file)
    (cs_ctx : constraint_context)
    (fsym : Sym.t)
    (at : unit AT.t)
    : constraint_context
    =
    let ty_ctx, (cs_ctx, cs) = collect_at filename prog5 cs_ctx [] at in
    (fsym, CD { fn = filename; name = fsym; iargs = ty_ctx; oarg = Unit; def = Spec cs })
    :: cs_ctx


  let collect (prog5 : unit Mucore.mu_file) (filenames : string list) : constraint_context
    =
    let aux (cs_ctx : constraint_context) (filename : string) : constraint_context =
      let data =
        prog5
        |> Core_to_mucore.collect_instrumentation
        |> fst
        |> List.filter_map (fun (inst : Core_to_mucore.instrumentation) ->
          match Cerb_location.get_filename inst.fn_loc with
          | Some filename' when String.equal filename filename' ->
            let lat = inst.internal |> Option.get |> AT.map (fun _ -> ()) in
            Some (inst.fn, lat)
          | _ -> None)
      in
      List.fold_left
        (fun cs_ctx' (fsym, lat) -> collect_spec filename prog5 cs_ctx' fsym lat)
        cs_ctx
        data
    in
    List.fold_left aux [] filenames
end

let collect = Collect.collect

module Simplify = struct
  let assume_good_and_representable (_cs_ctx : constraint_context) : constraint_context =
    failwith "todo: evaluate good and representable to true"


  let simplify (cs_ctx : constraint_context) : constraint_context = cs_ctx
end

let simplify = Simplify.simplify
