open Report
module IT = IndexTerms
module BT = BaseTypes
module RE = Resources
module RET = ResourceTypes
module LC = LogicalConstraints
module LS = LogicalSorts
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module StringMap = Map.Make(String)
module SymPairMap = Map.Make(SymRel.SymPair)
module C = Context
module Loc = Locations
module S = Solver

open ResourceTypes
open IndexTerms
open Pp
open C
open Resources



(* perhaps somehow unify with above *)
type action = 
  | Read of IndexTerms.t * IndexTerms.t
  | Write of IndexTerms.t * IndexTerms.t
  | Create of IndexTerms.t 
  | Kill of IndexTerms.t
  | Call of Sym.t * IndexTerms.t list
  | Return of IndexTerms.t

type log_entry = 
  | Action of action * Locations.t
  | State of Context.t

type log = log_entry list       (* most recent first *)




let clause_has_resource req c =
  let open LogicalArgumentTypes in
  let rec f = function
    | Resource ((_, (r, _)), _, c) -> RET.same_predicate_name req r || f c
    | Constraint (_, _, c) -> f c
    | Define (_, _, c) -> f c
    | I _ -> false
  in
  let open ResourcePredicates in
  f c.packing_ft

let relevant_predicate_clauses global name req =
  let open Global in
  let open ResourcePredicates in
  let clauses =
    let defs = SymMap.bindings global.resource_predicates in
    List.Old.concat_map (fun (nm, def) ->
        match def.clauses with
        | Some clauses -> List.Old.map (fun c -> (nm, c)) clauses
        | None -> []
      ) defs
  in
  List.Old.filter (fun (nm, c) -> 
      Sym.equal nm name
      || clause_has_resource req c
    ) clauses

type state_extras = {
    request : RET.t option;
    unproven_constraint : LC.t option;
  }

let no_ex = {request = None; unproven_constraint = None}


module ITSet = struct 
  include Simplify.ITSet

  let rec bigunion_map f = function
    | [] -> empty
    | x :: xs -> union (f x) (bigunion_map f xs)

end

  


let subterms_without_bound_variables bindings = 
  fold_subterms ~bindings (fun bindings acc t ->
      let pats = List.Old.map fst bindings in
      let bound = List.Old.concat_map bound_by_pattern pats in
      let bound = SymSet.of_list (List.Old.map fst bound) in
      if SymSet.(is_empty (inter bound (IT.free_vars t))) 
      then ITSet.add t acc
      else acc
    ) ITSet.empty


let state ctxt model_with_q extras = 

  let where = 
    let cur_colour = !Cerb_colour.do_colour in
    Cerb_colour.do_colour := false;
    let head_pos prfx loc = 
      let head,pos = Loc.head_pos_of_location loc in
      ((prfx^" "^head), pos)
    in
    let loc_cartesian, (loc_head, _loc_pos) = 
      match ctxt.where.statement, ctxt.where.expression with
      | _, Some loc -> Cerb_location.to_cartesian loc, head_pos "expr" loc
      | Some loc, None -> Cerb_location.to_cartesian loc, head_pos "stmt" loc
      | None, None -> None, ("", "\n")
    in
    let fnction = Option.map (Sym.pp_string) ctxt.where.fnction in
    let section = Option.map (fun s -> Pp.plain (Where.pp_section s)) ctxt.where.section in
    let result = Report.{ fnction; section; loc_cartesian; loc_head } in
    Cerb_colour.do_colour := cur_colour;
    result
  in

  let model, quantifier_counter_model = model_with_q in

  let evaluate it = Solver.eval ctxt.global model it in

  (* let _mevaluate it = *)
  (*   match evaluate it with *)
  (*   | Some v -> IT.pp v *)
  (*   | None -> parens !^"not evaluated" *)
  (* in *)



  let terms = 

    let variables =
      let make s ls = sym_ (s, ls, Locations.other __FUNCTION__) in
      let basetype_binding (s, (binding, _)) = 
        match binding with 
        | Value _ -> None 
        | BaseType ls -> Some (make s ls)
      in
      ITSet.of_list
          (List.Old.map (fun (s, ls) -> make s ls) quantifier_counter_model
           @ List.Old.filter_map basetype_binding (SymMap.bindings ctxt.computational)
           @ List.Old.filter_map basetype_binding (SymMap.bindings ctxt.logical))
    in

    let unproven = match extras.unproven_constraint with
      | Some (T lc) -> 
         subterms_without_bound_variables [] lc
      | Some (Forall ((s,bt), lc)) ->
         let binder = (Pat (PSym s, bt, Loc.other __FUNCTION__), None) in
         subterms_without_bound_variables [binder] lc
      | None -> 
         ITSet.empty
    in

    let request = match extras.request with
      | Some (P ret) ->
         ITSet.bigunion_map (subterms_without_bound_variables []) 
           (ret.pointer :: ret.iargs)
      | Some (Q ret) ->
         let binder = (Pat (PSym (fst ret.q), snd ret.q, Loc.other __FUNCTION__), None) in
         ITSet.union
           (ITSet.bigunion_map (subterms_without_bound_variables [])
              [ret.pointer; ret.step])
           (ITSet.bigunion_map (subterms_without_bound_variables [binder])
              (ret.permission :: ret.iargs))
      | None -> 
         ITSet.empty
    in

    let subterms = 
      List.Old.fold_left ITSet.union ITSet.empty 
        [variables; unproven; request] 
    in


    let filtered = 
      List.Old.filter_map (fun it -> 
          match evaluate it with
          | Some value when not (IT.equal value it) ->
             Some (it, {term = IT.pp it; value = IT.pp value})
          | Some _ -> 
             None
          | None -> 
             None
        ) (ITSet.elements subterms)
    in

    let interesting, uninteresting = 
      List.Old.partition (fun (it, _entry) ->
          match IT.bt it with
          | BT.Unit -> false
          | BT.Loc -> false
          | _ -> true
        ) filtered
    in

    (List.Old.map snd interesting, 
     List.Old.map snd uninteresting)

  in

  let constraints =
    let interesting, uninteresting = 
      List.Old.partition (fun lc ->
          match lc with
          (* | LC.T (IT (Aligned _, _, _)) -> false *)
          | LC.T (IT (Representable _, _, _)) -> false
          | LC.T (IT (Good _, _, _)) -> false
          | _ -> true
        ) (LCSet.elements ctxt.constraints)
    in
    (List.Old.map LC.pp interesting, 
     List.Old.map LC.pp uninteresting)
  in

  let resources =
    let (same_res, diff_res) = match extras.request with
      | None -> ([], get_rs ctxt)
      | Some req -> List.Old.partition (fun r -> RET.same_predicate_name req (RE.request r)) (get_rs ctxt)
    in
    let interesting_diff_res, uninteresting_diff_res = 
      List.Old.partition (fun (ret, _o) ->
          match ret with
          | P ret when equal_predicate_name ret.name ResourceTypes.alloc_name -> false
          | _ -> true
        ) diff_res
    in

    let interesting = 
      List.Old.map (fun re -> RE.pp re ^^^ parens !^"same type") same_res 
      @ List.Old.map RE.pp interesting_diff_res
    in
    let uninteresting = 
      List.Old.map RE.pp uninteresting_diff_res
    in
    (interesting, uninteresting)
  in

  { where;
    terms;
    resources;
    constraints }



let trace (ctxt,log) (model_with_q : Solver.model_with_q) (extras : state_extras) =

  let prev = ! Pp.html_escapes in
  Pp.html_escapes := true;


  (* let req_cmp = Option.bind extras.request (Spans.spans_compare_for_pp model ctxt.global) in *)
  (* let req_entry req_cmp req = { *)
  (*     res = RET.pp req; *)
  (*     res_span = Spans.pp_model_spans model ctxt.global req_cmp req *)
  (*   } *)
  (* in *)
  (* let res_entry req_cmp same res = { *)
  (*     res = RE.pp res; *)
  (*     res_span = Spans.pp_model_spans model ctxt.global req_cmp (RE.request res) *)
  (*       ^^ (if same then !^" - same-type" else !^"") *)
  (*   } *)
  (* in *)


  let req_entry ret = RET.pp ret in

  let trace = 
    let statef ctxt = state ctxt model_with_q extras in
    List.Old.rev (statef ctxt :: List.Old.filter_map (function State ctxt -> Some (statef ctxt) | _ -> None) log)
  in


  let predicate_hints = match extras.request with
    | None -> []
    | Some req ->
       let open ResourcePredicates in
       match predicate_name req with
       | Owned _ -> []
       | PName pname ->
          let doc_clause (_name, c) = {
              cond = IT.pp c.guard;
              clause = LogicalArgumentTypes.pp IT.pp c.packing_ft
            }
          in
          List.Old.map doc_clause (relevant_predicate_clauses ctxt.global pname req)
  in
  let requested = Option.map req_entry extras.request in

  let unproven = match extras.unproven_constraint with
    | Some lc -> 
       let lc_simp = Simplify.LogicalConstraints.simp (Simplify.default ctxt.global) lc in 
       Some (LC.pp lc_simp)
    | None ->
       None
  in

    

  Pp.html_escapes := prev;


  { requested;
    unproven;
    predicate_hints;
    trace }







