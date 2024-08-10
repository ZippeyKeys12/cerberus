module GT = GenTypes
module IT = IndexTerms
module LC = LogicalConstraints
open Constraints
open Utils
module CF = Cerb_frontend
module SymMap = Map.Make (Sym)
module SymSet = Set.Make (Sym)

type gen_term_ =
  | Arbitrary
  | Just of IT.t
  | Alloc of IT.t
  | Call of Sym.t * IT.t list

and gen_term = GT of GT.base_type * gen_term_

let rec pp_gen_term (gt : gen_term) : Pp.document =
  let open Pp in
  match gt with
  | GT (tys, Arbitrary) -> string "arbitrary<" ^^ GT.pp_base_type tys ^^ string ">()"
  | GT (tys, Just it) ->
    string "just<" ^^ GT.pp_base_type tys ^^ string ">(" ^^ IT.pp it ^^ string ")"
  | GT (tys, Alloc it) ->
    string "alloc<"
    ^^ GT.pp_base_type tys
    ^^ string ">("
    ^^ space
    ^^ IT.pp it
    ^^ space
    ^^ rparen
  | GT (tys, Call (fsym, its)) ->
    Sym.pp fsym
    ^^ string "<"
    ^^ GT.pp_base_type tys
    ^^ string ">"
    ^^ parens (nest 2 (separate_map (comma ^^ break 1) IT.pp its))


type gen =
  | Asgn of (IT.t * GT.base_type) * IT.t * gen
  | Let of Sym.t list * gen_term * gen
  | Return of IT.t
  | Assert of LC.t list * gen
  | ITE of IT.t * gen * gen

let rec pp_gen (g : gen) : Pp.document =
  let open Pp in
  match g with
  | Asgn ((it_addr, gt), it_val, g') ->
    GT.pp_base_type gt
    ^^ space
    ^^ IT.pp it_addr
    ^^ space
    ^^ colon
    ^^ equals
    ^^ space
    ^^ IT.pp it_val
    ^^ semi
    ^^ break 1
    ^^ pp_gen g'
  | Let (xs, gt, g') ->
    string "let "
    ^^ separate_map (comma ^^ space) Sym.pp xs
    ^^ string " = "
    ^^ pp_gen_term gt
    ^^ semi
    ^^ break 1
    ^^ pp_gen g'
  | Return it -> string "return " ^^ IT.pp it ^^ semi
  | Assert (its, g') ->
    string "assert"
    ^^ parens (nest 2 (break 1 ^^ separate_map (comma ^^ break 1) LC.pp its) ^^ break 1)
    ^^ semi
    ^^ break 1
    ^^ pp_gen g'
  | ITE (it, g_then, g_else) ->
    string "if"
    ^^ space
    ^^ parens (IT.pp it)
    ^^ space
    ^^ braces (nest 2 (break 1 ^^ pp_gen g_then) ^^ break 1)
    ^^ space
    ^^ string "else"
    ^^ space
    ^^ braces (nest 2 (break 1 ^^ pp_gen g_else) ^^ break 1)


let map_gen (f : gen -> gen) (g : gen) : gen =
  match g with
  | Asgn ((it_addr, gt), it_val, g') -> Asgn ((it_addr, gt), it_val, f g')
  | Let (xs, gt, g') -> Let (xs, gt, f g')
  | Return _ -> g
  | Assert (lcs, g') -> Assert (lcs, f g')
  | ITE (it, g_then, g_else) -> ITE (it, f g_then, f g_else)


type gen_def =
  { name : Sym.t;
    iargs : (Sym.t * GT.base_type) list;
    oargs : GT.base_type list;
    body : gen option
  }

let pp_gen_def (gd : gen_def) : Pp.document =
  let open Pp in
  group
    (string "generator"
     ^^ space
     ^^ parens (separate_map (comma ^^ space) GT.pp_base_type gd.oargs)
     ^^ space
     ^^ Sym.pp gd.name
     ^^ parens
          (separate_map
             (comma ^^ space)
             (fun (x, ty) -> GT.pp_base_type ty ^^ space ^^ Sym.pp x)
             gd.iargs)
     ^^
     match gd.body with
     | Some body ->
       space ^^ lbrace ^^ nest 2 (break 1 ^^ pp_gen body) ^^ break 1 ^^ rbrace
     | None -> semi)


type gen_context = (Sym.t * gen_def) list

let pp_gen_context (gtx : gen_context) : Pp.document =
  let open Pp in
  group
    (lbrace
     ^^ break 1
     ^^ separate_map
          (break 1)
          (fun (x, g) ->
            assert (x == g.name);
            pp_gen_def g)
          gtx)


(** Generate arbitrary values of type [ty] *)
let arbitrary_ (ty : GT.base_type) : gen_term = GT (ty, Arbitrary)

(** Generate exactly [it] of type [ty] *)
let just_ (it : IT.t) : gen_term = GT (GT.of_bt (IT.bt it), Just it)

(** Allocate memory containing the result of [gt] and return its address *)
let alloc_ (it : IT.t) : gen_term = GT (GT.of_bt (IT.bt it), Alloc it)

(** Call a defined generator named [fsym] with arguments [gts], from context [gtx] *)
let call_ (gtx : gen_context) (fsym : Sym.t) (its : IT.t list) : gen_term =
  let { oargs; _ } = List.assoc Sym.equal fsym gtx in
  GT (Tuple oargs, Call (fsym, its))


module Compile = struct
  module Order = struct
    module Pair = struct
      type t = Sym.t * BT.t

      let compare (x, _) (y, _) = Sym.compare x y

      let hash (x, _) = Sym.hash x

      let equal (x, x_bt) (y, y_bt) =
        if Sym.equal x y then (
          assert (BT.equal x_bt y_bt);
          true)
        else
          false
    end

    module G = Graph.Persistent.Digraph.Concrete (Pair)
    module Components = Graph.Components.Undirected (G)

    module Dot = Graph.Graphviz.Dot (struct
        include G (* use the graph module from above *)

        let edge_attributes _ = []

        let default_edge_attributes _ = []

        let get_subgraph _ = None

        let vertex_attributes _ = []

        let vertex_name (x, bt) =
          let doc =
            let open Pp in
            Sym.pp x ^^ space ^^ colon ^^ space ^^ BT.pp bt
          in
          Pp.plain doc


        let default_vertex_attributes _ = []

        let graph_attributes _ = []
      end)

    (** Build a dependency graph of all the variables in [cs] *)
    let construct_graph (args : (Sym.t * BT.t) list) (cs : constraints) : G.t =
      (* Add vertices *)
      let g = List.fold_left (fun g x -> G.add_vertex g x) G.empty args in
      let g =
        List.fold_left
          (fun g c ->
            match c with
            | Ownership { pointer; x; ty } ->
              G.add_vertex
                (G.add_vertex
                   g
                   ( x,
                     BT.of_sct
                       Memory.is_signed_integer_type
                       Memory.size_of_integer_type
                       ty ))
                (pointer, Loc)
            | Logical lc ->
              SymMap.fold (fun x bt g -> G.add_vertex g (x, bt)) (LC.free_vars_bts lc) g
            | Predicate { name = _; iargs; oarg } ->
              let g = List.fold_left (fun g y -> G.add_vertex g y) g iargs in
              G.add_vertex g oarg)
          g
          cs
      in
      let g =
        List.fold_left
          (fun g c ->
            match c with
            | Ownership { pointer; x; ty } ->
              G.add_edge_e
                g
                ( (pointer, Loc),
                  ( x,
                    BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type ty
                  ) )
            | Logical lc ->
              (match lc with
               | T (IT (Binop (EQ, it1, it2), _, _))
                 when not
                      @@ Bool.equal
                           (Option.is_some (IT.is_sym it1))
                           (Option.is_some (IT.is_sym it2)) ->
                 (match (it1, it2) with
                  | IT (Sym x, x_bt, _), it | it, IT (Sym x, x_bt, _) ->
                    let struct_indirection_hack = Option.is_some @@ IT.is_member it in
                    IT.SymMap.fold
                      (fun y y_bt g ->
                        if struct_indirection_hack then
                          G.add_edge_e g ((x, x_bt), (y, y_bt))
                        else
                          G.add_edge_e g ((y, y_bt), (x, x_bt)))
                      (IT.free_vars_bts it)
                      g
                  | _ -> failwith ("unreachable (" ^ __LOC__ ^ ")"))
               | _ ->
                 let free_vars_bts = LC.free_vars_bts lc in
                 SymMap.fold
                   (fun x x_bt g ->
                     SymMap.fold
                       (fun y y_bt g -> G.add_edge_e g ((x, x_bt), (y, y_bt)))
                       free_vars_bts
                       g)
                   free_vars_bts
                   g)
            | Predicate _ -> g)
          g
          cs
      in
      Pp.debug
        1
        (lazy
          (let buf = Buffer.create 50 in
           Dot.fprint_graph (Format.formatter_of_buffer buf) g;
           Pp.string (Buffer.contents buf)));
      g


    let pp_weak_topological (ho : G.vertex Graph.WeakTopological.t) : Pp.document =
      let open Pp in
      let rec aux (elem : G.vertex Graph.WeakTopological.element) : document =
        match elem with
        | Vertex (x, bt) -> Sym.pp x ^^ space ^^ colon ^^ space ^^ BT.pp bt
        | Component ((x, bt), elems) ->
          parens
            ((Sym.pp x ^^ space ^^ colon ^^ space ^^ BT.pp bt)
             ^^ semi
             ^^ break 1
             ^^ Graph.WeakTopological.fold_left
                  (fun acc elem -> acc ^^ space ^^ aux elem)
                  empty
                  elems)
      in
      surround_separate
        2
        1
        (lbracket ^^ rbracket)
        lbracket
        (semi ^^ break 1)
        rbracket
        (Graph.WeakTopological.fold_left (fun acc elem -> acc @ [ aux elem ]) [] ho)


    (** Choose an optimal linear ordering from a hierarchical ordering
        FIXME: Currently just selects arbitrary one, maybe wait on Leo's work?
        **)
    let choose_ordering (g : G.t) : G.vertex list =
      let module Topological = Graph.Topological.Make (G) in
      List.rev (Topological.fold List.cons g [])


    let select (args : (Sym.t * BT.t) list) (cs : constraints) : G.vertex list =
      construct_graph args cs |> choose_ordering
  end

  let rec get_dummy_context (cs_ctx : Constraints.t) : gen_context =
    match cs_ctx with
    | (name, CD { fn = _; name = _; iargs; oarg; def = _ }) :: cs_ctx' ->
      ( name,
        { name;
          iargs = [];
          oargs =
            (let l = List.map (fun (_, bt) -> GT.of_bt bt) iargs in
             match oarg with Some oarg -> GT.of_bt oarg :: l | None -> l);
          body = None
        } )
      :: get_dummy_context cs_ctx'
    | [] -> []


  let compile_gen_term
    (gtx : gen_context)
    ((x, bt) : Order.G.vertex)
    (cs : constraints)
    (g : gen)
    : gen
    =
    let resource_cs, logical_cs =
      List.partition (fun c -> match c with Logical _ -> false | _ -> true) cs
    in
    let lcs =
      List.map
        (fun c ->
          match c with Logical lc -> lc | _ -> failwith ("unreachable (" ^ __LOC__ ^ ")"))
        logical_cs
    in
    let g_assert g' = if List.is_empty lcs then g' else Assert (lcs, g') in
    match resource_cs with
    | _ :: _ :: _ ->
      Cerb_debug.error "todo: multiple resource constraints are not supported"
    | [ Ownership { pointer; x = x'; ty } ] ->
      let here = Cerb_location.other __FUNCTION__ in
      let bt' = BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type ty in
      let g_assign =
        Asgn
          ( (IT.sym_ (pointer, BT.Loc, here), GT.Loc (GT.of_sct ty)),
            IT.sym_ (x', bt', here),
            g )
      in
      Let ([ x ], arbitrary_ (GT.of_bt bt), g_assert g_assign)
    | [ Predicate { name; iargs; oarg } ] ->
      Let (List.map fst (oarg :: iargs), call_ gtx name [], g)
    | [] -> Let ([ x ], arbitrary_ (GT.of_bt bt), g_assert g)
    | [ Logical _ ] -> failwith ("unreachable (" ^ __LOC__ ^ ")")


  let get_constraint_to_elim (o : Order.G.vertex list) (xs : SymSet.t) (c : constraint_) =
    let relevant =
      match c with
      | Ownership { pointer = _; x; ty = _ } -> SymSet.mem x xs
      | Logical lc ->
        SymSet.subset
          (SymSet.inter (SymSet.of_list (List.map fst o)) (LC.free_vars lc))
          xs
      | Predicate { name = _; iargs; oarg } ->
        List.exists (fun (x', _) -> SymSet.mem x' xs) (oarg :: iargs)
    in
    if relevant then (
      Pp.debug
        1
        (lazy
          (let open Pp in
           string "Eliminating constraints: " ^^ Constraints.pp_constraint c));
      true)
    else
      false


  let compile_gen_terms
    (gtx : gen_context)
    (iargs : Order.G.vertex list)
    (cs : constraints)
    (oit : IT.t option)
    : gen
    =
    let rec aux (o : Order.G.vertex list) (cs : constraints) : gen =
      match o with
      | (x, bt) :: o' ->
        Pp.debug
          1
          (lazy
            (let open Pp in
             string "Compiling variable `" ^^ Sym.pp x ^^ string "`"));
        let predicate_cs, remaining_cs =
          List.partition
            (fun c ->
              match c with
              | Predicate _ -> get_constraint_to_elim o' (SymSet.singleton x) c
              | Ownership _ | Logical _ -> false)
            cs
        in
        let xs_generated =
          if List.is_empty predicate_cs then
            SymSet.singleton x
          else
            List.fold_left
              (fun acc c ->
                match c with
                | Predicate { name = _; iargs; oarg } ->
                  let more =
                    SymSet.diff (SymSet.of_list (List.map fst (oarg :: iargs))) acc
                  in
                  SymSet.iter
                    (fun x ->
                      Pp.debug
                        1
                        (lazy
                          (let open Pp in
                           string "Implicitly compiling variable `"
                           ^^ Sym.pp x
                           ^^ string "`")))
                    more;
                  SymSet.union more acc
                | Ownership _ | Logical _ -> failwith ("unreachable (" ^ __LOC__ ^ ")"))
              (SymSet.singleton x)
              predicate_cs
        in
        let o' = List.filter (fun (x, _) -> not (SymSet.mem x xs_generated)) o' in
        let primitive_cs, remaining_cs =
          List.partition
            (fun c ->
              match c with
              | Ownership _ | Logical _ -> get_constraint_to_elim o' xs_generated c
              | Predicate _ -> false)
            remaining_cs
        in
        compile_gen_term gtx (x, bt) (predicate_cs @ primitive_cs) (aux o' remaining_cs)
      | [] ->
        if List.length cs = 0 then (
          let here = Cerb_location.other __FUNCTION__ in
          let res = List.map (fun (x, bt) -> IT.sym_ (x, bt, here)) iargs in
          let res = match oit with Some it -> it :: res | None -> res in
          Return (IT.tuple_ res here))
        else
          failwith
            ("Constraints remaining: " ^ (cs |> Constraints.pp_constraints |> Pp.plain))
    in
    aux (Order.select iargs cs) cs


  let rec compile_clauses
    (gtx : gen_context)
    (iargs : (Sym.t * BT.t) list)
    (cls : clause list)
    : gen
    =
    match cls with
    | [ cl ] when IT.is_true cl.guard ->
      Pp.debug 1 (lazy (Pp.string "Compiling `else` clause"));
      compile_gen_terms gtx iargs cl.cs (Some cl.it)
    | cl :: cls' ->
      Pp.debug
        1
        (lazy
          (let open Pp in
           string "Compiling clause"
           ^^ space
           ^^ parens (string "guard: " ^^ IT.pp cl.guard)));
      let here = Locations.other __FUNCTION__ in
      let x_sym, it_x = IT.fresh BT.Bool here in
      Let
        ( [ x_sym ],
          arbitrary_ GT.Bool,
          ITE
            ( it_x,
              compile_gen_terms gtx iargs cl.cs (Some cl.it),
              compile_clauses gtx iargs cls' ) )
    | [] -> failwith ("unreachable (" ^ __LOC__ ^ ")")


  let compile_gen
    (gtx : gen_context)
    (CD { fn; name; def; iargs; oarg } : constraint_definition)
    : gen_def
    =
    Pp.debug
      1
      (lazy
        (let open Pp in
         string "Compiling generator for"
         ^^ space
         ^^ Sym.pp name
         ^^ space
         ^^ at
         ^^ space
         ^^ string fn));
    let g =
      match def with
      | Pred cls -> compile_clauses gtx iargs cls
      | Spec cs -> compile_gen_terms gtx iargs cs None
    in
    { name;
      iargs = [];
      oargs =
        (let l = List.map (fun (_, bt) -> GT.of_bt bt) iargs in
         match oarg with Some oarg -> GT.of_bt oarg :: l | None -> l);
      body = Some g
    }


  (** Compile from a constraint context [cs_ctx] into a generator context *)
  let compile (cs_ctx : Constraints.t) : gen_context =
    let dummy_gtx = get_dummy_context cs_ctx in
    List.map (fun (x, cd) -> (x, compile_gen dummy_gtx cd)) cs_ctx
end

let compile = Compile.compile

module Optimize = struct
  module BespokeGenerators = struct
    let rec equality_constraints (g : gen) : gen =
      let g =
        match g with
        | Let ([ x ], GT (gt, Arbitrary), Assert (lcs, g')) ->
          (* Find applicable constraints *)
          let lcs_eq, lcs_rest =
            List.partition
              (fun lc ->
                match lc with
                | LC.T (IT (Binop (EQ, IT (Sym x', _, _), _), _, _))
                | LC.T (IT (Binop (EQ, _, IT (Sym x', _, _)), _, _)) ->
                  Sym.equal x x'
                | _ -> false)
              lcs
          in
          (* The optimization itself *)
          let optimize (it : IT.t) (lcs' : LC.t list) =
            let lc_rest = if List.is_empty lcs' then lcs_rest else lcs' @ lcs_rest in
            let g' = if List.is_empty lc_rest then g' else Assert (lcs_rest, g') in
            Let ([ x ], GT (gt, Just it), g')
          in
          (match lcs_eq with
           | LC.T (IT (Binop (EQ, IT (Sym x', _, _), it), _, _)) :: lcs_eq'
             when Sym.equal x x' ->
             optimize it lcs_eq'
           | LC.T (IT (Binop (EQ, it, IT (Sym x', _, _)), _, _)) :: lcs_eq'
             when Sym.equal x x' ->
             optimize it lcs_eq'
           | _ :: _ -> failwith ("unreachable (" ^ __LOC__ ^ ")")
           | [] -> Let ([ x ], GT (gt, Arbitrary), Assert (lcs, g')))
        | _ -> g
      in
      map_gen equality_constraints g


    let run (g : gen) : gen = g |> equality_constraints
  end

  let optimize_gen (g : gen) : gen = g |> BespokeGenerators.run

  let optimize_gen_def ({ name; iargs; oargs; body } : gen_def) : gen_def =
    { name; iargs; oargs; body = Option.map optimize_gen body }


  let optimize (gtx : gen_context) : gen_context = List.map_snd optimize_gen_def gtx
end

let optimize = Optimize.optimize
