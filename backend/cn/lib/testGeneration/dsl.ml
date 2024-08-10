module GT = GenTypes
module IT = IndexTerms
module LC = LogicalConstraints
open Constraints
open Utils
module CF = Cerb_frontend

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
    Sym.pp_debug fsym
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
    ^^ separate_map (comma ^^ space) Sym.pp_debug xs
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


type gen_def =
  { name : Sym.t;
    args : (Sym.t * GT.base_type) list;
    rets : GT.base_type list;
    body : gen option
  }

let pp_gen_def (gd : gen_def) : Pp.document =
  let open Pp in
  group
    (string "generator"
     ^^ space
     ^^ parens (separate_map (comma ^^ space) GT.pp_base_type gd.rets)
     ^^ space
     ^^ Sym.pp_debug gd.name
     ^^ parens
          (separate_map
             (comma ^^ space)
             (fun (x, ty) -> GT.pp_base_type ty ^^ space ^^ Sym.pp_debug x)
             gd.args)
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
  let { rets; _ } = List.assoc Sym.equal fsym gtx in
  GT (Tuple rets, Call (fsym, its))


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
    module WeakTopological = Graph.WeakTopological.Make (G)
    module Choose = Graph.Oper.Choose (G)

    module Dot = Graph.Graphviz.Dot (struct
        include G (* use the graph module from above *)

        let edge_attributes _ = []

        let default_edge_attributes _ = []

        let get_subgraph _ = None

        let vertex_attributes _ = []

        let vertex_name (x, bt) =
          let doc =
            let open Pp in
            Sym.pp_debug x ^^ space ^^ colon ^^ space ^^ BT.pp bt
          in
          Pp.plain doc


        let default_vertex_attributes _ = []

        let graph_attributes _ = []
      end)

    (** Build a dependency graph of all the variables in [cs] *)
    let construct_graph (cs : constraints) : G.t =
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
                    List.fold_left
                      (fun g y -> G.add_edge_e g (y, (x, x_bt)))
                      g
                      (it |> IT.free_vars_bts |> IT.SymMap.bindings)
                  | _ -> failwith ("unreachable (" ^ __LOC__ ^ ")"))
               | _ ->
                 let free_vars_bts = LC.free_vars_bts lc |> LC.SymMap.bindings in
                 List.fold_left
                   (fun g x ->
                     List.fold_left (fun g y -> G.add_edge_e g (x, y)) g free_vars_bts)
                   g
                   free_vars_bts)
            | Predicate _ -> g)
          G.empty
          cs
      in
      Pp.debug
        1
        (lazy
          (let buf = Buffer.create 50 in
           Dot.fprint_graph (Format.formatter_of_buffer buf) g;
           let str = Buffer.contents buf in
           Buffer.clear buf;
           Pp.string str));
      g


    let pp_weak_topological (ho : G.vertex Graph.WeakTopological.t) : Pp.document =
      let open Pp in
      let rec aux (elem : G.vertex Graph.WeakTopological.element) : document =
        match elem with
        | Vertex (x, bt) -> Sym.pp_debug x ^^ space ^^ colon ^^ space ^^ BT.pp bt
        | Component ((x, bt), elems) ->
          lbrace
          ^^ parens (Sym.pp_debug x ^^ space ^^ colon ^^ space ^^ BT.pp bt)
          ^^ Graph.WeakTopological.fold_left
               (fun acc elem -> acc ^^ space ^^ aux elem)
               empty
               elems
          ^^ rbrace
      in
      Graph.WeakTopological.fold_left (fun acc elem -> acc @ [ aux elem ]) [] ho
      |> separate space


    (** Get a hierarchical ordering for generation *)
    let weak_topo_graph (g : G.t) : G.vertex Graph.WeakTopological.t =
      let root =
        G.fold_vertex
          (fun v ores ->
            match ores with None when G.in_degree g v = 0 -> Some v | _ -> None)
          g
          None
        |> Option.value ~default:(Choose.choose_vertex g)
      in
      let ho = WeakTopological.recursive_scc g root in
      Pp.debug 1 (lazy (pp_weak_topological ho));
      ho


    (** Choose an optimal linear ordering from a hierarchical ordering
        FIXME: Currently just selects arbitrary one, maybe wait on Leo's work?
        **)
    let choose_ordering (ho : G.vertex Graph.WeakTopological.t) : G.vertex list =
      let rec aux (elem : G.vertex Graph.WeakTopological.element) : G.vertex list =
        match elem with
        | Vertex x -> [ x ]
        | Component (x, elems) ->
          x :: Graph.WeakTopological.fold_left (fun acc elem -> aux elem @ acc) [] elems
      in
      List.rev (Graph.WeakTopological.fold_left (fun acc elem -> aux elem @ acc) [] ho)


    let select (cs : constraints) : G.vertex list =
      cs |> construct_graph |> weak_topo_graph |> choose_ordering
  end

  let rec get_dummy_context (cs_ctx : Constraints.t) : gen_context =
    match cs_ctx with
    | (name, CD { iargs; oarg; _ }) :: cs_ctx' ->
      ( name,
        { name;
          args = [];
          rets = GT.of_bt oarg :: List.map (fun (_, bt) -> GT.of_bt bt) iargs;
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
    let g = if List.is_empty lcs then g else Assert (lcs, g) in
    match resource_cs with
    | _ :: _ :: _ ->
      Cerb_debug.error "todo: multiple resource constraints are not supported"
    | [ Ownership { pointer; x = x'; ty } ] ->
      let here = Cerb_location.other __FUNCTION__ in
      let bt' = BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type ty in
      Asgn
        ( (IT.sym_ (pointer, BT.Loc, here), GT.Loc (GT.of_sct ty)),
          IT.sym_ (x', bt', here),
          g )
    | [ Predicate { name; iargs; x = x' } ] -> Let (x' :: iargs, call_ gtx name [], g)
    | [] -> Let ([ x ], arbitrary_ (GT.of_bt bt), g)
    | [ Logical _ ] -> failwith ("unreachable (" ^ __LOC__ ^ ")")


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
        let predicate_cs, remaining_cs =
          List.partition
            (fun c ->
              match c with
              | Predicate { iargs; _ } -> List.exists (fun x' -> Sym.equal x x') iargs
              | Ownership _ | Logical _ -> false)
            cs
        in
        let xs_generated =
          if List.is_empty predicate_cs then
            LC.SymSet.singleton x
          else
            List.fold_left
              (fun acc c ->
                match c with
                | Predicate { iargs; _ } -> LC.SymSet.union (LC.SymSet.of_list iargs) acc
                | Ownership _ | Logical _ -> failwith ("unreachable (" ^ __LOC__ ^ ")"))
              (LC.SymSet.singleton x)
              predicate_cs
        in
        let o' = List.filter (fun (x, _) -> not (LC.SymSet.mem x xs_generated)) o' in
        let primitive_cs, remaining_cs =
          List.partition
            (fun c ->
              match c with
              | Ownership { x; _ } -> LC.SymSet.mem x xs_generated
              | Logical lc ->
                LC.SymSet.subset
                  (LC.SymSet.filter
                     (fun x -> List.mem (fun _ (x', _) -> Sym.equal x x') x o')
                     (LC.free_vars lc))
                  xs_generated
              | Predicate _ -> failwith ("unreachable (" ^ __LOC__ ^ ")"))
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
    aux (Order.select cs) cs


  let rec compile_clauses
    (gtx : gen_context)
    (iargs : (Sym.t * BT.t) list)
    (cls : clause list)
    : gen
    =
    match cls with
    | [ cl ] when IT.is_true cl.guard -> compile_gen_terms gtx iargs cl.cs (Some cl.it)
    | cl :: cls' ->
      ITE
        ( cl.guard,
          compile_gen_terms gtx iargs cl.cs (Some cl.it),
          compile_clauses gtx iargs cls' )
    | [] -> failwith ("unreachable (" ^ __LOC__ ^ ")")


  let compile_gen
    (gtx : gen_context)
    (CD { fn = _; name; def; iargs; oarg } : constraint_definition)
    : gen_def
    =
    let g =
      match def with
      | Pred cls -> compile_clauses gtx iargs cls
      | Spec cs -> compile_gen_terms gtx iargs cs None
    in
    { name;
      args = [];
      rets = GT.of_bt oarg :: List.map (fun (_, bt) -> GT.of_bt bt) iargs;
      body = Some g
    }


  (** Compile from a constraint context [cs_ctx] into a generator context *)
  let compile (cs_ctx : Constraints.t) : gen_context =
    let dummy_gtx = get_dummy_context cs_ctx in
    List.map (fun (x, cd) -> (x, compile_gen dummy_gtx cd)) cs_ctx
end

let compile = Compile.compile

module Optimize = struct
  let optimize (gtx : gen_context) : gen_context = gtx
end

let optimize = Optimize.optimize
