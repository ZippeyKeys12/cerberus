module GT = GenTypes
module IT = IndexTerms
module LC = LogicalConstraints
open Constraints
open Utils
module CF = Cerb_frontend

type gen_term_ =
  | Arbitrary
  | Just of IT.t
  | Filter of gen_term * (Sym.t * LC.t list)
  | Map of gen_term * (Sym.t * IT.t)
  | Alloc of gen_term
  | Call of Sym.t * gen_term list

and gen_term = GT of GT.base_type * gen_term_

let rec pp_gen_term (gt : gen_term) : Pp.document =
  let open Pp in
  match gt with
  | GT (tys, Arbitrary) -> string "arbitrary<" ^^ GT.pp_base_type tys ^^ string ">()"
  | GT (tys, Just it) ->
    string "just<" ^^ GT.pp_base_type tys ^^ string ">(" ^^ IT.pp it ^^ string ")"
  | GT (tys, Filter (gt', (x, lc))) ->
    string "filter<"
    ^^ GT.pp_base_type tys
    ^^ string ">("
    ^^ pp_gen_term gt'
    ^^ string ", |"
    ^^ string (codify_sym x)
    ^^ string "|"
    ^^ nest 2 (break 1 ^^ separate_map (comma ^^ break 1) LC.pp lc)
    ^^ string ")"
  | GT (tys, Map (gt', (x, it))) ->
    string "map<"
    ^^ GT.pp_base_type tys
    ^^ string ">("
    ^^ pp_gen_term gt'
    ^^ string ","
    ^^ break 1
    ^^ enclose bar bar (string (codify_sym x))
    ^^ nest 2 (break 1 ^^ IT.pp it)
    ^^ string ")"
  | GT (tys, Alloc gt') ->
    string "alloc<"
    ^^ GT.pp_base_type tys
    ^^ string ">("
    ^^ space
    ^^ pp_gen_term gt'
    ^^ space
    ^^ rparen
  | GT (tys, Call (fsym, gts)) ->
    string (codify_sym fsym)
    ^^ string "<"
    ^^ GT.pp_base_type tys
    ^^ string ">"
    ^^ parens (nest 2 (separate_map (comma ^^ break 1) pp_gen_term gts))


type gen =
  | Asgn of IT.t * IT.t * gen
  | Let of Sym.t list * gen_term * gen
  | Return of IT.t
  | Assert of LC.t list * gen
  | ITE of IT.t * gen * gen

let rec pp_gen (g : gen) : Pp.document =
  let open Pp in
  match g with
  | Asgn (it_addr, it_val, g') ->
    IT.pp it_addr
    ^^ space
    ^^ string ":="
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
     ^^ string (codify_sym gd.name)
     ^^ parens
          (separate_map
             (comma ^^ space)
             (fun (x, ty) -> GT.pp_base_type ty ^^ space ^^ Sym.pp x)
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

(** Generate values for [x] using [gt], such that [lcs] are all true. *)
let filter_ (gt : gen_term) (x : Sym.t) (lcs : logical_constraints) : gen_term =
  match lcs with
  | _ :: _ ->
    let (GT (tys, _)) = gt in
    GT (tys, Filter (gt, (x, lcs)))
  | [] -> gt


(** Generate values for [x] using [gt], and apply [it_f] of type [ty_f]. *)
let map_ (gt : gen_term) (x : Sym.t) (it_f : IT.t) (ty_f : GT.base_type) : gen_term =
  GT (ty_f, Map (gt, (x, it_f)))


(** Allocate memory containing the result of [gt] and return its address *)
let alloc_ (gt : gen_term) : gen_term =
  let (GT (gbt, _)) = gt in
  GT (GT.Loc gbt, Alloc gt)


(** Call a defined generator named [fsym] with arguments [gts], from context [gtx] *)
let call_ (gtx : gen_context) (fsym : Sym.t) (gts : gen_term list) : gen_term =
  let { rets; _ } = List.assoc Sym.equal fsym gtx in
  GT (Tuple rets, Call (fsym, gts))


module Compile = struct
  module Order = struct
    module G = Graph.Persistent.Digraph.Concrete (Sym)
    module Components = Graph.Components.Undirected (G)
    module WeakTopological = Graph.WeakTopological.Make (G)
    module Choose = Graph.Oper.Choose (G)

    module Dot = Graph.Graphviz.Dot (struct
        include G (* use the graph module from above *)

        let edge_attributes _ = []

        let default_edge_attributes _ = []

        let get_subgraph _ = None

        let vertex_attributes _ = []

        let vertex_name v = Sym.pp_string v

        let default_vertex_attributes _ = []

        let graph_attributes _ = []
      end)

    (** Build a dependency graph of all the variables in [cs] *)
    let construct_graph ((_, lcs) : constraints) : G.t =
      let g =
        List.fold_left
          (fun g lc ->
            let free_vars = LC.free_vars lc |> LC.SymSet.to_seq |> List.of_seq in
            List.fold_left
              (fun g x -> List.fold_left (fun g y -> G.add_edge_e g (x, y)) g free_vars)
              g
              free_vars)
          G.empty
          lcs
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


    let pp_weak_topological (ho : Sym.t Graph.WeakTopological.t) : Pp.document =
      let open Pp in
      let rec aux (elem : Sym.t Graph.WeakTopological.element) : document =
        match elem with
        | Vertex x -> Sym.pp x
        | Component (x, elems) ->
          lbrace
          ^^ format [ Underline ] (Sym.pp_string x)
          ^^ Graph.WeakTopological.fold_left
               (fun acc elem -> acc ^^ space ^^ aux elem)
               empty
               elems
          ^^ rbrace
      in
      Graph.WeakTopological.fold_left (fun acc elem -> acc @ [ aux elem ]) [] ho
      |> separate space


    (** Get a hierarchical ordering for generation *)
    let weak_topo_graph (g : G.t) : Sym.t Graph.WeakTopological.t =
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
    let choose_ordering (ho : Sym.t Graph.WeakTopological.t) : Sym.t list =
      let rec aux (elem : Sym.t Graph.WeakTopological.element) : Sym.t list =
        match elem with
        | Vertex x -> [ x ]
        | Component (x, elems) ->
          x :: Graph.WeakTopological.fold_left (fun acc elem -> aux elem @ acc) [] elems
      in
      let o =
        List.rev (Graph.WeakTopological.fold_left (fun acc elem -> aux elem @ acc) [] ho)
      in
      Pp.debug
        1
        (lazy
          (let open Pp in
           lbracket ^^ separate_map (semi ^^ space) Sym.pp o ^^ rbracket));
      o


    let select (cs : constraints) : Sym.t list =
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


  let compile_gen_term (gtx : gen_context) (x : Sym.t) ((rcs, lcs) : constraints)
    : gen -> gen
    =
    if
      Option.is_some
        (List.find_opt
           (fun (_, ret) ->
             match RET.predicate_name ret with Owned _ -> false | PName _ -> true)
           rcs)
      && List.length rcs <> 1
    then
      Cerb_debug.error
        "todo: multiple resource constraints when involving a predicate are not supported";
    let rec aux (rcs : resource_constraints) (g : gen) : gen =
      match rcs with
      | (x', P { name = Owned (ty, _); pointer; iargs = _ }) :: rcs' ->
        let here = Cerb_location.other __FUNCTION__ in
        let g_asgn g =
          Asgn
            ( pointer,
              IT.sym_
                ( x',
                  BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type ty,
                  here ),
              g )
        in
        let g_assert g = Assert (lcs, g) in
        g_asgn (g_assert (aux rcs' g))
      | (x', P { name = PName fsym; pointer; iargs }) :: rcs' ->
        let g_let g =
          Let
            ( x'
              :: List.map
                   (fun it -> it |> IT.is_sym |> Option.get |> fst)
                   (pointer :: iargs),
              call_ gtx fsym [],
              g )
        in
        let g_assert g = Assert (lcs, g) in
        g_let (g_assert (aux rcs' g))
      | (_, Q _) :: _ -> Cerb_debug.error "todo: each not supported"
      | [] -> Let ([ x ], filter_ (arbitrary_ Unit) x lcs, g)
    in
    aux rcs


  let compile_gen_terms
    (gtx : gen_context)
    (iargs : (Sym.t * BT.t) list)
    (cs : constraints)
    (oit : IT.t option)
    : gen
    =
    let rec aux (o : Sym.t list) ((rcs, lcs) : constraints) : (gen -> gen) list =
      match o with
      | x :: o' ->
        let rcs, rcs' =
          List.partition
            (fun (x', ret) -> Sym.equal x x' || RET.SymSet.mem x (RET.free_vars ret))
            rcs
        in
        let xs_generated =
          if List.is_empty rcs then
            LC.SymSet.singleton x
          else
            List.fold_left
              (fun acc (x, ret) ->
                LC.SymSet.union acc (LC.SymSet.add x (RET.free_vars ret)))
              LC.SymSet.empty
              rcs
        in
        let o' = List.filter (fun x -> not (LC.SymSet.mem x xs_generated)) o' in
        let lcs, lcs' =
          List.partition
            (fun lc ->
              LC.SymSet.subset
                (LC.SymSet.filter (fun x -> List.mem Sym.equal x o') (LC.free_vars lc))
                xs_generated)
            lcs
        in
        compile_gen_term gtx x (rcs, lcs) :: aux o' (rcs', lcs')
      | [] ->
        if List.length rcs = 0 && List.length lcs = 0 then
          []
        else
          failwith
            ("Constraints remaining: "
             ^ ((rcs, lcs) |> Constraints.pp_constraints |> Pp.plain))
    in
    let o = Order.select cs in
    let xgts = aux o cs in
    let here = Cerb_location.other __FUNCTION__ in
    let g_ret =
      let res = List.map (fun (x, bt) -> IT.sym_ (x, bt, here)) iargs in
      let res = match oit with Some it -> it :: res | None -> res in
      Return (IT.tuple_ res here)
    in
    List.fold_right ( @@ ) xgts g_ret


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
    | [] -> failwith "unreachable"


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
