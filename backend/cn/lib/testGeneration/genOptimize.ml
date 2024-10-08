module CF = Cerb_frontend
module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module GT = GenTerms
module GD = GenDefinitions
module GA = GenAnalysis
module SymSet = Set.Make (Sym)
module SymMap = Map.Make (Sym)
module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

type opt_pass =
  { name : string;
    transform : GT.t -> GT.t
  }

(** This pass performs various inlinings *)
module Inline = struct
  (** This pass inlines generators that just return a constant or symbol *)
  module Returns = struct
    let name = "inline_return"

    let transform (gt : GT.t) : GT.t =
      let aux (gt : GT.t) : GT.t =
        let (GT (gt_, _, here)) = gt in
        match gt_ with
        | Let (_, (x, GT (Return it, _, loc_ret)), gt') ->
          let (IT (t_, _, _)) = it in
          (match t_ with
           (* Terms to inline *)
           | Const _ | Sym _ -> GT.subst (IT.make_subst [ (x, it) ]) gt'
           (* Otherwise, at least avoid pointless backtracking *)
           | _ -> GT.let_ (0, (x, GT.return_ it loc_ret), gt') here)
        | _ -> gt
      in
      GT.map_gen_pre aux gt


    let pass = { name; transform }
  end

  (* This pass inlines *)
  module SingleUse = struct
    module IndexTerms = struct
      let name = "inline_single_use_pure"

      let transform (_gt : GT.t) : GT.t = failwith __LOC__
      (* let aux (gt : GT.t) : GT.t =
         let (GT (gt_, _, _)) = gt in
         match gt_ with
         | Let (_, x, GT (Return it, _, _), gt') ->
         let single_uses = GA.get_single_uses ~pure:true gt' in
         if SymSet.mem x single_uses then
         GT.subst (IT.make_subst [ (x, it) ]) gt'
         else
         gt
         | _ -> gt
         in
         GT.map_gen_pre aux gt *)

      let pass = { name; transform }
    end

    module GenTerms = struct
      let name = "inline_single_use_gen"

      let subst (x : Sym.t) (gt_repl : GT.t) (gt : GT.t) : GT.t =
        let aux (gt : GT.t) : GT.t =
          let (GT (gt_, _, _)) = gt in
          match gt_ with
          | Return (IT (Sym y, _, _)) when Sym.equal x y -> gt_repl
          | _ -> gt
        in
        GT.map_gen_post aux gt


      let of_symset (s : SymSet.t) : bool SymMap.t =
        s |> SymSet.to_seq |> Seq.map (fun x -> (x, false)) |> SymMap.of_seq


      let union = SymMap.union (fun _ a b -> Some (not (a || b)))

      let rec transform_aux (gt : GT.t) : GT.t * bool SymMap.t =
        let (GT (gt_, _, loc)) = gt in
        match gt_ with
        | Arbitrary | Uniform _ -> (gt, SymMap.empty)
        | Pick wgts ->
          let wgts, only_ret =
            wgts
            |> List.map_snd transform_aux
            |> List.map (fun (a, (b, c)) -> ((a, b), c))
            |> List.split
          in
          (GT.pick_ wgts loc, List.fold_left union SymMap.empty only_ret)
        | Alloc it -> (gt, it |> IT.free_vars |> of_symset)
        | Call (_fsym, xits) ->
          ( gt,
            xits
            |> List.map snd
            |> List.map IT.free_vars
            |> List.map of_symset
            |> List.fold_left union SymMap.empty )
        | Asgn ((it_addr, sct), it_val, gt') ->
          let only_ret =
            [ it_addr; it_val ]
            |> List.map IT.free_vars
            |> List.map of_symset
            |> List.fold_left union SymMap.empty
          in
          let gt', only_ret' = transform_aux gt' in
          (GT.asgn_ ((it_addr, sct), it_val, gt') loc, union only_ret only_ret')
        | Let (backtracks, (x, gt_inner), gt') ->
          let gt', only_ret = transform_aux gt' in
          let only_ret = SymMap.remove x only_ret in
          if Option.equal Bool.equal (SymMap.find_opt x only_ret) (Some true) then
            (subst x gt_inner gt', only_ret)
          else (
            let gt_inner, only_ret' = transform_aux gt_inner in
            (GT.let_ (backtracks, (x, gt_inner), gt') loc, union only_ret only_ret'))
        | Return it ->
          ( gt,
            (match IT.is_sym it with
             | Some (x, _bt) -> SymMap.singleton x true
             | None -> it |> IT.free_vars |> of_symset) )
        | Assert (lc, gt') ->
          let only_ret = lc |> LC.free_vars |> of_symset in
          let gt', only_ret' = transform_aux gt' in
          (GT.assert_ (lc, gt') loc, union only_ret only_ret')
        | ITE (it_if, gt_then, gt_else) ->
          let only_ret = it_if |> IT.free_vars |> of_symset in
          let gt_then, only_ret' = transform_aux gt_then in
          let gt_else, only_ret'' = transform_aux gt_else in
          ( GT.ite_ (it_if, gt_then, gt_else) loc,
            [ only_ret; only_ret'; only_ret'' ] |> List.fold_left union SymMap.empty )
        | Map ((i, i_bt, it_perm), gt_inner) ->
          let only_ret = it_perm |> IT.free_vars |> SymSet.remove i |> of_symset in
          let gt_inner, only_ret' = transform_aux gt_inner in
          let only_ret' = only_ret' |> SymMap.remove i |> SymMap.map (fun _ -> false) in
          (GT.map_ ((i, i_bt, it_perm), gt_inner) loc, union only_ret only_ret')


      let transform (gt : GT.t) : GT.t = fst (transform_aux gt)

      let pass = { name; transform }
    end

    let passes = [ (* IndexTerms.pass; *) GenTerms.pass ]
  end

  let passes = Returns.pass :: SingleUse.passes
end

(** This pass breaks down constraints, so that
    other passes can optimize more *)
module SplitConstraints = struct
  let name = "split_constraints"

  let rec cnf_ (e : BT.t IT.term) : BT.t IT.term =
    match e with
    (* Double negation elimination *)
    | Unop (Not, IT (Unop (Not, IT (e, _, _)), _, _)) -> e
    (* Flip inequalities *)
    | Unop (Not, IT (Binop (LT, e1, e2), _, _)) -> Binop (LE, e2, e1)
    | Unop (Not, IT (Binop (LE, e1, e2), _, _)) -> Binop (LT, e2, e1)
    (* De Morgan's Law *)
    | Unop (Not, IT (Binop (And, e1, e2), info, loc)) ->
      Binop (Or, IT (Unop (Not, cnf e1), info, loc), IT (Unop (Not, cnf e2), info, loc))
    | Unop (Not, IT (Binop (Or, e1, e2), info, loc)) ->
      Binop (And, IT (Unop (Not, cnf e1), info, loc), IT (Unop (Not, cnf e2), info, loc))
    (* Distribute disjunction *)
    | Binop (Or, e1, IT (Binop (And, e2, e3), info, loc))
    | Binop (Or, IT (Binop (And, e2, e3), info, loc), e1) ->
      Binop (And, IT (Binop (Or, e1, e2), info, loc), IT (Binop (Or, e1, e3), info, loc))
    | _ -> e


  and cnf (e : IT.t) : IT.t =
    let (IT (e, info, loc)) = e in
    IT (cnf_ e, info, loc)


  let listify_constraints (it : IT.t) : IT.t list =
    let rec loop (c : IT.t) : IT.t list =
      match c with IT (Binop (And, e1, e2), _, _) -> loop e1 @ loop e2 | _ -> [ c ]
    in
    loop it


  let transform (gt : GT.t) : GT.t =
    let aux (gt : GT.t) : GT.t =
      let (GT (gt_, _bt, loc)) = gt in
      match gt_ with
      | Assert (T it, gt') ->
        it
        |> cnf
        |> listify_constraints
        |> List.fold_left (fun gt_rest it' -> GT.assert_ (LC.T it', gt_rest) loc) gt'
      | _ -> gt
    in
    GT.map_gen_pre aux gt


  let pass = { name; transform }
end

(** This pass looks at the relationships of the
    variables and reorders their generation *)
module Reordering = struct
  let name = "reordering"

  module Stmt = struct
    type t =
      | Asgn of (IT.t * Sctypes.t) * IT.t
      | Let of (int * (Sym.t * GT.t))
      | Assert of LC.t
    [@@deriving eq, ord]

    let hash = Hashtbl.hash
  end

  let stmts_of_gt (gt : GT.t) : Stmt.t list * GT.t =
    let open Stmt in
    let rec aux (gt : GT.t) : Stmt.t list * GT.t =
      let (GT (gt_, _, _)) = gt in
      match gt_ with
      | Arbitrary | Uniform _ | Pick _ | Alloc _ | Call _ | Return _ | ITE _ | Map _ ->
        ([], gt)
      | Asgn ((it_addr, sct), it_val, gt_rest) ->
        let stmts, gt_last = aux gt_rest in
        (Asgn ((it_addr, sct), it_val) :: stmts, gt_last)
      | Let (backtracks, (x, gt'), gt_rest) ->
        let stmts, gt_last = aux gt_rest in
        (Let (backtracks, (x, gt')) :: stmts, gt_last)
      | Assert (lc, gt_rest) ->
        let stmts, gt_last = aux gt_rest in
        (Assert lc :: stmts, gt_last)
    in
    aux gt


  let gt_of_stmts (stmts : Stmt.t list) (gt_end : GT.t) : GT.t =
    List.fold_right
      (fun (stmt : Stmt.t) gt_rest ->
        let loc = Locations.other __LOC__ in
        match stmt with
        | Asgn ((it_addr, sct), it_val) -> GT.asgn_ ((it_addr, sct), it_val, gt_rest) loc
        | Let (backtracks, (x, gt')) -> GT.let_ (backtracks, (x, gt'), gt_rest) loc
        | Assert lc -> GT.assert_ (lc, gt_rest) loc)
      stmts
      gt_end


  module SymGraph = Graph.Persistent.Digraph.Concrete (Sym)

  module Dot = Graph.Graphviz.Dot (struct
      include SymGraph

      let edge_attributes _ = []

      let default_edge_attributes _ = []

      let get_subgraph _ = None

      let vertex_name = Sym.pp_string

      let vertex_attributes _ = []

      let default_vertex_attributes _ = []

      let graph_attributes _ = []
    end)

  let get_pure_vars (stmts : Stmt.t list) : SymSet.t =
    stmts
    |> List.filter_map (fun (stmt : Stmt.t) ->
      match stmt with Let (_, (x, gt)) when GA.is_pure gt -> Some x | _ -> None)
    |> SymSet.of_list


  let get_variable_ordering (iargs : SymSet.t) (stmts : Stmt.t list) : SymGraph.t =
    let pure_vars = SymSet.inter (get_pure_vars stmts) in
    (* The hardest ordering constraint, so we do it first *)
    let rec order_lets (stmts : Stmt.t list) : SymGraph.t * Stmt.t list =
      match stmts with
      | Let (_, (x, gt')) :: stmts' ->
        let g, stmts' = order_lets stmts' in
        let inputs = GT.free_vars gt' in
        (SymSet.fold (fun inp g -> SymGraph.add_edge_e g (inp, x)) inputs g, stmts')
      | stmt :: stmts' ->
        let g, stmts' = order_lets stmts' in
        (g, stmt :: stmts')
      | [] -> (SymGraph.empty, [])
    in
    (* Purely heuristic *)
    let rec order_rest ((g, stmts) : SymGraph.t * Stmt.t list) : SymGraph.t =
      match stmts with
      | Asgn ((it_addr, _sct), it_val) :: stmts' ->
        let g' = order_rest (g, stmts') in
        let pointer_sym, it_offset = GA.get_addr_offset it_addr in
        (* We prefer to have correct values and
           only backtrack on the allocation, so
           we want the address later *)
        if SymSet.mem pointer_sym iargs then
          g'
        else (
          let before = SymSet.union (IT.free_vars it_offset) (IT.free_vars it_val) in
          SymSet.fold (fun x g'' -> SymGraph.add_edge_e g'' (x, pointer_sym)) before g')
      | Assert lc :: stmts' ->
        let g' = order_rest (g, stmts') in
        (match LC.is_equality lc with
         | Some ((it_x, it_y), true) ->
           (match (IT.is_sym it_x, IT.is_sym it_y) with
            | Some (x_sym, _x_bt), None | None, Some (x_sym, _x_bt) ->
              if SymSet.mem x_sym iargs then
                g'
              else (
                let before = IT.free_vars it_y in
                SymSet.fold (fun z g'' -> SymGraph.add_edge_e g'' (z, x_sym)) before g')
            | _, _ -> g')
         | _ ->
           let vars = LC.free_vars lc in
           let before = pure_vars vars in
           if SymSet.is_empty before then
             g'
           else (
             let after = SymSet.diff vars before in
             SymSet.fold
               (fun x ->
                 SymSet.fold (fun y g''' -> SymGraph.add_edge_e g''' (x, y)) after)
               before
               g'))
      | Let _ :: _ -> failwith ("unreachable @ " ^ __LOC__)
      | [] -> g
    in
    let remove_loops (g : SymGraph.t) : SymGraph.t =
      let g' =
        SymGraph.fold_vertex (fun x g'' -> SymGraph.add_vertex g'' x) g SymGraph.empty
      in
      SymGraph.fold_edges
        (fun x1 x2 g'' -> if Sym.equal x1 x2 then g'' else SymGraph.add_edge g'' x1 x2)
        g
        g'
    in
    stmts |> order_lets |> order_rest |> remove_loops


  (** FIXME: Make fewer choices and build a graph to decide the ordering? *)
  let get_statement_ordering (iargs : SymSet.t) (stmts : Stmt.t list) : Stmt.t list =
    let rec loop
      ((vars, res, g, stmts) : SymSet.t * Stmt.t list * SymGraph.t * Stmt.t list)
      : SymSet.t * Stmt.t list
      =
      if List.is_empty stmts then
        (vars, res)
      else (
        let g = SymSet.fold (fun x g' -> SymGraph.remove_vertex g' x) vars g in
        let res', stmts =
          List.partition
            (fun (stmt : Stmt.t) ->
              match stmt with
              | Asgn ((it_addr, _sct), it_val) ->
                SymSet.subset (IT.free_vars_list [ it_addr; it_val ]) vars
              | Assert lc -> SymSet.subset (LC.free_vars lc) vars
              | _ -> false)
            stmts
        in
        let res = res @ res' in
        let var =
          SymGraph.fold_vertex
            (fun x var ->
              if Option.is_none var && SymGraph.in_degree g x = 0 then Some x else var)
            g
            None
        in
        let vars, res, stmts =
          match var with
          (* If only let's without dependencies left... *)
          | None -> (vars, res @ stmts, [])
          | Some var ->
            let res', stmts =
              List.partition
                (fun (stmt : Stmt.t) ->
                  match stmt with
                  | Let (_backtracks, (x, _gt)) -> Sym.equal x var
                  | _ -> false)
                stmts
            in
            (SymSet.add var vars, res @ res', stmts)
        in
        loop (vars, res, g, stmts))
    in
    let g = get_variable_ordering iargs stmts in
    (* print_string
       (Pp.plain
       (* Pp.debug
       1
       (lazy *)
       (let buf = Buffer.create 50 in
       Dot.fprint_graph (Format.formatter_of_buffer buf) g;
       Pp.string (Buffer.contents buf))
       (* ); *));
       print_newline (); *)
    let _, res = loop (iargs, [], g, stmts) in
    res


  let reorder (iargs : SymSet.t) (gt : GT.t) : GT.t =
    let stmts, gt_last = stmts_of_gt gt in
    let stmts = get_statement_ordering iargs stmts in
    gt_of_stmts stmts gt_last


  let transform (gd : GD.t) : GD.t =
    let rec aux (iargs : SymSet.t) (gt : GT.t) : GT.t =
      let rec loop (gt : GT.t) : GT.t =
        let (GT (gt_, _bt, loc)) = gt in
        match gt_ with
        | Arbitrary | Uniform _ | Alloc _ | Call _ | Return _ -> gt
        | Pick wgts -> GT.pick_ (List.map_snd (aux iargs) wgts) loc
        | Asgn ((it_addr, sct), it_val, gt_rest) ->
          GT.asgn_ ((it_addr, sct), it_val, loop gt_rest) loc
        | Let (backtracks, (x, gt'), gt_rest) ->
          GT.let_ (backtracks, (x, (aux iargs) gt'), loop gt_rest) loc
        | Assert (lc, gt_rest) -> GT.assert_ (lc, loop gt_rest) loc
        | ITE (it_if, gt_then, gt_else) ->
          GT.ite_ (it_if, aux iargs gt_then, aux iargs gt_else) loc
        | Map ((i_sym, i_bt, it_perm), gt_inner) ->
          GT.map_ ((i_sym, i_bt, it_perm), aux (SymSet.add i_sym iargs) gt_inner) loc
      in
      (* print_string (Pp.plain (GT.pp gt));
         print_newline (); *)
      gt |> reorder iargs |> loop
    in
    let iargs = gd.iargs |> List.map fst |> SymSet.of_list in
    { gd with body = Some (aux iargs (Option.get gd.body)) }
end

(** This pass ... *)
module Specialization = struct end

(** This pass ... *)
module InferAllocationSize = struct
  let name = "infer_alloc_size"

  let infer_size (x : Sym.t) (gt : GT.t) : IT.t option =
    let merge loc oa ob =
      match (oa, ob) with
      | Some a, Some b -> Some (IT.max_ (a, b) loc)
      | Some a, _ | _, Some a -> Some a
      | None, None -> None
    in
    let rec aux (gt : GT.t) : IT.t option =
      let (GT (gt_, _, _)) = gt in
      match gt_ with
      | Arbitrary | Uniform _ | Alloc _ | Call _ | Return _ -> None
      | Pick wgts ->
        wgts
        |> List.map snd
        |> List.map aux
        |> List.fold_left (merge (Locations.other __LOC__)) None
      | Asgn ((it_addr, sct), _it_val, gt') ->
        let oit_size =
          let (IT (_, _, loc)) = it_addr in
          let open Option in
          let@ psym, it_offset = GA.get_addr_offset_opt it_addr in
          if Sym.equal x psym then
            return (IT.add_ (it_offset, IT.sizeOf_ sct loc) loc)
          else
            None
        in
        (merge (Locations.other __LOC__)) oit_size (aux gt')
      | Let (_, (y, gt_inner), gt') ->
        let oit = aux gt_inner in
        let gt' = if Sym.equal x y then snd (GT.alpha_rename_gen x gt') else gt' in
        (merge (Locations.other __LOC__)) oit (aux gt')
      | Assert (_, gt') -> aux gt'
      | ITE (_it_if, gt_then, gt_else) ->
        (merge (Locations.other __LOC__)) (aux gt_then) (aux gt_else)
      | Map ((i_sym, i_bt, it_perm), gt_inner) ->
        let j_sym, gt_inner =
          if Sym.equal x i_sym then GT.alpha_rename_gen x gt_inner else (i_sym, gt_inner)
        in
        let open Option in
        let@ it = aux gt_inner in
        if SymSet.mem j_sym (IT.free_vars it) then (
          let _, it_max = GA.get_bounds (i_sym, i_bt) it_perm in
          return (IT.subst (IT.make_subst [ (j_sym, it_max) ]) it))
        else
          return it
    in
    aux gt


  let transform (gt : GT.t) : GT.t =
    let aux (gt : GT.t) : GT.t =
      let (GT (gt_, _bt, loc_let)) = gt in
      match gt_ with
      | Let (backtracks, (x, GT (Alloc it_size, _bt, loc_alloc)), gt_rest) ->
        (match infer_size x gt_rest with
         | Some it_size' ->
           let loc = Locations.other __LOC__ in
           GT.let_
             ( backtracks,
               (x, GT.alloc_ (IT.max_ (it_size, it_size') loc) loc_alloc),
               gt_rest )
             loc_let
         | None -> gt)
      | _ -> gt
    in
    GT.map_gen_pre aux gt
end

(** This pass ... *)
module LazyPruning = struct end

(** This pass ... *)
module Fusion = struct
  (** This pass ... *)
  module Recursive = struct end

  (** This pass ... *)
  module Iterative = struct end
end

(** This pass uses [Simplify] to rewrite [IndexTerms.t] *)
module TermSimplification = struct
  let name = "simplify_term"

  let transform (prog5 : unit Mucore.mu_file) (gt : GT.t) : GT.t =
    let globals =
      { Global.empty with
        logical_functions = SymMap.of_seq (List.to_seq prog5.mu_logical_predicates)
      }
    in
    let simp_it (it : IT.t) : IT.t =
      Simplify.IndexTerms.simp ~inline_functions:true (Simplify.default globals) it
    in
    let simp_lc (lc : LC.t) : LC.t =
      Simplify.LogicalConstraints.simp
        ~inline_functions:true
        (Simplify.default globals)
        lc
    in
    let aux (gt : GT.t) : GT.t =
      let (GT (gt_, bt, loc)) = gt in
      match gt_ with
      | Alloc it -> GT.alloc_ (simp_it it) loc
      | Call (fsym, iargs) -> GT.call_ (fsym, List.map_snd simp_it iargs) bt loc
      | Asgn ((it_addr, sct), it_val, gt') ->
        GT.asgn_ ((simp_it it_addr, sct), simp_it it_val, gt') loc
      | Return it -> GT.return_ (simp_it it) loc
      | Assert (lc, gt') -> GT.assert_ (simp_lc lc, gt') loc
      | Map ((i, i_bt, it_perm), gt') -> GT.map_ ((i, i_bt, simp_it it_perm), gt') loc
      | _ -> gt
    in
    GT.map_gen_pre aux gt


  let pass (prog5 : unit Mucore.mu_file) = { name; transform = transform prog5 }
end

(** This pass ... *)
module ConstraintPropagation = struct end

(** This pass ... *)
module DraGen = struct end

(** This pass removes unused variables *)
module RemoveUnused = struct
  let name = "remove_unused"

  let transform (gt : GT.t) : GT.t =
    let aux (gt : GT.t) : GT.t =
      let (GT (gt_, _, _)) = gt in
      match gt_ with
      | Let (_, (x, gt1), gt2)
        when GA.is_pure gt1 && not (SymSet.mem x (GT.free_vars gt2)) ->
        gt2
      | _ -> gt
    in
    GT.map_gen_post aux gt


  let passes = [ { name; transform } ]
end

let all_passes (prog5 : unit Mucore.mu_file) =
  Inline.passes
  @ RemoveUnused.passes
  @ [ TermSimplification.pass prog5; SplitConstraints.pass ]


let optimize_gen (prog5 : unit Mucore.mu_file) (passes : StringSet.t) (gt : GT.t) : GT.t =
  let passes =
    all_passes prog5
    |> List.filter_map (fun { name; transform } ->
      if StringSet.mem name passes then Some transform else None)
  in
  let opt (gt : GT.t) : GT.t = List.fold_left (fun gt pass -> pass gt) gt passes in
  let rec loop (fuel : int) (gt : GT.t) : GT.t =
    if fuel <= 0 then
      gt
    else (
      let old_gt = gt in
      let new_gt = opt gt in
      if GT.equal old_gt new_gt then new_gt else loop (fuel - 1) new_gt)
  in
  gt |> loop 5 |> InferAllocationSize.transform


let optimize_gen_def
  (prog5 : unit Mucore.mu_file)
  (passes : StringSet.t)
  ({ name; iargs; oargs; body } : GD.t)
  : GD.t
  =
  Reordering.transform
    { name; iargs; oargs; body = Option.map (optimize_gen prog5 passes) body }


let optimize
  (prog5 : unit Mucore.mu_file)
  ?(passes : StringSet.t option = None)
  (ctx : GD.context)
  : GD.context
  =
  let default = all_passes prog5 |> List.map (fun p -> p.name) |> StringSet.of_list in
  let passes = Option.value ~default passes in
  List.map_snd (List.map_snd (optimize_gen_def prog5 passes)) ctx
