module IT = IndexTerms
module BT = BaseTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module RP = ResourcePredicates
module GBT = GenBaseTypes
module GT = GenTerms
module GD = GenDefinitions
module SymSet = Set.Make (Sym)

type s = GD.context

type 'a t = s -> 'a * s

type 'a m = 'a t

let ( let@ ) (g : 'a m) (f : 'a -> 'b m) : 'b m =
  fun s ->
  let x, s' = g s in
  f x s'


let return (x : 'a) : 'a m = fun s -> (x, s)

let run (f : 'a m) = f []

let backtrack_num = 10

let generated_size = 100

let rec compile_it_lat
  (preds : Mucore.T.resource_predicates)
  (iargs : SymSet.t)
  (allocs : SymSet.t)
  (lat : IT.t LAT.t)
  : GT.t m
  =
  match lat with
  | Define ((x, it), (loc, _), lat') ->
    let@ gt' = compile_it_lat preds iargs allocs lat' in
    return (GT.let_ (backtrack_num, (x, GT.return_ it (IT.loc it)), gt') loc)
  | Resource ((x, (P { name = Owned (ct, _); pointer; iargs = _ }, bt)), (loc, _), lat')
    ->
    let p, gt_size =
      match pointer with
      | IT (Sym p, _, _) -> (p, IT.sizeOf_ ct loc)
      | IT (ArrayShift { base = IT (Sym p, _, loc'); ct = ct'; index }, _, _) ->
        (p, IT.add_ (IT.sizeOf_ ct loc, IT.mul_ (index, IT.sizeOf_ ct' loc') loc') loc)
      | _ -> failwith ("unsupported : " ^ Pp.plain (IT.pp pointer))
    in
    let@ gt' = compile_it_lat preds iargs (SymSet.add p allocs) lat' in
    let gt_asgn = GT.asgn_ ((pointer, ct), IT.sym_ (x, bt, loc), gt') loc in
    let gt_val =
      if SymSet.mem x iargs then
        gt_asgn
      else
        GT.let_ (backtrack_num, (x, GT.uniform_ (bt, generated_size) loc), gt_asgn) loc
    in
    if SymSet.mem p iargs || SymSet.mem p allocs then
      return gt_val
    else (
      let gt_pointer = GT.alloc_ gt_size loc in
      return (GT.let_ (backtrack_num, (p, gt_pointer), gt_val) loc))
  | Resource
      ((x, (P { name = PName fsym; pointer; iargs = args_its' }, bt)), (loc, _), lat') ->
    let@ gt' = compile_it_lat preds iargs allocs lat' in
    let pred = List.assoc Sym.equal fsym preds in
    let arg_syms = pred.pointer :: fst (List.split pred.iargs) in
    let arg_its = pointer :: args_its' in
    let args = List.combine arg_syms arg_its in
    let gt_call = GT.call_ (fsym, args) bt loc in
    let gt_let = GT.let_ (backtrack_num, (x, gt_call), gt') loc in
    let desired_iargs = List.map fst args in
    let gd : GD.t =
      { name = fsym;
        iargs =
          (pred.pointer, BT.Loc) :: pred.iargs
          |> List.filter (fun (x, _) -> List.mem Sym.equal x desired_iargs)
          |> List.map (fun (x, bt) -> (x, GBT.of_bt bt));
        oargs =
          pred.oarg_bt
          :: (pred.iargs
              |> List.filter (fun (x, _) -> not (List.mem Sym.equal x desired_iargs))
              |> List.map snd)
          |> List.map GBT.of_bt;
        body = None
      }
    in
    fun s -> (gt_let, GD.add_context gd s)
  | Constraint (lc, (loc, _), lat') ->
    let@ gt' = compile_it_lat preds iargs allocs lat' in
    return (GT.assert_ ([ lc ], gt') loc)
  | I it -> return (GT.return_ it (IT.loc it))
  | _ -> failwith __LOC__


let rec compile_clauses
  (preds : Mucore.T.resource_predicates)
  (iargs : SymSet.t)
  (cls : RP.clause list)
  : GT.t m
  =
  match cls with
  | [ cl ] ->
    assert (IT.is_true cl.guard);
    compile_it_lat preds iargs SymSet.empty cl.packing_ft
  | cl :: cls' ->
    (* let here = Locations.other __FUNCTION__ in *)
    let it_if = cl.guard in
    (* Add guard as an assertion at the top of the body *)
    (* let lat = LAT.mConstraint (T it_if, (here, None)) cl.packing_ft in *)
    let@ gt_then = compile_it_lat preds iargs SymSet.empty cl.packing_ft in
    let@ gt_else = compile_clauses preds iargs cls' in
    return (GT.ite_ (it_if, gt_then, gt_else) cl.loc)
  | [] -> failwith "unreachable"


let compile_pred
  (preds : Mucore.T.resource_predicates)
  ({ name; iargs; oargs; body } : GD.t)
  : unit m
  =
  assert (Option.is_none body);
  let pred = List.assoc Sym.equal name preds in
  let@ gt =
    compile_clauses preds (SymSet.of_list (List.map fst iargs)) (Option.get pred.clauses)
  in
  let gd : GD.t = { name; iargs; oargs; body = Some gt } in
  fun s -> ((), GD.add_context gd s)


let compile_spec (preds : Mucore.T.resource_predicates) (name : Sym.t) (at : 'a AT.t)
  : unit m
  =
  let rec aux (at : 'a AT.t) =
    match at with
    | Computational ((x, bt), (loc, _), at') ->
      let acc, lat = aux at' in
      ((x, (x, bt, loc)) :: acc, lat)
    | L lat -> ([], lat)
  in
  let args, lat = aux at in
  let here = Locations.other __FUNCTION__ in
  let it_ret = IT.tuple_ (args |> List.map snd |> List.map IT.sym_) here in
  let iargs = SymSet.of_list (List.map fst args) in
  let@ gt = compile_it_lat preds iargs SymSet.empty (LAT.map (fun _ -> it_ret) lat) in
  let gd : GD.t =
    { name;
      iargs = [];
      oargs = args |> List.map (fun (_, (_, bt, _)) -> bt) |> List.map GBT.of_bt;
      body = Some gt
    }
  in
  fun s -> ((), GD.add_context gd s)


let compile (prog5 : unit Mucore.mu_file) : GD.context =
  let preds = prog5.mu_resource_predicates in
  let context_specs =
    prog5
    |> Core_to_mucore.collect_instrumentation
    |> fst
    |> List.filter (fun (inst : Core_to_mucore.instrumentation) ->
      Option.is_some inst.internal)
    |> List.map (fun (inst : Core_to_mucore.instrumentation) ->
      compile_spec preds inst.fn (Option.get inst.internal))
    |> List.fold_left
         (fun ctx f ->
           let (), ctx' = f ctx in
           ctx')
         GD.empty_context
  in
  let context_preds (ctx : GD.context) : GD.context =
    List.fold_left
      (fun ctx' (_, iargs_defs) ->
        List.fold_left
          (fun ctx'' ((_, gd) : _ * GD.t) ->
            if Option.is_some gd.body then
              ctx''
            else (
              let (), ctx''' = compile_pred preds gd ctx'' in
              ctx'''))
          ctx'
          iargs_defs)
      ctx
      ctx
  in
  let rec loop (ctx : GD.context) : GD.context =
    let old_ctx = ctx in
    let new_ctx = context_preds ctx in
    if GD.equal_context old_ctx new_ctx then ctx else loop new_ctx
  in
  loop context_specs
