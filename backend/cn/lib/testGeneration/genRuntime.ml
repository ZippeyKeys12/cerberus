module CF = Cerb_frontend
module A = CF.AilSyntax
module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module GT = GenTerms
module GD = GenDefinitions
module GBT = GenBaseTypes
module SymSet = Set.Make (Sym)

let bennet = Sym.fresh_named "bennet"

type term =
  | Uniform of
      { bt : BT.t;
        sz : int
      }
  | Pick of { choices : (int * term) list }
  | Alloc of { bytes : IT.t }
  | Call of
      { fsym : Sym.t;
        iargs : (Sym.t * Sym.t) list
      }
  | Asgn of
      { pointer : Sym.t;
        offset : IT.t;
        sct : Sctypes.t;
        value : IT.t;
        last_var : Sym.t;
        rest : term
      }
  | Let of
      { backtracks : int;
        x : Sym.t;
        x_bt : BT.t;
        value : term;
        last_var : Sym.t;
        rest : term
      }
  | Return of { value : IT.t }
  | Assert of
      { prop : LC.t;
        last_var : Sym.t;
        rest : term
      }
  | ITE of
      { bt : BT.t;
        cond : IT.t;
        t : term;
        f : term
      }
  | Map of
      { i : Sym.t;
        bt : BT.t;
        min : IT.t;
        max : IT.t;
        perm : IT.t;
        inner : term
      }
[@@deriving eq, ord]

let pp_term (_tm : term) : Pp.document = failwith __LOC__

let rec elaborate_gt (inputs : SymSet.t) (vars : Sym.t list) (gt : GT.t) : term =
  let (GT (gt_, bt, loc)) = gt in
  match gt_ with
  | Arbitrary ->
    failwith
      Pp.(
        plain (string "Value from " ^^ Locations.pp loc ^^ string " is still `arbitrary`"))
  | Uniform sz -> Uniform { bt; sz }
  | Pick wgts -> Pick { choices = List.map_snd (elaborate_gt inputs vars) wgts }
  | Alloc bytes -> Alloc { bytes }
  | Call (fsym, xits) ->
    let (iargs : (Sym.t * Sym.t) list), (gt_lets : Sym.t -> term -> term) =
      List.fold_left
        (fun (yzs, f) (y, it) ->
          let (IT.IT (it_, z_bt, _here)) = it in
          match it_ with
          | Sym z -> ((y, z) :: yzs, f)
          | _ ->
            let z = Sym.fresh () in
            ( (y, z) :: yzs,
              fun w gr ->
                Let
                  { backtracks = 0;
                    x = z;
                    x_bt = z_bt;
                    value = Return { value = it };
                    last_var = w;
                    rest = f y gr
                  } ))
        ([], fun _ gr -> gr)
        xits
    in
    gt_lets (match vars with v :: _ -> v | [] -> bennet) (Call { fsym; iargs })
  | Asgn ((it_addr, sct), value, rest) ->
    let pointer, offset =
      let (IT (it_addr_, _, loc)) = it_addr in
      match it_addr_ with
      | ArrayShift { base = IT (Sym p_sym, _, _); ct; index = it_offset } ->
        (p_sym, IT.mul_ (IT.sizeOf_ ct loc, IT.cast_ Memory.size_bt it_offset loc) loc)
      | Binop (Add, IT (Sym p_sym, _, _), it_offset) -> (p_sym, it_offset)
      | Sym p_sym -> (p_sym, IT.num_lit_ Z.zero Memory.size_bt loc)
      | _ ->
        failwith
          ("unsupported format for address: "
           ^ CF.Pp_utils.to_plain_string (IT.pp it_addr))
    in
    if not (SymSet.mem pointer inputs || List.exists (Sym.equal pointer) vars) then
      failwith
        (Sym.pp_string pointer
         ^ " not in ["
         ^ String.concat "; " (List.map Sym.pp_string vars)
         ^ "] from "
         ^ Pp.plain (Locations.pp (IT.loc it_addr)));
    Asgn
      { pointer;
        offset;
        sct;
        value;
        last_var = (if SymSet.mem pointer inputs then bennet else pointer);
        rest = elaborate_gt inputs vars rest
      }
  | Let (backtracks, x, gt1, gt2) ->
    Let
      { backtracks;
        x;
        x_bt = GT.bt gt1;
        value = elaborate_gt inputs vars gt1;
        last_var = (match vars with v :: _ -> v | [] -> bennet);
        rest = elaborate_gt inputs (x :: vars) gt2
      }
  | Return value -> Return { value }
  | Assert (prop, rest) ->
    Assert
      { prop;
        last_var =
          (match List.find_opt (fun x -> SymSet.mem x (LC.free_vars prop)) vars with
           | Some y -> y
           | None ->
             if SymSet.is_empty (SymSet.diff (LC.free_vars prop) inputs) then
               bennet
             else
               failwith __LOC__);
        rest = elaborate_gt inputs vars rest
      }
  | ITE (cond, gt_then, gt_else) ->
    ITE
      { bt;
        cond;
        t = elaborate_gt inputs vars gt_then;
        f = elaborate_gt inputs vars gt_else
      }
  | Map ((i, i_bt, perm), inner) ->
    let min, max = GenUtils.get_bounds (i, i_bt) perm in
    Map
      { i;
        bt = Map (i_bt, GT.bt inner);
        min;
        max;
        perm;
        inner = elaborate_gt inputs vars inner
      }


type definition =
  { name : Sym.t;
    iargs : (Sym.t * BT.t) list;
    oargs : (Sym.t * BT.t) list;
    body : term
  }
[@@deriving eq, ord]

let pp_definition (_def : definition) : Pp.document = failwith __LOC__

let elaborate_gd (gd : GD.t) : definition =
  { name = gd.name;
    iargs = List.map_snd GBT.bt gd.iargs;
    oargs = List.map_snd GBT.bt gd.oargs;
    body = elaborate_gt (SymSet.of_list (List.map fst gd.iargs)) [] (Option.get gd.body)
  }


type context = (A.ail_identifier * (A.ail_identifier list * definition) list) list

let pp (_ctx : context) : Pp.document = Pp.string ("TODO: " ^ __LOC__)

let elaborate (gtx : GD.context) : context = List.map_snd (List.map_snd elaborate_gd) gtx
