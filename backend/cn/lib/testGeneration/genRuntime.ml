module CF = Cerb_frontend
module A = CF.AilSyntax
module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module GT = GenTerms
module GD = GenDefinitions
module SymSet = Set.Make (Sym)

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
        i_bt : BT.t;
        min : IT.t;
        max : IT.t;
        perm : IT.t;
        inner : term
      }
[@@deriving eq, ord]

type definition =
  { name : Sym.t;
    iargs : (Sym.t * BT.t) list;
    oargs : (Sym.t * BT.t) list;
    body : term option
  }
[@@deriving eq, ord]

type context = (A.ail_identifier * (A.ail_identifier list * definition) list) list

let rec elaborate_gt (vars : Sym.t list) (gt : GT.t) : term =
  let (GT (gt_, bt, loc)) = gt in
  match gt_ with
  | Arbitrary ->
    failwith
      Pp.(
        plain (string "Value from " ^^ Locations.pp loc ^^ string " is still `arbitrary`"))
  | Uniform sz -> Uniform { bt; sz }
  | Pick wgts -> Pick { choices = List.map_snd (elaborate_gt vars) wgts }
  | Alloc bytes -> Alloc { bytes }
  | Call (fsym, xits) ->
    let (iargs : (Sym.t * Sym.t) list), (gt_lets : term -> term) =
      List.fold_left
        (fun (yzs, f) (y, it) ->
          let (IT.IT (it_, z_bt, _here)) = it in
          match it_ with
          | Sym z -> ((y, z) :: yzs, f)
          | _ ->
            let z = Sym.fresh () in
            ( (y, z) :: yzs,
              fun gr ->
                Let
                  { backtracks = 0;
                    x = z;
                    x_bt = z_bt;
                    value = Return { value = it };
                    rest = f gr
                  } ))
        ([], fun gr -> gr)
        xits
    in
    gt_lets (Call { fsym; iargs })
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
    assert (List.exists (Sym.equal pointer) vars);
    Asgn
      { pointer; offset; sct; value; last_var = pointer; rest = elaborate_gt vars rest }
  | Let (backtracks, x, gt1, gt2) ->
    Let
      { backtracks;
        x;
        x_bt = GT.bt gt1;
        value = elaborate_gt vars gt1;
        rest = elaborate_gt (x :: vars) gt2
      }
  | Return value -> Return { value }
  | Assert (prop, rest) ->
    Assert
      { prop;
        last_var = List.find (fun x -> SymSet.mem x (LC.free_vars prop)) vars;
        rest = elaborate_gt vars rest
      }
  | ITE (cond, gt_then, gt_else) ->
    ITE { bt; cond; t = elaborate_gt vars gt_then; f = elaborate_gt vars gt_else }
  | Map ((i, i_bt, perm), inner) ->
    let min, max = failwith "" in
    Map { i; i_bt; min; max; perm; inner = elaborate_gt vars inner }


let elaborate : CF.GenTypes.genTypeCategory A.sigma -> GD.context -> context =
  failwith "TODO"
