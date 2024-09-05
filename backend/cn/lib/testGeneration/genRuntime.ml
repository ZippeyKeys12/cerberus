[@@@warning "-5-26-27-32"]

module CF = Cerb_frontend
module A = CF.AilSyntax
module C = CF.Ctype
module CtA = Cn_internal_to_ail
module Utils = Executable_spec_utils
module BT = BaseTypes
module IT = IndexTerms
module GT = GenTerms

let names = ref []

let get_name (syms : Sym.t list) : Sym.t =
  let open Pp in
  match List.assoc_opt (List.equal Sym.equal) syms !names with
  | Some sym -> sym
  | None ->
    let doc = string "gen_" ^^ separate_map underscore Sym.pp syms in
    let res_sym = Sym.fresh_named (CF.Pp_utils.to_plain_string doc) in
    names := (syms, res_sym) :: !names;
    res_sym


let compile_it (sigma : CF.GenTypes.genTypeCategory A.sigma) it =
  CtA.cn_to_ail_expr_internal sigma.cn_datatypes [] it PassBack


let rec compile_gt
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (name : Sym.t)
  (gt : GT.t)
  : A.bindings
    * CF.GenTypes.genTypeCategory A.statement_ list
    * CF.GenTypes.genTypeCategory A.expression option
  =
  let (GT (gt_, bt, loc)) = gt in
  let mk_expr = Utils.mk_expr ~loc in
  let mk_stmt = Utils.mk_stmt in
  match gt_ with
  | Uniform (_bt, sz) ->
    ( [],
      [],
      Some
        (mk_expr
           (AilEcall (mk_expr (AilEident (Sym.fresh_named "uniform_placeholder")), [])))
    )
  | Pick wgts ->
    ( [],
      [],
      Some
        (mk_expr
           (AilEcall (mk_expr (AilEident (Sym.fresh_named "pick_placeholder")), []))) )
  | Alloc it ->
    let alloc_sym = Sym.fresh_named "malloc" in
    let b, s, e = compile_it sigma it in
    (b, s, Some (mk_expr (AilEcall (mk_expr (AilEident alloc_sym), [ e ]))))
  | Call (fsym, xits) ->
    let sym = get_name (fsym :: List.map fst xits) in
    ( [],
      [],
      Some
        (mk_expr
           (AilEcall (mk_expr (AilEident (Sym.fresh_named "call_placeholder")), []))) )
  | Asgn ((it_addr, ct), it_val, gt') ->
    let b1, s1, e1 = compile_it sigma it_addr in
    let b2, s2, e2 = compile_it sigma it_val in
    let ownership_sym = Sym.fresh_named "cn_assume_ownership" in
    let s3 =
      A.
        [ AilSexpr (mk_expr (AilEassign (e1, e2)));
          AilSexpr
            (mk_expr
               (AilEcall
                  ( mk_expr (AilEident ownership_sym),
                    [ mk_expr
                        (AilEcast
                           (C.no_qualifiers, C.mk_ctype_pointer C.no_qualifiers C.void, e1));
                      mk_expr (AilEsizeof (C.no_qualifiers, Sctypes.to_ctype ct));
                      mk_expr
                        (AilEstr (None, [ (Locations.unknown, [ Sym.pp_string name ]) ]))
                    ] )))
        ]
    in
    let b4, s4, oe4 = compile_gt sigma name gt' in
    (b1 @ b2 @ b4, s1 @ s2 @ s3 @ s4, oe4)
  | Let (backtracks, x, gt1, gt2) ->
    let b1, s1, oe1 = compile_gt sigma name gt1 in
    let e1 = Option.get oe1 in
    let b2, s2, e2 = compile_gt sigma name gt2 in
    ( b1 @ b2,
      s1 @ A.[ AilSexpr (mk_expr (AilEassign (mk_expr (AilEident x), e1))) ] @ s2,
      e2 )
  | Return it ->
    let b, s, e = compile_it sigma it in
    (b, s, Some e)
  | Assert (lcs, gt') ->
    compile_gt sigma name gt'
    (* ( [],
       [],
       Some
       (mk_expr
       (AilEcall (mk_expr (AilEident (Sym.fresh_named "assert_placeholder")), []))) ) *)
  | ITE (it_if, gt_then, gt_else) ->
    let b_if, s_if, e_if = compile_it sigma it_if in
    let b_then, s_then, oe_then = compile_gt sigma name gt_then in
    let e_then = Option.get oe_then in
    let b_else, s_else, oe_else = compile_gt sigma name gt_else in
    let e_else = Option.get oe_else in
    ( b_if,
      (s_if
       @ A.
           [ AilSif
               ( CtA.wrap_with_convert_from_cn_bool e_if,
                 mk_stmt
                   (AilSblock (b_then, List.map mk_stmt (s_then @ [ AilSreturn e_then ]))),
                 mk_stmt
                   (AilSblock (b_else, List.map mk_stmt (s_else @ [ AilSreturn e_else ])))
               )
           ]),
      None )
  | Map ((x, bt, it), gt') -> compile_gt sigma name gt'


let compile_gen_def
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  ((name, gd) : Sym.t * GenDefinitions.t)
  : A.sigma_declaration * 'a A.sigma_function_definition
  =
  let bt_ret =
    BT.Record (List.map (fun (x, (_, bt, _)) -> (Id.id (Sym.pp_string x), bt)) gd.oargs)
  in
  let bt_to_ctype = CtA.bt_to_ail_ctype ~pred_sym:(Some name) in
  let decl : A.declaration =
    A.Decl_function
      ( false,
        (C.no_qualifiers, bt_to_ctype bt_ret),
        List.map
          (fun (_, (_, bt, _)) -> (C.no_qualifiers, bt_to_ctype bt, false))
          gd.iargs,
        false,
        false,
        false )
  in
  let sigma_decl : A.sigma_declaration =
    (name, (Locations.unknown, CF.Annot.Attrs [], decl))
  in
  let b, s, oe = compile_gt sigma name (Option.get gd.body) in
  let s = match oe with Some e -> s @ A.[ AilSreturn e ] | None -> s in
  let sigma_def : CF.GenTypes.genTypeCategory A.sigma_function_definition =
    ( name,
      ( Locations.unknown,
        0,
        CF.Annot.Attrs [],
        List.map fst gd.iargs,
        Utils.mk_stmt (A.AilSblock (b, List.map Utils.mk_stmt s)) ) )
  in
  (sigma_decl, sigma_def)


let compile (sigma : CF.GenTypes.genTypeCategory A.sigma) (ctx : GenDefinitions.context)
  : CF.GenTypes.genTypeCategory CF.AilSyntax.ail_program
  =
  let defs =
    ctx
    |> List.map (fun (fsym, defs) ->
      List.map (fun (iargs, gd) -> (get_name (fsym :: iargs), gd)) defs)
    |> List.flatten
  in
  let declarations, function_definitions =
    List.split (List.map (compile_gen_def sigma) defs)
  in
  let sigma : 'a A.sigma = { A.empty_sigma with declarations; function_definitions } in
  (None, sigma)
