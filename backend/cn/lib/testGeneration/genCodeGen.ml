module CF = Cerb_frontend
module A = CF.AilSyntax
module C = CF.Ctype
module CtA = Cn_internal_to_ail
module Utils = Executable_spec_utils
module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module GT = GenTerms
module GD = GenDefinitions
module SymSet = Set.Make (Sym)

let bt_to_ctype (pred_sym : Sym.t) (bt : BT.t) : C.ctype =
  let pred_sym = Some pred_sym in
  if BT.equal BT.Unit bt then
    C.Ctype ([], C.Pointer (C.no_qualifiers, C.void))
  else
    CtA.bt_to_ail_ctype ~pred_sym bt


let name_of_bt (pred_sym : Sym.t) (bt : BT.t) : string =
  let ct = bt_to_ctype pred_sym bt in
  let ct' =
    match bt_to_ctype pred_sym bt with
    | Ctype (_, Pointer (_, ct')) -> ct'
    | _ -> failwith ""
  in
  let default = CF.Pp_utils.to_plain_string (CF.Pp_core_ctype.pp_ctype ct') in
  Utils.get_typedef_string ct |> Option.value ~default


let str_name_of_bt (pred_sym : Sym.t) (bt : BT.t) : string =
  name_of_bt pred_sym bt |> String.split_on_char ' ' |> String.concat "_"


let compile_it (sigma : CF.GenTypes.genTypeCategory A.sigma) (name : Sym.t) (it : IT.t) =
  CtA.cn_to_ail_expr sigma.cn_datatypes [] (Some name) it


let compile_lc (sigma : CF.GenTypes.genTypeCategory A.sigma) (lc : LC.t) =
  CtA.cn_to_ail_logical_constraint sigma.cn_datatypes [] lc


let rec compile_gt
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (name : Sym.t)
  (gt : GT.t)
  : A.bindings
    * CF.GenTypes.genTypeCategory A.statement_ list
    * CF.GenTypes.genTypeCategory A.expression
  =
  let (GT (gt_, (_, bt), loc)) = gt in
  let mk_expr = Utils.mk_expr ~loc in
  let mk_stmt = Utils.mk_stmt in
  match gt_ with
  | Arbitrary -> failwith __LOC__
  | Uniform sz ->
    let b, s, e =
      compile_it sigma name (IT.num_lit_ (Z.of_int sz) GenUtils.ocaml_int_bt loc)
    in
    ( b,
      s,
      A.(
        mk_expr
          (AilEcall
             ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_UNIFORM")),
               [ mk_expr (AilEident (Sym.fresh_named (name_of_bt name bt))); e ] ))) )
  | Pick _wgts ->
    ( [],
      [],
      mk_expr (AilEcall (mk_expr (AilEident (Sym.fresh_named "pick_placeholder")), [])) )
  | Alloc it ->
    let alloc_sym = Sym.fresh_named "cn_gen_alloc" in
    let b, s, e = compile_it sigma name it in
    (b, s, mk_expr (AilEcall (mk_expr (AilEident alloc_sym), [ e ])))
  | Call (fsym, xits) ->
    let sym = GenUtils.get_mangled_name (fsym :: List.map fst xits) in
    let b, s, es =
      xits
      |> List.map snd
      |> List.map (compile_it sigma name)
      |> List.fold_left
           (fun (b2, s2, es) (b1, s1, e) -> (b1 @ b2, s1 @ s2, e :: es))
           ([], [], [])
    in
    (b, s, mk_expr (AilEcall (mk_expr (AilEident sym), List.rev es)))
  | Asgn ((it_addr, ct), it_val, gt') ->
    let p_sym = Sym.fresh () in
    let b1, s1, e1 =
      let b1', s1', AnnotatedExpression (_, _, _, e1') = compile_it sigma name it_addr in
      ( b1' @ [ Utils.create_binding p_sym C.(mk_ctype_pointer no_qualifiers void) ],
        (s1'
         @ A.
             [ AilSdeclaration
                 [ (p_sym, Some (mk_expr (CtA.wrap_with_convert_from e1' (BT.Loc ())))) ]
             ]),
        mk_expr (A.AilEident p_sym) )
    in
    let b2, s2, e2 = compile_it sigma name it_val in
    let ownership_sym = Sym.fresh_named "cn_assume_ownership" in
    let s3 =
      A.
        [ AilSexpr
            (mk_expr
               (AilEassign
                  ( mk_expr
                      (AilEunary
                         ( Indirection,
                           mk_expr
                             (AilEcast
                                ( C.no_qualifiers,
                                  C.mk_ctype_pointer C.no_qualifiers (Sctypes.to_ctype ct),
                                  e1 )) )),
                    mk_expr
                      (AilEcall
                         ( mk_expr
                             (AilEident
                                (Sym.fresh_named
                                   ("convert_from_" ^ str_name_of_bt name (IT.bt it_val)))),
                           [ e2 ] )) )));
          AilSexpr
            (mk_expr
               (AilEcall
                  ( mk_expr (AilEident ownership_sym),
                    [ e1;
                      mk_expr (AilEsizeof (C.no_qualifiers, Sctypes.to_ctype ct));
                      mk_expr
                        (AilEcast
                           ( C.no_qualifiers,
                             C.pointer_to_char,
                             mk_expr
                               (AilEstr
                                  (None, [ (Locations.unknown, [ Sym.pp_string name ]) ]))
                           ))
                    ] )))
        ]
    in
    let b4, s4, oe4 = compile_gt sigma name gt' in
    (b1 @ b2 @ b4, s1 @ s2 @ s3 @ s4, oe4)
  | Let (backtracks, x, gt1, gt2) ->
    let s1 =
      A.
        [ AilSexpr
            (mk_expr
               (AilEcall
                  ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_LET_BEGIN")),
                    List.map
                      mk_expr
                      [ AilEconst
                          (ConstantInteger
                             (IConstant (Z.of_int backtracks, Decimal, None)));
                        AilEident x
                      ] )))
        ]
    in
    let b2, s2, e2 = compile_gt sigma name gt1 in
    let s3 =
      A.
        [ AilSexpr
            (mk_expr
               (AilEcall
                  ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_LET_END")),
                    List.map
                      mk_expr
                      [ AilEconst
                          (ConstantInteger
                             (IConstant (Z.of_int backtracks, Decimal, None)));
                        AilEident
                          (Sym.fresh_named
                             (name_of_bt
                                (Option.value ~default:name (GT.pred gt1))
                                (GT.bt gt1)));
                        AilEident x
                      ]
                    @ [ e2; mk_expr (AilEident (Sym.fresh_named "bennet")) ] )))
        ]
    in
    let b4, s4, e4 = compile_gt sigma name gt2 in
    ( b2 @ [ Utils.create_binding x (bt_to_ctype name (GT.bt gt1)) ] @ b4,
      s1 @ s2 @ s3 @ s4,
      e4 )
  | Return it ->
    let b, s, e = compile_it sigma name it in
    (b, s, e)
  | Assert (lc, gt') ->
    let b1, s1, e1 = compile_lc sigma lc in
    let s_assert =
      A.
        [ AilSexpr
            (mk_expr
               (AilEcall
                  ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_ASSERT")),
                    e1
                    :: List.map
                         (fun x -> mk_expr (AilEident x))
                         (Sym.fresh_named "bennet"
                          :: List.of_seq (SymSet.to_seq (LC.free_vars lc))) )))
        ]
    in
    let b2, s2, e2 = compile_gt sigma name gt' in
    (b1 @ b2, s1 @ s_assert @ s2, e2)
    (* ( [],
       [],
       Some
       (mk_expr
       (AilEcall (mk_expr (AilEident (Sym.fresh_named "assert_placeholder")), []))) ) *)
  | ITE (it_if, gt_then, gt_else) ->
    let b_if, s_if, e_if = compile_it sigma name it_if in
    let b_then, s_then, e_then = compile_gt sigma name gt_then in
    let b_else, s_else, e_else = compile_gt sigma name gt_else in
    let res_sym = Sym.fresh () in
    let res_expr = mk_expr (AilEident res_sym) in
    let res_binding = Utils.create_binding res_sym (bt_to_ctype name bt) in
    let res_stmt_ e = A.(AilSexpr (mk_expr (AilEassign (res_expr, e)))) in
    ( b_if @ [ res_binding ],
      (s_if
       @ A.
           [ AilSdeclaration [ (res_sym, None) ];
             AilSif
               ( CtA.wrap_with_convert_from_cn_bool e_if,
                 mk_stmt
                   (AilSblock (b_then, List.map mk_stmt (s_then @ [ res_stmt_ e_then ]))),
                 mk_stmt
                   (AilSblock (b_else, List.map mk_stmt (s_else @ [ res_stmt_ e_else ])))
               )
           ]),
      res_expr )
  | Map ((i_sym, i_bt, (it_min, it_max), it_perm), gt') ->
    let sym_map = Sym.fresh () in
    let b_map = Utils.create_binding sym_map (bt_to_ctype name bt) in
    let b_i = Utils.create_binding i_sym (bt_to_ctype name i_bt) in
    let b_min, s_min, e_min = compile_it sigma name it_min in
    let b_max, s_max, e_max = compile_it sigma name it_max in
    assert (b_max == []);
    assert (s_max == []);
    let e_args =
      [ mk_expr (AilEident sym_map);
        mk_expr (AilEident i_sym);
        mk_expr (AilEident (Sym.fresh_named (name_of_bt name i_bt)))
      ]
    in
    let s_begin =
      A.(
        s_min
        @ [ AilSexpr
              (mk_expr
                 (AilEcall
                    ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_MAP_BEGIN")),
                      e_args @ [ e_min; e_max ] )))
          ])
    in
    let b_perm, s_perm, e_perm = compile_it sigma name it_perm in
    let s_body =
      A.(
        s_perm
        @ [ AilSexpr
              (mk_expr
                 (AilEcall
                    (mk_expr (AilEident (Sym.fresh_named "CN_GEN_MAP_BODY")), [ e_perm ])))
          ])
    in
    let b_val, s_val, e_val = compile_gt sigma name gt' in
    let s_end =
      A.(
        s_val
        @ [ AilSexpr
              (mk_expr
                 (AilEcall
                    ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_MAP_END")),
                      e_args @ [ e_max; e_val ] )))
          ])
    in
    ( [ b_map; b_i ] @ b_min @ b_perm @ b_val,
      s_begin @ s_body @ s_end,
      mk_expr (AilEident sym_map) )


let compile_gen_def
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  ((name, gd) : Sym.t * GenDefinitions.t)
  : A.sigma_tag_definition * (A.sigma_declaration * 'a A.sigma_function_definition)
  =
  let bt_ret =
    BT.Record
      (List.map (fun (x, (_, (_, bt), _)) -> (Id.id (Sym.pp_string x), bt)) gd.oargs)
  in
  let struct_def = CtA.generate_record_opt name bt_ret |> Option.get in
  let decl : A.declaration =
    A.Decl_function
      ( false,
        (C.no_qualifiers, bt_to_ctype name bt_ret),
        List.map
          (fun (_, (_, (_, bt), _)) -> (C.no_qualifiers, bt_to_ctype name bt, false))
          gd.iargs,
        false,
        false,
        false )
  in
  let sigma_decl : A.sigma_declaration =
    (name, (Locations.unknown, CF.Annot.Attrs [], decl))
  in
  let s1 =
    A.(
      AilSexpr
        (Utils.mk_expr
           (AilEcall (Utils.mk_expr (AilEident (Sym.fresh_named "CN_GEN_INIT")), []))))
  in
  let b2, s2, e2 = compile_gt sigma name (Option.get gd.body) in
  let sigma_def : CF.GenTypes.genTypeCategory A.sigma_function_definition =
    ( name,
      ( Locations.unknown,
        0,
        CF.Annot.Attrs [],
        List.map fst gd.iargs,
        Utils.mk_stmt
          (A.AilSblock (b2, List.map Utils.mk_stmt ([ s1 ] @ s2 @ A.[ AilSreturn e2 ])))
      ) )
  in
  (struct_def, (sigma_decl, sigma_def))


let compile (sigma : CF.GenTypes.genTypeCategory A.sigma) (ctx : GenDefinitions.context)
  : Pp.document
  =
  let defs =
    ctx
    |> List.map (fun (_, defs) -> List.map (fun (_, gd) -> (GD.mangled_name gd, gd)) defs)
    |> List.flatten
  in
  let tag_definitions, funcs = List.split (List.map (compile_gen_def sigma) defs) in
  let declarations, function_definitions = List.split funcs in
  let sigma : 'a A.sigma =
    { A.empty_sigma with tag_definitions; declarations; function_definitions }
  in
  let open Pp in
  string "#ifndef CN_GEN_H"
  ^^ hardline
  ^^ string "#define CN_GEN_H"
  ^^ twice hardline
  ^^ string "#include <cn-testing/prelude.h>"
  ^^ twice hardline
  ^^ string "#include \"cn.h\""
  ^^ twice hardline
  ^^ separate_map
       (twice hardline)
       (CF.Pp_ail.pp_tag_definition ~executable_spec:true)
       tag_definitions
  ^^ twice hardline
  ^^ CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, sigma)
  ^^ hardline
  ^^ string "#endif // CN_GEN_H"
  ^^ hardline
