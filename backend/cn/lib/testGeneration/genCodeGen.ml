module CF = Cerb_frontend
module A = CF.AilSyntax
module C = CF.Ctype
module CtA = Cn_internal_to_ail
module Utils = Executable_spec_utils
module BT = BaseTypes
module IT = IndexTerms
module GT = GenTerms

let ocaml_int_bt = BT.Bits (Signed, Sys.int_size + 1)

let names = ref []

let get_name (syms : Sym.t list) : Sym.t =
  let open Pp in
  match List.assoc_opt (List.equal Sym.equal) syms !names with
  | Some sym -> sym
  | None ->
    let doc = string "cn_gen_" ^^ separate_map underscore Sym.pp syms in
    let res_sym = Sym.fresh_named (CF.Pp_utils.to_plain_string doc) in
    names := (syms, res_sym) :: !names;
    res_sym


let bt_to_ctype ?(pred_sym = None) bt =
  let ct = CtA.bt_to_ail_ctype ~pred_sym bt in
  if not (C.ctypeEqual C.void ct) then
    ct
  else
    C.Ctype ([], C.Pointer (C.no_qualifiers, C.void))


let name_of_bt (bt : BT.t) : string =
  let ct = bt_to_ctype bt in
  let default = CF.Pp_utils.to_plain_string (CF.Pp_core_ctype.pp_ctype ct) in
  Utils.get_typedef_string ct |> Option.value ~default


let stmt_of_doc (doc : Pp.document) : CF.GenTypes.genTypeCategory A.statement_ =
  A.(
    AilSexpr
      (Utils.mk_expr
         (AilEident
            (Sym.fresh_named
               Pp.(plain ~width:90 (string "/*" ^^ space ^^ doc ^^ space ^^ string "*/"))))))


let compile_it (sigma : CF.GenTypes.genTypeCategory A.sigma) it =
  CtA.cn_to_ail_expr_internal sigma.cn_datatypes [] it PassBack


let rec compile_gt
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (name : Sym.t)
  (gt : GT.t)
  : A.bindings
    * CF.GenTypes.genTypeCategory A.statement_ list
    * CF.GenTypes.genTypeCategory A.expression
  =
  let (GT (gt_, bt, loc)) = gt in
  let mk_expr = Utils.mk_expr ~loc in
  let mk_stmt = Utils.mk_stmt in
  match gt_ with
  | Arbitrary -> failwith __LOC__
  | Uniform sz ->
    (* let s_comment =
       stmt_of_doc
       (let open Pp in
       string "uniform" ^^ angles (BT.pp bt) ^^ parens (int sz))
       in *)
    let b, s, e = compile_it sigma (IT.num_lit_ (Z.of_int sz) ocaml_int_bt loc) in
    ( b,
      s,
      A.(
        mk_expr
          (AilEcall
             ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_UNIFORM")),
               [ mk_expr (AilEident (Sym.fresh_named (name_of_bt bt))); e ] ))) )
  | Pick _wgts ->
    ( [],
      [],
      mk_expr (AilEcall (mk_expr (AilEident (Sym.fresh_named "pick_placeholder")), [])) )
  | Alloc it ->
    (* let s_comment =
       stmt_of_doc
       (let open Pp in
       string "alloc" ^^ parens (IT.pp it))
       in *)
    let alloc_sym = Sym.fresh_named "cn_gen_alloc" in
    let b, s, e = compile_it sigma it in
    (b, s, mk_expr (AilEcall (mk_expr (AilEident alloc_sym), [ e ])))
  | Call (fsym, xits) ->
    (* let s_comment =
       stmt_of_doc
       (let open Pp in
       Sym.pp fsym
       ^^ parens
       (nest
       2
       (separate_map
       (comma ^^ break 1)
       (fun (x, it) -> Sym.pp x ^^ colon ^^ space ^^ IT.pp it)
       xits)))
       in *)
    let sym = get_name (fsym :: List.map fst xits) in
    let b, s, es =
      xits
      |> List.map snd
      |> List.map (compile_it sigma)
      |> List.fold_left
           (fun (b2, s2, es) (b1, s1, e) -> (b1 @ b2, s1 @ s2, es @ [ e ]))
           ([], [], [])
    in
    (b, s, mk_expr (AilEcall (mk_expr (AilEident sym), List.rev es)))
  | Asgn ((it_addr, ct), it_val, gt') ->
    (* let s_comment =
       stmt_of_doc
       (let open Pp in
       Sctypes.pp ct
       ^^ space
       ^^ IT.pp it_addr
       ^^ space
       ^^ string ":="
       ^^ space
       ^^ IT.pp it_val)
       in *)
    let b1, s1, e1 = compile_it sigma it_addr in
    let b2, s2, e2 = compile_it sigma it_val in
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
                                   ("convert_from_" ^ name_of_bt (IT.bt it_val)))),
                           [ e2 ] )) )));
          AilSexpr
            (mk_expr
               (AilEcall
                  ( mk_expr (AilEident ownership_sym),
                    [ mk_expr
                        (AilEcast
                           (C.no_qualifiers, C.mk_ctype_pointer C.no_qualifiers C.void, e1));
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
    (* let s_comment =
       stmt_of_doc
       (let open Pp in
       string "let"
       ^^ (if backtracks <> 0 then parens (int backtracks) else empty)
       ^^ (if GT.is_return gt1 then empty else star)
       ^^ space
       ^^ Sym.pp x
       ^^ space
       ^^ equals)
       in *)
    let s1 =
      A.
        [ AilSexpr
            (mk_expr
               (AilEcall
                  ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_LET_START")),
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
                        AilEident (Sym.fresh_named (name_of_bt (GT.bt gt1) ^ "*"));
                        AilEident x
                      ]
                    @ [ e2; mk_expr (AilEident (Sym.fresh_named "bennet")) ] )))
        ]
    in
    let b4, s4, e4 = compile_gt sigma name gt2 in
    (b2 @ [ Utils.create_binding x (bt_to_ctype (GT.bt gt1)) ] @ b4, s1 @ s2 @ s3 @ s4, e4)
  | Return it ->
    let s_comment =
      stmt_of_doc
        (let open Pp in
         string "return" ^^ space ^^ IT.pp it)
    in
    let b, s, e = compile_it sigma it in
    (b, [ s_comment ] @ s, e)
  | Assert (_lc, gt') ->
    compile_gt sigma name gt'
    (* ( [],
       [],
       Some
       (mk_expr
       (AilEcall (mk_expr (AilEident (Sym.fresh_named "assert_placeholder")), []))) ) *)
  | ITE (it_if, gt_then, gt_else) ->
    (* let s_comment_if =
       stmt_of_doc
       (let open Pp in
       string "if" ^^ space ^^ parens (IT.pp it_if) ^^ space ^^ lbrace)
       in
       let s_comment_else =
       stmt_of_doc
       (let open Pp in
       rbrace ^^ space ^^ string "else" ^^ space ^^ lbrace)
       in *)
    let s_comment_endif = stmt_of_doc Pp.rbrace in
    let b_if, s_if, e_if = compile_it sigma it_if in
    let b_then, s_then, e_then = compile_gt sigma name gt_then in
    let b_else, s_else, e_else = compile_gt sigma name gt_else in
    let res_sym = Sym.fresh () in
    let res_expr = mk_expr (AilEident res_sym) in
    let res_binding = Utils.create_binding res_sym (bt_to_ctype bt) in
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
           ])
      @ [ s_comment_endif ],
      res_expr )
  | Map ((i_sym, i_bt, (it_min, it_max), it_perm), gt') ->
    (* let s_comment =
       stmt_of_doc
       (let open Pp in
       string "map"
       ^^ space
       ^^ parens (BT.pp i_bt ^^ space ^^ Sym.pp i_sym ^^ semi ^^ space ^^ IT.pp it_perm))
       in *)
    let sym_map = Sym.fresh () in
    let b_map = Utils.create_binding sym_map (bt_to_ctype bt) in
    let s_map =
      A.(
        AilSdeclaration
          [ ( sym_map,
              Some
                (mk_expr
                   (AilEcall (mk_expr (AilEident (Sym.fresh_named "map_create")), []))) )
          ])
    in
    let i_it = IT.sym_ (i_sym, i_bt, loc) in
    let b_start, s_start, e_start = compile_it sigma it_min in
    let b_i = Utils.create_binding i_sym (bt_to_ctype i_bt) in
    let s_i = A.AilSdeclaration [ (i_sym, Some e_start) ] in
    let b_end, s_end, e_end = compile_it sigma (IT.lt_ (i_it, it_max) loc) in
    let b_perm, s_perm, e_perm = compile_it sigma it_perm in
    let b_body, s_body, e_body = compile_gt sigma name gt' in
    let e_cast =
      A.(
        AilEcall
          ( mk_expr
              (AilEident
                 (Sym.fresh_pretty
                    ("cast_"
                     ^ Option.get (Utils.get_typedef_string (bt_to_ctype i_bt))
                     ^ "_to_cn_integer"))),
            [ mk_expr (AilEident i_sym) ] ))
    in
    let s_set =
      A.(
        AilSexpr
          (mk_expr
             (AilEcall
                ( mk_expr (AilEident (Sym.fresh_pretty "cn_map_set")),
                  List.map mk_expr [ AilEident sym_map; e_cast ] @ [ e_body ] ))))
    in
    let s_loop =
      A.(
        AilSwhile
          ( e_end,
            mk_stmt
              (AilSif
                 ( e_perm,
                   mk_stmt (AilSblock (b_body, List.map mk_stmt (s_body @ [ s_set ]))),
                   mk_stmt AilSskip )),
            0 ))
    in
    let s_body =
      A.(
        AilSblock
          ( [ b_i ] @ b_start @ b_end @ b_perm,
            List.map mk_stmt ([ s_i ] @ s_start @ s_end @ s_perm @ [ s_loop ]) ))
    in
    ([ b_map ], [ s_map; s_body ], mk_expr (AilEident sym_map))


let compile_gen_def
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  ((name, gd) : Sym.t * GenDefinitions.t)
  : A.sigma_declaration * 'a A.sigma_function_definition
  =
  let bt_ret =
    BT.Record (List.map (fun (x, (_, bt, _)) -> (Id.id (Sym.pp_string x), bt)) gd.oargs)
  in
  let bt_to_ctype = bt_to_ctype ~pred_sym:(Some name) in
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
  (sigma_decl, sigma_def)


let compile (sigma : CF.GenTypes.genTypeCategory A.sigma) (ctx : GenDefinitions.context)
  : Pp.document
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
  let open Pp in
  string "#ifndef CN_GEN_H"
  ^^ hardline
  ^^ string "#define CN_GEN_H"
  ^^ twice hardline
  ^^ string "#include <cn-testing/dsl.h>"
  ^^ hardline
  ^^ string "#include <cn-testing/generators.h>"
  ^^ twice hardline
  ^^ string "#include \"cn.h\""
  ^^ twice hardline
  ^^ CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, sigma)
  ^^ hardline
  ^^ string "#endif // CN_GEN_H"
  ^^ hardline
