open Core

open Bmc_utils
open Bmc_inline
open Bmc_renaming
open Bmc_ssa

let bmc_normalize_file (f: 'a file) (sym_supply : ksym_supply) =
  (* Rename user variables that are repeated *)

  let (f, sym_supply) = ssa_file f sym_supply in
  print_string "INLINING FUNCTION CALLS\n";
  let (inlined_file, inlined_supply) = inline_file f sym_supply in

  (* pp_file inlined_file; *)
  print_string "\n";

  print_string "Rewriting Ivmin/Ivmax/issigned/etc \n";

  let (rewritten_file, rewritten_supply) = 
    rewrite_file inlined_file inlined_supply in

  (rewritten_file, rewritten_supply)


(* ========== Expr normalization ========== *)

(*
(* Create a fresh symbol of type bTy, make let equal to pexpr *)
let wrap_pexpr_with_let (bTy: core_base_type) 
                        (pexpr: pexpr)
                        (supply: ksym_supply ref) =
  let (new_sym, new_supply) = Sym.fresh (!supply) in
  let new_sym_expr = Pexpr(bTy, PEsym new_sym) in
  supply := new_supply;
  PElet(CaseBase (Some new_sym, bTy), 
        pexpr, 
        new_sym_expr), new_sym_expr

(* flatten let expressions *)
let rec flatten_pexpr_lets (Pexpr(bTy1, pe1) : pexpr)
                           (Pexpr(bTy2, pe2) as pexpr2 : pexpr) =
  match pe1 with 
    | PEsym _ -> pe2
    | PElet (pat, pe1, pe2) ->
       PElet(pat, pe1, Pexpr(bTy2, flatten_pexpr_lets pe2 pexpr2))
    | _ -> assert false

(* (normed, symbol) *)
let rec normalize_pexpr (Pexpr(annot, pexpr_) as pexpr: pexpr) 
                        (supply: ksym_supply ref) 
    : (pexpr * pexpr ) =
  let (norm_pexpr, sym) = match pexpr_ with
    | PEsym sym ->
        pexpr_, pexpr
    | PEimpl _ 
    | PEval _
    | PEconstrained _ 
    | PEundef _ 
    | PEerror _ ->
        wrap_pexpr_with_let annot pexpr supply 
    | PEctor (ctor, pelist) ->
        let norm_sym_list = 
          List.map (fun pe -> normalize_pexpr pe supply) pelist in
        let sym_list = List.map (fun (k,v) -> v) norm_sym_list in
        let new_pexpr = Pexpr(annot, PEctor(ctor, sym_list)) in
        let (new_let, sym) = wrap_pexpr_with_let annot new_pexpr supply in
        let (Pexpr(_, ret_)) = List.fold_right 
          (fun (k,v) b -> (Pexpr(annot, flatten_pexpr_lets k b))) 
                        norm_sym_list (Pexpr(annot, new_let)) in
        ret_, sym
    | PEcase (pe, caselist) ->

        (*wrap_pexpr_with_let annot pexpr supply *)
        let new_case_list = 
          List.map (fun (pat, pe) ->
             let (ret, _) = normalize_pexpr pe supply in 
             (pat, ret)) caselist in
        let new_pexpr = Pexpr(annot, PEcase(pe, new_case_list)) in
        let (new_let, sym) = wrap_pexpr_with_let annot new_pexpr supply in
        new_let, sym

    | PEarray_shift _
    | PEmember_shift _ ->
        wrap_pexpr_with_let annot pexpr supply 
    | PEnot pe ->
        (* TODO: double check *)
        let (norm_pe, sym_1) = normalize_pexpr pe supply in
        let new_pexpr = Pexpr(annot, PEnot sym_1) in
        let (new_let, sym_2) = wrap_pexpr_with_let annot new_pexpr supply in
        flatten_pexpr_lets norm_pe (Pexpr(annot, new_let)), sym_2
    | PEop (binop, pe1, pe2) ->
        let (norm_pe1, sym_1) = normalize_pexpr pe1 supply in
        let (norm_pe2, sym_2) = normalize_pexpr pe2 supply in
        let new_op = Pexpr(annot, PEop(binop, sym_1, sym_2)) in
        let (new_let, sym_binop) = wrap_pexpr_with_let annot new_op supply in
        (flatten_pexpr_lets 
            norm_pe1 
            (Pexpr(annot, (flatten_pexpr_lets norm_pe2 
                                              (Pexpr(annot, new_let))))),
         sym_binop)
    | PEstruct _
    | PEunion _
    | PEcall _ ->
        wrap_pexpr_with_let annot pexpr supply 
    | PElet (pat, pe1, pe2) ->
        let (norm_pe1, sym_1) = normalize_pexpr pe1 supply in
        let (norm_pe2, sym_2) = normalize_pexpr pe2 supply in
        let new_let = Pexpr(annot, PElet(pat, sym_1, norm_pe2)) in
        flatten_pexpr_lets norm_pe1 new_let, sym_2
    | PEif (pe1, pe2, pe3) ->
        let (norm_pe1, sym_1) = normalize_pexpr pe1 supply in
        let (norm_pe2, sym_2) = normalize_pexpr pe2 supply in
        let (norm_pe3, sym_3) = normalize_pexpr pe3 supply in
        let new_if = Pexpr(annot, PEif(sym_1, norm_pe2, norm_pe3)) in
        let (new_let, sym_if) = wrap_pexpr_with_let annot new_if supply in
        flatten_pexpr_lets norm_pe1 (Pexpr(annot, new_let)), sym_if
    | PEis_scalar _
    | PEis_integer _
    | PEis_signed _
    | PEis_unsigned _ ->
        wrap_pexpr_with_let annot pexpr supply 
    | PEstd (str, pe) ->
        wrap_pexpr_with_let annot pexpr supply 
        (*
        (* TODO: correct ?? *)
        let (norm_pe, sym_1) = normalize_pexpr pe supply in
        let new_std = (Pexpr(annot, PEstd(str, norm_pe))) in
        wrap_pexpr_with_let annot new_std supply 
        *)
  in 
  Pexpr(annot, norm_pexpr), sym

(* TODO: not done properly *)
let rec normalize_expr (Expr(annot, expr_): 'a expr) 
                       (supply: ksym_supply ref) =
  let norm_expr = match expr_ with
    | Epure pe ->
        let (norm, _) = normalize_pexpr pe supply in
        Epure norm 
    | Ememop( _, _) 
    | Eaction _ -> 
        expr_
    | Ecase (pe, clist) ->
        Ecase(pe, List.map (fun (k,v) -> (k, normalize_expr v supply)) clist)
    | Elet( pat, pe1, e2) ->
        let (norm_pe1, _) = normalize_pexpr pe1 supply in
        Elet( pat, norm_pe1, normalize_expr e2 supply)
    | Eif( pe1, e2, e3) ->
        let (norm_pe1, _) = normalize_pexpr pe1 supply in
        Eif(norm_pe1, 
            normalize_expr e2 supply,
            normalize_expr e3 supply)
    | Eskip 
    | Eccall( _, _, _) 
    | Eproc( _, _, _)  ->
        expr_
    | Eunseq es ->
        Eunseq (List.map (fun e -> normalize_expr e supply) es)
    | Ewseq( pat, e1, e2) ->
        Ewseq(pat, normalize_expr e1 supply, normalize_expr e2 supply)
    | Esseq( pat, e1, e2) ->
        Esseq(pat, normalize_expr e1 supply, normalize_expr e2 supply)
    | Easeq( _, _, _)  ->
        expr_
    | Eindet( i, e) ->
        Eindet(i, normalize_expr e supply)
    | Ebound( i, e) ->
        Ebound(i, normalize_expr e supply)
    | End es ->
        End (List.map (fun e -> normalize_expr e supply) es)
    | Esave( _, _, _) 
    | Erun( _, _, _) 
    | Epar _
    | Ewait _ ->
        expr_
  in (Expr(annot, norm_expr))

let normalize_fun_map (fun_map: ('a, 'b fun_map_decl) Pmap.map) 
                      (sym_supply: ksym_supply)  =
  let supply = ref (sym_supply) in
  ((Pmap.map ((function
    | Fun(ty, params, pe) ->
        let (norm, _) = normalize_pexpr pe supply in
        Fun (ty, params, norm)
    | ProcDecl(ty, params) ->
        assert false
    | Proc(ty, params, e) ->
        Proc(ty, params, normalize_expr e supply) 
   )) fun_map), !supply)
*)



(*
let normalize_file (file : 'a typed_file) (sym_supply: ksym_supply) =
  let (inlined_file, supply2) = inline_file file sym_supply in
  pp_file inlined_file;
  (*
  let (normed_map, supply1) = normalize_fun_map inlined_file.funs supply2 in
  ({inlined_file with funs = normed_map}), supply1
  *)
  Printf.printf "TODO: Normalize disabled";
  inlined_file, supply2
*)
