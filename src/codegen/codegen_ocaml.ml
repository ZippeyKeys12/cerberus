(* Created by Victor Gomes 2017-03-10 *)

open Util
open Core
open Cps_core
open Core_opt
open Pp_prelude
open Pp_ocaml

let print_head filename =
  !^"(* Generated by Cerberus from" ^^^ !^filename ^^ !^" *)" ^//^
  !^"module A = Rt_ocaml" ^/^
  !^"module M = Mem" ^/^
  !^"module I = Mem.Impl" ^/^
  !^"module T = AilTypes" ^/^
  !^"module C = Core_ctype" ^/^
  !^"module B = Nat_big_num" ^//^
  !^"let (>>=) = M.bind2" ^/^
  !^"let (>>) x y = x >>= fun _ -> y" ^//^
  !^"let rec _std_function_printf cont xs args =\
     \n  A.printf conv_int_2 xs args >>= fun x -> cont x"

let print_globals globs =
  let print_global_pair g =
    P.parens (!^"glob_" ^^ print_symbol g ^^ P.comma ^^^ print_symbol g)
  in
  List.map print_global_pair globs
  |> print_list id

let print_foot globs main =
  print_let !^"globals" (print_globals globs) ^//^
  print_let tunit (!^"A.run globals" ^^^ print_symbol main)

let opt_passes core =
  elim_wseq core
  |> assoc_seq
  |> elim_skip
  |> elim_loc
  |> elim_let

(* Generate Ocaml *)
let generate_ocaml filename sym_supply core =
  let globs_syms = List.map (fun (s,_,_) -> s) core.Core.globs in
  let cps_core = cps_transform sym_supply (run opt_passes core) globs_syms in
  let print_globals_init acc (sym, coreTy, bbs, bbody) =
    acc
    ^//^ tand ^^^ print_eff_function
      (!^"glob_" ^^ print_symbol sym ^^^ print_symbol default) []
      (print_base_type coreTy) (print_transformed globs_syms bbs bbody)
    ^/^ !^"and" ^^^ print_symbol sym ^^^ P.equals ^^^ print_ref !^"A.null_ptr"
  in
    print_head filename ^^
    print_impls globs_syms cps_core.impl ^^
    print_funs globs_syms cps_core.stdlib ^^
    List.fold_left print_globals_init P.empty cps_core.globs ^^
    print_funs globs_syms cps_core.funs ^//^
    print_foot globs_syms core.main

let compile filename sym_supply core =
  let fl = Filename.chop_extension filename in
  let fl_ml = fl ^ ".ml" in
  let oc = open_out fl_ml in
  begin
    generate_ocaml filename sym_supply core
    |> P.ToChannel.pretty 1. 80 oc;
    close_out oc;
    Exception.return0 0
  end
