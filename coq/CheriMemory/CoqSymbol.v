(* Generated by Lem from frontend/model/symbol.lem. *)

From Coq Require Import Arith Bool List String.
Require Import Coq.ZArith.ZArith.

Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.

Require Import StructTact.StructTactics.
Require Import Lia.
Require Import CoqLocation.
Require Import Common.Utils.

Inductive identifier : Type :=
  | Identifier:  location_ocaml  ->  string  -> identifier .

Definition ident_equal (a b: identifier) : bool :=
  match a, b with
  | Identifier _ s1, Identifier _ s2 => String.eqb s1 s2
  end.

Definition digest := string.

Inductive symbol_description : Type :=
  | SD_None: symbol_description
  | SD_unnamed_tag: location_ocaml -> symbol_description
  | SD_Id:  string  -> symbol_description
  | SD_CN_Id: string -> symbol_description
  | SD_ObjectAddress:  string  -> symbol_description
  | SD_Return: symbol_description
  | SD_FunArgValue: string -> symbol_description
  | SD_FunArg: location_ocaml ->  nat  -> symbol_description .

(* Symbolic identifiers *)
Inductive sym : Set :=
  Symbol:  digest  ->  Z  ->  symbol_description  -> sym .

Definition digest_compare (a b: digest): Z
  := match String.compare a b with
     | Eq => 0
     | Lt => -1
     | Gt => 1
     end.

Definition symbolEquality (sym1 sym2: sym): bool :=
  match sym1, sym2 with
  | Symbol d1 n1 _,  Symbol d2 n2 _ =>
      Z.eqb (digest_compare d1 d2) 0 && Z.eqb n1 n2
  end.

(*
(* for [@@deriving eq] *)
Definition equal_sym   : sym  -> sym  -> bool :=  symbolEquality.
(* [?]: removed value specification. *)
*)

Definition symbol_compare (s1 s2 : sym ): comparison :=
  match s1,s2 with
    Symbol d1 n1 _, Symbol d2 n2 _ =>
      let dcmp := digest_compare d1 d2 in
      if Z.eqb dcmp 0 then
        Z.compare n1 n2
      else
        if Z.ltb dcmp 0 then Lt else
          if Z.eqb dcmp 0 then Eq else Gt
  end.

(*
(* for [@@ deriving ord] *)
Definition compare_sym   : sym  -> sym  -> ordering :=  symbol_compare.
*)

Module Symbol_sym_as_OT <: OrderedType.
  Definition t := sym.

  Definition eq: t -> t -> Prop := fun a b => is_true (symbolEquality a b).
  Definition lt (a b: t): Prop := match symbol_compare a b with
                               | Lt => True
                               | _ => False
                               end.

  Lemma eq_refl: forall x : t, eq x x.
  Proof.
    intros.
    unfold eq, is_true, symbolEquality.
    destruct x as [d1 n1 z1].
    apply andb_true_intro.
    split.
    -
      unfold digest_compare.
      break_match.
      + apply Z.eqb_refl.
      + exfalso.
        clear z1 n1.
        induction d1.
        * inversion Heqc.
        * cbn in Heqc.
          break_match.
          -- auto.
          -- unfold Ascii.compare in *.
             rewrite N.compare_lt_iff in Heqc0.
             lia.
          -- inversion Heqc.
      + exfalso.
        clear z1 n1.
        induction d1.
        * inversion Heqc.
        * cbn in Heqc.
          break_match.
          -- auto.
          -- inversion Heqc.
          -- unfold Ascii.compare in *.
             rewrite N.compare_gt_iff in Heqc0.
             lia.
    -
      lia.
  Qed.

  Lemma eq_sym: forall x y : t, eq x y -> eq y x.
  Proof.
    unfold eq, symbolEquality, is_true.
    intros x y H.
    destruct x,y.
    apply andb_prop in H.
    destruct H as [D ZE].
    apply andb_true_intro.
    split.
    -
      clear - D.
      apply Z.eqb_eq in D.
      apply Z.eqb_eq.
      unfold digest_compare in *.
      repeat break_match;try lia.
      +
        rewrite compare_antisym in Heqc0.
        unfold CompOpp in Heqc0.
        rewrite Heqc in Heqc0.
        inversion Heqc0.
      +
        rewrite compare_antisym in Heqc0.
        unfold CompOpp in Heqc0.
        rewrite Heqc in Heqc0.
        inversion Heqc0.
    -
      apply Z.eqb_eq in ZE.
      lia.
  Qed.

  Lemma eq_trans: forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq, symbolEquality, is_true.
    intros x y z H H0.
    destruct x, y, z.

    apply andb_prop in H, H0.
    destruct H as [D0 ZE0].
    destruct H0 as [D1 ZE1].
    apply andb_true_intro.
    split.
    -
      clear - D0 D1.
      apply Z.eqb_eq in D0, D1.
      apply Z.eqb_eq.
      unfold digest_compare in *.
      repeat break_match;try lia.
      +
        erewrite string_eq_trans in Heqc; eauto.
        inversion Heqc.
      +
        erewrite string_eq_trans in Heqc; eauto.
        inversion Heqc.
    -
      apply Z.eqb_eq in ZE0, ZE1.
      lia.
  Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
  Admitted.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros x y H.
    unfold lt in H.
    destruct (symbol_compare x y) eqn:D; auto. clear H.
    unfold not, eq, is_true, symbolEquality.
    destruct x as [d1 n1 z1].
    destruct y as [d2 n2 z2].
    unfold symbol_compare in D.
    intros E.
    apply andb_prop in E.
    destruct E as [E1 E2].
    break_if.
    + clear E1.
      rewrite Z.compare_lt_iff in D.
      rewrite Z.eqb_eq in E2.
      lia.
    + lia.
  Qed.

  Lemma digest_compare_eq_sym:
    forall d1 d2,
      (Z.eqb (digest_compare d1 d2) 0) = true ->
      (Z.eqb (digest_compare d2 d1) 0) = true.
  Proof.
    unfold digest_compare.
    intros d1 d2.
    rewrite compare_antisym.
    destruct (d2 ?= d1)%string; auto.
  Qed.

  Lemma digest_compare_antisym:
    forall d1 d2,
      (Z.eqb (digest_compare d1 d2) 0) = false ->
      ((Z.ltb (digest_compare d1 d2) 0) = negb (Z.ltb (digest_compare d2 d1) 0)).
  Proof.
    unfold digest_compare.
    intros d1 d2.
    rewrite compare_antisym.
    destruct (d2 ?= d1)%string; auto.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros x y.
    case_eq (symbol_compare x y); intro.
    - apply EQ.
      unfold symbol_compare in H.
      destruct x as [d1 n1].
      destruct y as [d2 n2].
      break_if.
      + unfold eq, is_true, symbolEquality.
        apply andb_true_intro.
        split.
        * assumption.
        * apply Z.compare_eq in H.
          apply Z.eqb_eq.
          assumption.
      + break_if; inversion H.
    - apply LT.
      unfold symbol_compare in H.
      destruct x as [d1 n1].
      destruct y as [d2 n2].
      break_if.
      + unfold lt, is_true.
        break_match.
        * cbn in Heqc.
          break_if.
          -- rewrite H in Heqc. inversion Heqc.
          -- break_if; inversion Heqc.
        * trivial.
        * cbn in Heqc.
          break_if.
          -- rewrite H in Heqc. inversion Heqc.
          -- inversion Heqb.
      + break_if.
        * unfold lt.
          break_match.
          -- cbn in Heqc.
             break_if.
             ++ inversion Heqb.
             ++ break_if;inversion Heqc.
          -- trivial.
          -- cbn in Heqc.
             break_if.
             ++ inversion Heqb.
             ++ break_if.
                inversion Heqc.
                inversion Heqb0.
        * inversion H.
    - apply GT.
      unfold symbol_compare in H.
      destruct x as [d1 n1].
      destruct y as [d2 n2].
      break_if.
      + unfold lt, is_true.
        apply Zcompare_Gt_Lt_antisym in H.
        break_match.
        * cbn in Heqc.
          break_if.
          -- rewrite H in Heqc. inversion Heqc.
          -- break_if; inversion Heqc.
        * trivial.
        * cbn in Heqc.
          break_if.
          -- rewrite H in Heqc. inversion Heqc.
          -- break_if.
             inversion Heqc.
             apply digest_compare_eq_sym in Heqb.
             rewrite Heqb in Heqb0.
             inversion Heqb0.
      + break_if.
        * inversion H.
        * unfold lt.
          break_match.
          -- cbn in Heqc.
             break_if.
             ++ apply digest_compare_eq_sym in Heqb1.
                rewrite Heqb in Heqb1.
                inversion Heqb1.
             ++ break_if;inversion Heqc.
          -- trivial.
          -- cbn in Heqc.
             break_if.
             ++ apply digest_compare_eq_sym in Heqb1.
                rewrite Heqb in Heqb1.
                inversion Heqb1.
             ++ break_if.
                inversion Heqc.
                rewrite digest_compare_antisym in Heqb0.
                rewrite Heqb2 in Heqb0.
                cbv in Heqb0.
                inversion Heqb0.
                assumption.
  Defined.

  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros x y.
    destruct x, y.
    unfold eq, symbolEquality, digest_compare.
    break_match; cbn.
    destruct (z =? z0)%Z; cbv.
    + left; trivial.
    + right; lia.
    + right; cbv; lia.
    + right; cbv; lia.
  Defined.

End Symbol_sym_as_OT.


Module SymMap := FMapAVL.Make(Symbol_sym_as_OT).


(*
Instance x8_Eq : Eq sym := {
   isEqual             :=  (fun  sym1  sym2=>match ( (sym1, sym2)) with
    | (Symbol d1 n1 sd1,  Symbol d2 n2 sd2) =>
        if Z.eqb (FAKE_COQ.digest_compare d1 d2)((Z.pred (Z.pos (P_of_succ_nat 0%nat)))) && Nat.eqb n1 n2 then
          if nat_gteb (FAKE_COQ.get_level tt)( 5%nat) && unsafe_structural_inequality sd1 sd2 then
  match ( FAKE_COQ.print_debug ( 5%nat) []
            (fun u =>
               match ( (u) ) with ( tt) =>
                 String.append
                   "[Symbol.symbolEqual] suspicious equality ==> "
                   (String.append (show_symbol_description sd1)
                      (String.append " <-> " (show_symbol_description sd2)))
               end)) with tt => true end
          else
            true
        else
          false
  end);
   isInequal   sym1  sym2 :=  negb (match ( (sym1, sym2)) with
    | (Symbol d1 n1 sd1,  Symbol d2 n2 sd2) =>
        if Z.eqb (FAKE_COQ.digest_compare d1 d2)((Z.pred (Z.pos (P_of_succ_nat 0%nat)))) && Nat.eqb n1 n2 then
          if nat_gteb (FAKE_COQ.get_level tt)( 5%nat) && unsafe_structural_inequality sd1 sd2 then
  match ( FAKE_COQ.print_debug ( 5%nat) []
            (fun u =>
               match ( (u) ) with ( tt) =>
                 String.append
                   "[Symbol.symbolEqual] suspicious equality ==> "
                   (String.append (show_symbol_description sd1)
                      (String.append " <-> " (show_symbol_description sd2)))
               end)) with tt => true end
          else
            true
        else
          false
  end)
}.


Instance x7_Ord : Ord sym := {
   compare   sym1  sym2 :=
  match ( sym1) with ( Symbol d1 n1 _) =>
    match ( sym2) with ( Symbol d2 n2 _) =>
      if Z.eqb (FAKE_COQ.digest_compare d1 d2)
           ((Z.pred (Z.pos (P_of_succ_nat 0%nat)))) then
        (genericCompare nat_ltb Nat.eqb n1 n2) else
        let cmp := FAKE_COQ.digest_compare d1 d2 in
        if int_ltb cmp ((Z.pred (Z.pos (P_of_succ_nat 0%nat)))) then
        LT else
          if Z.eqb cmp ((Z.pred (Z.pos (P_of_succ_nat 0%nat)))) then
          EQ else GT end end;
   isLess   sym1  sym2 :=
  match ( sym1) with ( Symbol d1 n1 _) =>
    match ( sym2) with ( Symbol d2 n2 _) =>
      int_ltb (FAKE_COQ.digest_compare d1 d2)
        ((Z.pred (Z.pos (P_of_succ_nat 0%nat)))) ||
      ( Z.eqb (FAKE_COQ.digest_compare d1 d2)
          ((Z.pred (Z.pos (P_of_succ_nat 0%nat)))) && nat_ltb n1 n2) end end;
   isLessEqual   sym1  sym2 :=
  match ( sym1) with ( Symbol d1 n1 _) =>
    match ( sym2) with ( Symbol d2 n2 _) =>
      int_lteb (FAKE_COQ.digest_compare d1 d2)
        ((Z.pred (Z.pos (P_of_succ_nat 0%nat)))) ||
      ( Z.eqb (FAKE_COQ.digest_compare d1 d2)
          ((Z.pred (Z.pos (P_of_succ_nat 0%nat)))) && nat_lteb n1 n2) end end;
   isGreater   sym1  sym2 :=
  match ( sym1) with ( Symbol d1 n1 _) =>
    match ( sym2) with ( Symbol d2 n2 _) =>
      int_gtb (FAKE_COQ.digest_compare d1 d2)
        ((Z.pred (Z.pos (P_of_succ_nat 0%nat)))) ||
      ( Z.eqb (FAKE_COQ.digest_compare d1 d2)
          ((Z.pred (Z.pos (P_of_succ_nat 0%nat)))) && nat_gtb n1 n2) end end;
   isGreaterEqual   sym1  sym2 :=
  match ( sym1) with ( Symbol d1 n1 _) =>
    match ( sym2) with ( Symbol d2 n2 _) =>
      int_gteb (FAKE_COQ.digest_compare d1 d2)
        ((Z.pred (Z.pos (P_of_succ_nat 0%nat)))) ||
      ( Z.eqb (FAKE_COQ.digest_compare d1 d2)
          ((Z.pred (Z.pos (P_of_succ_nat 0%nat)))) && nat_gteb n1 n2) end end
}.


Instance x6_NumSucc : NumSucc sym := {
   succ   sym :=  match ( sym) with ( Symbol d n sd) =>
   Symbol d (Coq.Init.Peano.plus n ( 1%nat)) sd end
}.


Instance x5_SetType : SetType sym := {
   setElemCompare   sym1  sym2 :=  ordCompare sym1 sym2
}.


Definition show_symbol  (sym1 : sym )  : string :=
  match ( sym1) with Symbol d n sd =>
    String.append "Symbol"
      (stringFromPair lem_string_extra.stringFromNat show_symbol_description
         (n, sd)) end.

Instance x4_Show : Show sym := {
   show  :=  show_symbol
}.


Definition show_raw_less  (s : sym )  : string :=
  match ( (s)) with (( Symbol _ n sd)) =>
    String.append "Symbol("
      (String.append (lem_string_extra.stringFromNat n)
         (String.append ", " (String.append (show_symbol_description sd) ")")))
  end.
Definition show_raw  (s : sym )  : string :=
  match ( (s)) with (( Symbol d n sd)) =>
    String.append "Symbol("
      (String.append (FAKE_COQ.string_of_digest d)
         (String.append ", "
            (String.append (lem_string_extra.stringFromNat n)
               (String.append ", "
                  (String.append (show_symbol_description sd) ")"))))) end.

*)

(* Location prefix *)
Inductive prefix : Type :=
  | PrefSource:  location_ocaml  ->  list  sym  -> prefix
  | PrefFunArg:  location_ocaml  ->  digest  ->  Z  -> prefix
  | PrefStringLiteral:  location_ocaml  ->  digest  -> prefix
  | PrefTemporaryLifetime: location_ocaml -> digest -> prefix
  | PrefCompoundLiteral:  location_ocaml  ->  digest  -> prefix
  | PrefMalloc: prefix
  | PrefOther:  string  -> prefix .


(* Definition string_of_prefix (p:prefix) : string := "". (* TODO *) *)

(*
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

Definition digest_of_sym  (s : sym )  : digest :=
  match ( (s)) with (( Symbol dig _ _)) => dig end.
(* [?]: removed value specification. *)

Definition fresh   tt  : sym :=
  Symbol (FAKE_COQ.digesttt) (FAKE_COQ.fresh_int tt) SD_None.
(* [?]: removed value specification. *)

Definition fresh_pretty  (str : string )  : sym :=
  Symbol (FAKE_COQ.digesttt) (FAKE_COQ.fresh_int tt) (SD_Id str).
(* [?]: removed value specification. *)

Definition fresh_pretty_with_id  (mkStr : nat  -> string )  : sym :=
  let id := FAKE_COQ.fresh_int tt in
  Symbol (FAKE_COQ.digesttt) id (SD_Id (mkStr id)).
(* [?]: removed value specification. *)

Definition fresh_fancy   : option (string )  -> sym :=
  fun (x : option (string ) ) =>
    match (x) with | Some str => fresh_pretty str | None => fresh tt end.

Definition fresh_object_address  (name1 : string )  : sym :=
  Symbol (FAKE_COQ.digesttt) (FAKE_COQ.fresh_int tt) (SD_ObjectAddress name1).

Definition fresh_funarg  (loc : unit ) (i : nat )  : sym :=
  Symbol (FAKE_COQ.digest tt) (FAKE_COQ.fresh_int tt) (SD_FunArg loc i).

Definition fresh_description  (sd : symbol_description )  : sym :=
  Symbol (FAKE_COQ.digest tt) (FAKE_COQ.fresh_int tt) sd.

Definition set_symbol_description  (s : sym ) (sd : symbol_description )  : sym :=
  match ( (s,sd)) with (( Symbol d n _),  sd) => Symbol d n sd end.
(* [?]: removed value specification. *)

Definition from_same_translation_unit  (sym1 : sym ) (sym2 : sym )  : bool :=  Z.eqb((Z.pred (Z.pos (P_of_succ_nat 0%nat)))) (FAKE_COQ.digest_compare (digest_of_sym sym1) (digest_of_sym sym2)).


Definition symbol_description  (s : sym )  : symbol_description :=
  match ( (s)) with (( Symbol _ _ descr)) => descr end.
Definition symbol_num  (s : sym )  : nat :=
  match ( (s)) with (( Symbol _ num _)) => num end.
 *)