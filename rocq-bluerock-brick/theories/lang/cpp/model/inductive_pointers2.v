(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(**
Another (incomplete) consistency proof for [PTRS], based on Krebbers' PhD thesis, and
other formal models of C++ using structured pointers.
This is more complex than [SIMPLE_PTRS_IMPL], but will be necessary to justify [VALID_PTR_AXIOMS].

In this model, all valid pointers have an address pinned, but this is not meant
to be guaranteed.
*)

Require Import stdpp.relations.
Require Import stdpp.gmap.
Require Import bedrock.prelude.base.
Require Import bedrock.prelude.addr.
Require Import bedrock.prelude.avl.
Require Import bedrock.prelude.bytestring.
Require Import bedrock.prelude.option.
Require Import bedrock.prelude.numbers.

Require Import bedrock.lang.cpp.syntax.
Require Import bedrock.lang.cpp.semantics.sub_module.
Require Import bedrock.lang.cpp.semantics.values.
Require Import bedrock.lang.cpp.model.simple_pointers_utils.
Require Import bedrock.lang.cpp.model.inductive_pointers_utils.
Require Import bedrock.lang.cpp.semantics.ptrs2.

From Equations Require Import Equations.

Axiom irr : ∀ (P : Prop) (p q : P), p = q.

Implicit Types (σ : genv) (z : Z).
#[local] Close Scope nat_scope.
#[local] Open Scope Z_scope.

Module PTRS_IMPL <: PTRS_INTF.
  Import canonical_tu address_sums merge_elems.

  Inductive raw_offset_seg : Set :=
  | o_field_ (* type-name: *) (f : field)
  | o_sub_ (ty : type) (z : Z)
  | o_base_ (derived base : globname)
  | o_derived_ (base derived : globname).
  #[local] Instance raw_offset_seg_eq_dec : EqDecision raw_offset_seg.
  Proof. solve_decision. Defined.
  #[global] Declare Instance raw_offset_seg_countable : Countable raw_offset_seg.

  Definition raw_offset := list raw_offset_seg.
  #[local] Instance raw_offset_eq_dec : EqDecision raw_offset := _.
  #[local] Instance raw_offset_countable : Countable raw_offset := _.

  Variant roff_rw_local : raw_offset -> raw_offset -> Prop :=
  | CanonDerBase der base :
    roff_rw_local
      [o_derived_ base der; o_base_ der base]
      []
  | CanonBaseDer der base :
    roff_rw_local
      [o_base_ der base; o_derived_ base der]
      []
  | CanonSubZero ty :
    roff_rw_local
      [o_sub_ ty 0]
      []
  | CanonSubMerge ty n1 n2 :
      roff_rw_local
        [o_sub_ ty n1; o_sub_ ty n2]
        [o_sub_ ty (n1 + n2)].

  Definition roff_rw_global (os1 os2 : raw_offset) :=
    ∃ l r s t,
      os1 = l ++ s ++ r /\
      os2 = l ++ t ++ r /\
      roff_rw_local s t.

  Definition roff_rw := rtc roff_rw_global.

  #[global] Instance: RewriteRelation roff_rw := {}.
  #[global] Instance: subrelation roff_rw_global roff_rw.
  Proof. exact: rtc_once. Qed.
  (* #[global] Instance: Reflexive roff_rw.
  Proof. apply _. Abort.
  #[global] Instance: Transitive roff_rw.
  Proof. apply _. Abort. *)
  Definition roff_canon := nf roff_rw_global.

  #[global] Instance roff_rw_reflexive : Reflexive roff_rw.
  Proof.
    move=> x. done.
  Qed.
  #[global] Instance roff_rw_transitive : Transitive roff_rw.
  Proof.
    move=> x y z. apply rtc_transitive.
  Qed.

  Definition roff_canon := nf roff_rw_global.

  Lemma singleton_offset_canon :
    ∀ o,
      (¬∃ ty, o = o_sub_ ty 0) ->
      roff_canon [o].
  Proof.
    assert (Hn : ∀ A (x y z : A) (l r : list A), [x] ≠ l ++ [y; z] ++ r).
    {
      move=> A x y z l r H.
      destruct l. done.
      inversion H. subst.
      destruct l; done.
    }
    move=> o H.
    rewrite /roff_canon /nf /roff_rw_global /red.
    move=> [_ [l [r [s [t [H1 [_ H2]]]]]]].
    destruct H2.
    { apply: Hn. exact: H1. }
    { apply: Hn. exact: H1. }
    {
      destruct l; simpl in H1;
      inversion H1; subst.
      { apply: H. by exists ty. }
      destruct l; done.
    }
    { apply: Hn. exact: H1. }
  Qed.

  Lemma nil_canon :
    roff_canon [].
  Proof.
    rewrite /roff_canon /roff_rw_global /nf /not /red.
    move=> [o [l [r [s [t [H1 [H2 H3]]]]]]].
    subst.
    assert (l = []).
    { by destruct l. }
    subst.
    assert (s = []).
    { by destruct s. }
    subst.
    clear - H3. remember [].
    by destruct H3.
  Qed.

  Inductive roff_canon_syn : raw_offset -> Prop :=
  | NilCanon :
      roff_canon_syn []
  | SingCanon o :
      ¬(∃ ty, o = o_sub_ ty 0) ->
      roff_canon_syn [o]
  | SubCanon ty i o os :
      roff_canon_syn (o :: os) ->
      ¬(∃ i' ty', o = o_sub_ ty' i') ->
      i ≠ 0 ->
      roff_canon_syn (o_sub_ ty i :: o :: os)
  | FieldCanon f os :
      roff_canon_syn os ->
      roff_canon_syn (o_field_ f :: os)
  | BaseCanon der base o os :
      roff_canon_syn (o :: os) ->
      o ≠ o_derived_ base der ->
      roff_canon_syn (o_base_ der base :: o :: os)
  | DerCanon base der o os :
      roff_canon_syn (o :: os) ->
      o ≠ o_base_ der base ->
      roff_canon_syn (o_derived_ base der :: o :: os).

  Lemma canon_syn_sem_eqv :
    ∀ os,
      roff_canon os <-> roff_canon_syn os.
  Proof.
    rewrite /roff_canon /nf /red.
    move=> os. split; move=> Hc.
    {
      admit.
    }
    {
      induction Hc;
      try (
        remember (o :: os) as eos;
        destruct Hc; subst
      ); try done;
      try inversion Heqeos;
      subst.
      { apply: nil_canon. }
      { by apply: singleton_offset_canon. }
      all:
        move=> [y [l [r [s [t [Ho [Hl Hstep]]]]]]];
        subst; destruct l; simpl in *; destruct Hstep;
        simpl in *; inversion Ho; subst; try done;
        try (
          match goal with
          | H : ¬∃ i ty, o_sub_ _ _ = o_sub_ ty i |- False =>
            apply H
          end;
          try repeat eexists
        );
        try (
          match goal with
          | H : [?o] = ?l ++ ?r |- False =>
            destruct l; simpl in *;
            inversion H; subst;
            destruct l; simpl in *;
            inversion H
          end
        );
        try (
          match goal with
          | H : [?o] = ?l ++ ?r |- False =>
            destruct l; simpl in *;
            inversion H; subst
          end
        );
        try (
          match goal with
          | H : ¬∃ ty, o_sub_ _ 0 = o_sub_ ty 0 |- False =>
              apply H; repeat eexists
          end
        );
        try (
          match goal with
          | H : [] = ?l ++ ?r |- False =>
              destruct l; simpl in *;
              inversion H
          end
        ).
        all: admit.
    }
  Admitted.

  Definition offset := {o : raw_offset | roff_canon o}.
  #[global] Instance offset_eq_dec : EqDecision offset.
  Proof.
    move=> [o1 H1] [o2 H2].
    destruct (decide (o1 = o2)).
    {
      subst. left.
      f_equal.
      apply: irr.
    }
    {
      right.
      rewrite /not => H.
      apply n.
      now apply proj1_sig_eq in H.
    }
  Qed.

  Equations normalize (os : raw_offset) : raw_offset by wf (length os) lt :=
  | [] => []
  | o_derived_ base1 der1 :: o_base_ der2 base2 :: os =>
    if decide (base1 = base2 /\ der1 = der2) then
      normalize os
    else
      o_derived_ base1 der1 :: normalize (o_base_ der2 base2 :: os)
  | o_base_ der2 base2 :: o_derived_ base1 der1 :: os =>
    if decide (base1 = base2 /\ der1 = der2) then
      normalize os
    else
      o_base_ der2 base2 :: normalize (o_derived_ base1 der1 :: os)
  | o_sub_ ty1 i1 :: o_sub_ ty2 i2 :: os =>
    if decide (i1 = 0) then
      normalize (o_sub_ ty2 i2 :: os)
    else if decide (ty1 = ty2) then
      normalize (o_sub_ ty1 (i1 + i2) :: os)
    else
      o_sub_ ty1 i1 :: normalize (o_sub_ ty2 i2 :: os)
  | o_sub_ ty i :: os =>
    if decide (i = 0) then
      normalize os
    else
    o_sub_ ty i :: normalize os
  | o :: os => o :: normalize os.

  Goal normalize [o_sub_ Tint (-2); o_sub_ Tint 2] = [].
  Proof.
    simp normalize.
    repeat case_match; (done || lia).
  Qed.

  Goal normalize [o_sub_ Tint 2; o_sub_ Tint 2] = [o_sub_ Tint 4].
  Proof.
    simp normalize.
    repeat case_match; (done || lia).
  Qed.

  Section norm_lemmas.

    Lemma roff_rw_cong :
      ∀ ol1 ol2 or1 or2,
        roff_rw ol1 or1 ->
        roff_rw ol2 or2 ->
        roff_rw (ol1 ++ ol2) (or1 ++ or2).
    Proof.
      move=> ol1 ol2 or1 or2 Hrw0 Hrw1.
      induction Hrw0.
      {
        induction Hrw1.
        { done. }
        {
          rewrite -{}IHHrw1.
          apply rtc_once.
          move: H => [l [r [s [t [H1 [H2 H3]]]]]].
          subst. exists (x ++ l), r, s, t.
          split. by rewrite app_assoc.
          split. by rewrite app_assoc.
          done.
        }
      }
      {
        rewrite -{}IHHrw0.
        apply rtc_once.
        move: H => [l [r [s [t [H1 [H2 H3]]]]]].
        subst. exists l, (r ++ ol2), s, t.
        split. by repeat rewrite -app_assoc.
        split. by repeat rewrite -app_assoc.
        done.
      }
    Qed.

    #[global] Instance roff_rw_app_mono :
      Proper (roff_rw ==> roff_rw ==> roff_rw) (++).
    Proof.
      rewrite /Proper /respectful.
      move=> ol1 or1 H1 ol2 or2 H2.
      by apply roff_rw_cong.
    Qed.
    #[global] Instance roff_rw_app_flip_mono :
      Proper (flip roff_rw ==> flip roff_rw ==> flip roff_rw) (++).
    Proof. solve_proper. Qed.

    #[global] Instance roff_rw_cons_mono ro :
      Proper (roff_rw ==> roff_rw) (ro ::.).
    Proof.
      intros x y H.
      by apply roff_rw_cong with (ol1:=[ro]) (or1:=[ro]).
    Qed.

    #[global] Instance roff_rw_cons_flip_mono ro :
      Proper (flip roff_rw ==> flip roff_rw) (ro ::.).
    Proof. solve_proper. Qed.

    #[local] Hint Constructors roff_rw_local : core.

    Section norm_sound. (* <- Now unnecessary *)
      Lemma norm_sound :
        ∀ os, roff_rw os (normalize os).
      Proof.
        move=> os.
        funelim (normalize os);
        simp normalize in *; repeat case_match.
        all: try by [|rewrite -H| rewrite -H0|rewrite -H1].
        {
          subst.
          apply rtc_once.
          by exists [], [], [o_sub_ ty 0], [].
        }
        {
          subst.
          rewrite -H; last done.
          apply rtc_once.
          by exists [], (o_field_ f :: l), [o_sub_ ty 0], [].
        }
        {
          subst.
          rewrite -H; last done.
          apply rtc_once.
          by exists [], (o_sub_ ty2 i2 :: os), [o_sub_ ty1 0], [].
        }
        {
          subst.
          rewrite -H0; [|done..].
          apply rtc_once.
          by exists [], os, [o_sub_ ty2 i1; o_sub_ ty2 i2], [o_sub_ ty2 (i1 + i2)].
        }
        {
          subst.
          rewrite -H; [|done..].
          apply rtc_once.
          by exists [], (o_base_ derived base :: l), [o_sub_ ty 0], [].
        }
        {
          subst.
          rewrite -H; [|done..].
          apply rtc_once.
          by exists [], (o_derived_ base0 derived0 :: l), [o_sub_ ty 0], [].
        }
        {
          subst.
          apply: rtc_l. 2: by apply: H.
          by exists [], (o_invalid_ :: l), [o_sub_ ty 0], [].
        }
        {
          clear H1.
          move: a => [Hbase Hder].
          subst.
          rewrite -H; last done.
          apply rtc_once.
          by exists [], os, [o_base_ der2 base2; o_derived_ base2 der2], [].
        }
        {
          clear H1.
          move: a => [Hbase Hder].
          subst.
          rewrite -H //.
          apply: rtc_once.
          by exists [], os, [o_derived_ base2 der2; o_base_ der2 base2], [].
        }
      Qed.
    End norm_sound.

    Lemma norm_complete :
      ∀ o1 o2,
        roff_rw o1 o2 ->
        roff_canon o2 ->
        normalize o1 = o2.
    Proof.
      move=> o1 o2 Hrw Hc.
    Admitted.

    Lemma norm_canon :
      ∀ os, roff_canon (normalize os).
    Proof.
      move=> os.
    Admitted.

    Lemma norm_rel :
      ∀ o1 o2,
        normalize o1 = o2 <-> roff_rw o1 o2 /\ roff_canon o2.
    Proof.
      move=> o1 o2.
      split.
      {
        move=> H. subst.
        split.
        { apply: norm_sound. }
        { apply: norm_canon. }
      }
      {
        move=> [H1 H2].
        by apply norm_complete.
      }
    Qed.

    #[global] Instance normalize_mono :
      Proper (roff_rw ==> roff_rw) normalize.
    Proof.
      move=> o1 o2 E.
      move E1: (normalize o1) => o1'.
      move E2: (normalize o2) => o2'.
      move: E1 E2 => /norm_rel [E1 C1] /norm_rel [E2 C2].
      rewrite -E2 -E.
      (* only works for symmetric closure. *)
    Abort.

    Lemma norm_invol :
      ∀ os,
        roff_canon os ->
        normalize os = os.
    Proof.
      move=> o H.
      rewrite norm_rel.
      split.
      { constructor. }
      { done. }
    Qed.

    Lemma simp_norm_sub0 :
      ∀ ty os,
        normalize (o_sub_ ty 0 :: os) = normalize os.
    Proof.
      move=> ty os.
      induction os; simpl.
      {
        simp normalize.
        case_match.
        { by simp normalize. }
        { done. }
      }
      destruct a;
      simp normalize;
      by case_match.
    Qed.

    Lemma roff_rw_uncons_help_nil :
      ∀ s t r,
        roff_rw_local s t ->
        roff_rw (t ++ r) (normalize (s ++ r)).
    Proof.
      move=> s t r H1.
      destruct H1; simpl;
      simp normalize.
      {
        case_match.
        { apply norm_sound. }
        { exfalso. by apply n. }
      }
      {
        case_match.
        { apply norm_sound. }
        { exfalso. by apply n. }
      }
      {
        rewrite simp_norm_sub0.
        apply norm_sound.
      }
      {
        repeat case_match; try done.
        {
          subst.
          assert (0 + n2 = n2) as -> by lia.
          apply norm_sound.
        }
        {
          apply norm_sound.
        }
      }
    Qed.

    Lemma roff_rw_cong_cons :
      ∀ o os1 os2,
        roff_rw os1 os2 ->
        roff_rw (o :: os1) (o :: os2).
    Proof. by move=> o os1 os2 ->. Qed.

    Lemma roff_rw_sub_sub :
      ∀ os1 os2 ty i1 i2,
        roff_rw (o_sub_ ty (i1 + i2) :: os1) os2 ->
        roff_rw (o_sub_ ty i1 :: o_sub_ ty i2 :: os1) os2.
    Proof.
      move=> os1 os2 ty i1 i2 <-.
      apply: rtc_once.
      by exists [], os1, [o_sub_ ty i1; o_sub_ ty i2], [o_sub_ ty (i1 + i2)].
    Qed.

    Lemma roff_rw_sub0 :
      ∀ os1 os2 ty,
        roff_rw os1 os2 ->
        roff_rw (o_sub_ ty 0 :: os1) os2.
    Proof.
      move=> os1 os2 ty <-.
      apply: rtc_once.
      by exists [], os1, [o_sub_ ty 0], [].
    Qed.

    Lemma roff_rw_base_der :
      ∀ os1 os2 der base,
        roff_rw os1 os2 ->
        roff_rw (o_base_ der base :: o_derived_ base der :: os1) os2.
    Proof.
      move=> os1 os2 der base <-.
      apply: rtc_once.
      by exists [], os1, [o_base_ der base; o_derived_ base der], [].
    Qed.

    Lemma roff_rw_der_base :
      ∀ os1 os2 der base,
        roff_rw os1 os2 ->
        roff_rw (o_derived_ base der :: o_base_ der base :: os1) os2.
    Proof.
      move=> os1 os2 der base <-.
      apply: rtc_once.
      by exists [], os1, [o_derived_ base der; o_base_ der base], [].
    Qed.

    Equations roff_rw_uncons_help_sing r :
      ∀ o,
        roff_rw (o :: r) (normalize (o :: r))
      by wf (length r) lt :=
      roff_rw_uncons_help_sing r o := _.
    Next Obligation.
      destruct o; simp normalize.
      {
        apply roff_rw_cong_cons.
        apply norm_sound.
      }
      {
        destruct (decide (z = 0)).
        {
          subst. destruct r.
          {
            simp normalize.
            case_match; try done.
            apply: rtc_l. 2: done.
            by exists [], [], [o_sub_ ty 0], [].
          }
          destruct r;
          simp normalize;
          case_match; try done.
          { apply roff_rw_sub0, roff_rw_cong_cons, norm_sound. }
          { apply roff_rw_sub0, roff_rw_uncons_help_sing. simpl. lia. }
          { apply roff_rw_sub0, roff_rw_uncons_help_sing. simpl. lia. }
          { apply roff_rw_sub0, roff_rw_uncons_help_sing. simpl. lia. }
        }
        {
          destruct r.
          {
            simp normalize.
            case_match; try done.
          }
          destruct r;
          simp normalize;
          case_match; try done.
          { apply roff_rw_cong_cons, roff_rw_cong_cons, norm_sound. }
          {
            case_match; subst.
            { apply roff_rw_sub_sub, roff_rw_uncons_help_sing. simpl. lia. }
            { apply roff_rw_cong_cons, roff_rw_uncons_help_sing. simpl. lia. }
          }
          { apply roff_rw_cong_cons, norm_sound. }
          { apply roff_rw_cong_cons, norm_sound. }
        }
      }
      {
        destruct r.
        {
          simp normalize.
          constructor.
        }
        destruct r;
        simp normalize;
        repeat apply roff_rw_cong_cons;
        try apply norm_sound.
        {
          case_match.
          { destruct a. subst. apply roff_rw_base_der, norm_sound. }
          { apply roff_rw_cong_cons, roff_rw_uncons_help_sing. simpl. lia. }
        }
      }
      {
        destruct r.
        {
          simp normalize.
          constructor.
        }
        destruct r;
        simp normalize;
        repeat apply roff_rw_cong_cons;
        try apply norm_sound.
        {
          case_match.
          { destruct a. subst. apply roff_rw_der_base, norm_sound. }
          { apply roff_rw_cong_cons, roff_rw_uncons_help_sing. simpl. lia. }
        }
      }
    Qed.

    Lemma roff_rw_uncons_cons_sub :
      ∀ r ty s t z,
        z ≠ 0 ->
        roff_rw_local s t ->
        roff_rw (o_sub_ ty z :: t ++ r) (normalize (o_sub_ ty z :: s ++ r)).
    Proof.
      move => r ty s t z Hne H.
      destruct H; simpl;
      simp normalize;
      case_match; try done.
      {
        apply roff_rw_cong_cons.
        case_match. 2: exfalso; by apply n0.
        apply norm_sound.
      }
      {
        apply roff_rw_cong_cons.
        case_match. 2: exfalso; by apply n0.
        apply norm_sound.
      }
      {
        case_match.
        {
          subst.
          replace (z + 0) with z by lia.
          apply roff_rw_uncons_help_sing.
        }
        {
          rewrite simp_norm_sub0.
          apply roff_rw_cong_cons.
          apply norm_sound.
        }
      }
      {
        repeat case_match; subst;
        repeat apply roff_rw_sub_sub;
        try replace (z + (n1 + n2)) with (z + n1 + n2) by lia;
        try rewrite e0; try replace (0 + n2) with n2 by lia;
        try apply roff_rw_uncons_help_sing;
        try apply roff_rw_cong_cons;
        try apply roff_rw_uncons_help_sing;
        done.
      }
    Qed.

    Lemma roff_rw_uncons_cons_base :
      ∀ r der base s t,
        roff_rw_local s t ->
        roff_rw (o_base_ der base :: t ++ r) (normalize (o_base_ der base :: s ++ r)).
    Proof.
      move=> r der base s t H.
      destruct H; simpl;
      simp normalize.
      {
        case_match.
        {
          destruct a. subst.
          apply roff_rw_uncons_help_sing.
        }
        {
          case_match.
          2: exfalso; by apply n0.
          apply roff_rw_cong_cons, norm_sound.
        }
      }
      {
        case_match; apply roff_rw_cong_cons.
        { apply norm_sound. }
        { exfalso. by apply n. }
      }
      {
        apply roff_rw_cong_cons.
        rewrite simp_norm_sub0.
        apply norm_sound.
      }
      {
        case_match.
        {
          subst.
          replace (0 + n2) with n2 by lia.
          apply roff_rw_cong_cons, roff_rw_uncons_help_sing.
        }
        {
          case_match; try done.
          apply roff_rw_cong_cons, roff_rw_uncons_help_sing.
        }
      }
    Qed.

    Lemma roff_rw_uncons_cons_der :
      ∀ r der base s t,
        roff_rw_local s t ->
        roff_rw (o_derived_ base der :: t ++ r) (normalize (o_derived_ base der :: s ++ r)).
    Proof.
      move=> r der base s t H.
      destruct H; simpl;
      simp normalize.
      {
        case_match; apply roff_rw_cong_cons.
        { apply norm_sound. }
        { exfalso. by apply n. }
      }
      {
        case_match.
        {
          destruct a. subst.
          apply roff_rw_uncons_help_sing.
        }
        {
          case_match.
          2: exfalso; by apply n0.
          apply roff_rw_cong_cons, norm_sound.
        }
      }
      {
        apply roff_rw_cong_cons.
        rewrite simp_norm_sub0.
        apply norm_sound.
      }
      {
        case_match.
        {
          subst.
          replace (0 + n2) with n2 by lia.
          apply roff_rw_cong_cons, roff_rw_uncons_help_sing.
        }
        {
          case_match; try done.
          apply roff_rw_cong_cons, roff_rw_uncons_help_sing.
        }
      }
    Qed.

    Equations roff_rw_uncons_help (l : raw_offset) :
      ∀ s t r,
      roff_rw_local s t ->
      roff_rw (l ++ t ++ r) (normalize (l ++ s ++ r))
    by wf (length l) lt :=
    roff_rw_uncons_help l s t r H1 := _.
    Next Obligation.
      destruct l; simpl in *.
      { by apply roff_rw_uncons_help_nil. }
      destruct r0;
      simp normalize.
      {
        apply roff_rw_cong with
          (ol1:=[o_field_ f])
          (or1:=[o_field_ f]).
        { done. }
        {
          apply roff_rw_uncons_help.
          { done. }
          { lia. }
        }
      }
      {
        destruct (decide (z = 0)).
        {
          subst.
          rewrite simp_norm_sub0.
          apply rtc_l with
            (y:= l ++ t ++ r).
          {
            exists [], (l ++ t ++ r), [o_sub_ ty 0], [].
            split. done.
            split. done.
            constructor.
          }
          {
            apply roff_rw_uncons_help.
            { done. }
            { lia. }
          }
        }
        {
          destruct l; simpl in *.
          { by apply roff_rw_uncons_cons_sub. }
          destruct r0; simpl;
          simp normalize;
          case_match; try done.
          {
            do 2 apply roff_rw_cong_cons.
            apply roff_rw_uncons_help; (done || lia).
          }
          {
            case_match.
            {
              subst.
              apply rtc_l with
                (y:= o_sub_ ty0 (z + z0) :: l ++ t ++ r).
              {
                exists [], (l ++ t ++ r), [o_sub_ ty0 z; o_sub_ ty0 z0], [o_sub_ ty0 (z + z0)].
                split. done.
                split. done.
                constructor.
              }
              {
                change (o_sub_ ty0 (z + z0) :: l ++ t ++ r)
                with (([o_sub_ ty0 (z + z0)] ++ l) ++ t ++ r).
                change (o_sub_ ty0 (z + z0) :: l ++ s ++ r)
                with (([o_sub_ ty0 (z + z0)] ++ l) ++ s ++ r).
                apply roff_rw_uncons_help.
                { done. }
                { simpl. lia. }
              }
            }
            {
              apply roff_rw_cong_cons.
              change (o_sub_ ty0 z0 :: l ++ t ++ r)
              with (([o_sub_ ty0 z0] ++ l) ++ t ++ r).
              change (o_sub_ ty0 z0 :: l ++ s ++ r)
              with (([o_sub_ ty0 z0] ++ l) ++ s ++ r).
              apply roff_rw_uncons_help.
              { done. }
              { simpl. lia. }
            }
          }
          {
            apply roff_rw_cong_cons.
            change (o_base_ derived base :: l ++ t ++ r)
            with (([o_base_ derived base] ++ l) ++ t ++ r).
            change (o_base_ derived base :: l ++ s ++ r)
            with (([o_base_ derived base] ++ l) ++ s ++ r).
            apply roff_rw_uncons_help.
            { done. }
            { simpl. lia. }
          }
          {
            apply roff_rw_cong_cons.
            change (o_derived_ base derived :: l ++ t ++ r)
            with (([o_derived_ base derived] ++ l) ++ t ++ r).
            change (o_derived_ base derived :: l ++ s ++ r)
            with (([o_derived_ base derived] ++ l) ++ s ++ r).
            apply roff_rw_uncons_help.
            { done. }
            { simpl. lia. }
          }
        }
      }
      {
        destruct l; simpl in *.
        { by apply roff_rw_uncons_cons_base. }
        {
          destruct r0; simpl in *;
          simp normalize.
          {
            apply roff_rw_cong_cons.
            apply roff_rw_cong_cons.
            apply roff_rw_uncons_help; (done || lia).
          }
          {
            apply roff_rw_cong_cons.
            change (o_sub_ ty z :: l ++ t ++ r)
            with (([o_sub_ ty z] ++ l) ++ t ++ r).
            change (o_sub_ ty z :: l ++ s ++ r)
            with (([o_sub_ ty z] ++ l) ++ s ++ r).
            apply roff_rw_uncons_help; simpl; (done || lia).
          }
          {
            apply roff_rw_cong_cons.
            change (o_base_ derived0 base0 :: l ++ t ++ r)
            with (([o_base_ derived0 base0] ++ l) ++ t ++ r).
            change (o_base_ derived0 base0 :: l ++ s ++ r)
            with (([o_base_ derived0 base0] ++ l) ++ s ++ r).
            apply roff_rw_uncons_help; simpl; (done || lia).
          }
          {
            case_match.
            {
              destruct a. subst.
              apply rtc_l with
                (y:= l ++ t ++ r).
              {
                exists [], (l ++ t ++ r), [o_base_ derived base; o_derived_ base derived], [].
                split. done.
                split. done.
                constructor.
              }
              { apply roff_rw_uncons_help; (done || lia). }
            }
            {
              apply roff_rw_cong_cons.
              change (o_derived_ base0 derived0 :: l ++ t ++ r)
              with (([o_derived_ base0 derived0] ++ l) ++ t ++ r).
              change (o_derived_ base0 derived0 :: l ++ s ++ r)
              with (([o_derived_ base0 derived0] ++ l) ++ s ++ r).
              apply roff_rw_uncons_help; simpl; (done || lia).
            }
          }
        }
      }
      {
        destruct l; simpl in *.
        { by apply roff_rw_uncons_cons_der. }
        {
          destruct r0; simpl in *;
          simp normalize.
          {
            apply roff_rw_cong_cons.
            apply roff_rw_cong_cons.
            apply roff_rw_uncons_help; (done || lia).
          }
          {
            apply roff_rw_cong_cons.
            change (o_sub_ ty z :: l ++ t ++ r)
            with (([o_sub_ ty z] ++ l) ++ t ++ r).
            change (o_sub_ ty z :: l ++ s ++ r)
            with (([o_sub_ ty z] ++ l) ++ s ++ r).
            apply roff_rw_uncons_help; simpl; (done || lia).
          }
          {
            case_match.
            {
              destruct a. subst.
              apply rtc_l with
                (y:= l ++ t ++ r).
              {
                exists [], (l ++ t ++ r), [o_derived_ base0 derived0; o_base_ derived0 base0], [].
                split. done.
                split. done.
                constructor.
              }
              { apply roff_rw_uncons_help; (done || lia). }
            }
            {
              apply roff_rw_cong_cons.
              change (o_base_ derived0 base0 :: l ++ t ++ r)
              with (([o_base_ derived0 base0] ++ l) ++ t ++ r).
              change (o_base_ derived0 base0 :: l ++ s ++ r)
              with (([o_base_ derived0 base0] ++ l) ++ s ++ r).
              apply roff_rw_uncons_help; simpl; (done || lia).
            }
          }
          {
            apply roff_rw_cong_cons.
            change (o_derived_ base0 derived0 :: l ++ t ++ r)
            with (([o_derived_ base0 derived0] ++ l) ++ t ++ r).
            change (o_derived_ base0 derived0 :: l ++ s ++ r)
            with (([o_derived_ base0 derived0] ++ l) ++ s ++ r).
            apply roff_rw_uncons_help; simpl; (done || lia).
          }
        }
      }
    Qed.

    Lemma roff_rw_uncons :
      ∀ l r s t e,
        roff_canon e ->
        roff_rw (l ++ s ++ r) e ->
        roff_rw_local s t ->
        roff_rw (l ++ t ++ r) e.
    Proof.
      move=> l r s t e Hc H1 H2.
      assert (roff_rw (l ++ s ++ r) e /\ roff_canon e) by done.
      rewrite -norm_rel in H. subst. clear - H2.
      by apply: roff_rw_uncons_help.
    Qed.

    Example no_canon_rw_bwd_false :
      ¬(
        ∀ o1 o2 o2' o3,
          roff_rw o2 o2' ->
          roff_rw (o1 ++ o2) o3 ->
          roff_rw (o1 ++ o2') o3
      ).
    Proof.
      move=> H.
      specialize (H []). simpl in *.
      specialize (H
        [o_sub_ Tint 2; o_sub_ Tint 2]
        [o_sub_ Tint 4]
        [o_sub_ Tint 2; o_sub_ Tint 2]
      ).
      assert (roff_rw [o_sub_ Tint 4] [o_sub_ Tint 2; o_sub_ Tint 2]).
      {
        apply: H.
        {
          apply roff_rw_sub_sub.
          done.
        }
        { done. }
      }
      clear H.
      remember [o_sub_ Tint 4].
      remember [o_sub_ Tint 2; o_sub_ Tint 2].
      destruct H0.
      { subst. done. }
      {
        subst.
        move: H => [l [r [s [t [H1 [H2 H3]]]]]].
        subst.
        assert (l = []).
        {
          destruct H3; simpl in *;
          destruct l; simpl in *;
          try done; inversion H1;
          destruct l; simpl in *;
          done.
        }
        subst. simpl in *.
        destruct H3; inversion H1.
      }
    Qed.

    Lemma rw_bwd_r :
      ∀ o1 o2 o2' o3,
        roff_canon o3 ->
        roff_rw o2 o2' ->
        roff_rw (o1 ++ o2) o3 ->
        roff_rw (o1 ++ o2') o3.
    Proof.
      move=> o1 o2 o2' o3 Hc H1 H2.
      induction H1. done.
      move: H => [l [r [s [t [Hx [Hy Hrw]]]]]].
      subst. apply: IHrtc. rewrite app_assoc.
      apply: roff_rw_uncons. 3: done.
      { done. }
      { by rewrite -app_assoc. }
    Qed.

    Lemma norm_absorb_l :
      ∀ o1 o2,
        normalize (o1 ++ normalize o2) = normalize (o1 ++ o2).
    Proof.
      move=> o1 o2.
      rewrite norm_rel.
      split.
      {
        remember (normalize o2) as o2n.
        symmetry in Heqo2n. rewrite norm_rel in Heqo2n.
        remember (normalize (o1 ++ o2)) as ocn.
        symmetry in Heqocn. rewrite norm_rel in Heqocn.
        move: Heqo2n => [Hrw0 Hc0].
        move: Heqocn => [Hrw1 Hc1].
        apply: rw_bwd_r; done.
      }
      { apply: norm_canon. }
    Qed.

    Lemma rw_bwd_l :
      ∀ o1 o1' o2 o3,
        roff_canon o3 ->
        roff_rw o1 o1' ->
        roff_rw (o1 ++ o2) o3 ->
        roff_rw (o1' ++ o2) o3.
    Proof.
      move=> o1 o1' o2 o3 Hc H1 H2.
      induction H1. done.
      apply: IHrtc.
      move: H => [l [r [s [t [Hx [Hy Hrw]]]]]].
      subst. repeat rewrite -app_assoc.
      apply: roff_rw_uncons. 3: done.
      { done. }
      { by repeat rewrite -app_assoc in H2. }
    Qed.

    Lemma norm_absorb_r :
      ∀ o1 o2,
        normalize (normalize o1 ++ o2) = normalize (o1 ++ o2).
    Proof.
      move=> o1 o2.
      rewrite norm_rel.
      split.
      {
        remember (normalize o1) as o1n.
        symmetry in Heqo1n. rewrite norm_rel in Heqo1n.
        remember (normalize (o1 ++ o2)) as ocn.
        symmetry in Heqocn. rewrite norm_rel in Heqocn.
        move: Heqo1n => [Hrw0 Hc0].
        move: Heqocn => [Hrw1 Hc1].
        apply: rw_bwd_l; done.
      }
      { apply: norm_canon. }
    Qed.

  End norm_lemmas.

  Inductive root_ptr : Set :=
  | nullptr_
  | global_ptr_ (tu : translation_unit_canon) (o : obj_name)
  | fun_ptr_ (tu : translation_unit_canon) (o : obj_name)
  | alloc_ptr_ (a : alloc_id) (va : vaddr).
  Inductive ptr_ : Set :=
  | invalid_ptr_
  | offset_ptr (p : root_ptr) (o : offset).
  Definition ptr := ptr_.
  #[global] Instance ptr_eq_dec : EqDecision ptr.
  Admitted.
  #[global] Instance ptr_countable : Countable ptr.
  Admitted.

  Program Definition __offset_ptr (p : ptr) (o : offset) : ptr :=
    match p with
    | invalid_ptr_ => invalid_ptr_
    | offset_ptr rp ro => offset_ptr rp (normalize (ro ++ o))
    end.
  Next Obligation.
    (* move=> _ o _ ro. *)
    apply: norm_canon.
    exact: H.
  Qed.

  Program Definition __o_dot (o1 o2 : offset) : offset :=
    normalize (o1 ++ o2).
  Next Obligation.
    (* move=> _ o _ ro. *)
    apply: norm_canon.
    exact: H.
  Qed.

  Include PTRS_SYNTAX_MIXIN.

  Lemma sig_eq {A} {P : A -> Prop} :
  ∀ (x y : A) (p : P x) (q : P y),
    x = y ->
    x ↾ p = y ↾ q.
  Proof.
    move=> x y p q H.
    subst. f_equal.
    apply: irr.
  Qed.

  Program Definition o_id : offset :=
    [].
  Next Obligation.
    by apply: nil_canon.
  Qed.

  #[local] Ltac UNFOLD_dot := rewrite _dot.unlock/DOT_dot/=.

  Lemma id_dot : LeftId (=) o_id o_dot.
  Proof.
    UNFOLD_dot.
    move=> [o H].
    rewrite /o_id /__o_dot.
    simpl. apply: sig_eq.
    by apply norm_invol.
  Qed.

  Lemma dot_id : RightId (=) o_id o_dot.
  Proof.
    UNFOLD_dot.
    move=> [o H].
    rewrite /o_id /__o_dot.
    simpl. apply: sig_eq.
    by rewrite app_nil_r norm_invol.
  Qed.

  Lemma dot_assoc : Assoc (=) o_dot.
  Proof.
    UNFOLD_dot.
    move=> [o1 H1] [o2 H2] [o3 H3].
    rewrite /o_id /__o_dot.
    simpl. apply: sig_eq.
    by rewrite norm_absorb_l norm_absorb_r app_assoc.
  Qed.

  Lemma offset_ptr_id :
    ∀ p : ptr,
      p ,, o_id = p.
  Proof.
    move=> [| r [o H]]; UNFOLD_dot.
    { easy. }
    {
      f_equal. apply: sig_eq.
      by rewrite app_nil_r norm_invol.
    }
  Qed.

  Lemma offset_ptr_dot :
    ∀ (p : ptr) o1 o2,
      p ,, (o1 ,, o2) = p ,, o1 ,, o2.
  Proof.
    move=> [| r o]; UNFOLD_dot.
    { easy. }
    {
      move=> [o1 H1] [o2 H2].
      simpl. f_equal. apply: sig_eq.
      by rewrite norm_absorb_l norm_absorb_r app_assoc.
    }
  Qed.

  Program Definition nullptr : ptr :=
    offset_ptr nullptr_ [].
  Next Obligation.
  Proof.
    by apply: nil_canon.
  Qed.

  Definition invalid_ptr : ptr :=
    invalid_ptr_.

  Program Definition global_ptr (tu : translation_unit) (n : name) : ptr :=
    offset_ptr (global_ptr_ (tu_to_canon tu) n) [].
  Next Obligation.
    (* move=> _ _. *)
    by apply: nil_canon.
  Qed.

  Lemma global_ptr_nonnull :
    ∀ tu o,
      global_ptr tu o ≠ nullptr.
  Proof.
    by done.
  Qed.

  (* Definition eval_raw_offset_seg σ (ro : raw_offset_seg) : option Z :=
    match ro with
    | o_field_ f => o_field_off σ f
    | o_sub_ ty z => o_sub_off σ ty z
    | o_base_ derived base => o_base_off σ derived base
    | o_derived_ base derived => o_derived_off σ base derived
    | o_invalid_ => None
    end.

  Definition mk_offset_seg σ (ro : raw_offset_seg) : offset_seg :=
    match eval_raw_offset_seg σ ro with
    | None => (o_invalid_, 0%Z)
    | Some off => (ro, off)
    end. *)

  Program Definition o_field (f : field) : offset :=
    [o_field_ f].
  Next Obligation.
    (* move=> σ f. *)
    apply: singleton_offset_canon. 2: exact: H.
    clear H. by move=> [ty H].
  Qed.

  Program Definition o_base derived base : offset :=
    [o_base_ derived base].
  Next Obligation.
    (* move=> σ der base. *)
    apply: singleton_offset_canon. 2: exact: H.
    clear H. by move=> [ty H].
  Qed.

  Program Definition o_derived base derived : offset :=
    [o_derived_ base derived].
  Next Obligation.
    (* move=> σ base der. *)
    apply: singleton_offset_canon. 2: exact: H.
    clear H. by move=> [ty H].
  Qed.

  Program Definition o_sub ty z : offset :=
    if decide (z = 0)%Z then
      o_id
    else
      [o_sub_ ty z].
  Next Obligation.
    (* move=> σ ty z znz. *)
    apply: singleton_offset_canon. 2: exact: H.
    clear - n. move=> [ty' H]. congruence.
  Qed.

  #[global] Notation "p ., o" := (_dot p (o_field _ o))
    (at level 11, left associativity, only parsing) : stdpp_scope.
    #[global] Notation "p .[ t ! n ]" := (_dot p (o_sub _ t n))
      (at level 11, left associativity, format "p  .[  t  '!'  n  ]") : stdpp_scope.
    #[global] Notation ".[ t ! n ]" := (o_sub _ t n) (at level 11, no associativity, format ".[  t  !  n  ]") : stdpp_scope.

  Lemma o_sub_0 :
    ∀ ty, o_sub ty 0 = o_id.
  Proof.
    move=> ty.
    rewrite /o_sub.
    by case_match.
  Qed.

  Lemma o_base_derived :
    ∀ (p : ptr) base derived,
      p ,, o_base derived base ,, o_derived base derived = p.
  Proof.
    UNFOLD_dot.
    rewrite /__offset_ptr.
    move=> [| rp [o H]] base der.
    { done. }
    {
      f_equal. simpl. apply: sig_eq.
      rewrite norm_absorb_r -app_assoc norm_rel.
      split.
      {
        simpl. apply: rtc_l. 2: done.
        exists o, [], [o_base_ der base; o_derived_ base der], [].
        split. done.
        split. by repeat rewrite app_nil_r.
        constructor.
      }
      { done. }
    }
  Qed.

  Lemma o_derived_base :
    ∀ (p : ptr) base derived,
      p ,, o_derived base derived ,, o_base derived base = p.
  Proof.
    UNFOLD_dot.
    rewrite /__offset_ptr.
    move=> [| rp [o H]] base der.
    { done. }
    {
      f_equal. simpl. apply: sig_eq.
      rewrite norm_absorb_r -app_assoc norm_rel.
      split.
      {
        simpl. apply: rtc_l. 2: done.
        exists o, [], [o_derived_ base der; o_base_ der base], [].
        split. done.
        split. by repeat rewrite app_nil_r.
        constructor.
      }
      { done. }
    }
  Qed.

  Lemma o_dot_sub :
    ∀ i j ty,
      o_sub ty i ,, o_sub ty j = o_sub ty (i + j).
  Proof.
    UNFOLD_dot.
    move=> i j ty.
    rewrite /__o_dot /o_sub.
    repeat case_match;
    subst; try lia;
    rewrite /o_id; simpl in *;
    apply: sig_eq; try done;
    simp normalize;
    repeat case_match; try done.
    { by replace (i + 0) with i by lia. }
  Qed.

  Definition ptr_alloc_id (p : ptr) : option alloc_id :=
    match p with
    | offset_ptr (alloc_ptr_ a _) _ => Some a
    | _ => None
    end.
  
  Definition null_alloc_id : alloc_id.
  Admitted.
  Lemma ptr_alloc_id_nullptr :
    ptr_alloc_id nullptr = Some null_alloc_id.
  Admitted.

  Lemma ptr_alloc_id_offset :
    ∀ p o,
      is_Some (ptr_alloc_id (p ,, o)) ->
      ptr_alloc_id (p ,, o) = ptr_alloc_id p.
  Proof.
    UNFOLD_dot.
    rewrite /ptr_alloc_id.
    move=> [| r o1] o2; simpl.
    { done. }
    { by destruct r. }
  Qed.

  Definition eval_offset_seg (σ : genv) (o : raw_offset_seg) : option Z :=
    match o with
    | o_field_ f => o_field_off σ f
    | o_sub_ ty i => o_sub_off σ ty i
    | o_base_ der base => o_base_off σ der base
    | o_derived_ base der => o_derived_off σ base der
    end.

  Fixpoint eval_offset_aux (σ : genv) (os : list raw_offset_seg) : option Z :=
    match os with
    | [] => Some 0
    | o :: os =>
      eval_offset_seg σ o ≫= λ o,
      eval_offset_aux σ os ≫= λ os,
      Some (o + os)
    end.

  Definition eval_offset (σ : genv) (os : offset) : option Z :=
    eval_offset_aux σ (`os).

  Lemma eval_o_sub :
    ∀ σ ty (i : Z),
      is_Some (size_of σ ty) ->
      eval_offset σ (o_sub ty i) = (fun n => Z.of_N n * i) <$> size_of σ ty.
  Proof.
    rewrite /eval_offset /o_sub.
    move=> σ ty i [n Hsome].
    case_match; subst; simpl.
    {
      rewrite Hsome. simpl.
      by replace (n * 0) with 0 by lia.
    }
    {
      rewrite /o_sub_off Hsome. simpl.
      by replace (i * n + 0) with (n * i) by lia.
    }
  Qed.

  Lemma eval_o_field :
    ∀ σ n cls st,
      glob_def σ cls = Some (Gstruct st) ->
      st.(s_layout) = POD \/ st.(s_layout) = Standard ->
      eval_offset σ (o_field (Field cls n)) = offset_of σ cls n.
  Proof.
  Admitted.

  Lemma eval_offset_resp_norm :
    ∀ σ os,
      roff_canon os ->
      eval_offset_aux σ (normalize os) = eval_offset_aux σ os.
  Proof.
    move=> σ os.
    rewrite canon_syn_sem_eqv.
    move=> Hc. induction Hc;
    simp normalize.
    { done. }
    {
      destruct o;
      simp normalize;
      simpl; try done.
      case_match; subst; simpl.
      { exfalso. apply: H. repeat eexists. }
      { done. }
    }
    {
      destruct o; simp normalize in *;
      repeat case_match; subst; try done;
      simpl in *; f_equal;
      try (extensionality o;rewrite IHHc; done).
      { exfalso. apply H. repeat eexists. }
    }
    { simpl. by rewrite IHHc. }
    {
      destruct o;
      simp normalize in *;
      try case_match; simpl in *;
      try rewrite IHHc; try done.
      { exfalso. apply H. destruct a. by subst. }
    }
    {
      destruct o;
      simp normalize in *;
      try case_match; simpl in *;
      try rewrite IHHc; try done.
      { exfalso. apply H. destruct a. by subst. }
    }
  Qed.

  Lemma simp_norm_canon_sub :
    ∀ ty i o os,
      i ≠ 0 ->
      ¬(∃ i ty, o = o_sub_ ty i) ->
      normalize (o_sub_ ty i :: o :: os) = o_sub_ ty i :: normalize (o :: os).
  Proof.
    move=> ty i o os Hne H.
    destruct o; simpl;
    simp normalize;
    repeat case_match;
    subst; try done.
    exfalso. apply H.
    repeat eexists.
  Qed.

  Lemma simp_norm_canon_base :
    ∀ der base o os,
      o ≠ o_derived_ base der ->
      normalize (o_base_ der base :: o :: os) = o_base_ der base :: normalize (o :: os).
  Proof.
    move=> der base o os Hne.
    destruct o; simpl;
    simp normalize;
    repeat case_match;
    subst; try done.
    exfalso. apply Hne.
    destruct a. by subst.
  Qed.

  Lemma simp_norm_canon_der :
    ∀ base der o os,
      o ≠ o_base_ der base ->
      normalize (o_derived_ base der :: o :: os) = o_derived_ base der :: normalize (o :: os).
  Proof.
    move=> base der o os Hne.
    destruct o; simpl;
    simp normalize;
    repeat case_match;
    subst; try done.
    exfalso. apply Hne.
    destruct a. by subst.
  Qed.

  Lemma bind_assoc {A} :
    ∀ (m : option A) (k1 k2 : A -> option A),
      (m >>= k1) >>= k2 = m >>= λ x, k1 x >>= k2.
  Proof.
    move=> m k1 k2.
    by destruct m.
  Qed.

  (* TODO:
    this doesn't quite work. imagine this case for instance:
      o1 = [o_sub_ FOO 2]
      o2 = [o_sub_ FOO -2]
    the goal is then
      eval_offset_aux σ (normalize [o_sub_ FOO 2; o_sub_ FOO -2])
        =
      add_opt (eval_offset_aux σ [o_sub_ FOO 2]) (eval_offset_aux σ [o_sub_ FOO -2])
    key here: let's say FOO is an *invalid* type, as in size_ty σ ty
    will compute to None. in this case, the goal is this:
      eval_offset_aux σ o_id = add_opt None None
    which further computes to
      Some 0 = None
    this happens because offset normalization eagerly reduces o_sub_ ty 0 to
    o_id, even if ty is an invalid type!
  *)
  Equations eval_offset_dot_aux σ (o1 o2 : raw_offset)
      (H : roff_canon o1)
      (H0 : roff_canon o2) :
      eval_offset_aux σ (normalize (o1 ++ o2)) =
      add_opt (eval_offset_aux σ o1) (eval_offset_aux σ o2)
      by wf (length o1) lt :=
      eval_offset_dot_aux σ o1 o2 := _.
  Next Obligation.
    unfold add_opt, liftM2 in *.
    move: H H0.
    do 2 rewrite canon_syn_sem_eqv.
    move=> Hc1 Hc2. destruct Hc1; simpl.
    {
      rewrite eval_offset_resp_norm.
      { by destruct (eval_offset_aux σ o2). }
      { by rewrite canon_syn_sem_eqv. }
    }
    {
      destruct o; simp normalize;
      simpl.
      {
        rewrite eval_offset_resp_norm.
        2:{ by rewrite canon_syn_sem_eqv. }
        destruct (o_field_off σ f); simpl.
        2:{ done. }
        f_equal. extensionality os.
        replace (z + os) with (z + 0 + os) by lia.
        done.
      }
      {
        destruct Hc2; simp normalize;
        repeat case_match; subst;
        try match goal with
        | H : ¬∃ ty, o_sub_ _ 0 = o_sub_ ty 0 |- _ =>
          exfalso; apply H; repeat eexists
        end; simpl.
        {
          destruct (o_sub_off σ ty z); simpl.
          { by replace (z0 + 0 + 0) with (z0 + 0) by lia. }
          { done. }
        }
        {
          destruct o; simpl;
          simp normalize;
          repeat case_match;
          simpl; subst;
          try match goal with
          | H : ¬∃ ty, o_sub_ _ 0 = o_sub_ ty 0 |- _ =>
            exfalso; apply H; repeat eexists
          end;
          repeat (
            rewrite bind_assoc;
            simpl; f_equal
          ); simpl.
          {
            destruct (o_field_off σ f); simpl;
            extensionality o. 2: done.
            replace (o + 0 + (z0 + 0))
            with    (o + (z0 + 0))
            by lia.
            done.
          }
          all: admit.
        }
        all: admit.
      }
      {
        admit.
      }
      {
        admit.
      }
    }
    {
      rewrite simp_norm_canon_sub. 2: done. simpl.
      change (normalize (o :: os ++ o2))
      with   (normalize ((o :: os) ++ o2)).
      rewrite eval_offset_dot_aux.
      2:{ simpl. lia. }
      2:{ by rewrite canon_syn_sem_eqv. }
      2:{ by rewrite canon_syn_sem_eqv. }
      destruct (o_sub_off σ ty i); simpl.
      2:{ done. }
      destruct (eval_offset_seg σ o); simpl.
      2:{ done. }
      destruct (eval_offset_aux σ os); simpl.
      2:{ done. }
      destruct (eval_offset_aux σ o2); simpl.
      2:{ done. }
      {
        replace (z + (z0 + z1 + z2))
        with    (z + (z0 + z1) + z2)
        by lia.
        done.
      }
      { done. }
    }
    {
      simp normalize. simpl.
      rewrite eval_offset_dot_aux.
      2:{ simpl. lia. }
      2:{ by rewrite canon_syn_sem_eqv. }
      2:{ by rewrite canon_syn_sem_eqv. }
      destruct (o_field_off σ f); simpl.
      2:{ done. }
      destruct (eval_offset_aux σ os); simpl.
      2:{ done. }
      destruct (eval_offset_aux σ o2); simpl.
      2:{ done. }
      replace (z + (z0 + z1))
      with    (z + z0 + z1)
      by lia.
      { done. }
    }
    {
      rewrite simp_norm_canon_base. 2: done. simpl.
      change (normalize (o :: os ++ o2))
      with   (normalize ((o :: os) ++ o2)).
      rewrite eval_offset_dot_aux.
      2:{ simpl. lia. }
      2:{ by rewrite canon_syn_sem_eqv. }
      2:{ by rewrite canon_syn_sem_eqv. }
      destruct (o_base_off σ der base); simpl.
      2:{ done. }
      destruct (eval_offset_seg σ o); simpl.
      2:{ done. }
      destruct (eval_offset_aux σ os); simpl.
      2:{ done. }
      destruct (eval_offset_aux σ o2); simpl.
      2:{ done. }
      {
        replace (z + (z0 + z1 + z2))
        with    (z + (z0 + z1) + z2)
        by lia.
        done.
      }
    }
    {
      rewrite simp_norm_canon_der. 2: done. simpl.
      change (normalize (o :: os ++ o2))
      with   (normalize ((o :: os) ++ o2)).
      rewrite eval_offset_dot_aux.
      2:{ simpl. lia. }
      2:{ by rewrite canon_syn_sem_eqv. }
      2:{ by rewrite canon_syn_sem_eqv. }
      destruct (o_derived_off σ base der); simpl.
      2:{ done. }
      destruct (eval_offset_seg σ o); simpl.
      2:{ done. }
      destruct (eval_offset_aux σ os); simpl.
      2:{ done. }
      destruct (eval_offset_aux σ o2); simpl.
      2:{ done. }
      {
        replace (z + (z0 + z1 + z2))
        with    (z + (z0 + z1) + z2)
        by lia.
        done.
      }
    }
  Admitted.

  Lemma eval_offset_dot :
    ∀ σ (o1 o2 : offset),
      eval_offset σ (o1 ,, o2) =
      add_opt (eval_offset σ o1) (eval_offset σ o2).
  Proof.
    UNFOLD_dot. rewrite /eval_offset.
    move=> σ [o1 H1] [o2 H2]. simpl.
    induction o1; simpl.

  Definition ptr_vaddr (p : ptr) : option vaddr :=
    match p with
    | invalid_ptr_ => None
    | offset_ptr p (exist _ o _) =>
      foldr
        (λ off ova, Some 1)
        (match p with
        | nullptr_ => Some 0%N
        | fun_ptr_ tu o => Some (global_ptr_encode_vaddr o)
        | global_ptr_ tu o => Some (global_ptr_encode_vaddr o)
        | alloc_ptr_ aid va => Some va
        end)
        o
    end.
End PTRS_IMPL.
