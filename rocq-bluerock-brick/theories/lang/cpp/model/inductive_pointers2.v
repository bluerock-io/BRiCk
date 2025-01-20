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
  | o_derived_ (base derived : globname)
  | o_invalid_.
  #[local] Instance raw_offset_seg_eq_dec : EqDecision raw_offset_seg.
  Proof. solve_decision. Defined.
  #[global] Declare Instance raw_offset_seg_countable : Countable raw_offset_seg.

  Definition offset_seg : Set := raw_offset_seg * Z.
  #[local] Instance offset_seg_eq_dec : EqDecision offset_seg := _.
  #[local] Instance offset_seg_countable : Countable offset_seg := _.

  Definition raw_offset := list offset_seg.
  #[local] Instance raw_offset_eq_dec : EqDecision raw_offset := _.
  #[local] Instance raw_offset_countable : Countable raw_offset := _.

  Variant roff_rw_local : raw_offset -> raw_offset -> Prop :=
  | CanonDerBase der base o1 o2 :
    roff_rw_local
      [(o_derived_ base der, o1); (o_base_ der base, o2)]
      []
  | CanonBaseDer der base o1 o2 :
    roff_rw_local
      [(o_base_ der base, o1); (o_derived_ base der, o2)]
      []
  | CanonSubZero ty o :
    roff_rw_local
      [(o_sub_ ty 0, o)]
      []
  | CanonSubMerge ty n1 n2 o1 o2 :
      roff_rw_local
        [(o_sub_ ty n1, o1); (o_sub_ ty n2, o2)]
        [(o_sub_ ty (n1 + n2), o1 + o2)].

  Definition roff_rw_global (os1 os2 : raw_offset) :=
    ∃ l r s t,
      os1 = l ++ s ++ r /\
      os2 = l ++ t ++ r /\
      roff_rw_local s t.

  Definition roff_rw := rtc roff_rw_global.
  Definition roff_canon := nf roff_rw_global.
  
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
  | (o_derived_ base1 der1, o1) :: (o_base_ der2 base2, o2) :: os =>
    if decide (base1 = base2 /\ der1 = der2) then
      normalize os
    else
      (o_derived_ base1 der1, o1) :: normalize ((o_base_ der2 base2, o2) :: os)
  | (o_base_ der2 base2, o2) :: (o_derived_ base1 der1, o1) :: os =>
    if decide (base1 = base2 /\ der1 = der2) then
      normalize os
    else
      (o_base_ der2 base2, o2) :: normalize ((o_derived_ base1 der1, o1) :: os)
  | (o_sub_ ty1 i1, o1) :: (o_sub_ ty2 i2, o2) :: os =>
    if decide (i1 = 0) then
      normalize ((o_sub_ ty2 i2, o2) :: os)
    else if decide (ty1 = ty2) then
      normalize ((o_sub_ ty1 (i1 + i2), o1 + o2) :: os)
    else
      (o_sub_ ty1 i1, o1) :: normalize ((o_sub_ ty2 i2, o2) :: os)
  | (o_sub_ ty i, o) :: os =>
    if decide (i = 0) then
      normalize os
    else
    (o_sub_ ty i, o) :: normalize os
  | o :: os => o :: normalize os.

  Goal normalize [(o_sub_ Tint (-2), (-2)); (o_sub_ Tint 2, 2)] = [].
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
          apply: rtc_l. 2: exact: IHHrw1.
          move: H => [l [r [s [t [H1 [H2 H3]]]]]].
          subst. exists (x ++ l), r, s, t.
          split. by rewrite app_assoc.
          split. by rewrite app_assoc.
          done.
        }
      }
      {
        apply: rtc_l. 2: exact IHHrw0.
        move: H => [l [r [s [t [H1 [H2 H3]]]]]].
        subst. exists l, (r ++ ol2), s, t.
        split. by repeat rewrite -app_assoc.
        split. by repeat rewrite -app_assoc.
        done.
      }
    Qed.

    Lemma norm_sound :
      ∀ os, roff_rw os (normalize os).
    Proof.
      move=> os.
      funelim (normalize os);
      simp normalize in *.
      { constructor. }
      {
        by apply roff_rw_cong with
          (ol1:=[(o_field_ f, z)])
          (or1:=[(o_field_ f, z)]).
      }
      {
        case_match.
        {
          subst.
          apply: rtc_l. 2: done.
          exists [], [], [(o_sub_ ty 0, o)], [].
          split. easy.
          split. easy.
          constructor.
        }
        { done. }
      }
      {
        case_match.
        {
          subst.
          apply: rtc_l. 2: by apply: H.
          exists [], ((o_field_ f, z1) :: l), [(o_sub_ ty 0, o)], [].
          split. easy.
          split. easy.
          constructor.
        }
        {
          apply roff_rw_cong with
            (ol1:=[(o_sub_ ty i, o)])
            (or1:=[(o_sub_ ty i, o)]).
          { done. }
          { by apply H0. }
        }
      }
      {
        case_match.
        {
          subst.
          apply: rtc_l. 2: by apply H.
          exists [], ((o_sub_ ty2 i2, o2) :: os), [(o_sub_ ty1 0, o1)], [].
          split. easy.
          split. easy. 
          constructor.
        }
        case_match.
        {
          subst.
          apply: rtc_l. 2: by apply H0.
          exists [], os, [(o_sub_ ty2 i1, o1); (o_sub_ ty2 i2, o2)], [(o_sub_ ty2 (i1 + i2), o1 + o2)].
          split. easy.
          split. easy.
          constructor.
        }
        {
          apply roff_rw_cong with
            (ol1:=[(o_sub_ ty1 i1, o1)])
            (or1:=[(o_sub_ ty1 i1, o1)]).
          { done. }
          { by apply H1. }
        }
      }
      {
        case_match.
        {
          subst.
          apply: rtc_l. 2: by apply: H.
          exists [], ((o_base_ derived base, z1) :: l), [(o_sub_ ty 0, o)], [].
          split. easy.
          split. easy.
          constructor.
        }
        {
          apply roff_rw_cong with
            (ol1:=[(o_sub_ ty i, o)])
            (or1:=[(o_sub_ ty i, o)]).
          { done. }
          { by apply H0. }
        }
      }
      {
        case_match.
        {
          subst.
          apply: rtc_l. 2: by apply: H.
          exists [], ((o_derived_ base0 derived0, z1) :: l), [(o_sub_ ty 0, o)], [].
          split. easy.
          split. easy.
          constructor.
        }
        {
          apply roff_rw_cong with
            (ol1:=[(o_sub_ ty i, o)])
            (or1:=[(o_sub_ ty i, o)]).
          { done. }
          { by apply H0. }
        }
      }
      {
        case_match.
        {
          subst.
          apply: rtc_l. 2: by apply: H.
          exists [], ((o_invalid_, z1) :: l), [(o_sub_ ty 0, o)], [].
          split. easy.
          split. easy.
          constructor.
        }
        {
          apply roff_rw_cong with
            (ol1:=[(o_sub_ ty i, o)])
            (or1:=[(o_sub_ ty i, o)]).
          { done. }
          { by apply H0. }
        }
      }
      { done. }
      {
        apply roff_rw_cong with
          (ol1:=[(o_base_ derived base, z)])
          (or1:=[(o_base_ derived base, z)]).
        { done. }
        { done. }
      }
      {
        apply roff_rw_cong with
          (ol1:=[(o_base_ derived base, z)])
          (or1:=[(o_base_ derived base, z)]).
        { done. }
        { done. }
      }
      {
        apply roff_rw_cong with
          (ol1:=[(o_base_ derived base, z)])
          (or1:=[(o_base_ derived base, z)]).
        { done. }
        { done. }
      }
      {
        case_match.
        {
          clear H1.
          move: a => [Hbase Hder].
          subst.
          apply: rtc_l. 2: by apply: H.
          exists [], os, [(o_base_ der2 base2, o2); (o_derived_ base2 der2, o1)], [].
          split. easy.
          split. easy.
          constructor.
        }
        {
          apply roff_rw_cong with
          (ol1:=[(o_base_ der2 base2, o2)])
          (or1:=[(o_base_ der2 base2, o2)]).
        { done. }
        { by apply H0. }
        }
      }
      {
        apply roff_rw_cong with
          (ol1:=[(o_base_ derived base, z)])
          (or1:=[(o_base_ derived base, z)]).
        { done. }
        { done. }
      }
      { done. }
      {
        
        apply roff_rw_cong with
          (ol1:=[(o_derived_ base0 derived0, z)])
          (or1:=[(o_derived_ base0 derived0, z)]).
        { done. }
        { done. }
      }
      {
        apply roff_rw_cong with
          (ol1:=[(o_derived_ base0 derived0, z)])
          (or1:=[(o_derived_ base0 derived0, z)]).
        { done. }
        { done. }
      }
      {
        {
          case_match.
          {
            clear H1.
            move: a => [Hbase Hder].
            subst.
            apply: rtc_l. 2: by apply: H.
            exists [], os, [(o_derived_ base2 der2, o1); (o_base_ der2 base2, o2)], [].
            split. easy.
            split. easy.
            constructor.
          }
          {
            apply roff_rw_cong with
              (ol1:=[(o_derived_ base1 der1, o1)])
              (or1:=[(o_derived_ base1 der1, o1)]).
          { done. }
          { by apply H0. }
          }
        }
      }
      {
        apply roff_rw_cong with
          (ol1:=[(o_derived_ base0 derived0, z)])
          (or1:=[(o_derived_ base0 derived0, z)]).
        { done. }
        { done. }
      }
      {
        apply roff_rw_cong with
          (ol1:=[(o_derived_ base0 derived0, z)])
          (or1:=[(o_derived_ base0 derived0, z)]).
        { done. }
        { done. }
      }
      {
        apply roff_rw_cong with
          (ol1:=[(o_invalid_, z)])
          (or1:=[(o_invalid_, z)]).
        { done. }
        { done. }
      }
    Qed.

    Lemma norm_complete :
      ∀ o1 o2,
        roff_rw o1 o2 ->
        roff_canon o2 ->
        normalize o1 = o2.
    Proof.
      move=> o1 o2 Hrw Hc.
      admit.
    Admitted.

    Lemma norm_canon :
      ∀ os, roff_canon (normalize os).
    Proof.
      (* rewrite
        /roff_canon /nf /red
        /roff_rw_global.
      move=> os [o [l [r [s [t [H1 [H2 H3]]]]]]].
      subst. funelim (normalize os); simp normalize in *.
      {
        destruct l, s, r.
        { inversion H3. }
        all: done.
      }
      {
        assert (∃ l', l = (o_field_ f, z) :: l').
        {
          destruct l; simpl in *.
          {
            destruct H3; simpl in *;
            inversion H1.
          }
          {
            inversion H1.
            by repeat eexists.
          }
        }
        move: H0 => [l' Hl]. subst.
        simpl in *. inversion H1.
        apply: H. exact: H2. exact H3.
      }
      {
        case_match.
        { apply: H; done. }
        {
          destruct l.
          {
            simpl in *.
            destruct H3;
            simpl in *;
            inversion H1;
            done.
          }
          {
            simpl in H1.
            inversion H1.
            apply: H0; done.
          }
        }
      }
      {
        case_match.
        { apply: H; done. }
        {
          destruct l0.
          {
            simpl in *.
            destruct H3;
            simpl in *;
            inversion H1;
            done.
          }
          {
            simpl in H1.
            inversion H1.
            apply: H0; done.
          }
        }
      }
      {
        case_match.
        { apply: H; done. }
        case_match.
        {
          subst.
          apply: H0; done.
        }
        {
          destruct l.
          {
            simpl in *.
            destruct H3; simpl in *;
            inversion H2; subst.
            { done. }
            {
              induction os; simpl in *;
              simp normalize in *.
              {
                case_match.
                { done. }
                { inversion H9. subst. done. }
              }
              {
                destruct a, r0; simpl in *;
                simp normalize in *; case_match;
                inversion H9; subst; try done.
              }
            }
          }
          {
            simpl in *.
            inversion H2. subst.
            apply: H1; done.
          }
        }
      }
      {
        case_match.
        { apply: H; done. }
        {
          destruct l0.
          {
            simpl in *.
            destruct H3; simpl in *;
            inversion H1; subst.
            { done. }
            { admit. }
          }
          {
            simpl in H1.
            inversion H1.
            apply: H0; done.
          }
        }
      }
      {
        case_match.
        { apply: H; done. }
        {
          destruct l0.
          {
            simpl in *.
            destruct H3; simpl in *;
            inversion H1; subst.
            { done. }
            { admit. }
          }
          {
            simpl in H1.
            inversion H1.
            apply: H0; done.
          }
        }
      }
      {
        case_match.
        { apply: H; done. }
        {
          destruct l0.
          {
            simpl in *.
            destruct H3; simpl in *;
            inversion H1; subst.
            { done. }
          }
          {
            simpl in H1.
            inversion H1.
            apply: H0; done.
          }
        }
      }
      {
        destruct l; simpl in *.
        { destruct H3; done. }
        {
          inversion H1. subst.
          destruct l; simpl in *.
          { destruct H3; done. }
          { done. }
        }
      }
      {
        destruct l0; simpl in *.
        { destruct H3; done. }
        {
          inversion H1.
          apply: H; done.
        }
      } *)
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

    Lemma rw_bwd_r :
      ∀ o1 o2 o2' o3,
        roff_rw o2 o2' ->
        roff_rw (o1 ++ o2) o3 ->
        roff_rw (o1 ++ o2') o3.
    Proof.
    Admitted.

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
        roff_rw o1 o1' ->
        roff_rw (o1 ++ o2) o3 ->
        roff_rw (o1' ++ o2) o3.
    Proof.
    Admitted.

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

  Inductive root_ptr : Set :=
  | nullptr_
  | global_ptr_ (tu : translation_unit_canon) (o : obj_name)
  | fun_ptr_ (tu : translation_unit_canon) (o : obj_name)
  | alloc_ptr_ (a : alloc_id).
  
  Inductive ptr_ : Set :=
  | invalid_ptr_
  | offset_ptr (p : root_ptr) (o : offset).
  Definition ptr := ptr_.

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

  Lemma singleton_offset_canon :
    ∀ o : offset_seg,
      (¬∃ ty, fst o = o_sub_ ty 0) ->
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

  Definition eval_raw_offset_seg σ (ro : raw_offset_seg) : option Z :=
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
    end.

  Program Definition o_field (σ : genv) (f : field) : offset :=
    [mk_offset_seg σ (o_field_ f)].
  Next Obligation.
    (* move=> σ f. *)
    apply: singleton_offset_canon. 2: exact: H.
    rewrite /mk_offset_seg /eval_raw_offset_seg.
    clear H.
    move=> [ty H]. by destruct (o_field_off σ f).
  Qed.

  Program Definition o_base σ derived base : offset :=
    [mk_offset_seg σ (o_base_ derived base)].
  Next Obligation.
    (* move=> σ der base. *)
    apply: singleton_offset_canon. 2: exact: H.
    rewrite /mk_offset_seg /eval_raw_offset_seg.
    clear H. move=> [ty H]. by destruct (o_base_off σ derived base).
  Qed.

  Program Definition o_derived σ base derived : offset :=
    [mk_offset_seg σ (o_derived_ base derived)].
  Next Obligation.
    (* move=> σ base der. *)
    apply: singleton_offset_canon. 2: exact: H.
    rewrite /mk_offset_seg /eval_raw_offset_seg.
    clear H. move=> [ty H]. by destruct (o_derived_off σ base derived).
  Qed.

  Program Definition o_sub σ ty z : offset :=
    if decide (z = 0)%Z then
      o_id
    else
      [mk_offset_seg σ (o_sub_ ty z)].
  Next Obligation.
    (* move=> σ ty z znz. *)
    apply: singleton_offset_canon. 2: exact: H.
    clear - n. move=> [ty' H].
    unfold mk_offset_seg, eval_raw_offset_seg, o_sub_off in H.
    destruct (size_of σ ty); simpl in *.
    { inversion H. by subst. }
    { easy. }
  Qed.

  #[global] Notation "p ., o" := (_dot p (o_field _ o))
    (at level 11, left associativity, only parsing) : stdpp_scope.
    #[global] Notation "p .[ t ! n ]" := (_dot p (o_sub _ t n))
      (at level 11, left associativity, format "p  .[  t  '!'  n  ]") : stdpp_scope.
    #[global] Notation ".[ t ! n ]" := (o_sub _ t n) (at level 11, no associativity, format ".[  t  !  n  ]") : stdpp_scope.

  Lemma o_sub_0 :
    ∀ σ ty,
      is_Some (size_of σ ty) ->
      o_sub σ ty 0 = o_id.
  Proof.
    move=> σ ty _.
    rewrite /o_sub.
    by case_match.
  Qed.

  Lemma o_base_derived :
    ∀ σ (p : ptr) base derived,
      directly_derives σ derived base ->
      p ,, o_base σ derived base ,, o_derived σ base derived = p.
  Proof.
    UNFOLD_dot.
    rewrite /__offset_ptr.
    move=> σ [| r [o H]] base der [pz Hd].
    { easy. }
    {
      simpl. f_equal. apply: sig_eq.
      rewrite norm_absorb_r -app_assoc norm_rel.
      split. 2: easy. apply: rtc_l. 2: constructor.
      eexists o, [], [mk_offset_seg σ (o_base_ der base); mk_offset_seg σ (o_derived_ base der)], [].
      split. { easy. }
      split. { simpl. by rewrite app_nil_r. }
      rewrite /mk_offset_seg /eval_raw_offset_seg /o_base_off /o_derived_off.
      rewrite Hd. constructor.
    }
  Qed.
  
  Lemma o_derived_base :
    ∀ σ (p : ptr) base derived,
      directly_derives σ derived base ->
      p ,, o_derived σ base derived ,, o_base σ derived base = p.
  Proof.
    UNFOLD_dot.
    rewrite /__offset_ptr.
    move=> σ [| r [o H]] base der [pz Hd].
    { easy. }
    {
      simpl. f_equal. apply: sig_eq.
      rewrite norm_absorb_r -app_assoc norm_rel.
      split. 2: easy. apply: rtc_l. 2: constructor.
      eexists o, [], [mk_offset_seg σ (o_derived_ base der); mk_offset_seg σ (o_base_ der base)], [].
      split. { easy. }
      split. { simpl. by rewrite app_nil_r. }
      rewrite /mk_offset_seg /eval_raw_offset_seg /o_base_off /o_derived_off.
      rewrite Hd. constructor.
    }
  Qed.

  Lemma o_dot_sub :
    ∀ σ i j ty,
      is_Some (size_of σ ty) ->
      (o_sub _ ty i) ,, (o_sub _ ty j) = o_sub _ ty (i + j).
  Proof.
    UNFOLD_dot.
    move=> σ i j ty [sz HSome].
    rewrite /__o_dot /o_sub.
    repeat case_match;
    subst; try lia;
    rewrite /o_id; simpl in *;
    apply: sig_eq;
    try done.
    {
      rewrite /mk_offset_seg /eval_raw_offset_seg /o_sub_off.
      rewrite HSome. simpl. simp normalize. case_match; done.
    }
    {
      rewrite /mk_offset_seg /eval_raw_offset_seg /o_sub_off.
      rewrite HSome; simpl; simp normalize.
      assert (i + 0 = i) by lia.
      case_match.
      { lia. }
      { by rewrite H2. }
    }
    {
      rewrite /mk_offset_seg /eval_raw_offset_seg /o_sub_off.
      rewrite HSome; simpl. simp normalize.
      repeat case_match; done.
    }
    {
      rewrite /mk_offset_seg /eval_raw_offset_seg /o_sub_off.
      rewrite HSome; simpl. simp normalize.
      repeat case_match; subst; try (lia || congruence).
      assert (i * sz + j * sz = (i + j) * sz) by lia.
      by rewrite H5.
    }
  Qed.
End PTRS_IMPL.
