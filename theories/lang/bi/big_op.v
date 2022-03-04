(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

From iris.algebra Require Import list.
From iris.bi Require Import monpred big_op.
From iris.proofmode Require Import proofmode.
Require Import bedrock.prelude.list.

Section big_op.
  Context `{Monoid M o}.
  Implicit Types P : M → Prop.
  Infix "`o`" := o (at level 50, left associativity).

  Section list.
    Context {A : Type}.
    Implicit Types xs : list A.
    Implicit Types f : nat → A → M.

    (** Any [P] compatible with the monoid and with [f] is compatible
        with [big_opL o f] *)
    Lemma big_opL_gen (P : M → Prop) f xs :
      P monoid_unit → (∀ x y, P x → P y → P (x `o` y)) →
      (∀ k x, xs !! k = Some x → P (f k x)) →
      P ([^o list] k↦x ∈ xs, f k x).
    Proof.
      intros ? Hop. elim: xs f => [ |x xs IH] f /= Hf; first done.
      apply Hop; first by apply Hf. apply IH=>k y Hk. by apply Hf.
    Qed.
  End list.
End big_op.

Section big_sepL.
  Context {PROP : bi} {A : Type}.
  Implicit Types xs : list A.
  Implicit Types f g : nat → A → PROP.

  (** In contrast with [big_sepL_ne], the lists need not be equal. *)
  Lemma big_sepL_gen_ne f g l1 l2 n :
    length l1 = length l2 →
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → f k y1 ≡{n}≡ g k y2) →
    ([∗ list] k↦y ∈ l1, f k y)%I ≡{n}≡ ([∗ list] k↦y ∈ l2, g k y)%I.
  Proof.
    intros ? Hf. apply big_opL_gen_proper_2; [done|by apply _| ].
    move=>k. destruct (l1 !! k) eqn:Hl1, (l2 !! k) eqn:Hl2.
    - exact: Hf.
    - apply lookup_lt_Some in Hl1. apply lookup_ge_None_1 in Hl2. lia.
    - apply lookup_ge_None_1 in Hl1. apply lookup_lt_Some in Hl2. lia.
    - done.
  Qed.

  (** In contrast with [big_sepL_proper], the lists need not be equal. *)
  Lemma big_sepL_gen_proper f g l1 l2 :
    length l1 = length l2 →
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → f k y1 ≡ g k y2) →
    ([∗ list] k↦y ∈ l1, f k y)%I ≡ ([∗ list] k↦y ∈ l2, g k y)%I.
  Proof.
    intros ? Hf. apply big_opL_gen_proper_2; [done|by apply _| ].
    move=>k. destruct (l1 !! k) eqn:Hl1, (l2 !! k) eqn:Hl2.
    - exact: Hf.
    - apply lookup_lt_Some in Hl1. apply lookup_ge_None_1 in Hl2. lia.
    - apply lookup_ge_None_1 in Hl1. apply lookup_lt_Some in Hl2. lia.
    - done.
  Qed.

  (** Unlike [big_sepL_delete] and [big_sepL_delete'], this one uses [delete],
  but is restricted to comprehensions that do not use the list index.
  Unlike [big_sepL_difference_singleton], this works on lists with duplicates.
  TODO: This name would make more sense if the upstream lemmas were renamed, say,
  into [big_sepL_delete_{if,ne}].
  *)
  Lemma big_sepL_delete_delete xs i x (f : A → PROP)
    (Hl : xs !! i = Some x) :
    ([∗ list] k ∈ xs, f k) ⊣⊢ f x ∗ [∗ list] k ∈ delete i xs, f k.
  Proof.
    rewrite big_sepL_delete; last exact: Hl. f_equiv.
    elim: xs i Hl => [//|x' xs IHxs] [|i] /= Hl. {
      rewrite left_id. by apply big_sepL_proper.
    }
    f_equiv. rewrite -(IHxs i Hl). apply big_sepL_proper => k y Hl'.
    rewrite (decide_ext (S k = S i) (k = i)) //. lia.
  Qed.

  (** In contrast with [big_sepL_timeless], [big_sepL_persistent], and
      [big_sepL_affine], the following offer [xs !! k = Some x] in
      their premisses. *)
  Lemma big_sepL_gen_timeless `{!Timeless (emp%I : PROP)} f xs :
    (∀ k x, xs !! k = Some x → Timeless (f k x)) →
    Timeless ([∗ list] k↦x ∈ xs, f k x).
  Proof. apply big_opL_gen; apply _. Qed.
  Lemma big_sepL_gen_persistent f xs :
    (∀ k x, xs !! k = Some x → Persistent (f k x)) →
    Persistent ([∗ list] k↦x ∈ xs, f k x).
  Proof. apply big_opL_gen; apply _. Qed.
  Lemma big_sepL_gen_affine f xs :
    (∀ k x, xs !! k = Some x → Affine (f k x)) →
    Affine ([∗ list] k↦x ∈ xs, f k x).
  Proof. apply big_opL_gen; apply _. Qed.
End big_sepL.

Lemma big_sepL_mono_elem {PROP : bi} {A : Type} (Φ Ψ : A → PROP) (l : list A):
  (∀ (y : A),  y ∈ l -> Φ y  ⊢ Ψ y)
  → ([∗ list] y ∈ l, Φ y) ⊢ ([∗ list] y ∈ l, Ψ y).
Proof.
  intros Hin. apply big_sepL_mono => k y Hl. eapply Hin, elem_of_list_lookup_2, Hl.
Qed.

Lemma big_sepL_difference_singleton {PROP : bi} `{EqDecision A} (x : A)
    (f : A -> PROP) (l : list A) :
  x ∈ l ->
  NoDup l ->
  ([∗ list] i ∈ l, f i) ⊣⊢ f x ∗ [∗ list] id ∈ list_difference l [x], f id.
Proof.
  intros [j Hl]%elem_of_list_lookup_1 HnoDup.
  by rewrite big_sepL_delete_delete // (list_difference_delete j).
Qed.

Lemma big_sepL_difference_two {PROP: bi} {A} {eqd: EqDecision A} (f  : A -> PROP) l x y:
  x<>y ->
  x ∈ l ->
  y ∈ l ->
  NoDup l -> (* we only need x to be not duplicated *)
  ([∗ list] id ∈ l, f id)%I ≡ (f x ∗ f y ∗ (([∗ list] id ∈ (list_difference l [x;y]), f id)))%I.
Proof.
  intros Hneq H1l H2l Hnd.
  rewrite (big_sepL_difference_singleton x) //.
  rewrite (big_sepL_difference_singleton y); [| set_solver | exact: NoDup_list_difference].
  by rewrite (list_difference_app_r l [x] [y]).
Qed.

#[deprecated(note="Use big_sepL_difference_singleton")]
Notation big_sepL_difference_one := big_sepL_difference_singleton (only parsing).
