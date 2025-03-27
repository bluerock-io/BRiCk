(*
 * Copyright (c) 2021-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export stdpp.gmap.
Require Export stdpp.mapset.
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.fin_sets.
Require Import bluerock.prelude.list_numbers.

(* To upstream to Iris: using [mapseq_eq] directly would unfold a TC opaque
definition and interfere with TC search. *)
Lemma gset_eq `{Countable A} (X1 X2 : gset A) : X1 = X2 ↔ ∀ x, x ∈ X1 ↔ x ∈ X2.
Proof. apply mapset_eq. Qed.

(** [set_map] specialized to [gset]; avoids awkward type annotations such as
[set_map (C := gset _) (D := gset _)].
*)
#[global] Notation gset_map := (set_map (C := gset _) (D := gset _)) (only parsing).

#[global] Notation gset_concat_map :=
  (set_concat_map (C := gset _) (D := gset _)) (only parsing).

(* Like [set_concat_map], but purely in terms of gsets.
*)
Section gset_bind.
  Context `{Countable A} `{Countable B}.

  Definition gset_bind (f : A → gset B) (xs : gset A) : gset B :=
    gset_concat_map (elements ∘ f) xs.

  Lemma gset_bind_empty f :
    gset_bind f ∅ = ∅.
  Proof. done. Qed.

  Lemma elem_of_gset_bind f b xs :
    b ∈ gset_bind f xs ↔ ∃ x, x ∈ xs ∧ b ∈ f x.
  Proof. set_solver. Qed.

  #[global] Instance set_unfold_gset_bind f b xs P Q :
    (∀ x, SetUnfoldElemOf x xs (P x)) → (∀ x, SetUnfoldElemOf b (f x) (Q x)) →
    SetUnfoldElemOf b (gset_bind f xs) (∃ x, P x ∧ Q x).
  Proof. constructor. rewrite elem_of_gset_bind. set_solver. Qed.

  Lemma gset_bind_union f xs1 xs2 :
    gset_bind f (xs1 ∪ xs2) =
    gset_bind f xs1 ∪ gset_bind f xs2.
  Proof. set_solver. Qed.

  Lemma gset_bind_singleton f a :
    gset_bind f {[ a ]} = f a.
  Proof. set_solver. Qed.
End gset_bind.

Section lookup_insert.

  Lemma lookup_insert_iff `{Countable K, A} (m : gmap K A) k k' a :
    <[ k := a ]> m !! k' = if bool_decide (k = k') then Some a else m !! k'.
  Proof. by case: bool_decide_reflect => [<-|?]; rewrite (lookup_insert, lookup_insert_ne). Qed.

End lookup_insert.
