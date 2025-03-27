(*
 * Copyright (c) 2022-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.fin_map_dom.
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.list_numbers.
Require Import bluerock.prelude.fin_maps.
Require Import bluerock.prelude.fin_sets.
Section fin_map_dom.
  Context `{FinMapDom K M D}.
  Context {A : Type}.
  Implicit Type (m : M A).
  #[local] Set Default Proof Using "Type*".

  Lemma elem_of_map_to_list_dom m k v :
    (k, v) ∈ map_to_list m → k ∈ dom m.
  Proof. move=> /elem_of_map_to_list. apply elem_of_dom_2. Qed.
End fin_map_dom.

Section dom_map_seqZ.
  Import list_numbers.
  #[local] Open Scope Z_scope.
  Context  `{!∀ A, Dom (M A) D, !FMap M,
               HL : !∀ A, Lookup Z A (M A),
               HE : !∀ A, Empty (M A),
               HP : !∀ A, PartialAlter Z A (M A)}.
  Context `{!Singleton Z D, !Union D, !Intersection D, !Difference D}.
  Context `{!OMap M, !Merge M, HF : !∀ A, MapFold Z A (M A),
            !ElemOf Z D, !Empty D, !FinMapDom Z M D}.

  Lemma dom_seqZ {A} (start : Z) (xs : list A) :
    dom (map_seqZ start xs : M A) ≡ (set_rangeZ start (start + lengthZ xs) : D).
  Proof using FinMapDom0.
    rewrite /set_rangeZ.
    elim: xs start => [|x xs IH] start.
    - rewrite lengthN_nil /= Z.add_0_r rangeZ_oob //; apply dom_empty.
    - have ? : (start < start + (lengthN xs + 1)%N) by lia.
      rewrite [X in dom X] /= dom_insert lengthN_cons rangeZ_cons //.
      rewrite N.add_1_r N2Z.inj_succ -Z.add_succ_comm Z.add_1_r.
      by rewrite /= -IH.
  Qed.

  Lemma dom_seqZ_L `{!LeibnizEquiv D} {A} (start : Z) (xs : list A) :
    dom (map_seqZ start xs : M A) = (set_rangeZ start (start + lengthN xs) : D).
  Proof using FinMapDom0.
    apply leibniz_equiv, dom_seqZ.
  Qed.

End dom_map_seqZ.
