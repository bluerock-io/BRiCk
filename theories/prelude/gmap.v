(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

From stdpp Require Export gmap mapset.
From bedrock.prelude Require Import base.

(* To upstream to Iris: using [mapseq_eq] directly would unfold a TC opaque
definition and interfere with TC search. *)
Lemma gset_eq `{Countable A} (X1 X2 : gset A) : X1 = X2 ↔ ∀ x, x ∈ X1 ↔ x ∈ X2.
Proof. apply mapset_eq. Qed.

(** [set_map] specialized to [gset]; avoids awkward type annotations such as
[set_map (C := gset A) (D := gset B)].
*)
Notation gset_map := (set_map (C := gset _) (D := gset _)) (only parsing).