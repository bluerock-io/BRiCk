(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.prelude.base.
Require Import iris.proofmode.tactics.
From iris.bi.lib Require Import fractional.

Require Import bedrock.lang.cpp.ast.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred translation_unit.
Require Import bedrock.lang.cpp.semantics.
Require Import bedrock.lang.cpp.logic.z_to_bytes.
Require Import bedrock.lang.cpp.logic.arr.
Require Import bedrock.lang.cpp.logic.raw.

Require Import bedrock.lang.cpp.heap_notations.

Section with_Σ.
  Context `{Σ : cpp_logic} {resolve:genv}.

  Axiom struct_padding : genv -> Qp -> globname -> Rep.
  Axiom union_padding : genv -> Qp -> globname -> nat -> Rep.

  Axiom struct_padding_fractional : forall cls, Fractional (fun q => struct_padding resolve q cls).
  Axiom struct_padding_timeless : forall q cls, Timeless  (struct_padding resolve q cls).
  Axiom struct_padding_frac_valid : forall (q : Qp) cls, Observe [| q ≤ 1 |]%Qp (struct_padding resolve q cls).
  Axiom union_padding_fractional : forall cls idx, Fractional (fun q => union_padding resolve q cls idx).
  Axiom union_padding_timeless : forall q cls idx, Timeless (union_padding resolve q cls idx).
  Axiom union_padding_frac_valid : forall (q : Qp) cls idx, Observe [| q ≤ 1 |]%Qp (union_padding resolve q cls idx).

  #[global] Existing Instances
    struct_padding_fractional struct_padding_timeless struct_padding_frac_valid
    union_padding_fractional union_padding_timeless union_padding_frac_valid.

  #[global] Instance struct_padding_as_fractional q cls :
    AsFractional (struct_padding resolve q cls) (λ q, struct_padding resolve q cls) q.
  Proof. exact: Build_AsFractional. Qed.
  #[global] Instance union_padding_as_fractional q cls idx :
    AsFractional (union_padding resolve q cls idx) (λ q, union_padding resolve q cls idx) q.
  Proof. exact: Build_AsFractional. Qed.

  Axiom struct_padding_strict_valid_observe : forall q cls, Observe svalidR (struct_padding resolve q cls).
  #[global] Existing Instance struct_padding_strict_valid_observe.
  #[global] Instance struct_padding_valid_observe q cls : Observe validR (struct_padding resolve q cls).
  Proof. rewrite -svalidR_validR. apply _. Qed.

  Axiom union_padding_strict_valid_observe : forall q cls i, Observe svalidR (union_padding resolve q cls i).
  #[global] Existing Instance union_padding_strict_valid_observe.
  #[global] Instance union_padding_valid_observe q cls i : Observe validR (union_padding resolve q cls i).
  Proof. rewrite -svalidR_validR. apply _. Qed.

  (* TODO: Do we need type_ptrR here? *)
  Axiom struct_to_raw : forall cls st rss q,
    glob_def resolve cls = Some (Gstruct st) ->
    st.(s_layout) = POD ->
    ([∗ list] fld ∈ st.(s_fields), let '(n,ty,_,_) := fld in
       Exists rs, [| rss !! n = Some rs |] **
       _offsetR (_field {| f_name := n ; f_type := cls |}) (rawsR q rs))
      ** struct_padding resolve q cls -|-
      Exists rs, rawsR q rs ** [| raw_bytes_of_struct resolve cls rss rs |].

  (** decompose a struct into its constituent fields and base classes.
   *)
  Axiom decompose_struct
  : forall cls st,
    glob_def resolve cls = Some (Gstruct st) ->
        anyR (Tnamed cls) 1
    -|- ([∗list] base ∈ st.(s_bases),
              let '(gn,_) := base in
              _offsetR (_base cls gn) (anyR (Tnamed gn) 1)) **
           ([∗list] fld ∈ st.(s_fields),
              let '(n,ty,_,_) := fld in
              _offsetR (_field {| f_name := n ; f_type := cls |})
                       (anyR (erase_qualifiers ty) 1)) **
           (if has_vtable st
            then identityR cls None 1
            else emp)
           ** struct_padding resolve 1 cls.

  (** decompose a union into the classical conjunction of the alternatives
   *)
  Axiom decompose_union
  : forall (cls : globname) st,
    glob_def resolve cls = Some (Gunion st) ->
        anyR (Tnamed cls) 1
    -|- [∧list] idx↦it ∈ st.(u_fields),
           let '(i, t, _, _) := it in
           let f := _field {| f_name := i ; f_type := cls |} in
           _offsetR f (anyR (erase_qualifiers t) 1) **
           union_padding resolve 1 cls idx.

  (** decompose an array into individual components
      note that one past the end of an array is a valid location, but
      it doesn't store anything.
   *)
  Axiom decompose_array : forall t n,
        anyR (Tarray t n) 1
    -|- _offsetR (_sub t (Z.of_N n)) validR **
        [∗list] i ↦ _ ∈ repeat () (BinNatDef.N.to_nat n),
                _offsetR (_sub t (Z.of_nat i)) (anyR t 1).
End with_Σ.
