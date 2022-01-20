(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From iris.proofmode Require Import proofmode.
From iris_string_ident Require Import ltac2_string_ident.

From iris.bi.lib Require Import fractional.

From bedrock.lang.cpp Require Import logic.pred.
From bedrock.lang.cpp.semantics Require Import types genv values.
Require Import bedrock.prelude.addr.

Module Type VBYTE.
  Parameter vbyte_at : forall `{Σ:cpp_logic} (q : Qp) (addr : N) (n : N), mpred.
  (*[vbyte_at q va n]: Virtual address [va] contains byte [n] with
    permission [q].*)
  Axiom vbyte_at_fractional :
    forall `{Σ:cpp_logic} addr n, Fractional (λ q, vbyte_at q addr n).
  #[global] Existing Instance vbyte_at_fractional.
  Axiom vbyte_at_frac_valid :
    forall `{Σ:cpp_logic} addr n (q : Qp),
      Observe [| q ≤ 1 |]%Qp (vbyte_at q addr n).
  #[global] Existing Instance vbyte_at_frac_valid.
  Axiom vbyte_at_timeless :
    forall `{Σ:cpp_logic} q addr n, Timeless (vbyte_at q addr n).
  #[global] Existing Instance vbyte_at_timeless.
End VBYTE.
Declare Module Export Vbyte_impl : VBYTE.

Module Type PHANTDATA.
  (*[phantdata_at ty q p]: In the C++ abstract machine, [p] previously
    contained a [ty]-typed value with permission [q]. When you re-enter
    the C++ virtual machine (via [memory_entry]), you combine
    [phantdata_at] with a virtual points-to fact to get a C++-level
    points-to.*)
  Parameter phantdata_at :
    forall `{Σ:cpp_logic} {σ:genv} (ty : type) (q : Qp) (p : ptr), mpred.
  #[global] Notation phantbyte_at := (phantdata_at W8).
  #[global] Notation phantshort_at := (phantdata_at W16).
  #[global] Notation phantword_at := (phantdata_at W32).
  #[global] Notation phantdword_at := (phantdata_at W64).

  Axiom phantdata_at_fractional :
    forall `{Σ:cpp_logic} {σ:genv} ty p, Fractional (λ q, phantdata_at ty q p).
  #[global] Existing Instance phantdata_at_fractional.
  Axiom phantdata_at_frac_valid :
    forall `{Σ:cpp_logic} {σ:genv} ty (q : Qp) p,
      Observe [| q ≤ 1 |]%Qp (phantdata_at ty q p).
  #[global] Existing Instance phantdata_at_frac_valid.
  Axiom phantdata_at_timeless :
    forall `{Σ:cpp_logic} {σ:genv} ty q p, Timeless (phantdata_at ty q p).
  #[global] Existing Instance phantdata_at_timeless.
End PHANTDATA.
Declare Module Export Phantdata_impl : PHANTDATA.
