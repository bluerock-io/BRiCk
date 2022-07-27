(*
 * Copyright (c) 2021-2022 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.bytestring.
Require Import bedrock.prelude.list.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.

Require Import bedrocktest.virt_cpp.

#[local] Open Scope bs_scope.

Section with_env.
  Context `{MOD : module ⊧ σ}.

  #[global] Instance AA : @class_derives _ "_Z1A" [] := _.

  #[global] Instance AB : @class_derives _ "_Z1B" ["_Z1A"] := _.

  #[global] Instance AC : @class_derives _ "_Z1C" ["_Z1B";"_Z1A"] := _.

  #[global] Instance AD : @class_derives _ "_Z1D" ["_Z1C";"_Z1B";"_Z1A"] := _.

  Goal dispatch.tu_dispatch module "_Z1A" ["_Z1A"] "_ZN1A3fooEv" = Some ("_Z1A", [], "_ZN1A3fooEv").
  Proof. reflexivity. Qed.

  Goal dispatch.tu_dispatch module "_Z1A" ["_Z1C";"_Z1B";"_Z1A"] "_ZN1A3fooEv" = Some ("_Z1C", ["_Z1B"; "_Z1A"], "_ZN1C3fooEv").
  Proof. reflexivity. Qed.

End with_env.
