(*
 * Copyright (c) 2024-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.base.
Require Import bluerock.prelude.error.
Require Import bluerock.prelude.lens.
Require Import bluerock.upoly.upoly.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.syntax.mtraverse.

#[local] Notation translation_unit := translation_unit.translation_unit.

(** * Resolving aliases *)
(**
Expand type aliases using the alias information stored within a
[translation_unit].

NOTE: The current implementation relies on the fact that aliases
are already removed from definition, e.g.
<<
using T = int;
using U = T;
>>
will be represented the same way as
<<
using T = int;
using U = int;
>>
This avoids the potential for loops and makes de-aliasing structurally
recursive. Without this, we would need to rely on fuel (or well-foundedness
arguments to fully de-alias a type/name.
*)

#[local] Open Scope monad_scope.
#[local] Notation M := (trace.M Error.t).

Module internal.
  Import UPoly.
  (**
  Not monadic because not finding a value is not an error.
  *)
  Definition find_alias (tu : translation_unit) (n : name) : option decltype :=
    match NM.find n tu.(types) with
    | Some (Gtypedef ty) => Some ty
    | _ => None
    end.

  Section resolve.
    Context (tu : translation_unit).

    Definition handle_Tnamed (_ : name) (traverse : unit -> M name) : M type :=
      (fun nm => match find_alias tu nm with
              | None => Tnamed nm
              | Some t => t
              end) <$> traverse ().
    Definition handle_Tref (_ : type) (traverse : unit -> M type) : M type :=
      tref QM <$> traverse ().
    Definition handle_Trv_ref (_ : type) (traverse : unit -> M type) : M type :=
      trv_ref QM <$> traverse ().

    Definition handle_type : type_handler M :=
      (handle_type_traverse
       &: _handle_Tnamed .= handle_Tnamed
       &: _handle_Tref .= handle_Tref
       &: _handle_Trv_ref .= handle_Trv_ref)%lens.
  End resolve.
End internal.

Section resolve.
  Import MTraverse.
  Context (tu : translation_unit).

  #[local] Notation USE f := (
    f (internal.handle_type tu) handle_expr_traverse
  ) (only parsing).

  Definition resolveN := USE traverseN.
  Definition resolveT := USE traverseT.
  Definition resolveE := USE traverseE.
  Definition resolveTA := USE traverseTA.
  Definition resolveS := USE traverseS.
  Definition resolveVD := USE traverseD.

End resolve.

Succeed Example _1 :
  let tu := {| symbols := ∅ ; types := ∅ ; initializer := []; byte_order := Big |} in
  trace.runO (resolveN tu "test(int& &)") = Some ("test(int&)"%cpp_name) := eq_refl.
Succeed Example _1 :
  let tu := {| symbols := ∅ ; types := ∅ ; initializer := []; byte_order := Big |} in
  trace.runO (resolveN tu "test(int&& &)") = Some ("test(int&)"%cpp_name) := eq_refl.
Succeed Example _1 :
  let tu := {| symbols := ∅ ; types := ∅ ; initializer := []; byte_order := Big |} in
  trace.runO (resolveN tu "test(int& &&)") = Some ("test(int&)"%cpp_name) := eq_refl.
Succeed Example _1 :
  let tu := {| symbols := ∅ ; types := ∅ ; initializer := []; byte_order := Big |} in
  trace.runO (resolveN tu "test(int&& &&)") = Some ("test(int&&)"%cpp_name) := eq_refl.
