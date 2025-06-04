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
*)

#[local] Open Scope monad_scope.
#[local] Notation M := (trace.M Error.t).

Module internal.
  Import UPoly.
  (**
  This is not monadic because not finding a value is not an error.
  *)
  Definition find_alias (tu : translation_unit) (n : name) : option decltype :=
    match NM.find n tu.(types) with
    | Some (Gtypedef ty) => Some ty
    | _ => None
    end.

  Section resolve.
    Context (tu : translation_unit).

    Definition handle_Tnamed (gn : name) (traverse : unit -> M name) : M type :=
      match find_alias tu gn with
      | Some t => mret t
      | None => Tnamed <$> traverse ()
      end.

    Definition handle_type : type_handler M :=
      (handle_type_traverse &: _handle_Tnamed .= handle_Tnamed)%lens.
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
