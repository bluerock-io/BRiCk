(*
 * Copyright (C) 2020-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Stdlib.Strings.PrimString.
Require Import bluerock.prelude.base.
Require Export bluerock.prelude.tactics.base_dbs.

Export PStringNotations.

Require Ltac2.Ltac2.
Require Ltac2.Pstring.

(** NamedBinder is a type wrapper that can be used to record the name
    of a binder in a persistent way that is not affected by any computation.

    Existentials/universals of type [NamedBinder A str] are always
    eliminated/introduced directly as an assumption named [str] of type [A].
 *)
Definition NamedBinder (A:Type) (name : string) := A.
#[global] Arguments NamedBinder : simpl never.
#[global] Hint Opaque NamedBinder : typeclass_instances br_opacity.

Module Binder.
  Import Ltac2.
  Import Ltac2.Printf.
  Import Ltac2.Constr.
  Import Ltac2.Constr.Unsafe.
  Import Ltac2.Pstring.

  Ltac2 Type exn ::= [Impossible].

  Ltac2 binder (p : Ltac1.t) :=
    let p := Option.get (Ltac1.to_constr p) in
    (* printf "%t" p; *)
    let id := match Constr.Unsafe.kind p with
    | Constr.Unsafe.Lambda b _ =>
        (Option.default (@anon) (Constr.Binder.name b))
    | _ => @anon
    end in
    let str :=
      match Pstring.of_string (Ident.to_string id) with
      | Some s => s
      | None => Option.get (Pstring.of_string "anon")
      end
    in
    refine (Unsafe.make (String str)).

  (* Solve the goal with [fun (x : s) => x] *)
  Ltac2 to_id_fun (s : constr) : unit :=
    let str :=
      match kind s with
      | String s => Pstring.to_string s
      | _ => Control.throw (Invalid_argument None)
      end
    in
    let id := Ident.of_string str in
    let binder := Constr.Binder.make id 'unit in
    let f := Constr.Unsafe.make (
        Constr.Unsafe.Lambda binder (Constr.Unsafe.make (Constr.Unsafe.Rel 1))
      )
    in
    refine f.

  Ltac id_of := ltac2:(str |- to_id_fun (Option.get (Ltac1.to_constr str))).
End Binder.

(* [TCForceEq] disregards typeclass_instances opacity.  *)
Inductive TCForceEq {A : Type} (x : A) : A -> Prop :=  TCForceEq_refl : TCForceEq x x.
Existing Class TCForceEq.
#[global] Hint Extern 100 (TCForceEq ?x _) => refine (TCForceEq_refl x) : typeclass_instances.

Class IdOfBS (name : string) (ident : () -> ()) := ID_OF_BS {}.
#[global] Arguments IdOfBS name _%_function_scope.
#[global] Hint Mode IdOfBS ! - : typeclass_instances.

#[global] Hint Extern 100 (IdOfBS ?name _) =>
  refine (@ID_OF_BS name ltac:(Binder.id_of name)) : typeclass_instances.

(** Infrastructure to get names into terms using Ltac2 and a type class called [Binder] *)
Section Binder.
  #[local] Set Typeclasses Unique Instances.
  #[local] Set Typeclasses Strict Resolution.
  (** [Binder (fun x => _)] resolves to the bytestring "x". *)
  Class Binder {P : Type} (p : P) := binder : string.
End Binder.

Hint Opaque Binder : typeclass_instances.
Ltac binder p :=
  let f := ltac2:(p |- Binder.binder p) in
  f p.
#[global] Hint Extern 0 (Binder ?p) => binder p : typeclass_instances.

#[global] Notation "'[binder' x ]" := (_ :> @Binder (forall x, True) (fun x => I)) (at level 0, x binder, only parsing).
