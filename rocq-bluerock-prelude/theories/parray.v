(*
 * Copyright (c) 2025 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.base.
Require Import bluerock.prelude.uint63.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import Stdlib.Array.PArray.
Require Stdlib.Lists.List.

Import Uint63.
#[local] Close Scope nat_scope.
#[local] Open Scope Z_scope.

#[global] Instance Op_max_length : ZifyClasses.CstOp max_length :=
  { TCst := 4194303%Z ; TCstInj := eq_refl }.
Add Zify CstOp Op_max_length.

#[global] Arguments leb_length [A].

Module PArray.
  Export Array.PArray.

  Section Lists.
    Context {A : Type}.
    Implicit Type a : array A.

    #[local] Definition to_list_aux a : nat -> int -> list A -> list A :=
      fix go n i acc {struct n} :=
        match n with
        | O => acc
        | S n => go n (i + 1)%uint63 (PArray.get a i :: acc)
        end.

    #[local]
    Lemma to_list_aux_P a : forall n i acc,
      to_list_aux a n i acc = (List.map (fun i => PArray.get a i) (List.rev (seq_int i n))) ++ acc.
    Proof.
      elim => [//|n IHn] i acc.
      simpl. rewrite {}IHn.
      rewrite map_app -!app_assoc.
      f_equal.
    Qed.

    (** *** Array -> List *)

    (** Converts the array to a list dropping the default element. *)
    Definition to_list (a : array A) : list A  :=
      let len := PArray.length a in
      to_list_aux a (Z.to_nat (Uint63.to_Z len)) 0%uint63 [].

    (** Convert an array to a list including the default element of
        the array as the first element of the list.
     *)
    Definition to_list_with_def (a : array A) : list A  :=
      PArray.default a :: to_list a.

    Lemma to_list_P a :
      to_list a = (List.map (fun i => PArray.get a i) (List.rev (seq_int 0 (Z.to_nat (to_Z (PArray.length a)))))).
    Proof.
      unfold to_list.
      by rewrite to_list_aux_P app_nil_r.
    Qed.

    Lemma to_list_with_def_P a :
      to_list_with_def a = PArray.default a :: (List.map (fun i => PArray.get a i) (List.rev (seq_int 0 (Z.to_nat (to_Z (PArray.length a)))))).
    Proof.
      unfold to_list_with_def.
      repeat f_equal. apply to_list_P.
    Qed.

    (** *** List -> Array *)

    Fixpoint of_list_aux l i a {struct l} :=
      match l with
      | x :: l =>
          let i := (i - 1)%uint63 in
          of_list_aux l i (PArray.set a i x)
      | [] => a
      end.

    Lemma of_list_aux_length : forall l i a,
          length (of_list_aux l i a) = length a.
    Proof.
      elim => [|x l IHl] i a.
      - done.
      - by rewrite IHl length_set.
    Qed.

    Lemma of_list_aux_default : forall l i a,
          default (of_list_aux l i a) = default a.
    Proof.
      elim => [|x l IHl] i a.
      - done.
      - by rewrite IHl default_set.
    Qed.

    Lemma nth_cons {X:Type} (n : nat) (x : X) xs d :
      n > 0 ->
      nth n (x :: xs) d = nth (Nat.pred n) xs d.
    Proof. elim: n x xs => [|n IHn] x xs //=. Qed.

    Lemma of_list_aux_P : forall l a i,
        (List.length l <= to_Z (length a))%Z ->
        i = of_Z (List.length l) ->
        forall j,
          (of_list_aux l i a).[j] =
            if decide (0 <= to_Z j < (List.length l))%Z then
              List.nth ((Nat.pred (List.length l)) - Z.to_nat (to_Z j)) l a.[j]
            else
              a.[j]
    .
    Proof.
      elim => [|x l IHl] a i Hl -> j.
      - simpl. case_decide; last done. done.
      - simpl in Hl. cbn [of_list_aux].
        have /leb_spec Hl2:= leb_length a.
        cbn [List.length].
        have ->: (of_Z (S (List.length l)) - 1 = of_Z (List.length l))%uint63 by lia.
        rewrite {}IHl; [|rewrite length_set; lia|lia].
        have [H|[H|H]] := Ztrichotomy (to_Z j) (List.length l);
          (case_decide as H1; (try lia); []; case_decide as H2; try lia; []).
        + rewrite nth_cons; [|lia].
          rewrite get_set_other; [|lia].
          f_equal. lia.
        + rewrite -H in H1 H2 |- *.
          rewrite of_to_Z get_set_same; [|lia].
          rewrite [x in nth x](_ : _ = O); [done|lia].
        + rewrite get_set_other; [done|lia].
    Qed.

    Definition of_list (default : A) (l : list A) : array A :=
      let len := of_nat (List.length l) in
      let a := PArray.make len default in
      of_list_aux l len a.

    Definition of_list_with_def (l : list A) : option (array A) :=
      match l with
      | default :: l => Some (of_list default l)
      | _ => None
      end.
  End Lists.


  Definition foldl_i {A B} (f : int -> A -> B -> B) (a : array A) (b : B) : B :=
    let l := length a in
    let g k '(b,i) :=
      let a := get a i in
      (f i a b, (i+1)%uint63)
    in
    let '(res,_) :=
      nat_rect
        (fun _ => B * int)%type
        (b, 0%uint63)
        g
        (Z.to_nat (Uint63.to_Z (l)))
    in
    res.

  Definition foldr_i {A B} (f : int -> A -> B -> B) (a : array A) (b : B) : B :=
    let l := length a in
    let g k '(b,i) :=
      let a := get a (l - i - 1)%uint63 in
      (f i a b, (i+1)%uint63)
    in
    let '(res,_) :=
      nat_rect
        (fun _ => B * int)%type
        (b, 0%uint63)
        g
        (Z.to_nat (Uint63.to_Z (l)))
    in
    res.

  Lemma default_get {A} (a : array A) : default a = a.[length a].
  Proof. rewrite get_out_of_bounds //. lia. Qed.

  (* [eq_dec] implementation.
    It checks [length], then [default], then the contents.
    This is optimal for (in)equality checks. *)
  Section EqDec.
    Context `{EqDecision A}.
    Implicit Type a : array A.

    #[local] Unset Program Cases.
    #[program]
    Fixpoint eq_dec_partial a1 a2 (n : nat) {struct n} :
      {(forall m : int, (0 <= to_Z m < n)%Z -> get a1 m = get a2 m)} + {a1 <> a2} :=
      match n with
      | O => left _
      | S n =>
          match decide (get a1 (of_Z (Z.of_nat n)) = get a2 (of_Z (Z.of_nat n))) with
          | right Hm => right _
          | left Hm =>
              match eq_dec_partial a1 a2 n with
              | left Hr => left _
              | right Hr => right _
              end
          end
      end.
    Next Obligation. lia. Qed.
    Next Obligation.
      intros.
      case: (decide (to_Z m < n)%Z) => ?.
      - apply: Hr; lia.
      - clear Hr. by have <- : of_nat n = m by lia.
    Qed.
    Next Obligation.
      intros ** ?; subst. now auto.
    Qed.
    Next Obligation.
      intros ** ?; subst. now auto.
    Qed.

    #[program]
    Definition eq_dec a1 a2 : {a1 = a2} + {a1 <> a2} :=
      let s1 := PArray.length a1 in
      let s2 := PArray.length a2 in
      match eqs s1 s2 with
      | right H => right _
      | left H =>
        let d1 := PArray.default a1 in
        let d2 := PArray.default a2 in
        match decide (d1 = d2) with
        | right H => right _
        | left H =>
          let n := s1 in
          match eq_dec_partial a1 a2 (Z.to_nat (to_Z n)) with
          | right _ => right _
          | left H => left _
          end
        end
      end.
    Next Obligation.
      intros.
      apply PArray.array_ext.
      + auto.
      + intros i.
        clear -H.
        intros Hi%ltb_spec.
        assert (E : i = of_Z (Z.of_nat (Z.to_nat (to_Z i)))).
        { rewrite Znat.Z2Nat.id.
          - rewrite of_to_Z. now auto.
          - rewrite <-to_Z_0.
            pose proof (to_Z_bounded i).
            now auto.
        }
        specialize (H i).
        apply H.
        lia.
      + now auto.
    Qed.
    Next Obligation.
      intros **; subst; now auto.
    Qed.
    Next Obligation.
      intros ** ?; subst; now auto.
    Qed.
    Next Obligation.
      intros ** ?; subst; now auto.
    Qed.

    #[global] Instance array_eqdec : EqDecision (@array A) := eq_dec.
  End EqDec.

End PArray.
