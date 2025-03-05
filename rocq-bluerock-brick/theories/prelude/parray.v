(*
 * Copyright (c) 2025 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.prelude.base.
Require Import bedrock.prelude.uint63.
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
      to_list_aux a n i acc = (List.map (fun i => PArray.get a i) (List.rev (intseq i n))) ++ acc.
    Proof.
      elim => [//|n IHn] i acc.
      simpl. rewrite {}IHn.
      rewrite map_app -!app_assoc.
      f_equal.
    Qed.

    Definition to_list (a : array A) : list A  :=
      let len := PArray.length a in
      PArray.default a :: to_list_aux a (Z.to_nat (Uint63.to_Z len)) 0%uint63 [].

    Definition to_list_nodef a : list A  :=
      let len := PArray.length a in
      to_list_aux a (Z.to_nat (Uint63.to_Z len)) 0%uint63 [].

    Lemma to_list_P a :
      to_list a = PArray.default a :: (List.map (fun i => PArray.get a i) (List.rev (intseq 0 (Z.to_nat (to_Z (PArray.length a)))))).
    Proof.
      unfold to_list.
      repeat f_equal.
      by rewrite to_list_aux_P app_nil_r.
    Qed.

    Lemma to_list_nodef_P a :
      to_list_nodef a = (List.map (fun i => PArray.get a i) (List.rev (intseq 0 (Z.to_nat (to_Z (PArray.length a)))))).
    Proof.
      unfold to_list_nodef.
      by rewrite to_list_aux_P app_nil_r.
    Qed.

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

    Definition of_list (l : list A) : option (array A) :=
      match l with
      | default :: l =>
          let len := of_nat (List.length l) in
          let a := PArray.make len default in
          let a := of_list_aux l len a in
          Some a
      | _ => None
      end.

    Definition of_list_nodef (l : list A) : option (array A) :=
      match l with
      | (default :: _) as l => of_list (default :: l)
      | _ => None
      end.
  End Lists.


  Definition foldl_i {A B} : (int -> A -> B -> B) -> array A -> B -> B :=
    fun f a b =>
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

  Definition foldr_i {A B} : (int -> A -> B -> B) -> array A -> B -> B :=
    fun f a b =>
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

  (* TODO: move elsewhere. *)
  (* [SpecCompare] is the dual of [CompareSpec]. *)
  Class SpecCompare (Peq Plt Pgt : Prop) (c : comparison) :=
    { sc_eq : Peq -> c = Eq;
      sc_lt : Plt -> c = Lt;
      sc_gt : Pgt -> c = Gt;
    }.
  (* We expect any of the four arguments to uniquely identify the correct instance. *)
  #[global] Hint Mode SpecCompare - - - ! : typeclass_instances.
  #[global] Hint Mode SpecCompare ! - - - : typeclass_instances.
  #[global] Hint Mode SpecCompare - ! - - : typeclass_instances.
  #[global] Hint Mode SpecCompare - - ! - : typeclass_instances.
  Coercion sc_eq : SpecCompare >-> Funclass.
  Coercion sc_lt : SpecCompare >-> Funclass.
  Coercion sc_gt : SpecCompare >-> Funclass.

  (* [compare] implementation respecting the prefix order. [default] is treated as
    the last value. If we expect to compare mostly arrays from the same source we can
    expect the [default] values to be the same which means comparing them is a waste of time.

    This is not as fast as [eq_dec] for equality checks since it always performs
    work in the length of the common prefix even when [default] and [length]
    clearly disagree. *)
  Section Compare.
    Context `(CS: forall x y : A, CompareSpec (Peq x y) (Plt x y) (Pgt x y) (cmp x y)).
    Context `(SC: forall x y : A, SpecCompare (Peq x y) (Plt x y) (Pgt x y) (cmp x y)).
    #[local] Infix "?=" := cmp.
    Implicit Type a : array A.
    Context (a1 a2 : array A).

    #[local,program] Instance length_InjTyp : ZifyClasses.InjTyp (array A) Uint63.int :=
      { inj a := length a; pred l := (to_Z l <= to_Z max_length) }.
    Next Obligation. intros a. simpl. have/leb_spec:=(leb_length a). lia. Qed.
    Add Zify InjTyp length_InjTyp.

    #[local,program] Instance length_UnOp : ZifyClasses.UnOp (@length A) :=
      { TUOp x := to_Z x }.
    Next Obligation. simpl. lia. Qed.
    Add Zify UnOp length_UnOp.

    Definition length_min2 :=
      let l1 := length a1 in
      let l2 := length a2 in
      if Uint63.ltb l1 l2 then l1 else l2.

    Definition length_max2 :=
      let l1 := length a1 in
      let l2 := length a2 in
      if Uint63.ltb l1 l2 then l2 else l1.

    Lemma length_min2_spec :
      to_Z length_min2 = to_Z (length a1) `min` to_Z (length a2).
    Proof. unfold length_min2. case: Uint63.ltbP; lia. Qed.

    Lemma length_max2_spec :
      to_Z (length_max2) = to_Z (length a1) `max` to_Z (length a2).
    Proof. unfold length_max2. case: Uint63.ltbP; lia. Qed.

    #[local,program] Instance length_min2_CstOp : ZifyClasses.CstOp length_min2 :=
    { TCst := to_Z (length a1) `min` to_Z (length a2) }.
    Next Obligation. rewrite /= length_min2_spec //. Qed.
    Add Zify CstOp length_min2_CstOp.

    Lemma eq_helper
      (Hj : ∀ j : int, φ (j)%uint63 < to_Z (length_min2) → (a1.[j] ?= a2.[j]) = Eq)
      (Hlen : length a1 = length a2)
      (Hdef : (default a1 ?= default a2) = Eq) :
        ∀ j : int, (a1.[j] ?= a2.[j]) = Eq.
    Proof.
      move => j. case: (Z_lt_ge_dec (to_Z j) (to_Z (length a1))) => [?|?].
      + apply: Hj. lia.
      + rewrite !get_out_of_bounds; [done|lia..].
    Qed.

    Inductive pre_rel {Peq Plt Pgt}: forall (Cres : comparison), Prop :=
    | PreEq  : length a1 = length a2 -> (forall j, Peq a1.[j] a2.[j]) -> pre_rel Eq

    | PreLtA i :
      to_Z i < to_Z (length_min2) ->
      (forall j, to_Z j < to_Z i -> Peq a1.[j] a2.[j]) ->
      Plt a1.[i] a2.[i] ->
      pre_rel Lt
    | PreLtB :
      length a1 = length a2 ->
      (forall j, to_Z j < to_Z (length a1) -> Peq a1.[j] a2.[j]) ->
      Plt (default a1) (default a2) ->
      pre_rel Lt
    | PreLtC:
      to_Z (length a1) < to_Z (length a2) ->
      (forall j, to_Z j < to_Z (length a1) -> Peq a1.[j] a2.[j]) ->
      pre_rel Lt

    | PreGtA i:
      to_Z i < to_Z (length_min2) ->
      (forall j, to_Z j < to_Z i -> Peq a1.[j] a2.[j]) ->
      Pgt a1.[i] a2.[i] ->
      pre_rel Gt
    | PreGtB :
      length a1 = length a2 ->
      (forall j, to_Z j < to_Z (length a2) -> Peq a1.[j] a2.[j]) ->
      Pgt (default a1) (default a2) ->
      pre_rel Gt
    | PreGtC:
      to_Z (length a1) > to_Z (length a2) ->
      (forall j, to_Z j < to_Z (length a2) -> Peq a1.[j] a2.[j]) ->
      pre_rel Gt
    .
    Arguments pre_rel : clear implicits.

    Definition rel_cmp := pre_rel (fun x y => cmp x y = Eq) (fun x y => cmp x y = Lt) (fun x y => cmp x y = Gt).

    Definition inv (c : comparison) :=
      match c with
      | Lt => Gt
      | Eq => Eq
      | Gt => Lt
      end.

    Context (cmp_swap : forall x y, inv (cmp x y) = cmp y x).

    Lemma cmp_swap_aux x y c : cmp x y = c -> cmp y x = inv c.
    Proof using cmp_swap.
      rewrite -(cmp_swap x y).
      case H1: (cmp x y); case H2: (cmp y x); case H3: c => //=.
    Qed.

    Definition compare_seq (c1 c2 : comparison) :=
      match c1 with
      | (Lt as r|Gt as r) => r
      | Eq => c2
      end.

    (* [compare_aux] compares [a1.[j]] to [a2.[j]] for all [i <= j < i + n]. *)
    Fixpoint compare_aux a1 a2 (n : nat) (i : int) {struct n} :=
      match n with
      | O => Eq
      | S n =>
          match (a1.[i] ?= a2.[i]) with
          | (Lt as r| Gt as r)  => r
          | Eq => compare_aux a1 a2 n (i + 1)%uint63
          end
      end.

    Definition compare_help a1 a2 n i :=
      compare_seq
        (compare_aux a1 a2 n i)
        (compare_seq
          (length a1 ?= length a2)%uint63
          (default a1 ?= default a2)
        ).

    Definition compare :=
      Eval unfold compare_help in compare_help a1 a2 (Z.to_nat (to_Z (length_min2))) 0.

    Lemma compare_prep P :
      (∀ (n : nat) (i : int),
            n ≤ to_Z (length_min2)
            → φ (i)%uint63 ≤ to_Z (length_min2)
            → to_Z (length_min2) - φ (i)%uint63 = n
            → (∀ j : int, φ (j)%uint63 < φ (i)%uint63 → (a1.[j] ?= a2.[j]) = Eq)
            → P (compare_help a1 a2 n i)
      ) -> P compare.
    Proof.
      rewrite /compare/compare_help/compare_seq => IH.
      move Hn: (Z.to_nat _) => n.
      set i := 0%uint63.
      have {}Hni : Z.to_nat (to_Z (length a1) `min` to_Z (length a2)) - to_Z i = n; [lia|].
      have Hi1: to_Z i <= (to_Z (length a1) `min` to_Z (length a2)) by lia.
      have Hi2: forall j, to_Z j < to_Z i -> a1.[j] ?= a2.[j] = Eq by lia.
      have {}Hn : n <=  (to_Z (length a1) `min` to_Z (length a2)) by lia.
      apply: IH; lia.
    Qed.

    Lemma compare_ind P :
      ((∀ j : int, φ (j)%uint63 < φ (length_min2)%uint63 → (a1.[j] ?= a2.[j]) = Eq)
      → P (compare_seq (to_Z (length a1) ?= to_Z (length a2))%Z (default a1 ?= default a2))
      ) ->
      (∀ (n : nat) (i : int),
          n < to_Z (length_min2)
          → φ (i)%uint63 < (to_Z (length_min2))
          → to_Z (length_min2) - φ (i)%uint63 = S n
          → (∀ j : int, φ (j)%uint63 < φ (i)%uint63 → (a1.[j] ?= a2.[j]) = Eq)
          → (a1.[i] ?= a2.[i] = Lt -> P Lt)
          ∧ (a1.[i] ?= a2.[i] = Gt -> P Gt)
      ) -> P compare.
    Proof.
      intros HO HS.
      apply compare_prep.
      elim => [|n IHn] i Hn Hi Hni Hij.
      - have ?: i = length_min2 by lia. subst.
        rewrite /compare_help Uint63.compare_spec /=.
        move: {HS} HO.
        case: Z.compare_spec => Hlen => //; by apply.
      - rewrite /compare_help {1}/compare_seq.
        have ?:= leb_length a1.
        cbn.
        move: {HO} HS => /(_ n i).
        case Hai: (a1.[i] ?= a2.[i]) => HS.
        + apply: IHn; [lia|lia|lia|].
          move => j Hj. case: (Z.eq_dec (to_Z j) (to_Z i)).
          * move => /to_Z_inj ?; subst; done.
          * move => ?; apply Hij; lia.
        + apply HS; [lia|lia|lia|done|done].
        + apply HS; [lia|lia|lia|done|done].
    Qed.


    Lemma pre_rel_spec :
      rel_cmp compare.
    Proof.
      apply compare_ind.
      - move => Hj.
        case: Z.compare_spec => //= [/to_Z_inj Hlen|Hlen|Hlen].
        + case Hdef: cmp.
          * apply: PreEq => //. by apply: eq_helper.
          * apply: PreLtB; auto. move => j ?. apply Hj. lia.
          * apply: PreGtB; auto. move => j ?. apply Hj. lia.
        + apply: PreLtC; [lia|]. move => j ?. apply Hj. lia.
        + apply: PreGtC; [lia|]. move => j ?. apply Hj. lia.
      - intros n i Hn Hi Hni Hij.
        split => Hia.
        + apply (PreLtA i) => //.
        + apply (PreGtA i) => //.
    Qed.

    Lemma spec_pre_rel Hres : rel_cmp Hres -> Hres = compare.
    Proof.
      apply compare_ind.
      - move => Hj.
        move => [Hlen Hj2
                |i Hlen Hij Hia|Hlen Hj2 Hdef|Hlen Hj2
                |i Hlen Hij Hia|Hlen Hj2 Hdef|Hlen Hj2].
        + case: Z.compare_spec => // ?; [|lia..].
          rewrite !default_get !Hlen Hj2 //.
        + by rewrite Hj in Hia.
        + rewrite Hlen Z.compare_refl Hdef //.
        + case: Z.compare_spec => // ?; [lia|lia].
        + by rewrite Hj in Hia.
        + rewrite Hlen Z.compare_refl Hdef //.
        + case: Z.compare_spec => // ?; [lia|lia].
      - move => n i Hn Hi Hni Hij.
        suff:
          (a1.[i] ?= a2.[i]) <> Eq ->
          rel_cmp Hres →
          Hres = (a1.[i] ?= a2.[i]).
        { case Hia: cmp => //; split; auto =>//. }
        move => Hia.
        move => [Hlen Hj2
                |k Hlen Hkj Hka|Hlen Hj2 Hdef|Hlen Hj2
                |k Hlen Hkj Hka|Hlen Hj2 Hdef|Hlen Hj2].
        + by rewrite Hj2.
        + have [?|[/to_Z_inj ?|?]]:= Ztrichotomy (to_Z i) (to_Z k).
          * rewrite Hkj in Hia; [done|lia].
          * by subst; rewrite Hka.
          * rewrite Hij in Hka; [done|lia].
        + rewrite Hj2 in Hia; [done|lia].
        + rewrite Hj2 in Hia; [done|lia].
        + have [?|[/to_Z_inj ?|?]]:= Ztrichotomy (to_Z i) (to_Z k).
          * rewrite Hkj in Hia; [done|lia].
          * by subst; rewrite Hka.
          * rewrite Hij in Hka; [done|lia].
        + rewrite Hj2 in Hia; [done|lia].
        + rewrite Hj2 in Hia; [done|lia].
    Qed.

    Definition rel c := pre_rel Peq Plt Pgt c.

    Lemma rel_cmp_iff c : rel c <-> rel_cmp c.
    Proof using CS SC.
      split.
      - induction 1.
        + apply PreEq; eauto using sc_eq.
        + apply: PreLtA; eauto using sc_eq, sc_lt.
        + apply: PreLtB; eauto using sc_eq, sc_lt.
        + apply: PreLtC; eauto using sc_eq, sc_lt.
        + apply: PreGtA; eauto using sc_eq, sc_gt.
        + apply: PreGtB; eauto using sc_eq, sc_gt.
        + apply: PreGtC; eauto using sc_eq, sc_gt.
      - induction 1 as
          [Hlen Hj
          |k Hlen Hkj Hka|Hlen Hj' Hdef|Hlen Hj'
          |k Hlen Hkj Hka|Hlen Hj' Hdef|Hlen Hj'].
        + apply PreEq; eauto. move => j. by case: CS (Hj j).
        + apply: PreLtA; eauto.
          * move => j Hj. by case: CS (Hkj j Hj).
          * by case: CS Hka.
        + apply: PreLtB; eauto.
          * move => j Hj. by case: CS (Hj' j Hj).
          * by case: CS Hdef.
        + apply: PreLtC; eauto.
          move => j Hj. by case: CS (Hj' j Hj).
        + apply: PreGtA; eauto.
          * move => j Hj. by case: CS (Hkj j Hj).
          * by case: CS Hka.
        + apply: PreGtB; eauto.
          * move => j Hj. by case: CS (Hj' j Hj).
          * by case: CS Hdef.
        + apply: PreGtC; eauto.
          move => j Hj. by case: CS (Hj' j Hj).
    Qed.

    Definition lt  := rel Lt.
    Definition gt  := rel Gt.
    Definition eq' := rel Eq.

    Lemma compare_spec :
      CompareSpec eq' lt gt compare.
    Proof using CS SC.
      move: pre_rel_spec => /rel_cmp_iff []; econstructor; by repeat econstructor.
    Qed.

    #[global] Instance spec_compare :
      SpecCompare eq' lt gt compare.
    Proof using CS SC.
      suff: forall c, rel c -> compare = c.
      { split; move => ?; eauto. }
      move => ?.
      move/rel_cmp_iff. move/spec_pre_rel => -> //.
    Qed.
  End Compare.

  Section Compare2.
    Context `(CS: forall x y : A, CompareSpec (Peq x y) (Plt x y) (Pgt x y) (cmp x y)).
    Context `(SC: forall x y : A, SpecCompare (Peq x y) (Plt x y) (Pgt x y) (cmp x y)).
    #[local] Infix "?=" := cmp.
    Implicit Type a : array A.

    (* TODO: duplication *)
    #[local,program] Instance length_InjTyp' : ZifyClasses.InjTyp (array A) Uint63.int :=
      { inj a := length a; pred l := (to_Z l <= to_Z max_length) }.
    Next Obligation. intros a. simpl. have/leb_spec:=(leb_length a). lia. Qed.
    Add Zify InjTyp length_InjTyp'.

    #[local,program] Instance length_UnOp' : ZifyClasses.UnOp (@length A) :=
      { TUOp x := to_Z x }.
    Next Obligation. simpl. lia. Qed.
    Add Zify UnOp length_UnOp'.

    #[local,program] Instance length_min2_BinOp : ZifyClasses.BinOp length_min2 :=
    { TBOp x y := to_Z x `min` to_Z y }.
    Next Obligation. intros. rewrite /= length_min2_spec //. Qed.
    Add Zify BinOp length_min2_BinOp.

    Context (cmp_swap : forall x y, inv (cmp x y) = cmp y x).

    Lemma compare_swap a1 a2 : compare (cmp:=cmp) a1 a2 = inv (compare (cmp:=cmp) a2 a1).
    Proof using cmp_swap.
      rewrite /compare/compare_seq !length_min2_spec (Z.min_comm (to_Z (length a2))).
      move Hn: (Z.to_nat _) => n.
      set i := 0%uint63.
      have {}Hni : (to_Z (length a1) `min` to_Z (length a2)) - to_Z i = n; [lia|].
      have Hi1: to_Z i <= (to_Z (length a1) `min` to_Z (length a2)) by lia.
      have Hi2: forall j, to_Z j < to_Z i -> a1.[j] ?= a2.[j] = Eq by lia.
      have {}Hn : n <= to_Z (length a1) `min` to_Z (length a2) by lia.
      rewrite !Uint63.compare_spec.
      elim: n Hn i Hni Hi1 Hi2 => [|n IHn] Hn i Hni Hi1 Hi2 /=.
      - case: Z.compare_spec.
        + move => Hlen. rewrite Hlen Z.compare_refl cmp_swap //.
        + case: Z.compare_spec => //; lia.
        + case: Z.compare_spec => //; lia.
      - case Hia: cmp.
        + rewrite (cmp_swap_aux cmp_swap _ _ _ Hia).
          have ?:= leb_length a1.
          rewrite {}IHn //; [lia..|]. move => j Hj.
          suff: (to_Z j < to_Z i \/ to_Z j = to_Z i); [|lia].
          move => [|/to_Z_inj->]; auto.
        + rewrite (cmp_swap_aux cmp_swap _ _ _ Hia) //.
        + rewrite (cmp_swap_aux cmp_swap _ _ _ Hia) //.
    Qed.


    Context `{Peq_Trans: Transitive A Peq}.
    Context `{Plt_Trans: Transitive A Plt}.
    Context `{Plt_stepr : forall x y z, Plt x y -> Peq y z -> Plt x z}.
    Context `{Plt_stepl : forall x y z, Peq x y -> Plt y z -> Plt x z}.

    #[global] Instance lt_Transitive : Transitive (@lt A Peq Plt Pgt).
    Proof using Pgt Peq_Trans Plt_Trans Plt_stepl Plt_stepr.
      intros a1 a2 a3.
      unfold lt.
      move Hc: Lt => c H12; move: Hc.
      destruct H12 as
        [H12len H12j
        |k12 H12len H12kj H12ka|H12len H12j H12def|H12len H12j
        |k12 H12len H12kj H12ka|H12len H12j H12def|H12len H12j]
      .
      all: try (intros; discriminate).
      all: move => _.
      all: move Hc: Lt => c H23; move: Hc.
      all: destruct H23 as
        [H23len H23j
        |k23 H23len H23kj H23ka|H23len H23j H23def|H23len H23j
        |k23 H23len H23kj H23ka|H23len H23j H23def|H23len H23j].
      all: try (intros; discriminate).
      all: move => _.
      - apply (PreLtA _ _ (of_Z (to_Z k12 `min` to_Z k23))).
        + lia.
        + move => j Hj. etrans; [apply H12kj|apply H23kj]; lia.
        + case: (Ztrichotomy (to_Z k12) (to_Z k23)) => [?|[/to_Z_inj ?|?]].
          * rewrite Z.min_l; [|lia]. rewrite of_to_Z.
            apply: Plt_stepr; [by apply H12ka|by apply H23kj].
          * subst. rewrite Z.min_id of_to_Z. apply: Plt_Trans; by eauto.
          * rewrite Z.min_r; [|lia]. rewrite of_to_Z.
            apply: Plt_stepl; [apply H12kj; lia|by apply H23ka].
      - apply (PreLtA _ _ k12).
        + lia.
        + move => j Hj. apply: Peq_Trans; [by apply H12kj|apply H23j; lia].
        + apply: Plt_stepr; [done|apply H23j; lia].
      - apply (PreLtA _ _ k12).
        + lia.
        + move => j Hj. apply: Peq_Trans; [by apply H12kj|apply H23j; lia].
        + apply: Plt_stepr; [done|apply H23j; lia].
      - apply (PreLtA _ _ k23).
        + lia.
        + move => j Hj. apply: Peq_Trans; [apply H12j; lia|by apply H23kj].
        + apply: Plt_stepl; [apply H12j; lia|done].
      - apply (PreLtB).
        + lia.
        + move => j Hj. apply: Peq_Trans; [apply H12j; lia|apply H23j; lia].
        + by apply: Plt_Trans.
      - apply PreLtC.
        + lia.
        + move => j Hj. apply: Peq_Trans; [apply H12j; lia|apply H23j; lia].
      - case: (Z_lt_ge_dec (to_Z k23) (to_Z (length a1))) => [?|?].
        + apply: (PreLtA _ _ k23).
          * lia.
          * move => j Hj. apply: Peq_Trans; [apply H12j; lia|apply H23kj; lia].
          * apply: Plt_stepl; [|done]. apply: H12j. lia.
        + apply: PreLtC.
          * lia.
          * move => j Hj. apply: Peq_Trans; [eauto|]. apply H23kj. lia.
      - apply: PreLtC.
        * lia.
        * move => j Hj. apply: Peq_Trans; [apply H12j; lia|apply H23j; lia].
      - apply: PreLtC.
        * lia.
        * move => j Hj. apply: Peq_Trans; [apply H12j; lia|apply H23j; lia].
    Qed.


  End Compare2.


  (** The [ListBijection] module contains [to_list] and [of_list] functions that
      are optimized for use in [array_countable]. *)
  Module ListBijection.
    Section ListBijection.
    Context {A : Type}.
    Implicit Type a : array A.

    #[local] Definition to_list_aux a : nat -> int -> list A -> list A :=
      fix go n i acc {struct n} :=
        match n with
        | O => acc
        | S n => go n (i + 1)%uint63 (PArray.get a i :: acc)
        end.

    Lemma to_list_aux_P a : forall n i acc,
      to_list_aux a n i acc = (List.map (fun i => PArray.get a i) (List.rev (intseq i n))) ++ acc.
    Proof.
      elim => [//|n IHn] i acc.
      simpl. rewrite {}IHn.
      rewrite map_app -!app_assoc.
      f_equal.
    Qed.

    Definition to_list a : (int * list A)  :=
      let len := PArray.length a in
      (len, PArray.default a :: to_list_aux a (Z.to_nat (Uint63.to_Z len)) 0%uint63 []).

    Lemma to_list_P a :
      to_list a = (PArray.length a, PArray.default a :: (List.map (fun i => PArray.get a i) (List.rev (intseq 0 (Z.to_nat (to_Z (PArray.length a))))))).
    Proof.
      unfold to_list.
      repeat f_equal.
      by rewrite to_list_aux_P app_nil_r.
    Qed.


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

    Definition of_list (l : (int * list A)) : option (array A) :=
      match l with
      | (len, default :: l) =>
          let a := PArray.make len default in
          let a := of_list_aux l len a in
          Some a
      | _ => None
      end.

    End ListBijection.
  End ListBijection.

  (* [Countable] instance based on an encoding into a pair of [length] and a reversed [list A].
    The list includes [default] as the first element.
    Including [length] explicitly allows us to [decode] with only a single traversal. *)
  Section Countable.
    Context `{C : Countable A}.
    Implicit Type a : array A.

    Import ListBijection.

    #[global,program] Instance array_countable : Countable (array A) := inj_countable to_list of_list _.
    Next Obligation.
      intros a.
      rewrite to_list_P.
      unfold of_list.
      f_equal. f_equal. simpl.

      apply array_ext; swap 2 3.
      - rewrite of_list_aux_length length_make leb_length //.
      - rewrite of_list_aux_default default_make //.
      - intros i.
        set ls := map _ _.
        have Hls : List.length ls = Z.to_nat (to_Z (length a)).
        { rewrite length_map length_rev intseq_length. lia. }
        rewrite (_ : length (of_list_aux _ _ _) = of_Z (List.length ls)).
        2: { rewrite of_list_aux_length length_make leb_length. lia. }
        move => Hi.
        rewrite of_list_aux_P.
        all: rewrite Hls ?length_make ?leb_length.
        2,3: lia.
        case_decide as H; [|lia].
        rewrite (nth_indep _ _ a.[i]); [|lia].
        rewrite map_nth rev_nth; [|rewrite intseq_length; lia].
        rewrite intseq_nth intseq_length.
        case_decide as H1; [|lia].
        f_equal. lia.
    Qed.
  End Countable.

End PArray.

