Require Import iris.algebra.excl.
Require Import iris.algebra.gmap.
Require Import iris.algebra.lib.frac_auth.
Require Import iris.bi.monpred.
Require Import iris.bi.lib.fractional.
Require Import bedrock.lang.proofmode.proofmode.

Require Import bedrock.lang.bi.fractional.
Require Import bedrock.lang.bi.cancelable_invariants.
Require Import bedrock.lang.cpp.bi.cfractional.
Require Import bedrock.lang.base_logic.own_instances.

Require Import bedrock.lang.cpp.logic.mpred.
Require Import bedrock.lang.cpp.logic.pred2.
Require Import bedrock.lang.cpp.semantics.values2.

Require Import bedrock.lang.cpp.model.inductive_pointers2.
(* Stand-in for actual models.
Ensures that everything needed is properly functorized. *)
Import PTRS_IMPL.

(* todo: does this not exist as a library somewhere? *)
Definition cfractionalR (V : Type) : cmra :=
  prodR cQp.tR (agreeR (leibnizO V)).
Definition cfrac {V : Type} q (v : V) : cfractionalR V :=
  (q, to_agree v).

Lemma cfrac_op {V} (l : V) q1 q2 :
  cfrac q1 l ⋅ cfrac q2 l ≡ cfrac (q1 ⋅ q2) l.
Proof. by rewrite -pair_op agree_idemp. Qed.

Lemma cfrac_valid {A : Type} {q1 q2} {v1 v2 : A} :
  ✓ (cfrac q1 v1 ⋅ cfrac q2 v2) → ✓ (q1 ⋅ q2)%Qp ∧ v1 = v2.
Proof. by move /pair_valid => /= []? /to_agree_op_inv_L. Qed.

Section fractional.
  Context {K V : Type} `{Countable K} `{!HasOwn PROP (gmapR K (cfractionalR V))}.

  Let gmap_own γ q k v :=
    own (A := gmapR K (cfractionalR V)) γ {[ k := cfrac q v ]}.
  #[global] Instance cfractional_own_frac γ k v :
    CFractional (λ q, gmap_own γ q k v).
  Proof. intros q1 q2. by rewrite -own_op singleton_op cfrac_op. Qed.

  #[global] Instance fractional_own_frac_as_fractional γ k v q :
    AsCFractional (gmap_own γ q k v) (λ q, gmap_own γ q k v) q.
  Proof. solve_as_cfrac. Qed.

  #[global] Instance gmap_own_agree
    `{!BiEmbed siPropI PROP} `{!HasOwnValid PROP (gmapR K (cfractionalR V))}
    v1 v2 γ q1 q2 k :
    Observe2 [| v1 = v2 |] (gmap_own γ q1 k v1) (gmap_own γ q2 k v2).
  Proof.
    apply: observe_2_intro_only_provable.
    apply bi.wand_intro_r; rewrite /gmap_own -own_op singleton_op.
    rewrite own_valid discrete_valid singleton_valid.
    by iIntros "!%" => /cfrac_valid [].
  Qed.

  (**
  We keep this instance local because guarding it with [CFracValid2]
  prevents it from firing. (Perhaps due to the let binding.)
  *)
  Instance gmap_own_cfrac_valid γ
    `{!BiEmbed siPropI PROP} `{!HasOwnValid PROP (gmapR K (cfractionalR V))} :
    ∀ q k v, Observe [| cQp.frac q ≤ 1 |]%Qp (gmap_own γ q k v).
  Proof.
    intros. apply: observe_intro_only_provable.
    rewrite /gmap_own own_valid !discrete_valid singleton_valid.
    by iIntros "!%" => /pair_valid [? _].
  Qed.
End fractional.
#[local] Existing Instance gmap_own_cfrac_valid.

Declare Module Import VALUES_DEFS_IMPL : VALUES_INTF_FUNCTOR PTRS_IMPL.

Existing Instance ptr_countable.

#[local] Set Printing Coercions.

Implicit Types (vt : validity_type) (σ : genv) (q : cQp.t).

Module CPP_BASE <: CPP_LOGIC_CLASS.
  Definition addr : Set := N.
  Definition byte : Set := N.
  
  Record cpp_ghost' : Type := {
    blocks_name : gname
  }.
  Definition _cpp_ghost := cpp_ghost'.

  Record cppG' (Σ : gFunctors) : Type := {
    (* Maps pointers to each block's start and size *)
    blocksG : inG Σ (gmapUR ptr (agreeR (leibnizO (N * N))));
    has_inv' : invGS Σ;
    has_cinv' : cinvG Σ
  }.

  Definition cppPreG := cppG'.

  Definition has_inv Σ : cppPreG Σ -> invGS Σ := @has_inv' Σ.
  Definition has_cinv Σ : cppPreG Σ -> cinvG Σ := @has_cinv' Σ.
  
  Include CPP_LOGIC_CLASS_MIXIN.

  Section with_cpp.
    Context `{!cpp_logic thread_info Σ}.

    Existing Class cppG'.
    #[local] Instance cppPreG_cppG' : cppG' Σ := cpp_has_cppG.
    #[local] Existing Instances blocksG.

    Definition blocks_own (p : ptr) (s e : N) : mpred :=
      own (A := gmapUR ptr (agreeR (leibnizO (N * N))))
        cpp_ghost.(blocks_name) {[ p := to_agree (s, e) ]}.
  End with_cpp.

End CPP_BASE.

(* Module Type CPP_VIRTUAL.
  Import CPP_BASE.

  Parameter vbyte : forall `{!cpp_logic thread_info Σ}
    (va : addr) (rv : runtime_val') (q : Qp), mpred.
  Section with_cpp.
    Context `{cpp_logic}.

    Axiom vbyte_fractional : forall va rv, Fractional (vbyte va rv).
    Axiom vbyte_timeless : forall va rv q, Timeless (vbyte va rv q).
    #[global] Existing Instances vbyte_fractional vbyte_timeless.

    Definition vbytes (a : addr) (rv : list runtime_val') (q : Qp) : mpred :=
      [∗list] o ↦ v ∈ rv, (vbyte (a+N.of_nat o)%N v q).

    #[global] Instance vbytes_fractional va rv : Fractional (vbytes va rv).
    Proof. apply fractional_big_sepL; intros. apply vbyte_fractional. Qed.

    #[global] Instance vbytes_as_fractional va rv q :
      AsFractional (vbytes va rv q) (vbytes va rv) q.
    Proof. exact: Build_AsFractional. Qed.

    #[global] Instance vbytes_timeless va rv q : Timeless (vbytes va rv q) := _.
  End with_cpp.
End CPP_VIRTUAL. *)

Module CPP <: CPP_LOGIC.
  Import CPP_BASE.

  Section with_cpp.
    Context `{cpp_logic}.

    Definition _valid_ptr `{σ : genv} vt (p : ptr) : mpred :=
      match vt with
      | Relaxed =>
        [| p = nullptr |] \\//
        Exists base s e,
          blocks_own base s e **
          [|
            ∃ o no,
              (s <= no <= s + e)%N /\
              ptr_vaddr σ p <> Some 0%N /\
              eval_offset σ o = Some (Z.of_N no) /\
              p = base ,, o
          |]
      | Strict =>
        Exists base s e,
          blocks_own base s e **
          [|
            ∃ o no,
              (s <= no < s + e)%N /\
              ptr_vaddr σ p <> Some 0%N /\
              eval_offset σ o = Some (Z.of_N no) /\
              p = base ,, o
          |]
      end.
    
    Notation strict_valid_ptr := (_valid_ptr Strict).
    (* relaxed validity (past-the-end allowed) *)
    Notation valid_ptr := (_valid_ptr Relaxed).

    Instance _valid_ptr_persistent `{genv} : ∀ b p, Persistent (_valid_ptr b p).
    Admitted.
    Instance _valid_ptr_affine `{genv} : ∀ b p, Affine (_valid_ptr b p).
    Admitted.
    Instance _valid_ptr_timeless `{genv} : ∀ b p, Timeless (_valid_ptr b p).
    Admitted.

    Lemma valid_ptr_nullptr `{genv} :
      |-- valid_ptr nullptr.
    Proof. now iLeft. Qed.

    Lemma not_strictly_valid_ptr_nullptr `{genv} :
      strict_valid_ptr nullptr |-- False.
    Proof.
      iIntros "H". rewrite /strict_valid_ptr.
      iDestruct "H" as (???) "[H1 H2]".
      iDestruct "H2" as (??) "H2".
      iDestruct "H2" as "(%H2 & %H3)".
      simpl in *. now destruct H3.
    Qed.
      
    Lemma strict_valid_valid `{genv} :
      ∀ p,
        strict_valid_ptr p |-- valid_ptr p.
    Proof.
      intros.
      rewrite /strict_valid_ptr /valid_ptr.
      iIntros "H". iRight.
      iDestruct "H" as (base s e) "H".
      iExists base, s, e.
      iDestruct "H" as "[H1 H2]".
      iSplit. iAssumption.
      iDestruct "H2" as (o no) "H2".
      iDestruct "H2" as "[%H2 H3]".
      iExists o, no. iSplit.
      { iPureIntro. lia. }
      { iAssumption. }
    Qed.

End CPP.