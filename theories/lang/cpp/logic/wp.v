(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
(**
 * Definitions for the semantics
 *)
Require Import Coq.Lists.List.
Require Import iris.bi.monpred.
Require Import iris.base_logic.lib.fancy_updates.
From iris.proofmode Require Import tactics classes.

From bedrock.lang.cpp Require Import
     ast semantics logic.pred.

Set Primitive Projections.
Set Default Proof Using "Type".

Local Open Scope bi_scope.

Section with_cpp.
  Context `{Σ : cpp_logic thread_info}.

  (* expression continuations
   * - in full C++, this includes exceptions, but our current semantics
   *   doesn't treat those.
   *)
  Definition epred := mpred.

  Definition FreeTemps := mpred.

  (* [SP] denotes the sequence point for an expression *)
  Definition SP (Q : val -> mpred) (v : val) (free : FreeTemps) : mpred :=
    free ** Q v.

  (* evaluate an expression as an lvalue *)
  Parameter wp_lval
    : forall {resolve:genv}, coPset -> thread_info -> region ->
        Expr ->
        (val -> FreeTemps -> epred) -> (* result -> free -> post *)
        mpred. (* pre-condition *)

  Axiom wp_lval_shift : forall σ M ti ρ e Q,
      (|={M}=> wp_lval (resolve:=σ) M ti ρ e (fun v free => |={M}=> Q v free))
    ⊢ wp_lval (resolve:=σ) M ti ρ e Q.

  Axiom wp_lval_frame :
    forall σ1 σ2 M ti ρ e k1 k2,
      genv_leq σ1 σ2 ->
      Forall v f, k1 v f -* k2 v f |-- @wp_lval σ1 M ti ρ e k1 -* @wp_lval σ2 M ti ρ e k2.
  Global Instance Proper_wp_lval :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==>
            pointwise_relation _ (pointwise_relation _ lentails) ==> lentails)
           (@wp_lval).
  Proof. do 7 red. intros; subst.
         iIntros "X". iRevert "X".
         iApply wp_lval_frame; eauto.
         iIntros (v). iIntros (f). iApply H4.
  Qed.

  Section wp_lval.
    Local Close Scope bi_scope.
    Context {σ : genv} (M : coPset) (ti : thread_info) (ρ : region) (e : Expr).
    Local Notation WP := (wp_lval (resolve:=σ) M ti ρ e) (only parsing).
    Implicit Types P : mpred.
    Implicit Types Q : val → FreeTemps → epred.

    Lemma wp_lval_wand Q1 Q2 : WP Q1 |-- (∀ v f, Q1 v f -* Q2 v f) -* WP Q2.
    Proof. iIntros "Hwp HK". by iApply (wp_lval_frame with "HK Hwp"). Qed.
    Lemma fupd_wp_lval Q : (|={M}=> WP Q) |-- WP Q.
    Proof.
      rewrite -{2}wp_lval_shift. apply fupd_elim. rewrite -fupd_intro.
      iIntros "Hwp". iApply (wp_lval_wand with "Hwp"). auto.
    Qed.
    Lemma wp_lval_fupd Q : WP (λ v f, |={M}=> Q v f) |-- WP Q.
    Proof. iIntros "Hwp". by iApply (wp_lval_shift with "[$Hwp]"). Qed.

    (* proof mode *)
    Global Instance elim_modal_fupd_wp_lval p P Q :
      ElimModal True p false (|={M}=> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_lval.
    Qed.
    Global Instance elim_modal_bupd_wp_lval p P Q :
      ElimModal True p false (|==> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal (bupd_fupd M). exact: elim_modal_fupd_wp_lval.
    Qed.
    Global Instance add_modal_fupd_wp_lval P Q : AddModal (|={M}=> P) P (WP Q).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_lval.
    Qed.
  End wp_lval.

  (* evaluate an expression as an prvalue *)
  Parameter wp_prval
    : forall {resolve:genv}, coPset -> thread_info -> region ->
        Expr ->
        (val -> FreeTemps -> epred) -> (* result -> free -> post *)
        mpred. (* pre-condition *)

  Axiom wp_prval_shift : forall σ M ti ρ e Q,
      (|={M}=> wp_prval (resolve:=σ) M ti ρ e (fun v free => |={M}=> Q v free))
    ⊢ wp_prval (resolve:=σ) M ti ρ e Q.

  Axiom wp_prval_frame :
    forall σ1 σ2 M ti ρ e k1 k2,
      genv_leq σ1 σ2 ->
      Forall v f, k1 v f -* k2 v f |-- @wp_prval σ1 M ti ρ e k1 -* @wp_prval σ2 M ti ρ e k2.
  Global Instance Proper_wp_prval :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==>
            pointwise_relation _ (pointwise_relation _ lentails) ==> lentails)
           (@wp_prval).
  Proof. do 7 red; intros; subst.
         iIntros "X"; iRevert "X".
         iApply wp_prval_frame; eauto.
         iIntros (v); iIntros (f); iApply H4.
  Qed.

  Section wp_prval.
    Local Close Scope bi_scope.
    Context {σ : genv} (M : coPset) (ti : thread_info) (ρ : region) (e : Expr).
    Local Notation WP := (wp_prval (resolve:=σ) M ti ρ e) (only parsing).
    Implicit Types P : mpred.
    Implicit Types Q : val → FreeTemps → epred.

    Lemma wp_prval_wand Q1 Q2 : WP Q1 |-- (∀ v f, Q1 v f -* Q2 v f) -* WP Q2.
    Proof. iIntros "Hwp HK". by iApply (wp_prval_frame with "HK Hwp"). Qed.
    Lemma fupd_wp_prval Q : (|={M}=> WP Q) |-- WP Q.
    Proof.
      rewrite -{2}wp_prval_shift. apply fupd_elim. rewrite -fupd_intro.
      iIntros "Hwp". iApply (wp_prval_wand with "Hwp"). auto.
    Qed.
    Lemma wp_prval_fupd Q : WP (λ v f, |={M}=> Q v f) |-- WP Q.
    Proof. iIntros "Hwp". by iApply (wp_prval_shift with "[$Hwp]"). Qed.

    (* proof mode *)
    Global Instance elim_modal_fupd_wp_prval p P Q :
      ElimModal True p false (|={M}=> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_prval.
    Qed.
    Global Instance elim_modal_bupd_wp_prval p P Q :
      ElimModal True p false (|==> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal (bupd_fupd M). exact: elim_modal_fupd_wp_prval.
    Qed.
    Global Instance add_modal_fupd_wp_prval P Q : AddModal (|={M}=> P) P (WP Q).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_prval.
    Qed.
  End wp_prval.

  (* evaluate an initializing expression
   * - the [val] is the location of the value that is being initialized
   * - the expression denotes a prvalue with a "result object" (see
   *    https://en.cppreference.com/w/cpp/language/value_category)
   *)
  Parameter wp_init
    : forall {resolve:genv}, coPset -> thread_info -> region ->
                        type -> val -> Expr ->
                        (FreeTemps -> epred) -> (* free -> post *)
                        mpred. (* pre-condition *)

  Axiom wp_init_shift : forall σ M ti ρ ty v e Q,
      (|={M}=> wp_init (resolve:=σ) M ti ρ ty v e (fun free => |={M}=> Q free))
    ⊢ wp_init (resolve:=σ) M ti ρ ty v e Q.

  Axiom wp_init_frame :
    forall σ1 σ2 M ti ρ t v e k1 k2,
      genv_leq σ1 σ2 ->
      Forall f, k1 f -* k2 f |-- @wp_init σ1 M ti ρ t v e k1 -* @wp_init σ2 M ti ρ t v e k2.

  Global Instance Proper_wp_init :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==>
            pointwise_relation _ lentails ==> lentails)
           (@wp_init).
  Proof.
    do 9 red; intros; subst.
    iIntros "X"; iRevert "X"; iApply wp_init_frame; eauto.
    iIntros (f); iApply H6.
  Qed.

  Section wp_init.
    Local Close Scope bi_scope.
    Context {σ : genv} (M : coPset) (ti : thread_info) (ρ : region)
      (t : type) (v : val) (e : Expr).
    Local Notation WP := (wp_init (resolve:=σ) M ti ρ t v e) (only parsing).
    Implicit Types P : mpred.
    Implicit Types Q : FreeTemps → epred.

    Lemma wp_init_wand Q1 Q2 : WP Q1 |-- (∀ f, Q1 f -* Q2 f) -* WP Q2.
    Proof. iIntros "Hwp HK". by iApply (wp_init_frame with "HK Hwp"). Qed.
    Lemma fupd_wp_init Q : (|={M}=> WP Q) |-- WP Q.
    Proof.
      rewrite -{2}wp_init_shift. apply fupd_elim. rewrite -fupd_intro.
      iIntros "Hwp". iApply (wp_init_wand with "Hwp"). auto.
    Qed.
    Lemma wp_init_fupd Q : WP (λ f, |={M}=> Q f) |-- WP Q.
    Proof. iIntros "Hwp". by iApply (wp_init_shift with "[$Hwp]"). Qed.

    (* proof mode *)
    Global Instance elim_modal_fupd_wp_init p P Q :
      ElimModal True p false (|={M}=> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_init.
    Qed.
    Global Instance elim_modal_bupd_wp_init p P Q :
      ElimModal True p false (|==> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal (bupd_fupd M). exact: elim_modal_fupd_wp_init.
    Qed.
    Global Instance add_modal_fupd_wp_init P Q : AddModal (|={M}=> P) P (WP Q).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_init.
    Qed.
  End wp_init.

  (* evaluate an expression as an xvalue *)
  Parameter wp_xval
    : forall {resolve:genv}, coPset -> thread_info -> region ->
                        Expr ->
                        (val -> FreeTemps -> epred) -> (* result -> free -> post *)
                        mpred. (* pre-condition *)

  Axiom wp_xval_shift : forall σ M ti ρ e Q,
      (|={M}=> wp_xval (resolve:=σ) M ti ρ e (fun v free => |={M}=> Q v free))
    ⊢ wp_xval (resolve:=σ) M ti ρ e Q.

  Axiom wp_xval_frame :
    forall σ1 σ2 M ti ρ e k1 k2,
      genv_leq σ1 σ2 ->
      Forall v f, k1 v f -* k2 v f |-- @wp_xval σ1 M ti ρ e k1 -* @wp_xval σ2 M ti ρ e k2.
  Global Instance Proper_wp_xval :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==>
            pointwise_relation _ (pointwise_relation _ lentails) ==> lentails)
           (@wp_xval).
  Proof. do 7 red; intros; subst.
         iIntros "X"; iRevert "X".
         iApply wp_xval_frame; eauto.
         iIntros (v); iIntros (f); iApply H4.
  Qed.

  Section wp_xval.
    Local Close Scope bi_scope.
    Context {σ : genv} (M : coPset) (ti : thread_info) (ρ : region) (e : Expr).
    Local Notation WP := (wp_xval (resolve:=σ) M ti ρ e) (only parsing).
    Implicit Types P : mpred.
    Implicit Types Q : val → FreeTemps → epred.

    Lemma wp_xval_wand Q1 Q2 : WP Q1 |-- (∀ v f, Q1 v f -* Q2 v f) -* WP Q2.
    Proof. iIntros "Hwp HK". by iApply (wp_xval_frame with "HK Hwp"). Qed.
    Lemma fupd_wp_xval Q : (|={M}=> WP Q) |-- WP Q.
    Proof.
      rewrite -{2}wp_xval_shift. apply fupd_elim. rewrite -fupd_intro.
      iIntros "Hwp". iApply (wp_xval_wand with "Hwp"). auto.
    Qed.
    Lemma wp_xval_fupd Q : WP (λ v f, |={M}=> Q v f) |-- WP Q.
    Proof. iIntros "Hwp". by iApply (wp_xval_shift with "[$Hwp]"). Qed.

    (* proof mode *)
    Global Instance elim_modal_fupd_wp_xval p P Q :
      ElimModal True p false (|={M}=> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_xval.
    Qed.
    Global Instance elim_modal_bupd_wp_xval p P Q :
      ElimModal True p false (|==> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal (bupd_fupd M). exact: elim_modal_fupd_wp_xval.
    Qed.
    Global Instance add_modal_fupd_wp_xval P Q : AddModal (|={M}=> P) P (WP Q).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_xval.
    Qed.
  End wp_xval.

  (* evaluate an expression as a generalized lvalue *)

  Definition wp_glval {resolve} M ti (r : region) e Q :=
    @wp_lval resolve M ti r e Q \\// @wp_xval resolve M ti r e Q.

  (** note: you can not shift for [wp_glval] because [|==> wp_glval] allows the
      ghost code to decide which side you are in
   *)

  Theorem wp_glval_frame :
    forall σ1 σ2 M ti ρ e k1 k2,
      genv_leq σ1 σ2 ->
      Forall v f, k1 v f -* k2 v f |-- @wp_glval σ1 M ti ρ e k1 -* @wp_glval σ2 M ti ρ e k2.
  Proof.
    intros.
    iIntros "X"; iIntros "W".
    iDestruct "W" as "[W | W]"; [ iLeft | iRight ].
    - iRevert "W". iApply wp_lval_frame; eauto with iFrame.
    - iRevert "W". iApply wp_xval_frame; eauto with iFrame.
  Qed.

  Global Instance Proper_wp_glval :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==>
            pointwise_relation _ (pointwise_relation _ lentails) ==> lentails)
           (@wp_glval).
  Proof using .
    unfold wp_glval; simpl. do 7 red. intros.
    eapply bi.or_elim; [ rewrite <- bi.or_intro_l | rewrite <- bi.or_intro_r ].
    eapply Proper_wp_lval; eauto.
    eapply Proper_wp_xval; eauto.
  Qed.

  Section wp_glval.
    Context {σ : genv} (M : coPset) (ti : thread_info) (ρ : region) (e : Expr).
    Local Notation WP := (wp_glval (resolve:=σ) M ti ρ e) (only parsing).
    Implicit Types Q : val → FreeTemps → epred.

    Lemma wp_glval_wand Q1 Q2 : WP Q1 |-- (∀ v f, Q1 v f -* Q2 v f) -* WP Q2.
    Proof. iIntros "Hwp HK". by iApply (wp_glval_frame with "HK Hwp"). Qed.
    Lemma wp_glval_fupd Q : WP (λ v f, |={M}=> Q v f) |-- WP Q.
    Proof.
      iIntros "[?|?]".
      by iLeft; iApply wp_lval_fupd. by iRight; iApply wp_xval_fupd.
    Qed.
  End wp_glval.

  (* evaluate an expression as an rvalue *)

  Definition wp_rval {resolve} M ti (r : region) e Q :=
    @wp_prval resolve M ti r e Q \\// @wp_xval resolve M ti r e Q.

  Theorem wp_rval_frame :
    forall σ1 σ2 M ti ρ e k1 k2,
      genv_leq σ1 σ2 ->
      Forall v f, k1 v f -* k2 v f |-- @wp_rval σ1 M ti ρ e k1 -* @wp_rval σ2 M ti ρ e k2.
  Proof.
    intros.
    iIntros "X"; iIntros "W".
    iDestruct "W" as "[W | W]"; [ iLeft | iRight ].
    - iRevert "W". iApply wp_prval_frame; eauto with iFrame.
    - iRevert "W". iApply wp_xval_frame; eauto with iFrame.
  Qed.

  (** note: you can not shift for [wp_rval] because [|==> wp_rval] allows the
      ghost code to decide which side you are in
   *)

  Global Instance Proper_wp_rval :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==>
            pointwise_relation _ (pointwise_relation _ lentails) ==> lentails)
           (@wp_rval).
  Proof using .
    unfold wp_rval; simpl. do 7 red. intros.
    eapply bi.or_elim; [ rewrite <- bi.or_intro_l | rewrite <- bi.or_intro_r ].
    eapply Proper_wp_prval; eauto.
    eapply Proper_wp_xval; eauto.
  Qed.

  Section wp_rval.
    Context {σ : genv} (M : coPset) (ti : thread_info) (ρ : region) (e : Expr).
    Local Notation WP := (wp_rval (resolve:=σ) M ti ρ e) (only parsing).
    Implicit Types Q : val → FreeTemps → epred.

    Lemma wp_rval_wand Q1 Q2 : WP Q1 |-- (∀ v f, Q1 v f -* Q2 v f) -* WP Q2.
    Proof. iIntros "Hwp HK". by iApply (wp_rval_frame with "HK Hwp"). Qed.
    Lemma wp_rval_fupd Q : WP (λ v f, |={M}=> Q v f) |-- WP Q.
    Proof.
      iIntros "[?|?]".
      by iLeft; iApply wp_prval_fupd. by iRight; iApply wp_xval_fupd.
    Qed.
  End wp_rval.

  Section wpe.
    Context {resolve:genv}.
    Variable (M : coPset) (ti : thread_info) (ρ : region).

    Definition wpe (vc : ValCat)
      : Expr -> (val -> FreeTemps -> mpred) -> mpred :=
      match vc with
      | Lvalue => @wp_lval resolve M ti ρ
      | Rvalue => @wp_prval resolve M ti ρ
      | Xvalue => @wp_xval resolve M ti ρ
      end.

    Definition wpAny (vce : ValCat * Expr)
      : (val -> FreeTemps -> mpred) -> mpred :=
      let '(vc,e) := vce in
      wpe vc e.

    Definition wpAnys := fun ve Q free => wpAny ve (fun v f => Q v (f ** free)).
  End wpe.

  Lemma wpe_frame σ1 σ2 M ti ρ vc e k1 k2:
    genv_leq σ1 σ2 ->
    Forall v f, k1 v f -* k2 v f |-- wpe (resolve := σ1) M ti ρ vc e k1 -* wpe (resolve:=σ2) M ti ρ vc e k2.
  Proof. destruct vc => /=; by [apply wp_lval_frame| apply wp_prval_frame | apply wp_xval_frame ]. Qed.

  Global Instance Proper_wpe :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> eq ==> (eq ==> lentails ==> lentails) ==> lentails)
           (@wpe).
  Proof.
    do 9 red; intros; subst.
    iIntros "X"; iRevert "X"; iApply wpe_frame; eauto.
    iIntros (v f); iApply H5; reflexivity.
  Qed.

  Lemma wpAny_frame σ1 σ2 M ti ρ e k1 k2:
    genv_leq σ1 σ2 ->
    Forall v f, k1 v f -* k2 v f |-- wpAny (resolve := σ1) M ti ρ e k1 -* wpAny (resolve:=σ2) M ti ρ e k2.
  Proof. destruct e; apply: wpe_frame. Qed.

  Global Instance Proper_wpAny :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> (eq ==> lentails ==> lentails) ==> lentails)
           (@wpAny).
  Proof.
    do 9 red; intros; subst.
    iIntros "X"; iRevert "X"; iApply wpAny_frame; eauto.
    iIntros (v f); iApply H4; reflexivity.
  Qed.

  (** initializers *)
  Parameter wpi
    : forall {resolve:genv} (M : coPset) (ti : thread_info) (ρ : region)
        (cls : globname) (this : val) (init : Initializer)
        (Q : mpred -> mpred), mpred.

  Axiom wpi_shift : forall σ M ti ρ cls this e Q,
      (|={M}=> wpi (resolve:=σ) M ti ρ cls this e (fun k => |={M}=> Q k))
    ⊢ wpi (resolve:=σ) M ti ρ cls this e Q.

  Axiom wpi_frame :
    forall σ1 σ2 M ti ρ cls this e k1 k2,
      genv_leq σ1 σ2 ->
      Forall f, k1 f -* k2 f |-- @wpi σ1 M ti ρ cls this e k1 -* @wpi σ2 M ti ρ cls this e k2.

  Global Instance Proper_wpi :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> (lentails ==> lentails) ==> lentails)
           (@wpi).
  Proof. do 9 red; intros; subst.
         iIntros "X"; iRevert "X"; iApply wpi_frame; eauto.
         iIntros (f); iApply H6. reflexivity.
  Qed.

  Section wpi.
    Local Close Scope bi_scope.
    Context {σ : genv} (M : coPset) (ti : thread_info) (ρ : region)
      (cls : globname) (this : val) (init : Initializer).
    Local Notation WP := (wpi (resolve:=σ) M ti ρ cls this init) (only parsing).
    Implicit Types P : mpred.
    Implicit Types k : mpred → mpred.

    Lemma wpi_wand k1 k2 : WP k1 |-- (∀ Q, k1 Q -* k2 Q) -* WP k2.
    Proof. iIntros "Hwp HK". by iApply (wpi_frame with "HK Hwp"). Qed.
    Lemma fupd_wpi k : (|={M}=> WP k) |-- WP k.
    Proof.
      rewrite -{2}wpi_shift. apply fupd_elim. rewrite -fupd_intro.
      iIntros "Hwp". iApply (wpi_wand with "Hwp"). auto.
    Qed.
    Lemma wpi_fupd k : WP (λ Q, |={M}=> k Q) |-- WP k.
    Proof. iIntros "Hwp". by iApply (wpi_shift with "[$Hwp]"). Qed.

    (* proof mode *)
    Global Instance elim_modal_fupd_wpi p P k :
      ElimModal True p false (|={M}=> P) P (WP k) (WP k).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wpi.
    Qed.
    Global Instance elim_modal_bupd_wpi p P k :
      ElimModal True p false (|==> P) P (WP k) (WP k).
    Proof.
      rewrite /ElimModal (bupd_fupd M). exact: elim_modal_fupd_wpi.
    Qed.
    Global Instance add_modal_fupd_wpi P k : AddModal (|={M}=> P) P (WP k).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wpi.
    Qed.
  End wpi.

  (** destructors *)
  Parameter wpd
    : forall {resolve:genv} (M : coPset) (ti : thread_info) (ρ : region)
        (cls : globname) (this : val)
        (init : FieldOrBase * obj_name)
        (Q : epred), mpred.

  Axiom wpd_shift : forall σ M ti ρ cls this e Q,
      (|={M}=> wpd (resolve:=σ) M ti ρ cls this e (|={M}=> Q))
    ⊢ wpd (resolve:=σ) M ti ρ cls this e Q.

  Axiom wpd_frame :
    forall σ1 σ2 M ti ρ cls this e k1 k2,
      genv_leq σ1 σ2 ->
      k1 -* k2 |-- @wpd σ1 M ti ρ cls this e k1 -* @wpd σ2 M ti ρ cls this e k2.

  Global Instance Proper_wpd :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> lentails ==> lentails)
           (@wpd).
  Proof. do 9 red; intros; subst.
         iIntros "X"; iRevert "X"; iApply wpd_frame; eauto.
         iApply H6.
  Qed.

  Section wpd.
    Local Close Scope bi_scope.
    Context {σ : genv} (M : coPset) (ti : thread_info) (ρ : region)
      (cls : globname) (this : val) (init : FieldOrBase * obj_name).
    Local Notation WP := (wpd (resolve:=σ) M ti ρ cls this init) (only parsing).
    Implicit Types P : mpred.
    Implicit Types k : mpred.

    Lemma wpd_wand k1 k2 : WP k1 |-- (k1 -* k2) -* WP k2.
    Proof. iIntros "Hwp HK". by iApply (wpd_frame with "HK Hwp"). Qed.
    Lemma fupd_wpd k : (|={M}=> WP k) |-- WP k.
    Proof.
      rewrite -{2}wpd_shift. apply fupd_elim. rewrite -fupd_intro.
      iIntros "Hwp". iApply (wpd_wand with "Hwp"). auto.
    Qed.
    Lemma wpd_fupd k : WP (|={M}=> k) |-- WP k.
    Proof. iIntros "Hwp". by iApply (wpd_shift with "[$Hwp]"). Qed.

    (* proof mode *)
    Global Instance elim_modal_fupd_wpd p P k :
      ElimModal True p false (|={M}=> P) P (WP k) (WP k).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wpd.
    Qed.
    Global Instance elim_modal_bupd_wpd p P k :
      ElimModal True p false (|==> P) P (WP k) (WP k).
    Proof.
      rewrite /ElimModal (bupd_fupd M). exact: elim_modal_fupd_wpd.
    Qed.
    Global Instance add_modal_fupd_wpd P k : AddModal (|={M}=> P) P (WP k).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wpd.
    Qed.
  End wpd.

  (** Statements *)
  (* continuations
   * C++ statements can terminate in 4 ways.
   *
   * note(gmm): technically, they can also raise exceptions; however,
   * our current semantics doesn't capture this. if we want to support
   * exceptions, we should be able to add another case,
   * `k_throw : val -> mpred`.
   *)
  Record Kpreds :=
    { k_normal   : mpred
    ; k_return   : option val -> FreeTemps -> mpred
    ; k_break    : mpred
    ; k_continue : mpred
    }.

  Instance Kpreds_fupd: FUpd Kpreds :=
    fun l r Q =>
      {| k_normal := |={l,r}=> Q.(k_normal)
       ; k_return v f := |={l,r}=> Q.(k_return) v f
       ; k_break := |={l,r}=> Q.(k_break)
       ; k_continue := |={l,r}=> Q.(k_continue) |}.

  Definition void_return (P : mpred) : Kpreds :=
    {| k_normal := P
     ; k_return := fun r free => match r with
                              | None => free ** P
                              | Some _ => lfalse
                              end
     ; k_break := lfalse
     ; k_continue := lfalse
    |}.

  Definition val_return (P : val -> mpred) : Kpreds :=
    {| k_normal := lfalse
     ; k_return := fun r free => match r with
                              | None => lfalse
                              | Some v => free ** P v
                              end
     ; k_break := lfalse
     ; k_continue := lfalse |}.

  Definition Kseq (Q : Kpreds -> mpred) (k : Kpreds) : Kpreds :=
    {| k_normal   := Q k
     ; k_return   := k.(k_return)
     ; k_break    := k.(k_break)
     ; k_continue := k.(k_continue) |}.

  (* loop with invariant `I` *)
  Definition Kloop (I : mpred) (Q : Kpreds) : Kpreds :=
    {| k_break    := Q.(k_normal)
     ; k_continue := I
     ; k_return   := Q.(k_return)
     ; k_normal   := Q.(k_normal) |}.

  Definition Kat_exit (Q : mpred -> mpred) (k : Kpreds) : Kpreds :=
    {| k_normal   := Q k.(k_normal)
     ; k_return v free := Q (k.(k_return) v free)
     ; k_break    := Q k.(k_break)
     ; k_continue := Q k.(k_continue) |}.

  Definition Kfree (a : mpred) : Kpreds -> Kpreds :=
    Kat_exit (fun P => a ** P).

  Close Scope bi_scope.

  Definition Kpred_entails (k1 k2 : Kpreds) : Prop :=
      k1.(k_normal) |-- k2.(k_normal) ∧
      (∀ v free, k1.(k_return) v free |-- k2.(k_return) v free) ∧
      k1.(k_break) |-- k2.(k_break) ∧
      k1.(k_continue) |-- k2.(k_continue).

  Global Instance Kpreds_equiv : Equiv Kpreds :=
    fun (k1 k2 : Kpreds) =>
      k1.(k_normal) ≡ k2.(k_normal) ∧
      (∀ v free, k1.(k_return) v free ≡ k2.(k_return) v free) ∧
      k1.(k_break) ≡ k2.(k_break) ∧
      k1.(k_continue) ≡ k2.(k_continue).

  Lemma Kfree_Kfree : forall k P Q, Kfree P (Kfree Q k) ≡ Kfree (P ** Q) k.
  Proof using .
    split; [ | split; [ | split ] ]; simpl; intros;
      eapply bi.equiv_spec; split;
        try solve [ rewrite bi.sep_assoc; eauto ].
  Qed.

  Lemma Kfree_emp : forall k, Kfree empSP k ≡ k.
  Proof using .
    split; [ | split; [ | split ] ]; simpl; intros;
      eapply bi.equiv_spec; split;
        try solve [ rewrite bi.emp_sep; eauto ].
  Qed.

  (* evaluate a statement *)
  Parameter wp
    : forall {resolve:genv}, coPset -> thread_info -> region -> Stmt -> Kpreds -> mpred.

  Axiom wp_shift : forall σ M ti ρ s Q,
      (|={M}=> wp (resolve:=σ) M ti ρ s (|={M}=> Q))
    ⊢ wp (resolve:=σ) M ti ρ s Q.

  Axiom wp_frame :
    forall σ1 σ2 M ti ρ s k1 k2,
      genv_leq σ1 σ2 ->
      (k1.(k_normal) -* k2.(k_normal)) //\\
      (Forall v f, k1.(k_return) v f -* k2.(k_return) v f) //\\
      (k1.(k_break) -* k2.(k_break)) //\\
      (k1.(k_continue) -* k2.(k_continue))
      |-- @wp σ1 M ti ρ s k1 -* @wp σ2 M ti ρ s k2.

  Global Instance Proper_wp :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> Kpred_entails ==> lentails)
           (@wp).
  Proof. do 8 red; intros; subst.
         iIntros "X"; iRevert "X"; iApply wp_frame; eauto.
         destruct H4 as [ ? [ ? [ ? ? ] ] ].
         iSplit; [ iApply H0 | iSplit; [ | iSplit; [ iApply H2 | iApply H3 ] ] ].
         iIntros. iApply H1; eauto.
  Qed.

  Section wp.
    Context {σ : genv} (M : coPset) (ti : thread_info) (ρ : region) (s : Stmt).
    Local Notation WP := (wp (resolve:=σ) M ti ρ s) (only parsing).
    Implicit Types P : mpred.
    Implicit Types Q : Kpreds.

    Lemma wp_wand k1 k2 :
      WP k1 |--
      (* PDS: This conjunction shows up in several places and may
      deserve a definition and some supporting lemmas. *)
      ((k_normal k1 -* k_normal k2) ∧
      (∀ mv f, k_return k1 mv f -* k_return k2 mv f) ∧
      (k_break k1 -* k_break k2) ∧
      (k_continue k1 -* k_continue k2)) -*
      WP k2.
    Proof.
      iIntros "Hwp Hk". by iApply (wp_frame σ _ _ _ _ _ k1 with "[$Hk] Hwp").
    Qed.
    Lemma fupd_wp k : (|={M}=> WP k) |-- WP k.
    Proof.
      rewrite -{2}wp_shift. apply fupd_elim. rewrite -fupd_intro.
      iIntros "Hwp". iApply (wp_wand with "Hwp"). auto.
    Qed.
    Lemma wp_fupd k : WP (|={M}=> k) |-- WP k.
    Proof. iIntros "Hwp". by iApply (wp_shift with "[$Hwp]"). Qed.

    (* proof mode *)
    Global Instance elim_modal_fupd_wp p P k :
      ElimModal True p false (|={M}=> P) P (WP k) (WP k).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp.
    Qed.
    Global Instance elim_modal_bupd_wp p P k :
      ElimModal True p false (|==> P) P (WP k) (WP k).
    Proof.
      rewrite /ElimModal (bupd_fupd M). exact: elim_modal_fupd_wp.
    Qed.
    Global Instance add_modal_fupd_wp P k : AddModal (|={M}=> P) P (WP k).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp.
    Qed.
  End wp.

  (* this is the specification of assembly code
   *
   * [addr] represents the address of the entry point of the code.
   * note: the [list val] will be related to the register set.
   *)
  Parameter fspec
    : forall (tt : type_table) (fun_type : type) (ti : thread_info)
             (addr : val) (ls : list val) (Q : val -> epred), mpred.

  Section sub_decl.
    Variable Rtype : type -> type -> Prop.

    (* [decl_compatible a b g1 g2] states the type declaration [g1] (interpreted
       by the type environment [a]) is at least as defined as the declaration [g2]
       (interpreted by the type environment [b]).

       TODO(gmm): it is unclear if this definition works for cyclic types, e.g.
       [struct T { T* n; };] is not compatible with itself because the
       derivation is infinite.
     *)
    Variant decl_compatible : GlobDecl -> GlobDecl -> Prop :=
    | compat_Gtype : decl_compatible Gtype Gtype
    | compat_Gstruct_Gtype {st} : decl_compatible (Gstruct st) Gtype
    | compat_Gunion_Gtype {u} : decl_compatible (Gunion u) Gtype
    | compat_GtypedefL {t t'} (_ : Rtype t t')
      : decl_compatible (Gtypedef t) (Gtypedef t')
    | compat_Gstruct {st}
                     (_ : forall gn li, In (gn, li) st.(s_bases) -> Rtype (Tnamed gn) (Tnamed gn))
                     (_ : forall x t li, In (x, t, li) st.(s_fields) -> Rtype t t)
      : decl_compatible (Gstruct st) (Gstruct st)
    | compat_Gunion {u}
                    (_ : forall x t li, In (x, t, li) u.(u_fields) -> Rtype t t)
      : decl_compatible (Gunion u) (Gunion u)
    .
  End sub_decl.

  Section type_compatible.
    Variables a b : type_table.

    (* [type_compatible a b t1 t2] states that the type [t1] (interpreted by type
     environment [a]) is at least as defined as the type [t2] (interepreted by
     type environment [b]).

     "At least as defined as" means that they are essentially equal except that
     type environment [t2] might not have a body for a type that type
     environment [t1] has. For example, take the following:

     // x.hpp
     class F;
     class T { F* x; };

     // x.cpp
     #include "x.hpp"
     class F { int x; };

     // y.cpp
     #include "x.hpp"
     class F { bool x; };

     Here:
     - [type_compatible <x.cpp> <x.hpp> (Tnamed "T") (Tnamed "T")] is provable
     - [type_compatible <x.hpp> <y.cpp> (Tnamed "T") (Tnamed "T")] is *not* provable

     NOTE: this might not ensure that types are well-formed.
     Implementation note: as the goal is only to check if types are complete,
     we need not check the contents of pointers and references.
     *)
    Inductive type_compatible' (g : list globname) : type -> type -> Prop :=
    | compat_Tptr {t}
      : type_compatible' g (Tptr t) (Tptr t)
    | compat_Tref {t}
      : type_compatible' g (Tref t) (Tref t)
    | compat_Trf_ref {t}
      : type_compatible' g (Trv_ref t) (Trv_ref t)
    | compat_Tint {sz sgn} : type_compatible' g (Tint sz sgn) (Tint sz sgn)
    | compat_Tvoid : type_compatible' g Tvoid Tvoid
    | compat_Tarray {n t' t} (_ : type_compatible' g t t')
      : type_compatible' g (Tarray t n) (Tarray t' n)
    | compat_Tnamed {n s1 s2} (_ : a !! n = Some s1) (_ : b !! n = Some s2)
                    (_ : decl_compatible (type_compatible' (n :: g)) s1 s2)
      : type_compatible' g (Tnamed n) (Tnamed n)
    | compat_Tfunction {cc t t' args args'} (_ : type_compatible' g t t')
                       (_ : List.Forall2 (type_compatible' g) args args')
      : type_compatible' g (Tfunction (cc:=cc) t args) (Tfunction (cc:=cc) t' args')
    | compat_Tbool : type_compatible' g Tbool Tbool
    | compat_Tmember_pointer {n t t'}
                             (_ : type_compatible' g (Tnamed n) (Tnamed n))
                             (_ : type_compatible' g t t')
      : type_compatible' g (Tmember_pointer n t) (Tmember_pointer n t')
    | compat_Tfloat {sz} : type_compatible' g (Tfloat sz) (Tfloat sz)
    | compat_Tqualified {q t t'} (_ : type_compatible' g t t')
      : type_compatible' g (Tqualified q t) (Tqualified q t')
    | compat_Tnullptr : type_compatible' g Tnullptr Tnullptr
    | compat_Tarch {sz n} : type_compatible' g (Tarch sz n) (Tarch sz n)
    .
  End type_compatible.

  Definition type_compatible a b := type_compatible' a b nil.

  (*
  (* [wf_type' te guarded t] states that the type [t] is defined in the type
     environment [te]. [guarded] is used to track whether or not we are in a
     guarded context

     TODO(gmm): [guarded] doesn't seem sufficient to get around the type
     circularity.
   *)
  Inductive wf_type' (a : type_table) : bool -> type -> Prop := .

  Definition wf_type tt t := wf_type' tt false t.
  *)

  Axiom fspec_wf_type : forall te ft ti a ls Q,
      fspec te ft ti a ls Q
      |-- fspec te ft ti a ls Q **
          [| exists cc tret targs, ft = Tfunction (cc:=cc) tret targs |].

  (* this axiom states that the type environment for an [fspec] can be
     narrowed as long as the new type environment [small] is consistent
     with the old type environment ([big]) on all of the types mentioned
     in the type.

     NOTE: This is informally justified by the fact that (in the absence
     of ODR) the implementation of the function is encapsulated and only
     the public interface (the type) is need to know how to call the function.

     TODO one additional restriction that should be added here is that [ft]
     is a *complete type* in [tt2]. We will revist this when we define complete
     type, but for now, note that if we use this axiom to construct an [fspec tt ft]
     where [ft] is not complete in [tt], then we will not be able to use it in
     any module generated by cpp2v because cpp2v only generates code that
     is well-typed according to C++ which requires that [ft] is complete in the
     type environment of the translation unit.
   *)
  Axiom fspec_strengthen : forall tt1 tt2 ft ti a ls Q,
      type_compatible tt1 tt2 ft ft ->
      fspec tt1 ft ti a ls Q |-- fspec tt2 ft ti a ls Q.

  (* this axiom is the standard rule of consequence for weakest
     pre-condition.
   *)
  Axiom fspec_frame : forall tt ft a ls ti Q1 Q2,
      Forall v, Q1 v -* Q2 v |-- @fspec tt ft ti a ls Q1 -* @fspec tt ft ti a ls Q2.

  Global Instance Proper_fspec : forall tt ft a ls ti,
      Proper (pointwise_relation _ lentails ==> lentails) (@fspec tt ft ti a ls).
  Proof. do 3 red; intros.
         rewrite fspec_wf_type.
         iIntros "[X %]"; iRevert "X"; iApply fspec_frame; auto.
         iIntros (v); iApply H.
  Qed.

  Section fspec.
    Context {tt : type_table} {tf : type} (ti : thread_info) (addr : val) (ls : list val).
    Local Notation WP := (fspec tt tf ti addr ls) (only parsing).
    Implicit Types Q : val → epred.

    Lemma fspec_wand Q1 Q2 : WP Q1 |-- (∀ v, Q1 v -* Q2 v) -* WP Q2.
    Proof. iIntros "Hwp HK".
           iDestruct (fspec_wf_type with "Hwp") as "[Hwp %]".
           iApply (fspec_frame with "HK Hwp").
    Qed.
  End fspec.

End with_cpp.

Export stdpp.coPset.
