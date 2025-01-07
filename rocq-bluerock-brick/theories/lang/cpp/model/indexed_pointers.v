Require Import stdpp.gmap.
Require Import bedrock.prelude.base.
Require Import bedrock.prelude.addr.
Require Import bedrock.prelude.avl.
Require Import bedrock.prelude.bytestring.
Require Import bedrock.prelude.option.
Require Import bedrock.prelude.numbers.

Require Import bedrock.lang.cpp.syntax.
Require Import bedrock.lang.cpp.semantics.sub_module.
Require Import bedrock.lang.cpp.semantics.values.
Require Import bedrock.lang.cpp.model.simple_pointers_utils.

Implicit Types (σ : genv).
#[local] Close Scope nat_scope.
#[local] Open Scope Z_scope.

Import canonical_tu.
Module LAYERED_PTRS_IMPL <: PTRS_INTF.
  Variant wf_offset_seg `{σ : genv} : type -> Z -> type -> Prop :=
  | WfSub ty i n s :
      Some s = size_of σ ty ->
      (i < n)%N ->
      wf_offset_seg (Tarray ty n) (i * s) ty.
  Inductive wf_offset `{genv} : type -> Z -> type -> Prop :=
  | WfStop ty1 ty2 o :
      wf_offset_seg ty1 o ty2 ->
      wf_offset ty1 o ty2
  | WfStep oL oR ty1 ty2 ty3 :
      wf_offset_seg ty1 oL ty2 ->
      wf_offset ty2 oR ty3 ->
      wf_offset ty1 (oL + oR) ty3.

  Record eff_offset `{genv} := {
    offset_conc : Z;
    offset_src : type;
    offset_tar : type;
    offset_wf : wf_offset offset_src offset_conc offset_tar
  }.
  Variant valid_offset `{genv} :=
  | EffOff (o : eff_offset)
  | IdOff.
  Definition offset `{genv} := option valid_offset.

  Variant root_ptr :=
  | NullPtr
  | GlobalPtr
  | AllocPtr (a : alloc_id)
  | FunPtr (tu : translation_unit_canon) (o : obj_name).

  Record ptr_ `{genv} := {
    ptr_root : root_ptr;
    ptr_offset : valid_offset
  }.
  Definition ptr `{genv} := ptr_.

  Program Definition invalid_ptr `{genv} : ptr := {|
    ptr_root := NullPtr;
    ptr_offset := EffOff {|
      offset_conc := 0;
      offset_src := Tarray Tint 1;
      offset_tar := Tint
    |}
  |}.
  Next Obligation.
    move=> σ.
    eapply WfStop with (o:=0%N).
    eapply WfSub with (i:=0%N).
    - easy.
    - lia.
  Qed.

  Lemma wf_trans `{σ : genv} {oL oR ty1 ty2 ty3} :
    wf_offset ty1 oL ty2 ->
    wf_offset ty2 oR ty3 ->
    wf_offset ty1 (oL + oR) ty3.
  Proof.
    move=> HL HR.
    induction HL.
    - eapply WfStep.
      exact H.
      easy.
    - rewrite <-Z_add_assoc.
      eapply WfStep.
      exact H.
      by apply IHHL.
  Qed.

  Program Definition __o_dot `{genv} (o1 o2 : offset) : offset :=
    o1 ← o1;
    match o1 with
    | EffOff o1 =>
      o2 ← o2;
      match o2 with
      | EffOff o2 =>
        if decide (o1.(offset_tar) = o2.(offset_src)) then
          if decide (o1.(offset_src) = o2.(offset_tar)) then
            Some IdOff
          else
            Some (EffOff {|
              offset_conc := o1.(offset_conc) + o2.(offset_conc);
              offset_src := o1.(offset_src);
              offset_tar := o2.(offset_tar)
            |})
        else
          None
      | IdOff => Some (EffOff o1)
      end
    | IdOff => o2
    end.
  Next Obligation.
    move => σ ??? o1 ? o2 Heq Hneq.
    eapply wf_trans.
    - apply o1.(offset_wf).
    - rewrite Heq.
      apply o2.(offset_wf).
  Qed.

  Definition __offset_ptr `{genv} (p : ptr) (o : offset) : ptr :=
    match __o_dot (Some p.(ptr_offset)) o with
    | Some o' => {|
        ptr_root := p.(ptr_root);
        ptr_offset := o'
      |}
    | None => invalid_ptr
    end.
  
  Definition o_id `{genv} : offset := Some IdOff.

  Theorem id_dot `{genv} : LeftId (=) o_id __o_dot.
  Proof. by move=> [x|]. Qed.
  Theorem dot_id `{genv} : RightId (=) o_id __o_dot.
  Proof. by move=> [[x|]|]. Qed.
  Theorem dot_assoc `{genv} : Assoc (=) __o_dot.
  Proof.
    move=>
      [[[x_con x_src x_tar x_wf]|]|]
      [[[y_con y_src y_tar y_wf]|]|]
      [[[z_con z_src z_tar z_wf]|]|].
    all: (done || simpl).
    admit.
    admit.
    admit.
  Admitted.

  Theorem offset_ptr_id `{genv} : forall p : ptr, __offset_ptr p o_id = p.
  Proof.
    rewrite /__offset_ptr.
    by move => [root [o|]].
  Qed.

  Theorem offset_ptr_dot `{genv} : forall (p : ptr) o1 o2,
    __offset_ptr p (__o_dot o1 o2) = __offset_ptr (__offset_ptr p o1) o2.
  Proof.
    move => p o2 o3.
    rewrite /__offset_ptr dot_assoc.
    admit.
  Admitted.

  Definition nullptr `{genv} : ptr := {|
    ptr_root := NullPtr;
    ptr_offset := IdOff
  |}.

  