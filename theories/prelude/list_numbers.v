From stdpp Require Import propset option.
From bedrock.prelude Require Import base.
From bedrock.prelude Require Export list numbers.

#[local] Open Scope N_scope.

Definition seqN (from count : N) : list N :=
  N.of_nat <$> seq (N.to_nat from) (N.to_nat count).
#[global] Arguments seqN : simpl never.

Definition replicateN {A} (count : N) (x : A) : list A :=
  replicate (N.to_nat count) x.
#[global] Arguments replicateN : simpl never.
#[deprecated(since="2021-05-26",note="use [replicateN]")]
Notation repeatN := (flip replicateN) (only parsing).

Definition dropN {A} n := drop (A := A) (N.to_nat n).
Definition takeN {A} n := take (A := A) (N.to_nat n).
Definition lengthN {A} xs := N.of_nat (length (A := A) xs).
Definition resizeN {A} n := resize (A := A) (N.to_nat n).
Definition rotateN {A} n xs :=
  dropN (A := A) (n mod lengthN xs) xs ++ takeN (A := A) (n mod lengthN xs) xs.
#[global] Instance lookupN {A}: Lookup N A (list A) := fun i xs => lookup (N.to_nat i) xs.


Lemma fmap_lengthN {A B} (f : A → B) (l : list A) :
  lengthN (f <$> l) = lengthN l.
Proof. by rewrite /lengthN fmap_length. Qed.

Lemma length_lengthN {A} (xs : list A) :
  length xs = N.to_nat (lengthN xs).
Proof. by rewrite /lengthN Nat2N.id. Qed.

Section seqN.
  Lemma seqN_0 n : seqN n 0 = [].
  Proof. done. Qed.

  Lemma cons_seqN len start :
    start :: seqN (N.succ start) len = seqN start (N.succ len).
  Proof. by rewrite /seqN !N2Nat.inj_succ -cons_seq fmap_cons N2Nat.id. Qed.

  (** More natural version of [cons_seqN]. *)
  Lemma seqN_S_start start len :
    seqN start (N.succ len) = start :: seqN (N.succ start) len.
  Proof. apply symmetry, cons_seqN. Qed.

  (** [seqN_S_start], but without matching against [N.succ]. *)
  Lemma seqN_S_start' start len (Hpos : 0 < len) :
    seqN start len = start :: seqN (N.succ start) (N.pred len).
  Proof. by rewrite -{1}(N.succ_pred_pos len) // seqN_S_start. Qed.

  (* Lifts stdpp's [seq_S_end_app] aka stdlib's [seq_S] *)
  Lemma seqN_S_end_app start len :
    seqN start (N.succ len) = seqN start len ++ [start + len].
  Proof.
    rewrite /seqN !N2Nat.inj_succ seq_S_end_app fmap_app /=.
    by rewrite -N2Nat.inj_add N2Nat.id.
  Qed.

  (** [seqN_S_end_app], but without matching against [N.succ]. *)
  Lemma seqN_S_end_app' start len (Hpos : 0 < len) :
    seqN start len = seqN start (N.pred len) ++ [start + N.pred len].
  Proof. by rewrite -{1}(N.succ_pred_pos len) // seqN_S_end_app. Qed.

  Lemma seqN_lengthN len start : lengthN (seqN start len) = len.
  Proof. by rewrite /seqN fmap_lengthN /lengthN seq_length N2Nat.id. Qed.

  Lemma NoDup_seqN j n : NoDup (seqN j n).
  Proof. apply /NoDup_fmap_2 /NoDup_seq. Qed.
End seqN.

Lemma repeatN_replicateN {A} (x : A) n :
  repeat x (N.to_nat n) = replicateN n x.
Proof. apply repeat_replicate. Qed.

Lemma repeat_replicateN {A} (x : A) n :
  repeat x n = replicateN (N.of_nat n) x.
Proof. by rewrite repeat_replicate /replicateN Nat2N.id. Qed.

Lemma replicateN_0 {A} (x : A) : replicateN 0 x = [].
Proof. done. Qed.

Lemma replicateN_S {A} (x : A) n : replicateN (N.succ n) x = x :: replicateN n x.
Proof. by rewrite /replicateN/= N2Nat.inj_succ. Qed.

Lemma elem_of_replicateN {A} (count : N) (b a : A) : a ∈ replicateN count b → b = a.
Proof. by intros [-> _]%elem_of_replicate. Qed.

Section listN.
  Context {A : Type}.

  Implicit Type (x : A) (xs : list A) (i n m k : N).

  Lemma N2Nat_inj_le n m :
    n ≤ m ->
    (N.to_nat n <= N.to_nat m)%nat.
  Proof. lia. Qed.

  Lemma elem_of_seqN (len start n : N) :
    n ∈ seqN start len ↔ start <= n < start + len.
  Proof.
    rewrite /seqN -{1} (N2Nat.id n) elem_of_list_fmap_inj.
    rewrite elem_of_seq. lia.
  Qed.

  Lemma Forall_seqN P i n :
    List.Forall P (seqN i n) ↔ (∀ j : N, i <= j < i + n → P j).
  Proof. rewrite Forall_forall. by setoid_rewrite elem_of_seqN. Qed.

  (* TODO: extend the theory of [lengthN], we have few lemmas here. *)
  Lemma nil_lengthN :
    lengthN (A := A) [] = 0.
  Proof. done. Qed.

  Lemma cons_lengthN x xs :
    lengthN (x :: xs) = N.succ (lengthN xs).
  Proof. by rewrite /lengthN cons_length Nat2N.inj_succ. Qed.

  Lemma replicateN_zero x :
    replicateN 0 x = [].
  Proof. reflexivity. Qed.

  Lemma replicateN_succ n x :
    replicateN (n + 1) x = x :: replicateN n x.
  Proof. by rewrite /replicateN N.add_1_r N2Nat.inj_succ/=. Qed.

  Lemma replicateN_succ' n x :
    replicateN (n + 1) x = replicateN n x ++ [x].
  Proof.
    elim/N.induction: n=> [|n IH]//.
    rewrite -N.add_1_r replicateN_succ {2}replicateN_succ/=.
    by rewrite IH.
  Qed.

  Definition replicateN_simpl :=
    (@replicateN_zero, @replicateN_succ).

  Lemma replicateN_cons n x :
    0 < n ->
    replicateN n x = x :: replicateN (n - 1) x.
  Proof.
    rewrite /replicateN N2Nat.inj_sub. elim/N.case_analysis: n=> [|n']// _.
    by rewrite N2Nat.inj_succ/= Nat.sub_0_r.
  Qed.

  (* Lift all theory about [drop] and [replicate] interaction. *)
  Lemma dropN_replicateN n m x :
    dropN n (replicateN m x) = replicateN (m - n) x.
  Proof. by rewrite /dropN /replicateN drop_replicate N2Nat.inj_sub. Qed.

  Lemma dropN_replicateN_plus n m x :
    dropN n (replicateN (n + m) x) = replicateN m x.
  Proof. by rewrite /dropN /replicateN N2Nat.inj_add drop_replicate_plus. Qed.

  (* Lift all theory about [take] and [replicate] interaction. *)
  Lemma takeN_replicateN n m x :
    takeN n (replicateN m x) = replicateN (n `min` m) x.
  Proof. by rewrite /takeN /replicateN take_replicate N2Nat.inj_min. Qed.

  Lemma takeN_replicateN_plus n m x :
    takeN n (replicateN (n + m) x) = replicateN n x.
  Proof. by rewrite /takeN /replicateN N2Nat.inj_add take_replicate_plus. Qed.

  Lemma to_nat_lengthN xs :
    N.to_nat (lengthN xs) = length xs.
  Proof. by rewrite /lengthN Nat2N.id. Qed.

  Lemma lengthN_fold xs :
    N.of_nat (length xs) = lengthN xs.
  Proof. reflexivity. Qed.

  Lemma lengthN_nil :
    lengthN (A := A) [] = 0.
  Proof. reflexivity. Qed.

  Lemma lengthN_cons x xs :
    lengthN (x :: xs) = (lengthN xs) + 1.
  Proof. rewrite N.add_1_r /lengthN/=. by case: (length xs). Qed.

  Lemma lengthN_one x :
    lengthN [x] = 1.
  Proof. reflexivity. Qed.

  Lemma lengthN_app xs1 xs2 :
    lengthN (xs1 ++ xs2) = lengthN xs1 + lengthN xs2.
  Proof. by rewrite /lengthN app_length Nat2N.inj_add. Qed.

  Lemma lengthN_map {B} (f : A -> B) xs :
    lengthN (map f xs) = lengthN xs.
  Proof. by rewrite /lengthN map_length. Qed.

  Lemma lengthN_dropN k xs :
    lengthN (dropN k xs) = lengthN xs - k.
  Proof. by rewrite /lengthN/dropN drop_length Nat2N.inj_sub N2Nat.id. Qed.

  Lemma lengthN_takeN k xs :
    lengthN (takeN k xs) = k `min` lengthN xs.
  Proof. by rewrite /lengthN/takeN take_length Nat2N.inj_min N2Nat.id. Qed.

  Lemma lengthN_rotateN k xs :
    lengthN (rotateN k xs) = lengthN xs.
  Proof. rewrite /rotateN lengthN_app lengthN_dropN lengthN_takeN. lia. Qed.

  Lemma lengthN_replicateN n x :
    lengthN (replicateN n x) = n.
  Proof. by rewrite /lengthN/replicateN replicate_length N2Nat.id. Qed.

  Definition lengthN_simpl :=
    (@lengthN_fold,
     @lengthN_nil, @lengthN_cons,
     @lengthN_app, @lengthN_map,
     @lengthN_dropN, @lengthN_takeN,
     @lengthN_rotateN, @lengthN_replicateN).

  Lemma resizeN_spec l n x :
    resizeN n x l = takeN n l ++ replicateN (n - lengthN l) x.
  Proof.
    by rewrite /resizeN /replicateN resize_spec !N2Nat.inj_sub Nat2N.id.
  Qed.

  Lemma resizeN_all l x : resizeN (lengthN l) x l = l.
  Proof. by rewrite /resizeN /lengthN Nat2N.id resize_all. Qed.

  Lemma resizeN_0 l x : resizeN 0 x l = [].
  Proof. by rewrite /resizeN resize_0. Qed.

  Lemma resizeN_lengthN l n x :
    lengthN (resizeN n x l) = n.
  Proof. by rewrite /lengthN /resizeN /= resize_length N2Nat.id. Qed.

  Lemma resizeN_nil n x : resizeN n x [] = replicateN n x.
  Proof. apply resize_nil. Qed.

  Lemma resizeN_replicateN x n m:
    resizeN n x (replicateN m x) = replicateN n x.
  Proof. by rewrite /resizeN /replicateN resize_replicate. Qed.

  Lemma resizeN_idemp l n x :
    resizeN n x (resizeN n x l) = resizeN n x l.
  Proof. apply resize_idemp. Qed.

  Lemma resizeN_plusN l n m x :
    resizeN (n + m) x l = resizeN n x l ++ resizeN m x (dropN n l).
  Proof. by rewrite /resizeN /dropN N2Nat.inj_add resize_plus. Qed.

  Lemma resizeN_takeN_eq l n x :
    resizeN n x (takeN n l) = resizeN n x l.
  Proof. apply resize_take_eq. Qed.

  Lemma resizeN_le l n x :
    n <= lengthN l ->
    resizeN n x l = takeN n l.
  Proof. move=> /N2Nat_inj_le. rewrite to_nat_lengthN. apply resize_le. Qed.

  Lemma resizeN_takeN_le l n m x :
    (n <= m) → resizeN n x (takeN m l) = resizeN n x l.
  Proof. move=> /N2Nat_inj_le. apply resize_take_le. Qed.

  Lemma dropN_lengthN n xs :
    lengthN xs <= n -> dropN n xs = [].
  Proof.
    rewrite /lengthN/dropN=> /N2Nat_inj_le. rewrite Nat2N.id.
    by apply: drop_ge.
  Qed.

  Lemma dropN_zero xs :
    dropN 0 xs = xs.
  Proof. reflexivity. Qed.

  Lemma dropN_one x xs :
    dropN 1 (x :: xs) = xs.
  Proof. reflexivity. Qed.

  Lemma dropN_nil n :
    dropN (A := A) n [] = [].
  Proof. rewrite /dropN. by case: (N.to_nat _). Qed.

  Lemma dropN_app n xs1 xs2 :
    dropN n (xs1 ++ xs2) = dropN n xs1 ++ dropN (n - lengthN xs1) xs2.
  Proof.
    rewrite /dropN/lengthN N2Nat.inj_sub Nat2N.id. by apply: skipn_app.
  Qed.

  Lemma dropN_dropN n m xs :
    dropN n (dropN m xs) = dropN (n + m) xs.
  Proof.
    rewrite /dropN N2Nat.inj_add Nat.add_comm. by apply: drop_drop.
  Qed.

  Lemma dropN_takeN n m xs :
    dropN n (takeN m xs) = takeN (m - n) (dropN n xs).
  Proof.
    rewrite /dropN/takeN N2Nat.inj_sub. by apply: skipn_firstn_comm.
  Qed.

  Lemma dropN_resizeN_plus l m n x :
    dropN n (resizeN (n + m) x l) = resizeN m x (dropN n l).
  Proof. by rewrite /dropN /resizeN N2Nat.inj_add drop_resize_plus. Qed.

  Lemma dropN_resizeN_le l n m x :
    n <= m →
    dropN n (resizeN m x l) = resizeN (m - n) x (dropN n l).
  Proof.
    move=> /N2Nat_inj_le Hle.
    by rewrite /dropN /resizeN drop_resize_le // N2Nat.inj_sub.
  Qed.

  Lemma takeN_zero xs :
    takeN 0 xs = [].
  Proof. reflexivity. Qed.

  Lemma takeN_one x xs :
    takeN 1 (x :: xs) = [x].
  Proof. reflexivity. Qed.

  Lemma takeN_nil n :
    takeN (A := A) n [] = [].
  Proof. rewrite /takeN. by case: (N.to_nat _). Qed.

  Lemma takeN_lengthN n xs :
    lengthN xs <= n -> takeN n xs = xs.
  Proof.
    rewrite /lengthN/takeN=> /N2Nat_inj_le. rewrite Nat2N.id.
    by apply: take_ge.
  Qed.

  Lemma takeN_app n xs1 xs2 :
    takeN n (xs1 ++ xs2) = takeN n xs1 ++ takeN (n - lengthN xs1) xs2.
  Proof.
    rewrite /takeN/lengthN N2Nat.inj_sub Nat2N.id. by apply: firstn_app.
  Qed.

  Lemma takeN_takeN n m xs :
    takeN n (takeN m xs) = takeN (n `min` m) xs.
  Proof.
    rewrite /takeN N2Nat.inj_min. by apply: take_take.
  Qed.

  Lemma takeN_dropN n m xs :
    takeN n (dropN m xs) = dropN m (takeN (m + n) xs).
  Proof.
    rewrite /dropN/takeN N2Nat.inj_add. by apply: firstn_skipn_comm.
  Qed.

  Lemma takeN_resizeN_eq l n x :
    takeN n (resizeN n x l) = resizeN n x l.
  Proof. apply take_resize_eq. Qed.

  Lemma takeN_resizeN l n m x :
    takeN n (resizeN m x l) = resizeN (n `min` m) x l.
  Proof. by rewrite /takeN /resizeN take_resize N2Nat.inj_min. Qed.

  Lemma takeN_resizeN_plus l n m x :
    takeN n (resizeN (n + m) x l) = resizeN n x l.
  Proof. by rewrite /takeN /resizeN N2Nat.inj_add take_resize_plus. Qed.

  Lemma takeN_resizeN_le l n m x  :
    n ≤ m →
    takeN n (resizeN m x l) = resizeN n x l.
  Proof. move=> /N2Nat_inj_le. apply take_resize_le. Qed.

  Lemma rotateN_fold k xs :
    rotate (N.to_nat k) xs = rotateN k xs.
  Proof.
    rewrite /rotateN/rotate/dropN/takeN.
    case: xs=> [|x xs]; first by rewrite !drop_nil !take_nil.
    rewrite -Z_N_nat Z2N.inj_mod//; last by lia.
    by rewrite N_nat_Z N2Z.id -Z_nat_N Nat2Z.id lengthN_fold.
  Qed.

  Definition head_list {A} (xs : list A) := option_list (hd_error xs).

  Lemma tail_drop xs : tail xs = drop 1 xs.
  Proof. reflexivity. Qed.

  Lemma head_take xs : head_list xs = take 1 xs.
  Proof. by case: xs. Qed.

  Lemma rotateN_iter k xs :
    rotateN k xs = N.iter k (fun xs => tail xs ++ head_list xs) xs.
  Proof.
    elim/N.induction: k xs=> [|k IH] xs.
    { by rewrite /rotateN/rotate/= app_nil_r. }
    rewrite N.iter_succ//= -IH -N.add_1_r.
    rewrite -!rotateN_fold /rotate tail_drop head_take.
    case: xs=> [|x1 xs]; first by do !rewrite drop_nil take_nil.
    case: xs=> [|x2 xs]; first by rewrite !Z.mod_1_r/=.
    set n := length (x1 :: x2 :: xs). rewrite !N_nat_Z.
    have ?: (0%nat < n)%Z by apply: inj_lt; apply: Nat.lt_0_succ.
    have ?: (1 < n)%Z by rewrite /n/=; lia.
    have ?: (0 <= k)%Z by apply: N2Z.is_nonneg.
    have ?: (0 <= k `mod` n < n)%Z by apply: Z.mod_pos_bound.
    have ?: (1 <= n - Z.to_nat (k `mod` n))%nat by lia.
    rewrite drop_app_le; last by rewrite drop_length -/n.
    rewrite take_app_le; last by rewrite drop_length -/n.
    rewrite drop_drop -app_assoc take_take_drop.
    rewrite N2Z.inj_add/= -Zplus_mod_idemp_l.
    case/decide: (k `mod` n + 1 = n)%Z=> E.
    - rewrite E Z_mod_same_full/=.
      rewrite -[1%nat]/(Z.to_nat 1) -Z2Nat.inj_add//; last by lia.
      rewrite E Nat2Z.id drop_all firstn_all.
      by rewrite app_nil_l app_nil_r.
    - rewrite Z.mod_small; last by lia.
      by rewrite -[1%nat]/(Z.to_nat 1) -Z2Nat.inj_add//; last by lia.
  Qed.

  Lemma rotateN_nil k :
      rotateN (A := A) k [] = [].
  Proof. by rewrite /rotateN/rotate/= dropN_nil takeN_nil. Qed.

  Lemma rotateN_singleton k x :
    rotateN k [x] = [x].
  Proof. by rewrite -rotateN_fold /rotate Z.mod_1_r/=. Qed.

  Lemma rotateN_zero xs :
    rotateN 0 xs = xs.
  Proof.
    case: xs=> [|x xs]; first by rewrite rotateN_nil.
    by rewrite -rotateN_fold /rotate Z.mod_0_l//= app_nil_r.
  Qed.

  Lemma rotateN_one x xs :
    rotateN 1 (x :: xs) = xs ++ [x].
  Proof.
    rewrite -rotateN_fold /rotate [length (x :: xs)]/=.
    set n := S _. case/Z.lt_eq_cases: (ltac:(lia) : (1 <= n)%Z)=> H.
    - by rewrite Z.mod_1_l//.
    - rewrite -H/= app_nil_r. subst n. case: xs H=> [|??]//=. lia.
  Qed.

  Lemma rotateN_lengthN k xs :
    k = lengthN xs ->
    rotateN k xs = xs.
  Proof.
    move=> -> {k}. rewrite -rotateN_fold /rotate /lengthN Nat2N.id.
    rewrite Z_mod_same_full Z2Nat.inj_0/=. by apply: app_nil_r.
  Qed.

  Lemma rotateN_modulo k xs :
    rotateN (k `mod` lengthN xs) xs = rotateN k xs.
  Proof.
    case: xs=> [|x xs]; first by rewrite !rotateN_nil.
    set xs' := x :: xs. rewrite -!rotateN_fold /rotate/lengthN.
    by rewrite !N_nat_Z N2Z.inj_mod// nat_N_Z Zmod_mod.
  Qed.

  Lemma rotateN_modulo' k xs :
    rotateN (Z.to_N (k `mod` lengthN xs)) xs = rotateN k xs.
  Proof.
    case/N.eq_0_gt_0_cases: (lengthN xs)=> H.
    - case: xs H=> //. by rewrite !rotateN_nil.
    - rewrite Z2N.inj_mod ?N2Z.id; try by lia.
      by rewrite rotateN_modulo.
  Qed.

  Lemma rotateN_plus k1 k2 xs :
    rotateN (k1 + k2) xs = rotateN k1 (rotateN k2 xs).
  Proof. by rewrite !rotateN_iter N.iter_add. Qed.

  Lemma rotateN_succ k x xs :
    rotateN (k + 1) (x :: xs) = rotateN k (xs ++ [x]).
  Proof. by rewrite rotateN_plus rotateN_one. Qed.

  Lemma rotateN_index k xs :
    k <= lengthN xs ->
    rotateN k xs = dropN k xs ++ takeN k xs.
  Proof.
    case/N.le_lteq=> [H|->]; first by rewrite /rotateN N.mod_small//.
    by rewrite rotateN_lengthN// dropN_lengthN// takeN_lengthN//.
  Qed.

  Lemma rotateN_mid k xs zs :
    exists xs' zs', forall y, rotateN k (xs ++ [y] ++ zs) = xs' ++ [y] ++ zs'.
  Proof.
    elim/N.induction: k xs zs=> [|k IH] xs zs.
    - exists xs. exists zs. move=> y. by rewrite rotateN_zero.
    - rewrite -N.add_1_r. case: xs=> [|x xs].
      + case/(_ zs []): IH=> [xs' [zs' IH]].
        exists xs'. exists zs'. move=> y.
        rewrite app_nil_l/= rotateN_succ.
        by apply: IH.
      + case/(_ xs (zs ++ [x])): IH=> [xs' [zs' IH]].
        exists xs'. exists zs'. move=> y.
        rewrite -app_comm_cons rotateN_succ -2!app_assoc.
        by apply: IH.
  Qed.

  Lemma rotateN_replicateN k n x :
    rotateN k (replicateN n x) = replicateN n x.
  Proof. by rewrite -rotateN_fold /replicateN rotate_replicate. Qed.

  Definition rotateN_simpl :=
    (@rotateN_zero, @rotateN_one, @rotateN_succ,
     @rotateN_modulo, @rotateN_singleton, @rotateN_replicateN).

  Lemma lookupN_nil i :
    lookupN (A := A) i [] = None.
  Proof. rewrite /lookupN. by apply: lookup_nil. Qed.

  Lemma lookupN_cons_zero x xs :
    lookupN 0 (x :: xs) = Some x.
  Proof. reflexivity. Qed.

  Lemma lookupN_cons_succ x xs i :
    lookupN (i + 1) (x :: xs) = lookupN i xs.
  Proof. by rewrite /lookupN N.add_1_r N2Nat.inj_succ -lookup_tail. Qed.

  Lemma lookupN_dropN xs k i :
    lookupN i (dropN k xs) = lookupN (k + i) xs.
  Proof. rewrite /lookupN/dropN N2Nat.inj_add. by apply: lookup_drop. Qed.

  Lemma lookupN_takeN xs k i :
    i < k ->
    lookupN i (takeN k xs) = lookupN i xs.
  Proof. rewrite /lookupN/takeN=> H. by apply: lookup_take; lia. Qed.

  Lemma lookupN_is_Some xs i :
    i < lengthN xs <-> is_Some (lookupN i xs).
  Proof. rewrite /lookupN/lengthN lookup_lt_is_Some. lia. Qed.

  Lemma lookupN_is_None {A'} (xs : list A') i :
    i >= lengthN xs <-> lookupN i xs = None.
  Proof. rewrite /lookupN/lengthN lookup_ge_None. lia. Qed.

  Lemma lookupN_replicateN n x i :
    lookupN i (replicateN n x) = Some x <-> i < n.
  Proof.
    rewrite /lookupN/replicateN lookup_replicate. split; [|split=> //]; lia.
  Qed.

  Lemma lookupN_head xs :
    lookupN 0 xs = head xs.
  Proof. by case: xs. Qed.

  Lemma lookupN_tail xs i :
    lookupN i (tail xs) = lookupN (i + 1) xs.
  Proof. rewrite /lookupN N.add_1_r N2Nat.inj_succ. by apply: lookup_tail. Qed.

  Lemma lookupN_app_l xs1 xs2 i :
    i < lengthN xs1 ->
    lookupN i (xs1 ++ xs2) = lookupN i xs1.
  Proof.
    rewrite /lookupN/lengthN=> H. by apply: lookup_app_l; lia.
  Qed.

  Lemma lookupN_app_r xs1 xs2 i :
    i >= lengthN xs1 ->
    lookupN i (xs1 ++ xs2) = lookupN (i - lengthN xs1) xs2.
  Proof.
    rewrite /lookupN/lengthN N2Nat.inj_sub Nat2N.id=> H.
    by apply: lookup_app_r; lia.
  Qed.

  Lemma lookupN_nth_error {A'} i (xs : list A') :
    lookupN i xs = nth_error xs (N.to_nat i).
  Proof.
    elim/N.induction: i xs=> [|i IH]//=; case=> [|x xs]//=.
    - rewrite /lookupN lookup_nil. by case: (N.to_nat).
    - rewrite N2Nat.inj_succ/= /lookupN N2Nat.inj_succ -lookup_tail/=.
      by apply: IH.
  Qed.

  Lemma lookupN_map {B} (f : A -> B) xs i :
    lookupN i (map f xs) = if lookupN i xs is Some x then Some (f x) else None.
  Proof.
    set n := lengthN xs.
    case/decide: (i < n)=> [/lookupN_is_Some[x]/[dup]|/[dup]/lookupN_is_None].
    - by rewrite !lookupN_nth_error=> /(map_nth_error f _ _)=> -> ->.
    - by rewrite /n -(lengthN_map f)=> -> /lookupN_is_None ->.
  Qed.

  Lemma lookupN_rotateN xs k i :
    i < lengthN xs ->
    lookupN i (rotateN k xs) = lookupN ((k + i) mod lengthN xs) xs.
  Proof.
    rewrite /lookupN -rotateN_fold /lengthN=> H.
    rewrite lookup_rotate_r /rotate_nat_add; last by lia.
    f_equal. rewrite !N_nat_Z -N2Z.inj_add -nat_N_Z -N2Z.inj_mod; last by lia.
    by rewrite -Z_N_nat N2Z.id.
  Qed.

  Lemma lookupN_any i xs :
    A (* nonempty *) ->
    (forall x, exists y, x <> y :> A) ->
    (forall x, lookupN i xs = Some x) ->
    False.
  Proof.
    move=> x0 H. case: (lookupN i xs)=> [y|].
    - case/(_ y): H=> x + /(_ x) []. by apply.
    - by case/(_ x0).
  Qed.

  Lemma lookupN_mid i xs zs :
    A (* nonempty *) ->
    (forall x, exists y, x <> y :> A) ->
    (forall y, lookupN i (xs ++ [y] ++ zs) = Some y) ->
    lengthN xs = i.
  Proof.
    move=> x0 H. elim/N.induction: i xs zs=> [|i IH] xs zs.
    - case: xs=> [|x xs]//.
      move/(_ x): H=> [y H].
      move/(_ y). rewrite lookupN_cons_zero=> - [].
      by [].
    - rewrite -N.add_1_r. case: xs=> [|x xs].
      + move=> H'. exfalso. apply: (lookupN_any i zs x0 H).
        move=> y. move/(_ y): H'=> /=. by rewrite lookupN_cons_succ.
      + move/(_ xs zs): IH=> IH. rewrite lengthN_cons.
        move=> H'. f_equal. apply: IH. move=> y. rewrite -H'.
        by rewrite -[(x :: xs) ++ _]app_comm_cons lookupN_cons_succ.
  Qed.

  Definition lookupN_simpl :=
    (@lookupN_nil, @lookupN_cons_zero, @lookupN_cons_succ,
     @lookupN_dropN, @lookupN_takeN,
     @lookupN_is_Some, @lookupN_is_None,
     @lookupN_replicateN,
     @lookupN_tail, @lookupN_head,
     @lookupN_app_l, @lookupN_app_r,
     @lookupN_map,
     @lookupN_rotateN).
End listN.

(* Not necessarily restricted to [Finite] *)
Lemma nat_fin_iter_lt (c : nat) (P : nat -> Prop) :
  Forall P (seq 0 c) ->
  forall i, (i < c)%nat -> P i.
Proof. move=>/Forall_seq /= F. eauto with lia. Qed.

Lemma nat_fin_iter_le (c : nat) (P : nat -> Prop) :
  Forall P (seq 0 (S c)) ->
  forall i, (i <= c)%nat -> P i.
Proof. move=> F i Hle. eapply nat_fin_iter_lt; [done | lia]. Qed.

Lemma N_fin_iter_lt (c : N) (P : N -> Prop) :
  Forall P (seqN 0 c) ->
  forall i, i < c -> P i.
Proof.
  move=> F i Hle. rewrite -(N2Nat.id i).
  apply (nat_fin_iter_lt (N.to_nat c) (P ∘ N.of_nat)); [| lia] => {i Hle}.
  rewrite -Forall_fmap. apply F.
Qed.

Lemma N_fin_iter_le (c : N) (P : N -> Prop) :
  Forall P (seqN 0 (N.succ c)) ->
  forall i, i <= c -> P i.
Proof. move=> F i Hle. eapply N_fin_iter_lt; [done | lia]. Qed.

Lemma N_enumerate n m :
  n < m -> N.recursion False (fun k H => (n = k) \/ H) m.
Proof.
  elim/N.induction: m=> [|m']//=; first by move/N.nlt_0_r.
  rewrite N.recursion_succ// N.lt_succ_r N.lt_eq_cases=> IH.
  case=> [{} /IH IH|H]; by [right|left].
Qed.
