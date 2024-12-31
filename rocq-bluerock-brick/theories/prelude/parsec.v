(*
 * Copyright (C) BlueRock Security Inc. 2023-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.prelude.
Require Import bedrock.prelude.bytestring.

Require Export bedrock.upoly.upoly.
Require Export bedrock.upoly.parsec.

#[local] Set Universe Polymorphism.
#[local] Unset Universe Minimization ToSet.

Import UPoly.
Section char_parsec.
  Context {F : Type -> Type} {MR : MRet F} {FM : FMap F} {MB : MBind F}.
  Notation M := (M bs F).

  #[global] Instance bs_next : Next bs Byte.byte := {|
    next_token bs :=
      match bs with
      | BS.EmptyString => None
      | BS.String x bs => Some (x, bs)
      end
  |}.
  #[global] Instance bs_parse_string : ParseString bs bs := {|
    parse_string :=
      fix go str bs {struct str} :=
        match str, bs with
        | BS.EmptyString, _ => Some bs
        | BS.String x str, BS.String y bs =>
            if bool_decide (x = y) then
              go str bs
            else
              None
        | BS.String _ _, BS.EmptyString => None
        end
  |}.

  Definition run_bs {T} (p : M T) (b : bs) : F (option (bs * T)) := run p b.

  Definition run_full_bs {T} (p : M T) (b : bs) : F (option T) := run_full p b.

  Definition digit : M Byte.byte :=
    char (fun x => bool_decide (Byte.to_N "0" ≤ Byte.to_N x ≤ Byte.to_N "9")%N).

  Definition exact_bs (b : bs) : M unit :=
    exact $ b.

  Definition exact_char (b : Byte.byte) : M unit :=
    fmap (fun _ => ()) $ char (fun b' => bool_decide (b = b')).

  Definition quoted {U V T} (pre : M U) (post : M V) (p : M T) : M T :=
    (fun _ x _ => x) <$> pre <*> p <*> post.

  Definition ws : M unit :=
    const () <$> (star $ char (fun x => strings.Ascii.is_space $ Ascii.ascii_of_byte x)).

  Definition ignore_ws {T} (p : M T) : M T :=
    quoted ws ws p.

  (* A note about effects:
     [not p] will roll-back monadic changes of parsec, but will *not* roll back
     monadic changes in [F]. Therefore, users should be careful about [F] effects
     in [p]. Generally, [p] should be effect free in [F].
   *)
End char_parsec.


(* The combination of [compile] and [interp] create an optimized parser
   based on a list of literals.

   More optimizations are likely possible here.
 *)
Module keyword_set.
Section keyword_set.
  Import parsec.
  Import UPoly.

  #[local] Open Scope monad_scope.

  Context {token : Set}.
  Context {token_dec : EqDecision token}.
  #[local] Fixpoint deriv {A} (ls : list (list token * A)) (b : token)
    : option (option A * list (list token * A) * list (list token * A)) :=
    match ls with
    | nil => Some (None, nil, nil)
    | ([], t) :: rest =>
        let* '(a,l,r) := deriv rest b in
        match a with
        | None => Some (Some t, l, r)
        | _ => None
        end
    | (x :: xs, t) :: rest =>
        let* '(a, l, r) := deriv rest b in
        if bool_decide (x = b) then
          Some (a, (xs, t) :: l, r)
        else
          Some (a, l, (x :: xs, t) :: r)
    end.

  (* Generic compilation infrastructure *)
  Inductive DTree {T : Type} : Type :=
  | FAIL
  | OK (_ : list token) (_ : T)
  | OR (_ _ : DTree)
  | COMMIT (_ : token) (_ : DTree) (_ : DTree).
  Arguments DTree _ : clear implicits.

  #[local] Definition opt_COMMIT {T} a (b c : DTree T) :=
    match b , c with
    | OK xs v , FAIL => OK (a :: xs) v
    | _ , _ => COMMIT a b c
    end.

  Fixpoint compile {A} (fuel : nat) (ls : list (list token * A)) {struct fuel} : option (DTree A) :=
    match ls with
    | nil => Some FAIL
    | (xs, t) :: nil =>
        Some (OK xs t)
    | ([], t) :: ls =>
        match fuel with
        | S fuel =>
            let* r := compile fuel ls in
            mret (OR r (OK [] t))
        | _ => None
        end
    | (b :: bs, t) :: ls =>
        let* '(eps, here, rest) := deriv ls b in
        match fuel with
        | S fuel =>
            let* rest := opt_COMMIT b <$> (compile fuel $ (bs, t) :: here) <*> (compile fuel rest) in
            match eps with
            | None => mret rest
            | Some v => mret $ OR rest (OK [] v)
            end
        | _ => None (* compilation failure *)
        end
    end.

  Context {Mbase : Type -> Type}.
  Context {RET : MRet Mbase} {FMAP : FMap Mbase}
    {AP : Ap Mbase} {MBIND : MBind Mbase}.
  Notation M := (parsec.M@{Set _ _ _ _ _ _ _ _} bs Mbase).

  #[local] Fixpoint seqs_to {T} (tokenD : token -> M ()) (v : T) (m : list token) : M T :=
    match m with
    | nil => mret v
    | m :: ms => tokenD m *> seqs_to tokenD v ms
    end.

  Fixpoint interp {T} (tokenD : token -> M ()) (dt : DTree T) : M T :=
    match dt with
    | FAIL => mfail
    | OK ts v => seqs_to tokenD v ts
    | OR a b => interp tokenD a <|> interp tokenD b
    | COMMIT b thn els =>
        let* x := optional (tokenD b) in
        match x with
        | None => interp tokenD els
        | Some dt => interp tokenD thn
        end
    end.
End keyword_set.
End keyword_set.
