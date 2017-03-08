Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Maps.

Module AExp.

Inductive aexp : Type :=
| ANum: nat -> aexp
| APlus: aexp -> aexp -> aexp
| AMinus: aexp -> aexp -> aexp
| AMult: aexp -> aexp -> aexp.

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (a: aexp) : nat :=
  match a with
  | ANum n => n
  | APlus l r => (aeval l) + (aeval r)
  | AMinus l r => (aeval l) - (aeval r)
  | AMult l r => (aeval l) * (aeval r)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Fixpoint beval (b: bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq l r => beq_nat (aeval l) (aeval r)
  | BLe l r => leb (aeval l) (aeval r)
  | BNot b' => negb (beval b')
  | BAnd l r => andb (beval l) (beval r)
  end.

Fixpoint optimize_0plus (a: aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) r => (optimize_0plus r)
  | APlus l r => APlus (optimize_0plus l) (optimize_0plus r)
  | AMinus l r => AMinus (optimize_0plus l) (optimize_0plus r)
  | AMult l r => AMult (optimize_0plus l) (optimize_0plus r)
  end.


Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros.
  induction a.
  - reflexivity.
  - destruct a1.
    + destruct n.
      * simpl. apply IHa2.
      * simpl. rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1.
      rewrite IHa1. rewrite IHa2.
      reflexivity.
    + simpl. simpl in IHa1.
      rewrite IHa1. rewrite IHa2.
      reflexivity.
    + simpl. simpl in IHa1.
      rewrite IHa1. rewrite IHa2.
      reflexivity.
  - simpl.
    rewrite IHa1. rewrite IHa2.
    reflexivity.
  - simpl.
    rewrite IHa1. rewrite IHa2.
    reflexivity.
Qed.


Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof.
  intros. try reflexivity.
Qed.

Theorem silly2 : forall (P: Prop), P -> P.
Proof.
  intros.
  try reflexivity.
  apply H.
Qed.

Lemma foo' : forall (n: nat), leb 0 n = true.
Proof.
  intros.
  destruct n; simpl; reflexivity.
Qed.

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros.
  induction a;
    try reflexivity;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  - destruct a1;
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    + destruct n;
        simpl; rewrite IHa2; reflexivity.
Qed.


Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.


Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (right; try (left; reflexivity)).
Qed.


Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BEq l r => BEq (optimize_0plus l) (optimize_0plus r)
  | BLe l r => BLe (optimize_0plus l) (optimize_0plus r)
  | BNot b' => BNot (optimize_0plus_b b')
  | BAnd l r => BAnd (optimize_0plus_b l) (optimize_0plus_b r)
  | _ => b
  end.


Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros.
  induction b;
    try (simpl; reflexivity);
    try (simpl; repeat rewrite optimize_0plus_sound; reflexivity).
  - simpl. rewrite IHb. reflexivity.
  - simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.


