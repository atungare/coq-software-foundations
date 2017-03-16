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


Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum: forall (n: nat),
    aevalR (ANum n) n
| E_APlus: forall (e1 e2: aexp) (n1 n2: nat),
    aevalR e1 n1 ->
    aevalR e2 n2 ->
    aevalR (APlus e1 e2) (n1 + n2)
| E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
    aevalR e1 n1 ->
    aevalR e2 n2 ->
    aevalR (AMinus e1 e2) (n1 - n2)
| E_AMult: forall (e1 e2: aexp) (n1 n2: nat),
    aevalR e1 n1 ->
    aevalR e2 n2 ->
    aevalR (AMult e1 e2) (n1 * n2).


Notation "e '\\' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.

End aevalR_first_try.

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.

Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  intros.
  split.
  - intros.
    induction H; subst; reflexivity.
  - intros. generalize dependent n.
    induction a; simpl; intros; subst; constructor;
      try apply IHa1; try apply IHa2; reflexivity.
Qed.

Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue: bevalR BTrue true
  | E_BFalse: bevalR BFalse false
  | E_BEq: forall (e1 e2: aexp) (n1 n2: nat),
      (aevalR e1 n1) -> (aevalR e2 n2) ->
      (bevalR (BEq e1 e2) (beq_nat n1 n2))
  | E_BLe: forall (e1 e2: aexp) (n1 n2: nat),
      (aevalR e1 n1) -> (aevalR e2 n2) ->
      (bevalR (BLe e1 e2) (leb n1 n2))
  | E_BNot: forall (e: bexp) (b: bool),
      (bevalR e b) ->
      (bevalR (BNot e) (negb b))
  | E_BAnd: forall (e1 e2: bexp) (b1 b2: bool),
      (bevalR e1 b1) -> (bevalR e2 b2) ->
      (bevalR (BAnd e1 e2) (andb b1 b2)).



Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  intros. split.
  - intros.
    induction H; subst; simpl;
      try reflexivity;
      try (rewrite aeval_iff_aevalR in H, H0;
           rewrite H, H0;
           reflexivity).
  - intros. generalize dependent bv.
    induction b; simpl; intros; subst; constructor;
      try (apply aeval_iff_aevalR; reflexivity);
      try (apply IHb; reflexivity);
      try (apply IHb1; reflexivity);
      try (apply IHb2; reflexivity).
Qed.


End AExp.

Module aevalR_division.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv : aexp -> aexp -> aexp.

Reserved Notation "e '\\' n"
                  (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)
  | E_ADiv :  forall (a1 a2: aexp) (n1 n2 n3: nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) \\ n3

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_division.


Module aevalR_extended.

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aexp : Type :=
  | AAny  : aexp                   (* <--- NEW *)
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.


Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any : forall (n:nat),
      AAny \\ n                 (* <--- new *)
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_extended.

Definition state := total_map nat.

Definition empty_state : state :=
  t_empty 0.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Definition W : id := Id "W".
Definition X : id := Id "X".
Definition Y : id := Id "Y".
Definition Z : id := Id "Z".

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x     (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => leb (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Example aexp1 :
  aeval (t_update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
  beval (t_update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.
Proof. reflexivity. Qed.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' b1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf b1 c2 c3) (at level 80, right associativity).

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1).

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
  Z ::= ANum 5 ;;
  subtract_slowly.

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip: forall st,
    SKIP / st \\ st
| E_Ass: forall st ae x n,
    aeval st ae = n ->
    (x ::= ae) / st \\ (t_update st x n)
| E_Seq: forall c1 c2 st st' st'',
    c1 / st \\ st' ->
    c2 / st' \\ st'' ->
    (c1 ;; c2) / st \\ st''
| E_IfTrue: forall b1 c1 c2 st st',
    beval st b1 = true ->
    c1 / st \\ st' ->
    (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
| E_IfFalse: forall b1 c1 c2 st st',
    beval st b1 = false ->
    c2 / st \\ st' ->
    (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
| E_WhileEnd: forall b1 c1 st,
    beval st b1 = false ->
    (WHILE b1 DO c1 END) / st \\ st
| E_WhileLoop: forall b1 c1 st st' st'',
    beval st b1 = true ->
    c1 / st \\ st' ->
    (WHILE b1 DO c1 END) / st' \\ st'' ->
    (WHILE b1 DO c1 END) / st \\ st''

    where "c1 '/' st '\\' st'" := (ceval c1 st st').


Example ceval_example1:
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   \\ (t_update (t_update empty_state X 2) Z 4).
Proof.
  apply E_Seq with (t_update empty_state X 2).
  - apply E_Ass. reflexivity.
  - apply E_IfFalse.
    + reflexivity.
    + apply E_Ass. reflexivity.
Qed.

Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state \\
    (t_update (t_update (t_update empty_state X 0) Y 1) Z 2).
Proof.
  apply E_Seq with (t_update empty_state X 0).
  - apply E_Ass. reflexivity.
  - apply E_Seq with (t_update (t_update empty_state X 0) Y 1).
    + apply E_Ass. reflexivity.
    + apply E_Ass. reflexivity.
Qed.

Definition pup_to_n : com :=
  Y ::= (ANum 0);;
  WHILE BLe (ANum 1) (AId X)
     DO Y ::= (APlus (AId Y) (AId X));;
        X ::= (AMinus (AId X) (ANum 1))
    END.


Theorem pup_to_2_ceval :
  pup_to_n / (t_update empty_state X 2) \\
    t_update (t_update (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  apply E_Seq with (t_update (t_update empty_state X 2) Y 0).
  - apply E_Ass. reflexivity.
  - apply E_WhileLoop with (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1).
    + reflexivity.
    + apply E_Seq with (t_update (t_update (t_update empty_state X 2) Y 0) Y 2).
      * apply E_Ass. reflexivity.
      * apply E_Ass. reflexivity.
    + apply E_WhileLoop with (t_update (t_update (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0).
      * reflexivity.
      * apply E_Seq with  (t_update (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1) Y 3).
        { apply E_Ass. reflexivity. }
        { apply E_Ass. reflexivity. }
      * apply E_WhileEnd. reflexivity.
Qed.

Theorem ceval_deterministic: forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros.
  generalize dependent st2.
  induction H; intros st2 H'; inversion H'; subst.
  - reflexivity.
  - reflexivity.
  - assert (st' = st'0).
    { apply IHceval1. assumption. }
    subst st'0.
    apply IHceval2.
    assumption.
  - apply IHceval.
    assumption.
  - rewrite H in H6. inversion H6.
  - rewrite H in H6. inversion H6.
  - apply IHceval.
    assumption.
  - reflexivity.
  - rewrite H in H2. inversion H2.
  - rewrite H in H6. inversion H6.
  - assert (st' = st'0).
    { apply IHceval1. assumption. }
    subst st'0.
    apply IHceval2.
    assumption.
Qed.

Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st \\ st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval.
  subst.
  simpl.
  apply t_update_eq.
Qed.

Theorem XtimesYinZ_spec : forall st x y st',
  st X = x ->
  st Y = y ->
  XtimesYinZ / st \\ st' ->
  st' Z = x * y.
Proof.
  intros.
  inversion H1.
  subst.
  simpl.
  apply t_update_eq.
Qed.

Theorem loop_never_stops : forall st st',
  ~(loop / st \\ st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef
           eqn:Heqloopdef.
  induction contra; inversion Heqloopdef.
  - rewrite H1 in H. inversion H.
  - apply IHcontra2. rewrite H1, H2. reflexivity.
Qed.

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP =>
      true
  | _ ::= _ =>
      true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  =>
      false
  end.

Inductive no_whilesR: com -> Prop :=
| nw_skip: no_whilesR SKIP
| nw_ass: forall x ex,
    no_whilesR (x ::= ex)
| nw_seq: forall c1 c2,
    no_whilesR c1 ->
    no_whilesR c2 ->
    no_whilesR (c1 ;; c2)
| nw_ifb: forall b c1 c2,
    no_whilesR c1 ->
    no_whilesR c2 ->
    no_whilesR (IFB b THEN c1 ELSE c2 FI).

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  intros. split.
  - intros.
    induction c.
    + apply nw_skip.
    + apply nw_ass.
    + simpl in H.
      apply andb_true_iff in H.
      destruct H.
      apply nw_seq.
      * apply IHc1. apply H.
      * apply IHc2. apply H0.
    + simpl in H.
      apply andb_true_iff in H.
      destruct H.
      apply nw_ifb.
      * apply IHc1. apply H.
      * apply IHc2. apply H0.
    + simpl in H. inversion H.
  - intros.
    induction c; simpl.
    + reflexivity.
    + reflexivity.
    + inversion H. 
      apply andb_true_iff.
      split.
      * apply IHc1. apply H2.
      * apply IHc2. apply H3.
    + inversion H.
      apply andb_true_iff.
      split.
      * apply IHc1. apply H2.
      * apply IHc2. apply H4.
    + inversion H.
Qed.

Theorem no_whiles_terminating: forall c st,
    no_whilesR c ->
    exists st', c / st \\ st'.
Proof.
  intros.
  generalize dependent st.
  induction H; intros.
  - exists st.
    apply E_Skip.
  - exists (t_update st x (aeval st ex)).
    apply E_Ass. reflexivity.
  - destruct (IHno_whilesR1 st).
    destruct (IHno_whilesR2 x).
    exists x0.
    apply (E_Seq c1 c2 st x x0).
    + apply H1.
    + apply H2.
  - destruct (beval st b) eqn:bval.
    + destruct (IHno_whilesR1 st).
      exists x.
      apply E_IfTrue.
      apply bval.
      apply H1.
    + destruct (IHno_whilesR2 st).
      exists x.
      apply E_IfFalse.
      apply bval.
      apply H1.
Qed.

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.


Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
  match prog with
  | [] => stack
  | (SPush n) :: prog' => s_execute st (n :: stack) prog'
  | (SLoad k) :: prog' => s_execute st ((st k) :: stack) prog'
  | SPlus :: prog' => s_execute st (((hd 0 (tl stack)) + (hd 0 stack)) :: (tl (tl stack)))
                                prog'
  | SMinus :: prog' => s_execute st (((hd 0 (tl stack)) - (hd 0 stack)) :: (tl (tl stack)))                                    
                                prog'
  | SMult :: prog' => s_execute st (((hd 0 (tl stack)) * (hd 0 stack)) :: (tl (tl stack)))
                                prog'
  end.


Example s_execute1 :
     s_execute empty_state []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
Proof. reflexivity. Qed.

Example s_execute2 :
     s_execute (t_update empty_state X 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
Proof. reflexivity. Qed.


Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum x => [SPush x]
  | AId k => [SLoad k]
  | APlus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SPlus]
  | AMinus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMinus]
  | AMult a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMult]
  end.


Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. reflexivity. Qed.


Lemma s_execute_app: forall st stack si1 si2,
  s_execute st stack (si1 ++ si2) = 
  s_execute st (s_execute st stack si1) si2.
Proof.
  intros.
  generalize dependent st.
  generalize dependent stack.
  generalize dependent si2.
  induction si1; intros.
  - reflexivity.
  - destruct a; simpl; apply IHsi1.
Qed.

Lemma s_compile_append: forall st stack e,
  s_execute st stack (s_compile e) =
  (aeval st e) :: stack.
Proof.
  intros.
  generalize dependent st.
  generalize dependent stack.
  induction e; simpl; intros;
    try reflexivity;
    repeat rewrite s_execute_app;
    rewrite IHe1; rewrite IHe2;
    reflexivity.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros.
  apply s_compile_append.
Qed.


Fixpoint beval_ss (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => leb (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval_ss st b1)
  | BAnd b1 b2  => if (beval_ss st b1)
                     then (beval_ss st b2)
                     else false
  end.

Theorem beval_beval_ss: forall st b,
  beval st b = beval_ss st b.
Proof.
  intros.
  destruct b; reflexivity.
Qed.


Module BreakImp.

Inductive com : Type :=
  | CSkip : com
  | CBreak : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Inductive result : Type :=
  | SContinue : result
  | SBreak : result.

Reserved Notation "c1 '/' st '\\' s '/' st'"
                  (at level 40, st, s at level 39).


Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      CSkip / st \\ SContinue / st
  | E_Break : forall st,
      CBreak / st \\ SBreak / st
  | E_Ass : forall st a1 n x,
      aeval st a1 =  n ->
      (x ::= a1) / st \\ SContinue / (t_update st x n)
  | E_IfTrue : forall st st' b c1 c2 cont,
      beval st b = true ->
      c1 / st \\ cont / st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ cont / st'
  | E_IfFalse : forall st st' b c1 c2 cont,
      beval st b = false ->
      c2 / st \\ cont / st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ cont / st'
  | E_SeqBreak : forall st st' c1 c2,
      c1 / st \\ SBreak / st' ->
      (c1 ;; c2) / st \\ SBreak / st'
  | E_SeqContinue : forall st st' st'' c1 c2 prog,
      c1 / st \\ SContinue / st' ->
      c2 / st' \\ prog / st'' ->
      (c1 ;; c2) / st \\ prog / st''
  | E_WhileEnd : forall st b c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ SContinue / st
  | E_WhileLoopBreak : forall st st' b c,
      beval st b = true ->
      c / st \\ SBreak / st' ->
      (WHILE b DO c END) / st \\ SContinue / st'
  | E_WhileLoopContinue : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ SContinue / st' ->
      (WHILE b DO c END) / st' \\ SContinue / st'' ->
      (WHILE b DO c END) / st \\ SContinue / st''

  where "c1 '/' st '\\' s '/' st'" := (ceval c1 st s st').


Theorem break_ignore : forall c st st' s,
     (BREAK;; c) / st \\ s / st' ->
     st = st'.
Proof.
  intros.
  inversion H; subst.
  - inversion H5. reflexivity.
  - inversion H2.
Qed.


Theorem while_continue : forall b c st st' s,
  (WHILE b DO c END) / st \\ s / st' ->
  s = SContinue.
Proof.
  intros.
  inversion H; subst; reflexivity.
Qed.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  c / st \\ SBreak / st' ->
  (WHILE b DO c END) / st \\ SContinue / st'.
Proof.
  intros.
  inversion H0; subst; apply E_WhileLoopBreak;
    try apply H;
    try apply H0.
Qed.

Theorem while_break_true : forall b c st st',
  (WHILE b DO c END) / st \\ SContinue / st' ->
  beval st' b = true ->
  exists st'', c / st'' \\ SBreak / st'.
Proof.
  intros.
  remember (WHILE b DO c END) as loop.
  induction H; try inversion Heqloop; try subst.
  - rewrite H0 in H. inversion H.
  - exists st. apply H1.
  - apply IHceval2.
    * reflexivity.
    * apply H0.
Qed.


End BreakImp.