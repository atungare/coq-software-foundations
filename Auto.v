Require Import Coq.omega.Omega.
Require Import Maps.
Require Import Imp.

Ltac inv H := inversion H; subst; clear H.

Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. assumption.
Qed.

Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P->Q) -> (P->S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  auto 6.
Qed.

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. omega. Qed.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto using le_antisym.
Qed.

Hint Resolve le_antisym.

Example auto_example_6' : forall n m p : nat,
  (n<= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto.
Qed.


Definition is_fortytwo x := x = 42.

Hint Unfold is_fortytwo.

Example auto_example_7' : forall x,
    (x <=42 /\ 42 <= x) -> is_fortytwo x.
Proof. auto. Qed.


Theorem ceval_deterministic': forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
    induction E1; intros st2 E2; inv E2; auto.
  - assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
  - rewrite H in H5. inversion H5.
  - rewrite H in H5. inversion H5.
  - rewrite H in H2. inversion H2.
  - rewrite H in H4. inversion H4.
  - assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
Qed.


Theorem ceval_deterministic'_alt: forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
    induction E1; intros st2 E2; inv E2...
  - assert (st' = st'0) as EQ1...
    subst st'0...
  - rewrite H in H5. inversion H5.
  - rewrite H in H5. inversion H5.
  - rewrite H in H2. inversion H2.
  - rewrite H in H4. inversion H4.
  - assert (st' = st'0) as EQ1...
    subst st'0...
Qed.


Ltac rwinv H1 H2 := rewrite H1 in H2; inv H2.


Theorem ceval_deterministic'': forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
    induction E1; intros st2 E2; inv E2...
  - assert (st' = st'0) as EQ1...
    subst st'0...
  - rwinv H H5.
  - rwinv H H5.
  - rwinv H H2.
  - rwinv H H4.
  - assert (st' = st'0) as EQ1...
    subst st'0...
Qed.

Ltac find_rwinv :=
  match goal with
  H1: ?E = true,
  H2: ?E = false
  |- _ => rwinv H1 H2
  end.

Theorem ceval_deterministic''': forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
    induction E1; intros st2 E2; inv E2; try find_rwinv...
  - assert (st' = st'0) as EQ1...
    subst st'0...
  - assert (st' = st'0) as EQ1...
    subst st'0...
Qed.

Theorem ceval_deterministic'''': forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
    induction E1; intros st2 E2; inv E2; try find_rwinv...
  - rewrite (IHE1_1 st'0 H1) in *...
  - rewrite (IHE1_1 st'0 H3) in *...
Qed.

Ltac find_eqn :=
  match goal with
  H1: forall x, ?P x -> ?L = ?r,
  H2: ?P ?X
  |- _ => rewrite (H1 X H2) in *
  end.

Theorem ceval_deterministic''''': forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
    induction E1; intros st2 E2; inv E2; try find_rwinv;
    repeat find_eqn...
Qed.

Module Repeat.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
  (CRepeat e1 b2) (at level 80, right associativity).

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass  : forall st a1 n X,
      aeval st a1 = n ->
      ceval st (X ::= a1) (t_update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
  | E_RepeatEnd : forall st st' b1 c1,
      ceval st c1 st' ->
      beval st' b1 = true ->
      ceval st (CRepeat c1 b1) st'
  | E_RepeatLoop : forall st st' st'' b1 c1,
      ceval st c1 st' ->
      beval st' b1 = false ->
      ceval st' (CRepeat c1 b1) st'' ->
      ceval st (CRepeat c1 b1) st''.

Notation "c1 '/' st '\\' st'" := (ceval st c1 st')
                                 (at level 40, st at level 39).

Theorem ceval_deterministic''''': forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
    induction E1; intros st2 E2; inv E2;
    repeat find_eqn; try find_rwinv...
Qed.

End Repeat.

Example ceval'_example1:
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   \\ (t_update (t_update empty_state X 2) Z 4).
Proof.
  eapply E_Seq.
  - apply E_Ass.
    reflexivity.
  - apply E_IfFalse.
    + reflexivity.
    + apply E_Ass. reflexivity.
Qed.   

Hint Constructors ceval.
Hint Transparent state.
Hint Transparent total_map.

Definition st12 := t_update (t_update empty_state X 1) Y 2.
Definition st21 := t_update (t_update empty_state X 2) Y 1.

Example auto_example_8 : exists s',
  (IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI) / st21 \\ s'.
Proof. eauto. Qed.

