
Require Export Logic.


Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall (n: nat), ev n -> ev (S (S n)).

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.


Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros.
  simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.


Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros.
  induction n as [| n' IH].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IH.
Qed.

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros.
  inversion H as [| n' H'].
  - simpl. apply ev_0.
  - simpl. apply H'.
Qed.

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros.
  destruct H.
  - simpl. apply ev_0.
  - simpl. apply H.
Qed.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros.
  inversion H.
  apply H1.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros.
  induction H as [| n' H' IH].
  - exists 0. reflexivity.
  - destruct IH as [k' Hk'].
    exists (S k').
    rewrite -> Hk'.
    reflexivity.
Qed.

Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
  intros.
  split.
  - apply ev_even.
  - intros.
    destruct H as [k' Hk'].
    rewrite -> Hk'.
    apply ev_double.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros.
  induction H.
  - apply H0.
  - simpl.
    apply ev_SS.
    apply IHev.
Qed.


Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros.
  split.
  - intros.
    induction H.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply (ev_sum n m IHev'1 IHev'2).
  - intros.
    induction H.
    + apply ev'_0.
    + rewrite -> plus_1_r.
      rewrite -> plus_1_r.
      rewrite -> plus_comm.
      rewrite <- plus_swap.
      simpl.
      apply (ev'_sum n 2 IHev ev'_2).
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros.
  induction H0.
  - apply H.
  - simpl in H.
    apply evSS_ev in H.
    apply IHev.
    apply H.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros.
  apply ev_sum with (n:=n+m) (m:=n+p) in H.
  - replace (n + m + (n + p)) with ((n + n) + (m + p)) in H.
    + rewrite <- double_plus in H.
      apply (ev_ev__ev (double n) (m + p)) in H.
      * apply H.
      * apply ev_double.
    + rewrite -> plus_assoc.
      rewrite -> plus_assoc.
      replace (n + (m + p)) with (m + (n + p)).
      * reflexivity.
      * apply plus_swap.
  - apply H0.
Qed.

Module Playground.

Inductive le : nat -> nat -> Prop :=
| le_n: forall n, le n n
| le_S: forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n.
Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S. apply le_n.
Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros.
  inversion H.
  inversion H2.
Qed.

End Playground.

Definition lt (n m: nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  | sq: forall (n: nat), square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall (n: nat), next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1: forall (n: nat), (ev (S n)) -> (next_even n (S n))
  | ne_2: forall (n: nat), (ev (S (S n))) -> (next_even n (S (S n))).

Inductive total_relation : nat -> nat -> Prop :=
  | tot_rel: forall (n m: nat), total_relation n m.

Inductive empty_relation : nat -> nat -> Prop := .

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros.
  induction H0.
  - apply H.
  - apply le_S. apply IHle.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros.
  induction n as [| n' IH].
  - apply le_n.
  - apply le_S. apply IH.
Qed.

Theorem n_le_Sn: forall n,
  n <= S n.
Proof.
  intros. apply le_S. apply le_n.
Qed.

Theorem Sn_le_m__n_le_m: forall n m,
  (S n) <= m -> n <= m.
Proof.
  intros.
  apply (le_trans n (S n) m (n_le_Sn n)) in H.
  apply H.
Qed.

Theorem n_le_m__n_le_Sm: forall n m,
  n <= m -> n <= S m.
Proof.
  intros.
  induction H.
  - apply le_S. apply le_n.
  - apply le_S. apply IHle.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros.
  induction H.
  - apply le_n.
  - apply le_S.
    apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros.
  inversion H.
  - apply le_n.
  - apply le_trans with (n:=S n).
    + apply n_le_Sn.
    + apply H1.
Qed.


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros.
  induction a as [| a' IH].
  - apply O_le_n.
  - simpl.
    apply n_le_m__Sn_le_Sm.
    apply IH.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt.
 intros.
 split.
 - assert (I: S n1 <= S (n1 + n2)).
    { apply n_le_m__Sn_le_Sm. apply le_plus_l. }
   apply (le_trans (S n1) (S (n1 + n2)) m I) in H.
   apply H.
 - assert (I: S n2 <= S (n1 + n2)).
    { apply n_le_m__Sn_le_Sm. 
      rewrite -> plus_comm.
      apply le_plus_l. }
   apply (le_trans (S n2) (S (n1 + n2)) m I) in H.
   apply H.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt.
  intros.
  apply n_le_m__Sn_le_Sm.
  apply Sn_le_m__n_le_m in H.
  apply H.
Qed.

Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.
  intros.
  generalize dependent m. 
  induction n.
  - intros. apply O_le_n.
  - intros. 
    destruct m.
    + inversion H.
    + rewrite -> plus_1_r in H.
      replace (S m) with (m + 1) in H.
      rewrite -> plus_comm in H.
      replace (m + 1) with (1 + m) in H.
      apply n_le_m__Sn_le_Sm.
      apply IHn.
      apply (plus_ble_compat_l n m 1 H).
      apply plus_comm.
      rewrite <- plus_1_r.
      reflexivity.
Qed.


Theorem leb_correct : forall n m,
  n <= m ->
  leb n m = true.
Proof.
  intros.
  generalize dependent n.
  induction m.
  - intros. inversion H. reflexivity.
  - intros.
    destruct n.
    + reflexivity.
    + simpl.
      apply IHm.
      apply Sn_le_Sm__n_le_m in H.
      apply H.
Qed.

Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  intros.
  apply leb_correct.
  apply leb_complete in H.
  apply leb_complete in H0.
  apply (le_trans n m o H H0).
Qed.

Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof.
  intros.
  split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

Module R.