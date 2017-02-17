Require Export Basic.

Theorem n_plus_O: forall n:nat,
  n = n + O.
Proof.
  intros.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

 Print LoadPath.

Theorem minus_diag: forall n:nat,
  n - n = O.
Proof.
  intros.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_O_r: forall n:nat,
  n * O = O.
Proof.
  intros.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.

Theorem plus_n_Sm: forall n m:nat,
  S (n + m) = n + (S m).
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm: forall (n m:nat),
  n + m = m + n.
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. rewrite <- plus_O_r. reflexivity.
  - induction m as [| m' IHm'].
    + simpl. rewrite <- plus_O_r. reflexivity.
    + simpl. rewrite -> IHn'. simpl. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc: forall (n m p: nat),
  (n + m) + p = n + (m + p).
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus: forall n:nat, double n = n + n.
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem evenb_S: forall n: nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite -> IHn'. simpl. rewrite -> negb_involutive. reflexivity.
Qed.

Theorem mult_O_plus: forall n m:nat,
  (O + n) * m = n * m.
Proof.
  intros.
  assert (H: O + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q:nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros.
  assert (H: n + m = m + n). { rewrite -> plus_comm. reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_swap : forall n m p:nat,
  n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite <- plus_assoc.
  assert (H: m + (n + p) = (m + n) + p). { rewrite -> plus_assoc. reflexivity. }
  rewrite -> H.
  rewrite <- plus_comm.
  assert (I: m + n + p = p + (m + n)). { rewrite -> plus_comm. reflexivity. }
  rewrite -> I.
  assert (J: n + m = m + n). { rewrite -> plus_comm. reflexivity. }
  rewrite -> J.
  reflexivity.
Qed.


Theorem mult_comm: forall n m:nat,
  m * n = n * m.
Proof.
  intros.
  induction n as [| n' IHn'].
  - rewrite -> mult_O_l. rewrite -> mult_O_r. reflexivity.
  - simpl. rewrite <- IHn'. induction m as [| m' IHm'].
    + simpl. reflexivity.
    Abort.  

  