Require Export Poly.

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros.
  rewrite <- H.
  apply H0.
Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros.
  apply H0. apply H.
Qed.


Theorem silly2a : forall(n m : nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros.
  apply H0. apply H.
Qed.

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros.
  apply H.
  apply H0.
Qed.

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros.
  simpl.
  symmetry.
  apply H.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros.
  rewrite -> H.
  symmetry.
  apply rev_involutive.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros.
  rewrite -> H.
  rewrite -> H0.
  reflexivity.
Qed.

Theorem trans_eq : forall (X: Type) (n m o: X),
  n = m -> m = o -> n = o.
Proof.
  intros.
  rewrite -> H.
  rewrite -> H0.
  reflexivity.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros.
  apply trans_eq with (m:=[c;d]).
  apply H. apply H0.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minusTwo o) ->
     (n + p) = m ->
     (n + p) = (minusTwo o).
Proof.
  intros.
  apply trans_eq with (m).
  apply H0. apply H.
Qed.  

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Lemma S_injective_backwards : forall (n m : nat),
  n = m ->
  S n = S m.
Proof.
  intros. inversion H. reflexivity.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Example inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros.
  inversion H0.
  reflexivity.
Qed.

Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros.
  destruct n as [| n'].
  - reflexivity.
  - inversion H.
Qed.

Theorem inversion_ex4 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros.
  inversion H.
Qed.

Theorem inversion_ex5 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros.
  inversion H.
Qed.

Example inversion_ex6 : forall (X : Type)
                          (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  y :: l = z :: j ->
  x = z.
Proof.
  intros.
  inversion H.
Qed.


Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof.
  intros.
  rewrite -> H.
  reflexivity.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b ->
     beq_nat n m = b.
Proof.
  intros.
  simpl in H. apply H.
Qed.

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5 ->
  true = beq_nat (S (S n)) 7.
Proof.
  intros.
  symmetry in H0. apply H in H0. symmetry in H0. apply H0.
Qed.

(* didn't work when I used 'intros.' at the outset... *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n.
  induction n as [| n' IHn].
  - intros. destruct m as [| m'].
    + reflexivity.
    + inversion H.
  - intros. destruct m as [| m'].
    + intros. inversion H.
    + intros. inversion H.
      rewrite <- plus_n_Sm in H1.
      rewrite <- plus_n_Sm in H1.
      inversion H1.
      apply IHn in H2.
      rewrite -> H2.
      reflexivity.
Qed.


Theorem double_injective : forall n m : nat,
     double n = double m ->
     n = m.
Proof.
  intros n.
  induction n as [| n' IHn].
  - intros.
    destruct m as [| m'].
    + reflexivity.
    + inversion H.
  - intros.
    destruct m as [| m'].
    + inversion H.
    + apply f_equal.
      apply IHn.
      inversion H.
      reflexivity.
Qed.

Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n.
  induction n as [| n' IHn].
  - intros.
    destruct m as [| m'].
    + reflexivity.
    + inversion H.
  - intros.
    destruct m as [| m'].
    + inversion H.
    + apply f_equal.
      apply IHn.
      inversion H.
      reflexivity.
Qed.

