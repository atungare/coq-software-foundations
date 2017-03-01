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

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros.
  generalize dependent n.
  induction m as [| m' IHm].
  - intros.
    destruct n as [| n'].
    + reflexivity.
    + inversion H.
  - intros.
    destruct n as [| n'].
    + inversion H.
    + apply f_equal.
      apply IHm.
      inversion H.
      reflexivity.
Qed.


Theorem beq_id_true : forall x y,
  beq_id x y = true -> x = y.
Proof.
  intros [m] [n].
  simpl.
  intros.
  assert (H' : m = n).
  - apply beq_nat_true. apply H.
  - rewrite -> H'. reflexivity.
Qed.


Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros.
  generalize dependent n.
  induction l as [| h t IH].
  - intros.
    rewrite <- H.
    reflexivity.
  - intros.
    rewrite <- H.
    simpl.
    apply IH.
    reflexivity.
Qed.

Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros.
  unfold square.
  rewrite -> mult_assoc.
  assert (H : n * m * n = n * n * m).
  - rewrite -> mult_comm. apply mult_assoc.
  - rewrite -> H. rewrite -> mult_assoc.
    reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros.
  unfold sillyfun.
  destruct (beq_nat n 3).
  - reflexivity.
  - destruct (beq_nat n 5).
    + reflexivity.
    + reflexivity.
Qed.

Theorem tail_eq: forall (X: Type) (h: X) (l1 l2: list X),
    l1 = l2 -> h :: l1 = h :: l2.
Proof.
  intros. apply f_equal. apply H.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| h t IH].
  - intros.
    inversion H.
    reflexivity.
  - intros.
    inversion H.
    destruct h.
    destruct (split t).
    simpl in H1.
    inversion H1.
    simpl.
    apply tail_eq.
    apply IH.
    reflexivity.
Qed.


Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros.
  unfold sillyfun1 in H.
  destruct (beq_nat n 3) eqn:neq3.
  - apply beq_nat_true in neq3.
    rewrite -> neq3.
    reflexivity.
  - destruct (beq_nat n 5) eqn:neq5.
    + apply beq_nat_true in neq5.
      rewrite -> neq5.
      reflexivity.
    + inversion H.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros.
  destruct b.
  - destruct (f true) eqn:fTrue.
    + rewrite -> fTrue.
      apply fTrue.
    + destruct (f false) eqn:fFalse.
      * apply fTrue.
      * apply fFalse.
 - destruct (f false) eqn: fFalse.
   + destruct (f true) eqn:fTrue.
     * apply fTrue.
     * apply fFalse.
   + rewrite -> fFalse.
     apply fFalse.
Qed.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros.
  generalize dependent m.
  induction n as [| n' IHn].
  - intros. destruct m as [| m'].
    + reflexivity.
    + reflexivity.
  - intros. destruct m as [| m'].
    + reflexivity.
    + apply IHn.
Qed.

Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  intros.
  destruct n as [| n'].
  - apply beq_nat_true in H.
    rewrite <- H in H0.
    apply beq_nat_true in H0.
    rewrite <- H0.
    reflexivity.
  - apply beq_nat_true in H.
    rewrite <- H in H0.
    apply H0.
Qed.


Definition split_combine_statement : Prop :=
  forall (X: Type) (l1 l2: list X),
  length l1 = length l2 ->
  split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  intros X l1.
  induction l1 as [| h1 t1 IH1].
  - intros.
    simpl.
    destruct l2 as [| h2 t2 IH2].
    + reflexivity.
    + inversion H.
  - intros.
    inversion H.
    destruct l2 as [| h2 t2].
    + inversion H1.
    + inversion H1.
      apply IH1 in H2.
      simpl.
      rewrite -> H2.
      reflexivity.
Qed.


Theorem filter_exercise : forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros.
  generalize dependent lf.
  induction l as [| h t IH].
  - intros.
    simpl in H.
    inversion H.
  - intros.
    generalize dependent H.
    destruct lf as [| hf tf].
    + simpl.
      intros.
      destruct (test h) eqn:testH.
      * inversion H.
        rewrite -> H1 in testH.        
        apply testH.
      * apply IH in H.
        apply H.
    + simpl.
      intros.
      destruct (test h) eqn:testH.
      * inversion H.
        rewrite -> H1 in testH.
        apply testH.
      * apply IH in H.
        apply H.
Qed.

Fixpoint forallb {X: Type} (test: X -> bool) (l: list X) : bool :=
  match l with
  | [] => true
  | h :: t => (test h) && (forallb test t)
  end.

Fixpoint existsb {X: Type} (test: X -> bool) (l: list X) : bool :=
  match l with
  | [] => false
  | h :: t => (test h) || (existsb test t)
  end.

Example forallb_1: forallb oddb [1;3;5;7;9] = true.
Proof. reflexivity. Qed.

Example forallb_2: forallb negb [false;false] = true.
Proof. reflexivity. Qed.

Example forallb_3: forallb evenb [0;2;4;5] = false.
Proof. reflexivity. Qed.

Example forallb_4: forallb (beq_nat 5) [] = true.
Proof. reflexivity. Qed.

Example existsb_1: existsb (beq_nat 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.

Example existsb_2: existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.

Example existsb_3: existsb oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.

Example existsb_4: existsb evenb [] = false.
Proof. reflexivity. Qed.


Definition existsb' {X: Type} (test: X -> bool) (l: list X) :=
  negb (forallb (fun a => negb (test a)) l).

Example existsb'_1: existsb' (beq_nat 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.

Example existsb'_2: existsb' (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.

Example existsb'_3: existsb' oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.

Example existsb'_4: existsb' evenb [] = false.
Proof. reflexivity. Qed.


Theorem existsb_existsb': forall (X: Type) (test: X -> bool) (l: list X),
  existsb test l = existsb' test l.
Proof.
  intros.
  unfold existsb.
  unfold existsb'.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl.
    destruct (test h) eqn:testH.
    + simpl. reflexivity.
    + simpl. apply IH.
Qed.

Definition forallb' {X: Type} (test: X -> bool) (l: list X) : bool :=
  fold (fun item acc => acc && (test item)) l true.

Example forallb'_1: forallb' oddb [1;3;5;7;9] = true.
Proof. reflexivity. Qed.

Example forallb'_2: forallb' negb [false;false] = true.
Proof. reflexivity. Qed.

Example forallb'_3: forallb' evenb [0;2;4;5] = false.
Proof. reflexivity. Qed.

Example forallb'_4: forallb' (beq_nat 5) [] = true.
Proof. reflexivity. Qed.

Theorem andb_true_r: forall (a: bool),
    a && true = a.
Proof.
  intros.
  destruct a.
  - reflexivity.
  - reflexivity.
Qed.

Theorem forallb_forallb': forall (X: Type) (test: X -> bool) (l: list X),
  forallb test l = forallb' test l.
Proof.
  intros.
  unfold forallb.
  unfold forallb'.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl.
    destruct (test h) eqn:testH.
    + simpl.
      rewrite -> IH.
      rewrite -> andb_true_r.
      reflexivity.
    + simpl.
      rewrite -> andb_false_r.
      reflexivity.
Qed.

Theorem map_length_unchanged: forall (A B: Type) (f: A -> B) (l: list A),
    length l = length (map f l).
Proof.
  intros.
  induction l as [| h t IH].
  - reflexivity.
  - simpl.
    rewrite -> IH.
    reflexivity.
Qed.

Definition flat_map_fold {X Y: Type} (f: X -> list Y) (l: list X) : list Y :=
  fold (fun item acc => (f item) ++ acc) l [].

Theorem flat_map_fold_correct: forall (X Y: Type) (f: X -> list Y) (l: list X),
  flat_map f l = flat_map_fold f l.
Proof.
  intros.
  unfold flat_map_fold.
  unfold flat_map.
  induction l as [| h t IH].
  - reflexivity.
  - simpl.
    rewrite -> IH.
    reflexivity.
Qed.
