Require Export Tactics.

Check (3 = 3).
Check forall n m : nat, n + m = m + n.

Check forall n : nat, n = 2.
Check 3 = 5.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_injective: injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

Check @eq.


Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro: forall A B: Prop,
    A -> B -> (A /\ B).
Proof.
  intros.
  split.
  - apply H.
  - apply H0.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros.
  split.
  - destruct n as [| n'].
    + reflexivity.
    + inversion H.
  - destruct m as [| m'].
    + reflexivity.
    + rewrite -> plus_comm in H.
      inversion H.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros.
  destruct H as [Hn Hm].
  rewrite -> Hn.
  rewrite -> Hm.
  reflexivity.
Qed.

Lemma proj1: forall P Q: Prop,
    P /\ Q -> P.
Proof.
  intros.
  destruct H as [L R].
  apply L.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros.
  assert (J: n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct J as [L R].
  rewrite -> L.
  rewrite -> R.
  reflexivity.
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros.
  destruct H as [L R].
  apply R.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros.
  destruct H as [L R].
  split.
  - apply R.
  - apply L.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros.
  destruct H as [Hl [Hm Hr]].
  split.
  - split.
    + apply Hl.
    + apply Hm.
  - apply Hr.
Qed.

Check and.

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros.
  destruct H as [Hl | Hr].
  - rewrite -> Hl.
    reflexivity.
  - rewrite -> Hr.
    rewrite -> mult_O_r.
    reflexivity.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros.
  left.
  apply H.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros.
  destruct n as [| n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.


Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros.
  destruct n as [| n'].
  - left. reflexivity.
  - destruct m as [| m'].
    + right. reflexivity.
    + inversion H.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros.
  destruct H as [Hl | Hr].
  - right. apply Hl.
  - left. apply Hr.
Qed.

Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

End MyNot.


Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros.
  destruct H.
Qed.

Fact not_implies_our_not : forall (P:Prop),
  ~P -> (forall (Q:Prop), P -> Q).
Proof.
  intros.
  destruct H.
  apply H0.
Qed.

Theorem zero_not_one : ~(0 = 1).
Proof.
  intros H. inversion H.
Qed.

Check (0 <> 1).

Theorem zero_not_one': 0 <> 1.
Proof.
  intros H. inversion H.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not.
  intros.
  destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros.
  unfold not in H.
  destruct H as [Hr Hl].
  destruct Hl.
  apply Hr.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros.
  unfold not.
  intros.
  apply H0.
  apply H.
Qed.

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros.
  unfold not.
  unfold not in H0.
  intros.
  apply H0 in H. 
  apply H.
  apply H1.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros.
  unfold not.
  intros.
  destruct H as [Hl Hr].
  apply Hr in Hl.
  apply Hl.
Qed.


Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros.
  destruct b.
  - unfold not in H.
    exfalso.
    apply H.
    reflexivity.
  - reflexivity.
Qed.


Lemma True_is_true : True.
Proof. apply I. Qed.


Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros.
  destruct H as [Hl Hr].
  split.
  - apply Hr.
  - apply Hl.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros.
  split.
  - apply not_true_is_false.
  - intros.
    rewrite -> H.
    unfold not.
    intros.
    inversion H0.
Qed.

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros.
  split.
  - intros. apply H.
  - intros. apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros.
  destruct H as [Hpq Hqp].
  destruct H0 as [Hqr Hrq].
  split.
  - intros.
    apply Hqr.
    apply Hpq.
    apply H.
  - intros.
    apply Hqp.
    apply Hrq.
    apply H.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros.
  split.
  - intros.
    split.
    + destruct H.
      * left. apply H.
      * destruct H.
        right.
        apply H.
    + destruct H.
      * left. apply H.
      * destruct H.
        right.
        apply H0.
  - intros.
    destruct H.
    destruct H.
    + left. apply H.
    + destruct H0.
      * left.
        apply H0.
      * right.
        split.
          apply H.
          apply H0.
Qed.

Require Import Coq.Setoids.Setoid.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  intros.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros.
  split.
  - intros.
    destruct H.
    + left. left. apply H.
    + destruct H.
      * left. right. apply H.
      * right. apply H.
  - intros.
    destruct H.
    + destruct H.
      * left. apply H.
      * right. left. apply H.
    + right. right. apply H.
Qed.


Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros.
  rewrite -> mult_0.
  rewrite -> mult_0.
  rewrite -> or_assoc.
  reflexivity.
Qed.


Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros.
  apply mult_0.
  apply H.
Qed.


Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros.
  destruct H as [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros.
  unfold not.
  intros.
  destruct H0.
  apply H0.
  apply H.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  split.
  - intros.
    destruct H as [x Hx].
    destruct Hx.
    + left. exists x. apply H.
    + right. exists x. apply H.
  - intros.
    destruct H.
    + destruct H as [x Hx].
      exists x.
      left.
      apply Hx.
    + destruct H as [x Hx].
      exists x.
      right.
      apply Hx.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | h :: t => x = h \/ In x t
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl.
  right. right. right. left.
  reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros.
  destruct H as [H' | [H' | []]].
  - exists 1.
    rewrite -> H'.
    reflexivity.
  - exists 2.
    rewrite -> H'.
    reflexivity.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros.
  generalize dependent H.
  induction l as [| h t IH].
  - intros.
    simpl in H.
    destruct H.
  - intros.
    simpl in H.
    destruct H as [Hl | Hr].
    + rewrite -> Hl.
      simpl.
      left.
      reflexivity.
    + simpl.
      right.
      apply IH.
      apply Hr.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros.
  split.
  - induction l as [| h t IH].
    + intros. simpl in H. destruct H.
    + intros.
      simpl.
      destruct H.
      * exists h.
        split.
          rewrite -> H. reflexivity.
          left. reflexivity.
      * apply IH in H.
        destruct H.
          exists x.
          destruct H.
          split.
            apply H.
            right. apply H0.
  - induction l as [| h t IH].
    + intros.
      simpl.
      destruct H.
      destruct H.
      destruct H0.
    + simpl.
      intros.
      destruct H.
      destruct H.
      destruct H0.
      * rewrite -> H0 in H.
        left.
        rewrite -> H.
        reflexivity.
      * simpl.
        right.
        apply IH.
        exists x.
        split.
          apply H.
          apply H0.
Qed.

Lemma in_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros.
  split.
  - induction l as [| h t IH].
    + simpl. intros. right. apply H.
    + simpl. intros.
      apply or_assoc.
      destruct H.
      * left. apply H.
      * right. apply IH. apply H.
  - induction l as [| h t IH].
    + simpl. intros. destruct H.
        destruct H.
        apply H.
    + simpl. intros. destruct H. destruct H.
        left. apply H.
        right. apply IH. left. apply H.
        right. apply IH. right. apply H.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ All P t
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros.
  split.
  - induction l as [| h t IH].
    + simpl. intros. reflexivity.
    + simpl. intros.
      split.
      * apply H. left. reflexivity.
      * apply IH. intros.
        apply H. right. apply H0.
  - induction l as [| h t IH].
    + simpl. intros. destruct H0.
    + simpl. intros.
      destruct H.
      destruct H0.
      * rewrite -> H0. apply H.
      * apply IH.
          apply H1.
          apply H0.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun (x:nat) => if oddb x then Podd x
                           else Peven x.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true ->  Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros.
  unfold combine_odd_even.
  destruct (oddb n).
  - apply H. reflexivity.
  - apply H0. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros.
  unfold combine_odd_even in H.
  rewrite -> H0 in H.
  apply H.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros.
  unfold combine_odd_even in H.
  rewrite -> H0 in H.
  apply H.
Qed.

