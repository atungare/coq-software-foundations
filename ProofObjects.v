Require Export IndProp.

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.


Theorem ev_8 : ev 8.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Definition ev_8' : ev 8 :=
  (ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0)))).


Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) =>
    fun (H : ev n) =>
      ev_SS (S (S n)) (ev_SS n H).

Definition ev_plus4'' (n : nat) (H : ev n) : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).


Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).


Theorem implication_forall: forall (P Q: Prop),
   (P -> Q) <->
   forall (_: P), Q.
Proof.
  intros.
  split.
  - intros. apply H. apply H0.
  - intros. apply H. apply H0.
Qed.


Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n.
Defined.

Module Props.

Module And.

Inductive and (P Q: Prop) : Prop :=
| conj: P -> Q -> and P Q.

End And.


Lemma and_comm : forall P Q : Prop, P /\Q <-> Q /\ P.
Proof.
  intros.
  split.
  - intros. destruct H.
    split.
    + apply H0.
    + apply H.
  - intros. destruct H.
    split.
    + apply H0.
    + apply H.
Qed.

Definition and_comm'_aux P Q (H : P /\ Q) :=
  match H with
  | conj p q => conj q p
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R: Prop) (PQ: P /\ Q) (QR: Q /\ R) =>
    conj (proj1 P Q PQ) (proj2 Q R QR).


Module Or.

Inductive or (P Q: Prop) :=
| or_introl: P -> or P Q
| or_intror: Q -> or P Q.

End Or.

Definition or_comm : forall P Q, P \/ Q -> Q \/ P :=
  fun (P Q: Prop) (H: P \/ Q) =>
    match H with
    | or_introl P => or_intror P
    | or_intror Q => or_introl Q
    end.


Module Ex.

Inductive ex {A: Type} (P: A -> Prop) : Prop :=
| ex_intro: forall (x : A), P x -> ex P.

End Ex.

Definition some_nat_is_even: exists (x: nat), ev x :=
  ex_intro (fun n => ev n) 0 ev_0.

Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).


Inductive True : Prop :=
| I: True.  

Inductive False : Prop :=.

End Props.

Module MyEquality.

Inductive eq {X: Type} : X -> X -> Prop :=
| eq_refl: forall x, eq x x.

Notation "x = y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.

Lemma leibniz_equality : forall (X : Type) (x y: X),
  x = y ->
  forall (P: X -> Prop), P x -> P y.
Proof.
  intros.
  destruct H.
  apply H0.
Qed.

Lemma four: 2 + 2 = 1 + 3.
Proof.
  apply eq_refl.
Qed.


Definition four' : 2 + 2 = 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Set) (x:X), []++[x] = x::[] :=
  fun (X:Set) (x:X) => eq_refl [x].

End MyEquality.

Definition quiz6 : exists x, x + 3 = 4
  := ex_intro (fun z => (z + 3 = 4)) 1 (refl_equal 4).

