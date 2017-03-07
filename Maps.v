Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.


Inductive id : Type :=
| Id: string -> id.

Definition beq_id (a b: id) : bool :=
  match a, b with
  | Id a', Id b' => if string_dec a' b' then true else false
  end.

Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
  intros [x'].
  simpl.
  destruct (string_dec x' x').
  - reflexivity.
  - destruct n. reflexivity.
Qed.


Theorem beq_id_true_iff : forall x y : id,
  beq_id x y = true <-> x = y.
Proof.
  intros [x'] [y'].
  unfold beq_id.
  destruct (string_dec x' y').
  - rewrite -> e. 
    split.
    + reflexivity.
    + reflexivity.
  - split.
    + intros. inversion H.
    + intros. inversion H. destruct n. apply H1.
Qed.

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false <->
  x <> y.
Proof.
  intros.
  rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false.
  reflexivity.
Qed.


Theorem false_beq_id : forall x y : id,
   x <> y ->
   beq_id x y = false.
Proof.
  intros.
  rewrite -> beq_id_false_iff.
  apply H.
Qed.

Definition total_map (A: Type) := id -> A.

Definition t_empty {A: Type} (v: A) : total_map A :=
  fun (_ : id) => v.

Definition t_update {A: Type} (m: total_map A) (k: id) (v: A) : total_map A :=
  fun (x : id) => if beq_id k x then v else m x.


Definition examplemap :=
  t_update (t_update (t_empty false) (Id "foo") false)
           (Id "bar") true.


Example update_example1 : examplemap (Id "baz") = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap (Id "foo") = false.
Proof. reflexivity. Qed.

Example update_example3 : examplemap (Id "quux") = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap (Id "bar") = true.
Proof. reflexivity. Qed.

Lemma t_apply_empty: forall A x v, @t_empty A v x = v.
Proof.
  intros.
  unfold t_empty. reflexivity.
Qed.

Lemma t_update_eq : forall A (m: total_map A) x v,
  (t_update m x v) x = v.
Proof.
  intros.
  unfold t_update.
  rewrite <- beq_id_refl.
  reflexivity.
Qed.

Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  (t_update m x1 v) x2 = m x2.
Proof.
  intros.
  apply false_beq_id in H.
  unfold t_update.
  rewrite -> H.
  reflexivity.
Qed.

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality_dep.
  intros.
  destruct (beq_id x x0).
  + reflexivity.
  + reflexivity.
Qed.

Lemma beq_idP : forall x y, reflect (x = y) (beq_id x y).
Proof.
  intros.
  apply iff_reflect.
  rewrite <- beq_id_true_iff.
  reflexivity.
Qed.

Theorem t_update_same : forall X x (m : total_map X),
  t_update m x (m x) = m.
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality_dep.
  intros.
  destruct (beq_idP x x0).
  + rewrite -> e. reflexivity.
  + reflexivity.
Qed.

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
    (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality_dep.
  intros.
  destruct (beq_idP x1 x).
  - destruct (beq_idP x2 x).
    + exfalso. apply H. rewrite e, e0. reflexivity.
    + reflexivity.
  - destruct (beq_idP x2 x).
    + reflexivity.
    + reflexivity.
Qed.



Definition partial_map (A:Type) := total_map (option A).

Definition empty {A: Type} : partial_map A :=
  t_empty None.

Definition update {A: Type} (m: partial_map A) (k: id) (v: A) :=
  t_update m k (Some v).


Lemma apply_empty : forall A x, @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty. reflexivity.
Qed.

Lemma update_eq : forall A (m: partial_map A) x v,
  (update m x v) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq. reflexivity.
Qed.

Lemma update_neq : forall A (m: partial_map A) x1 x2 v,
  x2 <> x1 ->
  (update m x2 v) x1 = m x1.
Proof.
  intros. unfold update. rewrite t_update_neq.
  - reflexivity.
  - apply H.
Qed.

Lemma update_shadow : forall A (m: partial_map A) x v1 v2,
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros. unfold update. rewrite t_update_shadow. reflexivity.
Qed.

Lemma update_same : forall A (m: partial_map A) x v,
  m x = Some v ->
  update m x v = m.
Proof.
  intros. unfold update. rewrite <- H. rewrite t_update_same. reflexivity.
Qed.

Lemma update_permute : forall A (m: partial_map A) x1 x2 v1 v2,
  x2 <> x1 ->
  (update (update m x2 v2) x1 v1) =
  (update (update m x1 v1) x2 v2).
Proof.
  intros. unfold update. rewrite t_update_permute.
  - reflexivity.
  - apply H.
Qed.

