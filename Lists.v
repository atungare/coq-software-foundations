Require Export Induction.
Module NatList.

Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p: natprod) : nat :=
  match p with
  | pair x _ => x
  end.

Definition snd (p: natprod) : nat :=
  match p with
  | pair _ y => y
  end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (snd (4, 7)).

Definition swap_pair (p: natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
  end.

Theorem surjective_pairing: forall p:natprod,
  p = (fst p, snd p).
Proof.
  intros.
  destruct p as [n m].
  simpl. reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros.
  destruct p as [n m].
  simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p: natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros.
  destruct p as [n m].
  simpl. reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count: nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: repeat n count'
  end.

Fixpoint length (l: natlist) : nat :=
  match l with
  | [] => O
  | _ :: l' => S (length l')
  end.

Fixpoint app (l1 l2: natlist) : natlist :=
  match l1 with
  | nil => l2
  | x :: xs => x :: (app xs l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (def:nat) (l:natlist) : nat :=
  match l with
  | nil => def
  | h :: _ => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | _ :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | 0 :: t => nonzeros t
  | h :: t => h :: nonzeros t
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => if (evenb h) then oddmembers t
                           else h :: oddmembers t
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.


Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. simpl. reflexivity. Qed. 

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | [], r2 => r2
  | r1, [] => r1
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.


Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | [] => 0
  | h :: t => (count v t) + (if beq_nat h v then 1 else 0)
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  blt_nat 0 (count v s).

Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | [] => []
  | h :: t => if beq_nat v h then t else h :: remove_one v t
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | [] => []
  | h :: t => if beq_nat v h then remove_all v t else h :: remove_all v t
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | [] => true
  | h :: t => (member h s2) && (subset t (remove_one h s2))
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.

Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros.
  destruct l as [| n l'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros.
  induction l1 as [| h1 t1 IH1'].
  - simpl. reflexivity.
  - simpl. rewrite -> IH1'. reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | [] => []
  | h :: t => (rev t) ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem app_length: forall l1 l2: natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros.
  induction l1 as [| n l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem rev_length: forall l:natlist,
  length (rev l) = length l.
Proof.
  intros.
  induction l as [| h l' IHl'].
  - simpl. reflexivity.
  - simpl.
    rewrite -> app_length, plus_comm.
    rewrite -> IHl'.
    reflexivity.
Qed.

