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
  | h :: t => (if beq_nat h v then 1 else 0) + (count v t)
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

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1 as [| h1 t1 IH].
  - simpl. destruct l2 as [| h2 t2].
    + simpl. reflexivity.
    + simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. destruct l2 as [| h2 t2].
    + simpl. rewrite -> app_nil_r. reflexivity.
    + rewrite -> IH. simpl. rewrite -> app_assoc. reflexivity.
Qed.


Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr.
    simpl. rewrite -> IH.
    reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros.
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros.
  induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl.
    destruct h as [| h'].
    + simpl. rewrite -> IH. reflexivity.
    + simpl. rewrite -> IH. reflexivity.
Qed.


Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ => false
  | _, [] => true
  | h1 :: t1, h2 :: t2 => (beq_nat h1 h2) && (beq_natlist t1 t2)
  end.

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
Proof. reflexivity. Qed.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intros.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. induction h as [| h' IH'].
    + simpl. rewrite <- IH. reflexivity.
    + simpl. rewrite <- IH'. reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
  intros.
  destruct s as [| h t].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


Theorem leb_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem remove_decreases_count: forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros. 
  induction s as [| h t IH].
  - simpl. reflexivity.
  - destruct h as [| h'].
    + simpl. rewrite -> leb_n_Sn. reflexivity.
    + simpl. rewrite -> IH. reflexivity.
Qed.

Theorem bag_count_sum: forall (s1 s2:bag),
  count 0 (sum s1 s2) = (count 0 s1) + (count 0 s2).
Proof.
  intros.
  induction s1 as [| h1 t1 IH].
  - simpl. reflexivity.
  - destruct h1 as [| h1'].
    + simpl. rewrite -> IH. reflexivity.
    + simpl. rewrite -> IH. reflexivity.
Qed.


Theorem rev_injective: forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.



Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | [] => None
  | x :: l' => match n with
               | O => Some x
               | S n' => nth_error l' n'
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.


Definition option_elim (def : nat) (o : natoption) : nat :=
  match o with
  | None => def
  | Some x => x
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | [] => None
  | h :: _ => Some h
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros.
  destruct l.
  - reflexivity.
  - reflexivity.
Qed.

End NatList.

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id (i j: id) :=
  match i, j with
  | Id x, Id y => beq_nat x y
  end.

Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
  intros.
  destruct x as [x'].
  simpl. rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Module PartialMap.
Export NatList.

Inductive partial_map : Type :=
  | empty : partial_map
  | record : id -> nat -> partial_map -> partial_map.

Definition update (d:partial_map) (x:id) (val:nat) :=
  record x val d.

Fixpoint find (x:id) (d:partial_map) : natoption :=
  match d with
  | empty => None
  | record k v d' => if beq_id x k then Some v
                                    else find x d'
  end.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros.
  simpl. rewrite <- beq_id_refl. reflexivity.
Qed.


Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    beq_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros.
  simpl. rewrite -> H. reflexivity.
Qed.

End PartialMap.

