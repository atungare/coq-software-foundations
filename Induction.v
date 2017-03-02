Require Export Basic.

Theorem n_plus_O: forall n:nat,
  n = n + O.
Proof.
  intros.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

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
Qed.

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

Theorem mult_a_Sb: forall a b:nat,
  a * S b = a + a * b.
Proof.
  intros.
  induction a as [| a' IHa'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHa'.
    rewrite -> plus_swap.
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
    + simpl.
      rewrite -> mult_a_Sb.
      rewrite -> plus_swap.
      reflexivity.
Qed.

(* exercises *)
Theorem leb_refl : forall n:nat,
  true = leb n n.
Proof.
  intros.
  induction n as [| n' IHn'].
  - reflexivity.
  - rewrite -> IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  intros.
  destruct n as [| n'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros.
  destruct b as [| b'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  intros.
  induction p as [| p' IHp'].
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> IHp'. reflexivity.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  intros.
  replace (S n) with (n + 1).
  - rewrite -> plus_1_neq_0. reflexivity.
  - rewrite <- plus_1_r. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros.
  destruct n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- plus_O_r. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros.
  destruct b as [| b'].
  destruct c as [| c'].
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> mult_plus_distr_r. reflexivity.
Qed.

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_swap' : forall n m p:nat,
  n + (m + p) = m + (n + p).
Proof.
  intros.
  intros.
  rewrite <- plus_assoc.
  assert (H: m + (n + p) = (m + n) + p). { rewrite -> plus_assoc. reflexivity. }
  rewrite -> H.
  rewrite <- plus_comm.
  replace (m + n + p) with (p + (m + n)).
  - replace (n + m) with (m + n).
    + reflexivity.
    + rewrite -> plus_comm. reflexivity.
  - rewrite -> plus_comm. reflexivity.
Qed.

Theorem bin_to_nat_pres_incr: forall b:bin,
  (bin_to_nat (incr b)) = S (bin_to_nat b).
Proof.
  intros.
  induction b as [| b' | b'' IHb'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHb'. simpl.
    replace (bin_to_nat b' + 0) with (bin_to_nat b').
    + rewrite <- plus_1_r. rewrite <- plus_n_Sm. reflexivity.
    + rewrite <- plus_O_r. reflexivity.
  - simpl. rewrite <- plus_1_r. reflexivity.
Qed.

(* binary inverse *)
Fixpoint nat_to_bin (n: nat) : bin :=
  match n with
  | O => Zero
  | S n' => incr (nat_to_bin n')
  end.       

Theorem nat_bin_nat: forall (n: nat),
  bin_to_nat (nat_to_bin n) = n.
Proof.
  intros.
  induction n as [| n' IH].
  - reflexivity.
  - simpl.
    rewrite -> bin_to_nat_pres_incr.
    rewrite -> IH.
    reflexivity.
Qed.

Fixpoint normalize (b: bin) : bin :=
  match b with
  | Zero => Zero
  | Twice b' => match (normalize b') with
                | Zero => Zero
                | _ => Twice (normalize b')
                end
  | TwicePlusOne b' => TwicePlusOne (normalize b')
  end.

Compute (normalize (TwicePlusOne (Twice (TwicePlusOne (Twice (TwicePlusOne (Twice Zero))))))).

Compute (normalize (normalize (Twice Zero))).

Theorem nat_twice_plus_one: forall (n:nat),
    nat_to_bin (n + n + 1) = TwicePlusOne (nat_to_bin n).
Proof.
  intros.
  induction n as [| n' IH].
  - reflexivity.
  - simpl.
    replace (n' + S n') with (S (n' + n')).
    + simpl.
      rewrite -> IH.
      reflexivity.
    + rewrite -> plus_n_Sm.
      reflexivity.
Qed.

Theorem normalize_incr: forall (b: bin),
  incr (normalize b) = normalize (incr b).
Proof.
  intros.
  induction b as [| b' | b'' IH].
  - reflexivity.
  - simpl.
    rewrite <- IHb'.
    destruct (normalize b').
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - simpl.
    destruct (normalize b'').
    + reflexivity.
    + reflexivity.
    + reflexivity. 
Qed.

Theorem nat_twice: forall (n: nat),
    nat_to_bin (n + n) = normalize (Twice (nat_to_bin n)).
Proof.
  intros.
  induction n as [| n' IH].
  - reflexivity.
  - rewrite <- plus_n_Sm.
    simpl.
    rewrite <- normalize_incr.
    rewrite -> IH.
    induction (nat_to_bin n') as [| b | b' IHb].
    + reflexivity.
    + reflexivity.
    + rewrite <- IH.
Admitted.

Theorem normalize_idemp: forall (b: bin),
  normalize (normalize b) = normalize b.
Proof.
  intros.
  induction b as [| b' | b'' IH].
  - reflexivity.
  - simpl.
    rewrite -> IHb'.
    reflexivity.
  - induction (normalize (Twice b'')).
    + reflexivity.
    + simpl.
      rewrite -> IHb.
      reflexivity.
    + 
      rewrite -> IHb.
      simpl.

  - induction b'' as [| c | c' IH'].
    + reflexivity.
    + simpl.
      simpl in IH.
      rewrite -> IH.
      reflexivity.
Admitted.


Theorem bin_nat_bin: forall (b: bin),
  nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intros.
  induction b as [| b' | b'' IH].
  - reflexivity.
  - simpl.
    rewrite <- plus_O_r.
    rewrite -> nat_twice_plus_one.
    rewrite -> IHb'.
    reflexivity.
  - simpl.
    rewrite <- plus_O_r.
    rewrite -> nat_twice.
    simpl.
    rewrite -> IH.
    rewrite -> normalize_idemp.
    reflexivity.
Qed.