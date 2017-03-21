Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import Maps.
Require Import Imp.


Definition aequiv (a1 a2: aexp) : Prop :=
  forall (st: state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2: bexp) : Prop :=
  forall (st: state),
    beval st b1 = beval st b2.

Theorem aequiv_example:
  aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof.
  unfold aequiv. intros. simpl. omega.
Qed.

Theorem bequiv_example:
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
Proof.
  unfold bequiv. intros.
  unfold beval. rewrite aequiv_example. 
  reflexivity.
Qed.

Definition cequiv (c1 c2: com) : Prop :=
  forall (st st': state),
    (c1 / st \\ st') <-> (c2 / st \\ st').

Theorem skip_left: forall c,
  cequiv
     (SKIP ;; c)
     c.
Proof.
  unfold cequiv. intros.
  split; intros.
  - inversion H. subst.
    inversion H2. subst.
    assumption.
  - apply E_Seq with st.
    + apply E_Skip.
    + assumption.
Qed.

Theorem skip_right: forall c,
  cequiv
    (c ;; SKIP)
    c.
Proof.
  unfold cequiv. intros.
  split; intros.
  - inversion H. subst.
    inversion H5. subst.
    assumption.
  - apply E_Seq with st'.
    + assumption.
    + apply E_Skip.
Qed.

Theorem IFB_true_simple: forall c1 c2,
  cequiv
    (IFB BTrue THEN c1 ELSE c2 FI)
    c1.
Proof.
  unfold cequiv. intros.
  split; intros.
  - inversion H; subst.
    + assumption.
    + inversion H5.
  - apply E_IfTrue. 
    + reflexivity.
    + assumption.
Qed.

Theorem IFB_true: forall b c1 c2,
    bequiv b BTrue ->
    cequiv
      (IFB b THEN c1 ELSE c2 FI)
      c1.
Proof.
  unfold bequiv, cequiv.
  split; intros.
  - inversion H0; subst.
    + assumption.
    + rewrite H in H6.
      inversion H6.
  - apply E_IfTrue.
    + apply H.
    + assumption.
Qed.

Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.
Proof.
  unfold bequiv, cequiv.
  split; intros.
  - inversion H0; subst.
    + rewrite H in H6.
      inversion H6.
    + assumption.
  - apply E_IfFalse.
    + apply H.
    + assumption.
Qed.

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  unfold cequiv. intros.
  split; intros. 
  - inversion H; subst.
    + apply E_IfFalse.
      * simpl. rewrite H5. reflexivity.
      * assumption.
    + apply E_IfTrue.
      * simpl. rewrite H5. reflexivity.
      * assumption.
  - inversion H; subst.
    + apply E_IfFalse.
      * simpl in H5. rewrite negb_true_iff in H5. apply H5.
      * assumption.
    + apply E_IfTrue.
      * simpl in H5. rewrite negb_false_iff in H5. apply H5.
      * assumption.
Qed.

Theorem WHILE_false : forall b c,
  bequiv b BFalse ->
  cequiv
    (WHILE b DO c END)
    SKIP.
Proof.
  unfold bequiv, cequiv. intros.
  split; intros.
  - inversion H0; subst.
    + apply E_Skip.
    + rewrite H in H3. inversion H3.
  - inversion H0; subst.
    apply E_WhileEnd.
    apply H.
Qed.


Theorem WHILE_true_nonterm : forall b c st st',
    bequiv b BTrue ->
    ~( (WHILE b DO c END) / st \\ st').
Proof.
  unfold not, bequiv. intros.
  remember (WHILE b DO c END) as cw.
  induction H0;
    inversion Heqcw; subst.
  - rewrite H in H0. inversion H0.
  - apply IHceval2. apply Heqcw.
Qed.

Lemma bequiv_self : forall b,
    bequiv b b.
Proof.
  unfold bequiv; intros; reflexivity.
Qed.

Theorem WHILE_true: forall b c,
  bequiv b BTrue ->
  cequiv
    (WHILE b DO c END)
    (WHILE BTrue DO SKIP END).
Proof.
  unfold cequiv; intros.
  split; intros.
  - exfalso.
    apply (WHILE_true_nonterm b c st st' H).
    apply H0.
  - inversion H0; subst.
    + apply E_WhileEnd.
      inversion H5.
    + exfalso.
      apply (WHILE_true_nonterm BTrue SKIP st st').
      * apply bequiv_self.
      * apply H0.
Qed.

Theorem loop_unrolling: forall b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c ;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  unfold cequiv; intros.
  split; intros.
  - inversion H; subst.
    + apply E_IfFalse.
      * assumption.
      * apply E_Skip.
    + apply E_IfTrue.
      * assumption.
      * apply E_Seq with (st' := st'0).
        assumption.
        assumption.
  - inversion H; subst.
    + inversion H6; subst.
      apply E_WhileLoop with (st' := st'0).
      * assumption.
      * assumption.
      * assumption.
    + inversion H6; subst.
      apply E_WhileEnd.
      assumption.
Qed.

Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  unfold cequiv; intros.
  split; intros.
  - inversion H; subst.
    inversion H2; subst.
    apply E_Seq with (st' := st'1).
      assumption.
    apply E_Seq with (st' := st'0).
      assumption.
      assumption.
  - inversion H; subst.
    inversion H5; subst.
    apply E_Seq with (st' := st'1).
      apply E_Seq with (st' := st'0).
        assumption.
        assumption.
      assumption.
Qed.

Theorem identity_assignment : forall (X:id),
  cequiv
    (X ::= AId X)
    SKIP.
Proof.
  unfold cequiv; intros.
  split; intros.
  - inversion H; subst.
    simpl in *.
    replace (t_update st X (st X)) with st.
    + apply E_Skip.
    + apply functional_extensionality. intros.
      rewrite t_update_same. reflexivity.
  - replace st' with (t_update st' X (aeval st' (AId X))).
    + inversion H; subst.
      apply E_Ass.
      reflexivity.
    + simpl. rewrite t_update_same. reflexivity.
Qed.

Theorem assign_aequiv : forall X e,
  aequiv (AId X) e ->
  cequiv SKIP (X ::= e).
Proof.
  unfold aequiv; intros.
  split; intros.
  - inversion H0; subst.
    assert (st' = t_update st' X (st' X)).
    + apply functional_extensionality. intros.
      rewrite t_update_same.
      reflexivity.
    + rewrite H1 at 2.
      apply E_Ass.
      rewrite <- H.
      reflexivity.
  - inversion H0; subst.
    assert (st = t_update st X (aeval st e)).
    + apply functional_extensionality. intros.
      rewrite <- H.
      simpl.
      rewrite t_update_same.
      reflexivity.
    + rewrite <- H1.
      apply E_Skip.
Qed.

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  unfold aequiv. reflexivity.
Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  unfold aequiv; intros.
  rewrite H. reflexivity.
Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
    aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv; intros.
  rewrite H, H0.
  reflexivity.
Qed.

Definition refl_bequiv := bequiv_self.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv; intros.
  rewrite H.
  reflexivity.
Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv; intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma refl_cequiv : forall (c: com), cequiv c c.
Proof.
  unfold cequiv; intros.
  reflexivity.
Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv; intros.
  rewrite H.
  reflexivity.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv; intros.
  apply (iff_trans (c1 / st \\ st') (c2 / st \\ st') (c3 / st \\ st') (H st st') (H0 st st')).
Qed.

Theorem CAss_congruence : forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
  unfold aequiv, cequiv; intros.
  split; intros; inversion H0; subst;
    first [rewrite H | rewrite <- H];
    apply E_Ass;
    reflexivity.
Qed.

Theorem CWhile_congruence : forall b1 b2 c1 c2,
  bequiv b1 b2 ->
  cequiv c1 c2 ->
  cequiv
    (WHILE b1 DO c1 END)
    (WHILE b2 DO c2 END).
Proof.
  unfold bequiv, cequiv; intros.
  split; intros.
  - remember (WHILE b1 DO c1 END) as cwhile.
    induction H1; inversion Heqcwhile; subst.
    + apply E_WhileEnd. rewrite <- H. assumption.
    + apply E_WhileLoop with (st' := st').
      * rewrite <- H. assumption.
      * rewrite <- H0. assumption.
      * apply IHceval2. reflexivity.
  - remember (WHILE b2 DO c2 END) as cwhile.
    induction H1; inversion Heqcwhile; subst.
    + apply E_WhileEnd. rewrite H. assumption.
    + apply E_WhileLoop with (st' := st').
      * rewrite H. assumption.
      * rewrite H0. assumption.
      * apply IHceval2. reflexivity.
Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
  unfold cequiv; intros.
  split; intros.
  - remember (c1;;c2) as cseq.
    destruct H1; inversion Heqcseq; subst.
    + apply E_Seq with (st' := st').
      * apply H. assumption.
      * apply H0. assumption.
  - remember (c1';;c2') as cseq.
    destruct H1; inversion Heqcseq; subst.
    + apply E_Seq with (st' := st').
      * apply H. assumption.
      * apply H0. assumption.
Qed.

Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI)
         (IFB b' THEN c1' ELSE c2' FI).
Proof.
  unfold bequiv, cequiv; intros.
  split; intros.
  - remember (IFB b THEN c1 ELSE c2 FI) as cif.
    destruct H2; inversion Heqcif; subst.
    + apply E_IfTrue.
      * rewrite <- H. assumption.
      * apply H0. assumption.
    + apply E_IfFalse.
      * rewrite <- H. assumption.
      * apply H1. assumption.
  - remember (IFB b' THEN c1' ELSE c2' FI) as cif.
    destruct H2; inversion Heqcif; subst.
    + apply E_IfTrue.
      * rewrite  H. assumption.
      * apply H0. assumption.
    + apply E_IfFalse.
      * rewrite H. assumption.
      * apply H1. assumption.
Qed.  

Example congruence_example:
  cequiv
    (* Program 1: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= ANum 0
     ELSE
       Y ::= ANum 42
     FI)
    (* Program 2: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= AMinus (AId X) (AId X) (* <--- changed here *)
     ELSE
       Y ::= ANum 42
     FI).
Proof.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CIf_congruence.
    + apply refl_bequiv.
    + apply CAss_congruence.
      unfold aequiv. simpl.
      symmetry.
      apply minus_diag.
    + apply refl_cequiv.
Qed.

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId i        => AId i
  | APlus a1 a2  =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2  =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp
      (AMult (APlus (ANum 1) (ANum 2)) (AId X))
  = AMult (ANum 3) (AId X).
Proof.
  reflexivity.
Qed.

Example fold_aexp_ex2 :
    fold_constants_aexp
      (AMinus (AId X) (APlus (AMult (ANum 0) (ANum 6))
                             (AId Y)))
  = AMinus (AId X) (APlus (ANum 0) (AId Y)).
Proof. reflexivity. Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue        => BTrue
  | BFalse       => BFalse
  | BEq a1 a2  =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if beq_nat n1 n2 then BTrue else BFalse
      | (a1', a2') =>
          BEq a1' a2'
      end
  | BLe a1 a2  =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if leb n1 n2 then BTrue else BFalse
      | (a1', a2') =>
          BLe a1' a2'
      end
  | BNot b1  =>
      match (fold_constants_bexp b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2  =>
      match (fold_constants_bexp b1, fold_constants_bexp b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Example fold_bexp_ex1 :
    fold_constants_bexp (BAnd BTrue (BNot (BAnd BFalse BTrue)))
  = BTrue.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
    fold_constants_bexp
      (BAnd (BEq (AId X) (AId Y))
            (BEq (ANum 0)
                 (AMinus (ANum 2) (APlus (ANum 1)
                                         (ANum 1)))))
  = BAnd (BEq (AId X) (AId Y)) BTrue.
Proof. reflexivity. Qed.

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP      =>
      SKIP
  | i ::= a  =>
      i ::= (fold_constants_aexp a)
  | c1 ;; c2  =>
      (fold_constants_com c1) ;; (fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => IFB b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.

Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    (X ::= APlus (ANum 4) (ANum 5);;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y))
             (APlus (ANum 2) (ANum 4)) THEN
       SKIP
     ELSE
       Y ::= ANum 0
     FI;;
     IFB BLe (ANum 0)
             (AMinus (ANum 4) (APlus (ANum 2) (ANum 1)))
     THEN
       Y ::= ANum 0
     ELSE
       SKIP
     FI;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END)
  = (* After constant folding: *)
    (X ::= ANum 9;;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
       SKIP
     ELSE
       (Y ::= ANum 0)
     FI;;
     Y ::= ANum 0;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END).
Proof. reflexivity. Qed.


Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound;
  unfold aequiv. intros.
  induction a; simpl; try reflexivity;
    destruct (fold_constants_aexp a1);
    destruct (fold_constants_aexp a2);
    rewrite IHa1; rewrite IHa2;
    reflexivity.
Qed.

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound;
  unfold bequiv. intros.
  induction b; try reflexivity.
  - rename a into a1. rename a0 into a2.
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1').
    replace (aeval st a2) with (aeval st a2').
    destruct a1'; destruct a2'; try reflexivity.
    simpl.
    destruct (beq_nat n n0); reflexivity.
    + rewrite Heqa2'.
      rewrite <- fold_constants_aexp_sound.
      reflexivity.
    + rewrite Heqa1'.
      rewrite <- fold_constants_aexp_sound.
      reflexivity.
  - rename a into a1. rename a0 into a2.
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1').
    replace (aeval st a2) with (aeval st a2').
    destruct a1'; destruct a2'; try reflexivity.
    simpl.
    destruct (leb n n0); reflexivity.
    + rewrite Heqa2'.
      rewrite <- fold_constants_aexp_sound.
      reflexivity.
    + rewrite Heqa1'.
      rewrite <- fold_constants_aexp_sound.
      reflexivity.
  - simpl.
    remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1, IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound; intros.
  induction c; simpl.
  - apply refl_cequiv.
  - apply CAss_congruence.
    apply fold_constants_aexp_sound.
  - apply CSeq_congruence.
    + assumption.
    + assumption.
  - assert (bequiv b (fold_constants_bexp b)).
    { apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
    + apply trans_cequiv with c1; try assumption.
      apply IFB_true. assumption.
    + apply trans_cequiv with c2; try assumption.
      apply IFB_false. assumption.
  - assert (bequiv b (fold_constants_bexp b)).
    { apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CWhile_congruence; assumption).
    + apply (WHILE_true b c H).
    + apply (WHILE_false b c H).
Qed.

Fixpoint optimize_0plus_aexp (e:aexp) : aexp :=
      match e with
      | AId x => AId x
      | ANum n =>
          ANum n
      | APlus (ANum 0) e2 =>
          optimize_0plus_aexp e2
      | APlus e1 e2 =>
          APlus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
      | AMinus e1 e2 =>
          AMinus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
      | AMult e1 e2 =>
          AMult (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
      end.

Theorem optimize_0plus_aexp_sound :
    atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound, aequiv; intros. 
  induction a; try reflexivity.
  - destruct a1.
    + destruct n.
      * simpl. apply IHa2.
      * simpl. rewrite IHa2. reflexivity.
    + simpl. rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1.
      rewrite IHa1. rewrite IHa2.
      reflexivity.
    + simpl. simpl in IHa1.
      rewrite IHa1. rewrite IHa2.
      reflexivity.
    + simpl. simpl in IHa1.
      rewrite IHa1. rewrite IHa2.
      reflexivity.
  - simpl.
    rewrite IHa1. rewrite IHa2.
    reflexivity.
  - simpl.
    rewrite IHa1. rewrite IHa2.
    reflexivity.
Qed.

Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
  match b with
  | BEq l r => BEq (optimize_0plus_aexp l) (optimize_0plus_aexp r)
  | BLe l r => BLe (optimize_0plus_aexp l) (optimize_0plus_aexp r)
  | BNot b' => BNot (optimize_0plus_bexp b')
  | BAnd l r => BAnd (optimize_0plus_bexp l) (optimize_0plus_bexp r)
  | _ => b
  end.

Theorem optimize_0plus_bexp_sound :
    btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound;
  unfold bequiv. intros.
  induction b; try reflexivity.
  - rename a into a1. rename a0 into a2.
    simpl.
    remember (optimize_0plus_aexp a1) as a1' eqn:Heqa1'.
    remember (optimize_0plus_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1').
    replace (aeval st a2) with (aeval st a2').
    reflexivity.
    + rewrite Heqa2'.
      rewrite <- optimize_0plus_aexp_sound.
      reflexivity.
    + rewrite Heqa1'.
      rewrite <- optimize_0plus_aexp_sound.
      reflexivity.
  - rename a into a1. rename a0 into a2.
    simpl.
    remember (optimize_0plus_aexp a1) as a1' eqn:Heqa1'.
    remember (optimize_0plus_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1').
    replace (aeval st a2) with (aeval st a2').
    reflexivity.
    + rewrite Heqa2'.
      rewrite <- optimize_0plus_aexp_sound.
      reflexivity.
    + rewrite Heqa1'.
      rewrite <- optimize_0plus_aexp_sound.
      reflexivity.
  - simpl.
    remember (optimize_0plus_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - simpl.
    remember (optimize_0plus_bexp b1) as b1' eqn:Heqb1'.
    remember (optimize_0plus_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1, IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.

Fixpoint optimize_0plus_com (c : com) : com :=
  match c with
  | SKIP      =>
      SKIP
  | i ::= a  =>
      i ::= (optimize_0plus_aexp a)
  | c1 ;; c2  =>
      (optimize_0plus_com c1) ;; (optimize_0plus_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      match optimize_0plus_bexp b with
      | BTrue => optimize_0plus_com c1
      | BFalse => optimize_0plus_com c2
      | b' => IFB b' THEN optimize_0plus_com c1
                     ELSE optimize_0plus_com c2 FI
      end
  | WHILE b DO c END =>
      match optimize_0plus_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (optimize_0plus_com c) END
      end
  end.

Theorem optimize_0plus_com_sound :
    ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound; intros.
  induction c; simpl.
  - apply refl_cequiv.
  - apply CAss_congruence.
    apply optimize_0plus_aexp_sound.
  - apply CSeq_congruence.
    + assumption.
    + assumption.
  - assert (bequiv b (optimize_0plus_bexp b)).
    { apply optimize_0plus_bexp_sound. }
    destruct (optimize_0plus_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
    + apply trans_cequiv with c1; try assumption.
      apply IFB_true. assumption.
    + apply trans_cequiv with c2; try assumption.
      apply IFB_false. assumption.
  - assert (bequiv b (optimize_0plus_bexp b)).
    { apply optimize_0plus_bexp_sound. }
    destruct (optimize_0plus_bexp b) eqn:Heqb;
      try (apply CWhile_congruence; assumption).
    + apply (WHILE_true b c H).
    + apply (WHILE_false b c H).
Qed.

Definition optimizer (c: com) : com :=
  optimize_0plus_com (fold_constants_com c).


Example optimizer_ex :
  optimizer
    (* Original program: *)
    (X ::= APlus (APlus (ANum 0) (ANum 2)) (ANum 5))
  = (* After constant folding: *)
    (X ::= ANum 7).
Proof. reflexivity. Qed.

Theorem optimizer_sound:
    ctrans_sound optimizer.
Proof.
  unfold ctrans_sound, optimizer; intros.
  apply trans_cequiv with (fold_constants_com c).
  - apply fold_constants_com_sound.
  - apply (optimize_0plus_com_sound (fold_constants_com c)).
Qed.



Fixpoint subst_aexp (i : id) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n       =>
      ANum n
  | AId i'       =>
      if beq_id i i' then u else AId i'
  | APlus a1 a2  =>
      APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 =>
      AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2  =>
      AMult (subst_aexp i u a1) (subst_aexp i u a2)
  end.

Example subst_aexp_ex :
  subst_aexp X (APlus (ANum 42) (ANum 53))
             (APlus (AId Y) (AId X))
= (APlus (AId Y) (APlus (ANum 42) (ANum 53))).
Proof. reflexivity. Qed.

Definition subst_equiv_property := forall i1 i2 a1 a2,
  cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold not, subst_equiv_property.
  intros.
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= AId X)
      as c1.
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= APlus (AId X) (ANum 1))
      as c2.
  assert (cequiv c1 c2)
    by (subst; apply H). 
  remember (t_update (t_update empty_state X 1) Y 1) as st1.
  remember (t_update (t_update empty_state X 1) Y 2) as st2.
  assert (H1: c1 / empty_state \\ st1);
  assert (H2: c2 / empty_state \\ st2);
  try (subst;
       apply E_Seq with (st' := (t_update empty_state X 1));
       apply E_Ass; reflexivity).
  apply H0 in H1.
  assert (Hcontra: st1 = st2)
    by (apply (ceval_deterministic c2 empty_state); assumption).
  assert (Hcontra': st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst.
  inversion Hcontra'.
Qed.


Inductive var_not_used_in_aexp (X:id) : aexp -> Prop :=
  | VNUNum: forall n, var_not_used_in_aexp X (ANum n)
  | VNUId: forall Y, X <> Y -> var_not_used_in_aexp X (AId Y)
  | VNUPlus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (APlus a1 a2)
  | VNUMinus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMinus a1 a2)
  | VNUMult: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMult a1 a2).

Lemma aeval_weakening : forall i st a ni,
  var_not_used_in_aexp i a ->
  aeval (t_update st i ni) a = aeval st a.
Proof.
  intros.
  induction a; simpl; inversion H; subst;
    try reflexivity;
    try (
        apply IHa1 in H2; apply IHa2 in H3;
        rewrite H2, H3;
        reflexivity
      ).
  - apply (t_update_neq _ ni i i0 st H1).
Qed.

(* Theorem not_used_then_subst_equiv_property : forall i1 i2 a1 a2,
         var_not_used_in_aexp i1 a1 ->
         cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).
         Proof.
         intros.
         apply CSeq_congruence.
         - apply refl_cequiv.
         - apply CAss_congruence.
         unfold aequiv.
         remember (subst_aexp i1 a1 a2) as sa.
         induction a1; intros; simpl.
         + simpl in Heqsa. *)

Theorem inequiv_exercise:
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof.
  unfold not; intros.
  eapply loop_never_stops with empty_state empty_state.
  unfold loop.
  apply H.
  apply E_Skip.
Qed.

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' l" := (CHavoc l) (at level 60).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st \\ st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
      aeval st a1 = n ->
      (X ::= a1) / st \\ t_update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
      c1 / st \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
      beval st b1 = true ->
      c1 / st \\ st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
      beval st b1 = false ->
      c2 / st \\ st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st \\ st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
      beval st b1 = true ->
      c1 / st \\ st' ->
      (WHILE b1 DO c1 END) / st' \\ st'' ->
      (WHILE b1 DO c1 END) / st \\ st''
  | E_Havoc : forall (X: id) (st: state) (n: nat),
      (HAVOC X) / st \\ t_update st X n

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

Example havoc_example1 : (HAVOC X) / empty_state \\ t_update empty_state X 0.
Proof.
  apply E_Havoc.
Qed.


Example havoc_example2 :
  (SKIP;; HAVOC Z) / empty_state \\ t_update empty_state Z 42.
Proof.
  apply E_Seq with (st' := empty_state).
  - apply E_Skip.
  - apply E_Havoc.
Qed.

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  c1 / st \\ st' <-> c2 / st \\ st'.


Definition pXY :=
  HAVOC X;; HAVOC Y.

Definition pYX :=
  HAVOC Y;; HAVOC X.

Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~ cequiv pXY pYX.
Proof.
  left.
  unfold not, cequiv, pXY, pYX; intros.
  split; intros; inversion H; subst.
  - inversion H2; inversion H5; subst.
    apply E_Seq with (st' := (t_update st Y n0)).
    + apply E_Havoc.
    + assert (J :  t_update (t_update st X n) Y n0 =  t_update (t_update st Y n0) X n).
      { apply t_update_permute.
        unfold not; intros; inversion H0. }
      rewrite J.
      apply E_Havoc.
  - inversion H2; inversion H5; subst.
    apply E_Seq with (st' := (t_update st X n0)).
    + apply E_Havoc.
    + assert (J :  t_update (t_update st X n0) Y n =  t_update (t_update st Y n) X n0).
      { apply t_update_permute.
        unfold not; intros; inversion H0. }
      rewrite <- J.
      apply E_Havoc.
Qed.

Definition ptwice :=
  HAVOC X;; HAVOC Y.

Definition pcopy :=
  HAVOC X;; Y ::= AId X.

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~ cequiv ptwice pcopy.
Proof.
  right.
  unfold not, cequiv; intros.
  remember (t_update (t_update empty_state X 1) Y 5) as st'.
  assert (ptwice / empty_state \\ st' -> 
          pcopy / empty_state \\ st')
         by apply H.
  assert (~ (pcopy / empty_state \\ st')).
  {
   unfold not; intros.
   inversion H1; subst.
   inversion H7; subst.
   simpl in H8.
   assert (t_update (t_update empty_state X 1) Y 5 X = 1).
   { reflexivity. }
   assert (t_update (t_update empty_state X 1) Y 5 Y = 5).
   { reflexivity. }
   rewrite <- H8 in H2, H3.
   assert (st'0 X = 1).
   { apply H2. }
   assert (st'0 X = 5).
   { apply H3. }
   rewrite H5 in H6.
   inversion H6.   
  }
  apply H1.
  apply H0.
  unfold ptwice.
  rewrite Heqst'.
  apply E_Seq with (st' := (t_update empty_state X 1)).
  - apply E_Havoc.
  - apply E_Havoc.
Qed.


Definition p1 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC Y;;
    X ::= APlus (AId X) (ANum 1)
  END.

Definition p2 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    SKIP
  END.

Lemma p1_may_diverge : forall st st', st X <> 0 ->
  ~ p1 / st \\ st'.
Proof.
  unfold not, p1; intros.
  remember (WHILE BNot (BEq (AId X) (ANum 0))
        DO HAVOC Y;; X ::= APlus (AId X) (ANum 1) END) as p1.
  induction H0; inversion Heqp1.
  - subst. 
    apply H.
    simpl in H0.
    apply negb_false_iff in H0.
    apply beq_nat_true in H0.
    assumption.
  - apply IHceval2.
    + rewrite H3 in H0_.
      inversion H0_; subst.
      inversion H8; subst.
      rewrite t_update_eq.
      simpl.
      rewrite <- plus_n_Sm.
      intros.
      inversion H1.
    + assumption.
Qed.

Lemma p2_may_diverge : forall st st', st X <> 0 ->
  ~ p2 / st \\ st'.
Proof.
  unfold not, p2; intros.
  remember (WHILE (BNot (BEq (AId X) (ANum 0))) DO
    SKIP
  END) as p2. 
  induction H0; inversion Heqp2.
  - apply H.
    rewrite H2 in H0.
    simpl in H0.
    apply negb_false_iff in H0.
    apply beq_nat_true in H0.
    assumption.
  - apply IHceval2.
    + rewrite H3 in H0_.
      inversion H0_; subst.
      assumption.
    + rewrite H2, H3. reflexivity.
Qed.

Theorem p1_p2_equiv : cequiv p1 p2.
Proof.
  split; intros; inversion H; subst;
    try (apply E_WhileEnd; assumption);
    try ((apply p1_may_diverge with (st := st) (st' := st') in H);
         inversion H;
         simpl in H2;
         apply negb_true_iff in H2;
         apply beq_nat_false in H2;
         assumption).
    - (apply p1_may_diverge with (st := st) (st' := st') in H).
      inversion H.
              apply negb_true_iff in H2;
        apply beq_nat_false in H2.
        assumption.
   - (apply p2_may_diverge with (st := st) (st' := st') in H).
      inversion H.
              apply negb_true_iff in H2;
        apply beq_nat_false in H2.
        assumption.
Qed.

