
Require Export Logic.


Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall (n: nat), ev n -> ev (S (S n)).

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.


Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros.
  simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.


Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros.
  induction n as [| n' IH].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IH.
Qed.

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros.
  inversion H as [| n' H'].
  - simpl. apply ev_0.
  - simpl. apply H'.
Qed.

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros.
  destruct H.
  - simpl. apply ev_0.
  - simpl. apply H.
Qed.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros.
  inversion H.
  apply H1.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros.
  induction H as [| n' H' IH].
  - exists 0. reflexivity.
  - destruct IH as [k' Hk'].
    exists (S k').
    rewrite -> Hk'.
    reflexivity.
Qed.

Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
  intros.
  split.
  - apply ev_even.
  - intros.
    destruct H as [k' Hk'].
    rewrite -> Hk'.
    apply ev_double.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros.
  induction H.
  - apply H0.
  - simpl.
    apply ev_SS.
    apply IHev.
Qed.


Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros.
  split.
  - intros.
    induction H.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply (ev_sum n m IHev'1 IHev'2).
  - intros.
    induction H.
    + apply ev'_0.
    + rewrite -> plus_1_r.
      rewrite -> plus_1_r.
      rewrite -> plus_comm.
      rewrite <- plus_swap.
      simpl.
      apply (ev'_sum n 2 IHev ev'_2).
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros.
  induction H0.
  - apply H.
  - simpl in H.
    apply evSS_ev in H.
    apply IHev.
    apply H.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros.
  apply ev_sum with (n:=n+m) (m:=n+p) in H.
  - replace (n + m + (n + p)) with ((n + n) + (m + p)) in H.
    + rewrite <- double_plus in H.
      apply (ev_ev__ev (double n) (m + p)) in H.
      * apply H.
      * apply ev_double.
    + rewrite -> plus_assoc.
      rewrite -> plus_assoc.
      replace (n + (m + p)) with (m + (n + p)).
      * reflexivity.
      * apply plus_swap.
  - apply H0.
Qed.

Module Playground.

Inductive le : nat -> nat -> Prop :=
| le_n: forall n, le n n
| le_S: forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n.
Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S. apply le_n.
Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros.
  inversion H.
  inversion H2.
Qed.

End Playground.

Definition lt (n m: nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  | sq: forall (n: nat), square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall (n: nat), next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1: forall (n: nat), (ev (S n)) -> (next_even n (S n))
  | ne_2: forall (n: nat), (ev (S (S n))) -> (next_even n (S (S n))).

Inductive total_relation : nat -> nat -> Prop :=
  | tot_rel: forall (n m: nat), total_relation n m.

Inductive empty_relation : nat -> nat -> Prop := .

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros.
  induction H0.
  - apply H.
  - apply le_S. apply IHle.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros.
  induction n as [| n' IH].
  - apply le_n.
  - apply le_S. apply IH.
Qed.

Theorem n_le_Sn: forall n,
  n <= S n.
Proof.
  intros. apply le_S. apply le_n.
Qed.

Theorem Sn_le_m__n_le_m: forall n m,
  (S n) <= m -> n <= m.
Proof.
  intros.
  apply (le_trans n (S n) m (n_le_Sn n)) in H.
  apply H.
Qed.

Theorem n_le_m__n_le_Sm: forall n m,
  n <= m -> n <= S m.
Proof.
  intros.
  induction H.
  - apply le_S. apply le_n.
  - apply le_S. apply IHle.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros.
  induction H.
  - apply le_n.
  - apply le_S.
    apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros.
  inversion H.
  - apply le_n.
  - apply le_trans with (n:=S n).
    + apply n_le_Sn.
    + apply H1.
Qed.


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros.
  induction a as [| a' IH].
  - apply O_le_n.
  - simpl.
    apply n_le_m__Sn_le_Sm.
    apply IH.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt.
 intros.
 split.
 - assert (I: S n1 <= S (n1 + n2)).
    { apply n_le_m__Sn_le_Sm. apply le_plus_l. }
   apply (le_trans (S n1) (S (n1 + n2)) m I) in H.
   apply H.
 - assert (I: S n2 <= S (n1 + n2)).
    { apply n_le_m__Sn_le_Sm. 
      rewrite -> plus_comm.
      apply le_plus_l. }
   apply (le_trans (S n2) (S (n1 + n2)) m I) in H.
   apply H.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt.
  intros.
  apply n_le_m__Sn_le_Sm.
  apply Sn_le_m__n_le_m in H.
  apply H.
Qed.

Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.
  intros.
  generalize dependent m. 
  induction n.
  - intros. apply O_le_n.
  - intros. 
    destruct m.
    + inversion H.
    + rewrite -> plus_1_r in H.
      replace (S m) with (m + 1) in H.
      rewrite -> plus_comm in H.
      replace (m + 1) with (1 + m) in H.
      apply n_le_m__Sn_le_Sm.
      apply IHn.
      apply (plus_ble_compat_l n m 1 H).
      apply plus_comm.
      rewrite <- plus_1_r.
      reflexivity.
Qed.


Theorem leb_correct : forall n m,
  n <= m ->
  leb n m = true.
Proof.
  intros.
  generalize dependent n.
  induction m.
  - intros. inversion H. reflexivity.
  - intros.
    destruct n.
    + reflexivity.
    + simpl.
      apply IHm.
      apply Sn_le_Sm__n_le_m in H.
      apply H.
Qed.

Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  intros.
  apply leb_correct.
  apply leb_complete in H.
  apply leb_complete in H0.
  apply (le_trans n m o H H0).
Qed.

Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof.
  intros.
  split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

Module R.

Inductive R : nat -> nat -> nat -> Prop :=
| c1 : R 0 0 0
| c2 : forall m n o, R m n o -> R (S m) n (S o)
| c3 : forall m n o, R m n o -> R m (S n) (S o)
| c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
| c5 : forall m n o, R m n o -> R n m o.

Theorem r112: R 1 1 2.
Proof.
  intros.
  apply c2. apply c3. apply c1.
Qed.

Definition fR : nat -> nat -> nat := plus.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  intros.
  split.
  - intros.
    unfold fR.
    induction H.
    + reflexivity.
    + simpl.
      rewrite -> IHR.
      reflexivity.
    + rewrite <- plus_n_Sm.
      rewrite -> IHR.
      reflexivity.
    + simpl in IHR.
      apply S_injective in IHR.
      rewrite <- plus_n_Sm in IHR.
      apply S_injective in IHR.
      apply IHR.
    + rewrite -> plus_comm.
      apply IHR.
  - unfold fR.
    intros.
    destruct H.
    + induction m.
      * induction n.
          simpl. apply c1.
          simpl. apply c3. simpl in IHn. apply IHn.
      * simpl. apply c2. apply IHm.
Qed.

End R.

Inductive subseq : list nat -> list nat -> Prop :=
| nil_is_subseq: forall (l2: list nat), subseq [] l2
| combine_subseq: forall (l1 l2: list nat) (x: nat),
    subseq l1 l2  ->
    subseq (x :: l1) (x :: l2)
| subseq_larger: forall (l1 l2: list nat) (x: nat),
    subseq l1 l2 -> subseq l1 (x :: l2).

Theorem subseq_refl : forall (l: list nat),
    subseq l l.
Proof.
  intros.
  induction l as [| h t IH].
  - apply nil_is_subseq.
  - apply combine_subseq. apply IH.
Qed.

Theorem subseq_app : forall (l1 l2 l3: list nat),
  subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros.
  induction H.
  - apply nil_is_subseq.
  - simpl. apply combine_subseq. apply IHsubseq.
  - simpl. apply subseq_larger. apply IHsubseq.
Qed.

Theorem subseq_trans :  forall (l1 l2 l3: list nat),
  subseq l1 l2 /\ subseq l2 l3 -> subseq l1 l3.
Proof.
  intros.
  destruct H.
  generalize dependent H.
  generalize dependent l1.
  induction H0.
  - intros.
    inversion H.
    apply nil_is_subseq.
  - intros.
    inversion H.
    + apply nil_is_subseq.
    + apply combine_subseq.
      apply IHsubseq.
      apply H3.
    + apply subseq_larger.
      apply IHsubseq.
      apply H3.
  - intros.
    apply subseq_larger.
    apply IHsubseq.
    apply H.
Qed.

Inductive R : nat ->  list nat -> Prop :=
| c1 : R 0 []
| c2 : forall n l, R n l -> R (S n) (n :: l)
| c3 : forall n l, R (S n) l -> R n l.

Example r210: R 2 [1;0].
Proof.
  apply c2. apply c2. apply c1.
Qed.

Example r11210: R 1 [1;2;1;0].
Proof.
  apply c3. apply c2. apply c3.
  apply c3. apply c2. apply c2.
  apply c2. apply c1.
Qed.

Inductive reg_exp (T : Type) : Type :=
| EmptySet : reg_exp T
| EmptyStr : reg_exp T
| Char : T -> reg_exp T
| App : reg_exp T -> reg_exp T -> reg_exp T
| Union : reg_exp T -> reg_exp T -> reg_exp T
| Star : reg_exp T -> reg_exp T.

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : forall x,
    exp_match [x] (Char x)
| MApp : forall s1 re1 s2 re2,
    exp_match s1 re1 -> exp_match s2 re2 ->
    exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : forall s re1 re2,
    exp_match s re1 ->
    exp_match s (Union re1 re2)
| MUnionR : forall s re1 re2,
    exp_match s re2 ->
    exp_match s (Union re1 re2)
| MStar0: forall re,
    exp_match [] (Star re)
| MStarApp: forall s1 s2 re,
    exp_match s1 re -> exp_match s2 (Star re) ->
    exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof. apply MChar. Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.


Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | h :: t => App (Char h) (reg_exp_of_list t)
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl.
  apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros.
  destruct H.
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros.
  induction ss.
  - simpl.
    apply MStar0.
  - simpl.
    apply MStarApp.
    + apply H.
      simpl. left. reflexivity.
    + simpl.
      apply IHss.
      intros.
      apply H.
      simpl. right. apply H0.
Qed.

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros.
  split.
  - intros.
    generalize dependent s1.
    induction s2.
    + intros. inversion H. reflexivity.
    + intros. simpl in H.
      inversion H.
      apply IHs2 in H4.
      inversion H3.
      rewrite -> H4.
      reflexivity.
  - intros.
    generalize dependent s1.
    induction s2.
    + intros. simpl. rewrite -> H. apply MEmpty.
    + intros. simpl.
      rewrite -> H.
      apply (MApp [x] _ s2).
      * apply MChar.
      * apply IHs2. reflexivity.
Qed.

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re: reg_exp T) (x: T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch.
  - inversion Hin.
  - apply Hin.
  - simpl. rewrite -> in_app_iff in *.
    destruct Hin.
    + left. apply IHHmatch1. apply H.
    + right. apply IHHmatch2. apply H.
  - simpl. rewrite -> in_app_iff in *.
    left. apply IHHmatch. apply Hin.
  - simpl. rewrite -> in_app_iff in *.
    right. apply IHHmatch. apply Hin.
  - inversion Hin.
  - rewrite -> in_app_iff in *.
    destruct Hin.
    + simpl. apply IHHmatch1. apply H.
    + apply IHHmatch2. apply H.
Qed.

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => re_not_empty re1 && re_not_empty re2
  | Union re1 re2 => re_not_empty re1 || re_not_empty re2
  | Star re => true
  end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros.
  split.
  - intros.
    destruct H.
    induction H.
    + reflexivity.
    + reflexivity.
    + simpl.
      rewrite -> IHexp_match1.
      rewrite -> IHexp_match2.
      reflexivity.
    + simpl.
      apply orb_true_iff.
      left. apply IHexp_match.
    + simpl.
      apply orb_true_iff.
      right. apply IHexp_match.
    + reflexivity.
    + reflexivity.
  - intros.
    induction re.
    + inversion H.
    + exists [].
      apply MEmpty.
    + exists [t].
      apply MChar.
    + simpl in H.
      apply andb_true_iff in H.
      destruct H.
      apply IHre1 in H. apply IHre2 in H0.
      destruct H. destruct H0.
      exists (x ++ x0).
      apply MApp.
      * apply H.
      * apply H0.
    + simpl in H.
      apply orb_true_iff in H.
      destruct H.
      * apply IHre1 in H.
        destruct H.
        exists x.
        apply MUnionL. apply H.
      * apply IHre2 in H.
        destruct H.
        exists x.
        apply MUnionR. apply H.
    + exists [].
      apply MStar0.
Qed.

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1 as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
                   |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
                   |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
    intros. apply H.
  - inversion Heqre'.
    rewrite -> H0 in IH2, Hmatch1.
    intros. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * reflexivity.
      * apply H.
Qed.

Lemma cons_app_equiv: forall (T: Type) (t: list T) (h: T),
  h :: t = [h] ++ t.
Proof.
  simpl. reflexivity.
Qed.

Lemma s_re__s_star_re: forall (T: Type) (s: list T) (re: reg_exp T),
    s =~ re -> s =~ Star re.
Proof.
  intros.
  destruct re.
  + inversion H.
  + inversion H.
    apply MStar0.
  + inversion H.
    rewrite <- (app_nil_r T [t]).
    apply MStarApp.
    - apply MChar.
    - apply MStar0.
  + rewrite <- (app_nil_r T s).
    apply MStarApp.
    - apply H.
    - apply MStar0.
  + rewrite <- (app_nil_r T s).
    apply MStarApp.
    - apply H.
    - apply MStar0.
  + rewrite <- (app_nil_r T s).
    apply MStarApp.
    - apply H.
    - apply MStar0.
Qed.


Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros.
  remember (Star re) as re'.
  induction H.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
    exists [].
    split.
    + reflexivity.
    + intros. inversion H.
  - inversion Heqre'.
    rewrite -> H2 in *.
    induction s1.
    + intros. simpl. apply IHexp_match2. apply Heqre'.
    + intros.
      apply IHexp_match2 in Heqre'.
      destruct Heqre'.
      destruct H1.
      exists ((x::s1)::x0).
      split.
      * rewrite -> H1. simpl. reflexivity.
      * intros. simpl.
        destruct H4.
        { rewrite -> H4. apply H. }
        { apply H3 in H4. apply H4. }
Qed.


Theorem filter_not_empty_In : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros.
  induction l as [| h t IH].
  - apply H. reflexivity.
  - simpl. destruct (beq_nat n h) eqn:beqnh.
    + rewrite beq_nat_true_iff in beqnh.
      left. apply beqnh.
    + simpl in H. rewrite beqnh in H.
      right. apply IH. apply H.
Qed.

Module FirstTry.

Inductive reflect : Prop -> bool -> Prop :=
| ReflectT: forall P:Prop, P -> reflect P true
| ReflectF: forall P:Prop, ~ P -> reflect P false.

End FirstTry.


Inductive reflect (P: Prop) : bool -> Prop :=
| ReflectT: P -> reflect P true
| ReflectF: ~ P -> reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros. destruct b.
  - apply ReflectT.
    rewrite H.
    reflexivity.
  - apply ReflectF.
    unfold not. intros.
    apply H in H0.
    inversion H0.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros.
  destruct b.
  - inversion H.
    split.
    + intros.
      reflexivity.
    + intros.
      apply H0.
  - inversion H.
    unfold not in H0.
    split.
    + intros.
      exfalso.
      apply H0.
      apply H1.
    + intros.
      inversion H1.
Qed.


Lemma beq_natP : forall n m, reflect (n = m) (beq_nat n m).
Proof.
  intros.
  apply iff_reflect.
  rewrite beq_nat_true_iff.
  reflexivity.
Qed.

Theorem filter_not_empty_In' : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l.
  induction l as [| h t IH].
  - intros. apply H. reflexivity.
  - simpl. destruct (beq_natP n h).
    + intros. left. apply H.
    + intros. right. apply IH. apply H0.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if beq_nat n m then 1 else 0) + count n l'
  end.


Theorem beq_natP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  unfold not.
  intros n l.
  induction l as [| h t IH].
  - intros. inversion H0.
  - simpl. destruct (beq_natP n h).
    + intros. inversion H0.
    + simpl. intros.
      apply IH.
      * apply H0.
      * destruct H1.
        { exfalso. apply H. apply H1. }
        { apply H1. }
Qed.

Inductive nostutter {X:Type} : list X -> Prop :=
| nostutter_nil: nostutter []
| nostutter_cons: forall (x:X), nostutter (x :: [])
| nostutter_xy: forall (x y: X) (l: list X),
    x <> y -> nostutter (y :: l) -> nostutter (x :: y :: l).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
  repeat constructor; apply beq_nat_false_iff; auto.
Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof.
  repeat constructor.
Qed.

Example test_nostutter_3: nostutter [5].
Proof.
  repeat constructor.
Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction H1; auto.
Qed.


Inductive in_order_merge {X:Type} : list X -> list X -> list X -> Prop :=
| iom_nil: in_order_merge [] [] []
| iom_left: forall (x: X) (l1 l2 l: list X),
    in_order_merge l1 l2 l ->
    in_order_merge (x :: l1) l2 (x :: l)
| iom_right: forall (x: X) (l1 l2 l: list X),
    in_order_merge l1 l2 l ->
    in_order_merge l1 (x :: l2) (x :: l).


Theorem filter_in_order_merge: forall (X: Type) (test: X -> bool) (l l1 l2: list X),
  in_order_merge l1 l2 l ->
  All (fun a => test a = true) l1 ->
  All (fun b => test b = false) l2 ->
  filter test l = l1.
Proof.
  intros.
  induction H.
  - reflexivity.
  - simpl. 
    inversion H0.
    rewrite H2.
    apply tail_eq.
    apply IHin_order_merge.
    + apply H3.
    + apply H1.
  - simpl.
    inversion H1.
    rewrite H2.
    apply IHin_order_merge.
    + apply H0.
    + apply H3.
Qed.

Inductive pal {X:Type} : list X -> Prop :=
| pal_nil: pal []
| pal_single: forall (x: X), pal [x]
| pal_inductive: forall (x: X) (l: list X),
    pal l ->
    pal (x :: l ++ [x]).

Theorem pal_app_rev: forall (X: Type) (l: list X),
  pal (l ++ rev l).
Proof.
  intros.
  induction l as [|h t IH].
  - simpl. apply pal_nil.
  - simpl.
    rewrite -> app_assoc.
    apply (pal_inductive h (t ++ rev t)).
    apply IH.
Qed.

Theorem pal_rev: forall (X: Type) (l: list X),
  pal l -> l = rev l.
Proof.
  intros.
  induction H.
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite -> rev_app_distr.
    rewrite <- IHpal.
    simpl.
    reflexivity.
Qed.


Inductive disjoint {X:Type} : list X -> list X -> Prop :=
| disjoint_nil: disjoint [] []
| disjoint_left: forall (x: X) (l1 l2: list X),
    ~ In x l2 ->
    disjoint l1 l2 ->
    disjoint (x :: l1) l2
| disjoint_right: forall (x: X) (l1 l2: list X),
    ~ In x l1 ->
    disjoint l1 l2 ->
    disjoint l1 (x :: l2).


Inductive NoDup {X:Type} : list X -> Prop :=
| nodup_nil: NoDup []
| nodup_inductive: forall (x: X) (l: list X),
    ~ In x l ->
    NoDup l ->
    NoDup (x :: l).

Lemma disjoint_nil_r: forall (X: Type) (l: list X),
    disjoint l [].
Proof.
  intros.
  induction l as [| h t IH].
  + apply disjoint_nil.
  + apply disjoint_left.
    * intro. destruct H.
    * apply IH.
Qed.

Lemma disjoint_nil_l: forall (X: Type) (l: list X),
    disjoint [] l.
Proof.
  intros.
  induction l as [| h t IH].
  + apply disjoint_nil.
  + apply disjoint_right.
    * intro. destruct H.
    * apply IH.
Qed.


Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros.
  generalize dependent x.
  induction l as [| h t IH].
  - intros. inversion H.
  - intros.
    simpl in H.
    destruct H.
    + rewrite -> H.
      exists [].
      exists t.
      simpl.
      reflexivity.
    + apply IH in H.
      destruct H.
      destruct H.
      exists (h :: x0).
      exists x1.
      simpl.
      rewrite <- H.
      reflexivity.
Qed.

(* Inductive repeats {X:Type} : list X -> Prop :=
 | repeats_any_larger: forall (x: X) (l: list X),
     repeats l ->
     repeats (x :: l)
 | repeats_inductive: forall (x: X) (l: list X),
     In x l ->
     repeats (x :: l).


 Theorem pigeonhole_principle: forall (X:Type) (l1 l2:list X),
     excluded_middle ->
     (forall x, In x l1 -> In x l2) ->
     length l2 < length l1 ->
     repeats l1.
 Proof.
   intros X l1.
   induction l1 as [|x l1' IHl1'].
   - intros.
     inversion H1.
   - intros.
     
     
     apply (IHl1' (x :: l1') H _ H1).
     + 
       aply 
       + apply repeats_any_larger.
       apply H.
     + intros.
       rewrite -> cons_app_equiv.
       apply in_app_iff.
       right.
       apply H2.
     + *)

