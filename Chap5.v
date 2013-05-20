Add LoadPath "D:\sfsol".
Require Export Chap4.

Inductive beautiful : nat -> Prop :=
  b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

Theorem three_is_beautiful: beautiful 3.
Proof.
  apply b_3.
  Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   apply b_sum with (n:=3) (m:=5).
   apply b_3.
   apply b_5.
Qed.

Theorem eight_is_beautiful': beautiful 8.
Proof.
   apply (b_sum 3 5 b_3 b_5).
Qed.

Theorem eight_is_beautiful'': beautiful 8.
Proof.
   apply b_sum with (n:=3) (m:=5).
   Show Proof.
   apply b_3.
   Show Proof.
   apply b_5.
   Show Proof.
Qed.

Definition eight_is_beautiful''' : beautiful 8 :=
  b_sum 3 5 b_3 b_5.

Print eight_is_beautiful.

Print eight_is_beautiful'.

Print eight_is_beautiful''.

Print eight_is_beautiful'''.

Theorem six_is_beautiful :
  beautiful 6.
Proof.
  apply b_sum with (n:=3) (m:=3).
  apply b_3.
  apply b_3.
  Qed.

Definition six_is_beautiful' : beautiful 6 :=
  b_sum 3 3 b_3 b_3.

Theorem b_plus3: forall n, beautiful n -> beautiful (3+n).
Proof.
   intros n H.
   apply b_sum.
   apply b_3.
   apply H.
Qed.

Definition b_plus3' : forall n, beautiful n -> beautiful (3+n) :=
  fun n => fun H : beautiful n =>
    b_sum 3 n b_3 H.
Check (fun n => fun H : beautiful n => b_sum 3 n b_3 H).

Definition b_plus3'' (n : nat) (H : beautiful n) : beautiful (3+n) :=
  b_sum 3 n b_3 H.
Check b_plus3''.

Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
  intros n H.
  simpl.
  apply b_sum.
  apply H.
  apply b_sum.
  apply H.
  apply b_0.
  Qed.

Definition b_times2': forall n, beautiful n -> beautiful (2*n) :=
  fun n => fun H : beautiful n => b_sum n (n + 0) H (b_sum n 0 H b_0).
Check b_times2'.

Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
  intros n m H.
  induction m.
  simpl. apply b_0.
  simpl.
  apply b_sum.
  apply H.
  apply IHm.
  Qed.

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

Theorem gorgeous__beautiful : forall n,
  gorgeous n -> beautiful n.
Proof.
   intros.
   induction H as [|n'|n'].
   Case "g_0".
       apply b_0.
   Case "g_plus3".
       apply b_sum. apply b_3.
       apply IHgorgeous.
   Case "g_plus5".
       apply b_sum. apply b_5. apply IHgorgeous.
Qed.

Theorem gorgeous_plus13: forall n,
  gorgeous n -> gorgeous (13+n).
Proof.
  intros.
  apply g_plus3.
  apply g_plus5.
  apply g_plus5.
  apply H.
  Qed.

Definition gorgeous_plus13_po: forall n, gorgeous n -> gorgeous (13+n):=
  fun n => fun H : gorgeous n => g_plus3 (10 + n) (g_plus5 (5 + n) (g_plus5 n H)).

Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros.
  induction H.
  apply H0.
  apply g_plus3 with (n:=n+m).
  apply IHgorgeous.
  apply g_plus5 with (n:=n+m).
  apply IHgorgeous.
  Qed.

Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros.
  induction H.
  apply g_0.
  apply g_plus3.
  apply g_0.
  apply g_plus5.
  apply g_0.
  apply gorgeous_sum.
  apply IHbeautiful1.
  apply IHbeautiful2.
  Qed.

Lemma helper_g_times2 : forall x y z, x + (z + y)= z + x + y.
Proof.
  intros.
  rewrite -> plus_swap.
  rewrite -> plus_assoc.
  reflexivity.
  Qed.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
   intros n H. simpl.
   induction H.
   simpl.
   apply g_0.
   rewrite -> plus_O_r.
   rewrite -> plus_O_r in IHgorgeous.
   rewrite <- plus_assoc.
   assert (n + (3 + n) = 3 + n + n).
     apply helper_g_times2.
   rewrite -> H0.
   apply g_plus3.
   rewrite <- plus_assoc.
   apply g_plus3.
   apply IHgorgeous.
   rewrite -> plus_O_r.
   rewrite -> plus_O_r in IHgorgeous.
   rewrite <- plus_assoc.
   assert (n + (5 + n) = 5 + n + n).
     apply helper_g_times2.
   rewrite -> H0.
   apply g_plus5.
   rewrite <- plus_assoc.
   apply g_plus5.
   apply IHgorgeous.
   Qed.

Definition even (n:nat) : Prop :=
  evenb n = true.

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

Theorem double_even : forall n,
  ev (double n).
Proof.
  intros.
  induction n.
  apply ev_0.
  simpl.
  apply ev_SS.
  apply IHn.
  Qed.

Check double_even.

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'. Qed.

Theorem ev__even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0".
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".
    unfold even. apply IHE'.
Qed.

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof.
  intros.
  generalize dependent H0.
  induction H.
  intros H.
  apply H.
  intros H0.
  simpl.
  apply ev_SS.
  apply IHev.
  apply H0.
  Qed.

Theorem SSev_ev_secondtry : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. remember (S (S n)) as n2.
  destruct E as [| n' E'].
  Case "n = 0". inversion Heqn2.
  Case "n = S n'". inversion Heqn2. rewrite <- H0. apply E'.
Qed.

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E']. apply E'. Qed.

