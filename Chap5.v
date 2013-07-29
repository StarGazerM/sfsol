Add LoadPath "F:\sfsol".
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

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E. inversion E as [| n' E']. inversion E' as [| n'' E''].
  apply E''. Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros E. inversion E. inversion H0. inversion H2. Qed.

Theorem ev_minus2': forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E. inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'. Qed.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m E1 E2.
  induction E2 as [| n' E2'].
  simpl in E1. apply E1.
  simpl in E1.
  inversion E1.
  apply IHE2'.
  apply H0.
  Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  assert(forall n m p,n + m + n + p = double n + m + p).
    intros.
    induction n.
    simpl. rewrite -> plus_O_r. reflexivity.
    simpl. rewrite <- plus_n_Sm. rewrite <- IHn.
    simpl. reflexivity.
  assert (forall n m, ev(double n + m) -> ev m).
    intros.
    induction n.
    simpl in H0. apply H0.
    simpl in H0. inversion H0 as [| m' H1]. apply IHn. apply H2.
  intros n m p E1 E2.
  assert (ev (n + m + n + p)).
    replace (n + m + n + p) with (n + m + (n + p)).
    apply ev_sum. apply E1. apply E2.
    apply plus_assoc.
  rewrite H in H1. rewrite <- plus_assoc in H1. apply H0 in H1.
  apply H1.
  Qed.

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed.

Definition strange_prop1 : Prop :=
  (2 + 2 = 5) -> (99 + 26 = 42).

Definition strange_prop2 :=
  forall n, (ble_nat n 17 = true) -> (ble_nat n 99 = true).

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

Definition teen : nat->Prop := between 13 19.

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.


Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

Check nat_ind.

Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  Case "O". reflexivity.
  Case "S". simpl. intros n IHn. rewrite -> IHn.
    reflexivity. Qed.

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  reflexivity.
  intros. simpl. rewrite -> H. reflexivity.
  Qed.

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
Check rgb_ind.

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Check natlist_ind.

Inductive ExSet : Type :=
  | con1 : bool -> ExSet
  | con2 : nat -> ExSet -> ExSet.

Check ExSet_ind.

Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.
Check tree_ind.

Inductive mytype (X:Type) : Type :=
  | constr1 : X -> mytype X
  | constr2 : nat -> mytype X
  | constr3 : mytype X -> nat -> mytype X.

Check mytype_ind.

Inductive foo (X Y:Type) : Type :=
  | bar : X -> foo X Y
  | baz : Y -> foo X Y
  | quux : (nat -> foo X Y) -> foo X Y.

Check foo_ind.

Inductive foo' (X:Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.

Check foo'_ind.

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

Definition P_m0r' : nat->Prop :=
  fun n => n * 0 = 0.

Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  Case "n = O". reflexivity.
  Case "n = S n'".
    (* Note the proof state at this point! *)
    unfold P_m0r. simpl. intros n' IHn'.
    apply IHn'. Qed.

Module P.

Inductive p : (tree nat) -> nat -> Prop :=
   | c1 : forall n, p (leaf _ n) 1
   | c2 : forall t1 t2 n1 n2,
            p t1 n1 -> p t2 n2 -> p (node _ t1 t2) (n1 + n2)
   | c3 : forall t n, p t n -> p t (S n).

(* p t n is provale for all n>=size(t) where 
size(t) is number of elements in t *)

End P.

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n'].
  reflexivity.
  simpl. rewrite -> IHn'. reflexivity.
  Qed.

Theorem plus_comm' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  Case "n = O". intros m. rewrite -> plus_O_r. reflexivity.
  Case "n = S n'". intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

Theorem plus_comm'' : forall n m : nat,
  n + m = m + n.
Proof.
  induction m as [| m'].
  Case "m = O". simpl. rewrite -> plus_0_r. reflexivity.
  Case "m = S m'". simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

Definition p_plus_assoc (n : nat) : Prop :=
  forall (m p : nat), n + ( m + p ) = ( n + m ) + p.

Theorem plus_assoc'' : forall (n : nat),
  p_plus_assoc n.
Proof.
  apply nat_ind.
  unfold p_plus_assoc. reflexivity.
  unfold p_plus_assoc. intros. simpl. rewrite -> H.
  reflexivity.
  Qed.

Definition p_plus_comm (n : nat) : Prop :=
  forall (m : nat), n + m = m + n.

Theorem plus_comm''' : forall (n : nat),
  p_plus_comm n.
Proof.
  apply nat_ind.
  unfold p_plus_comm. intros. simpl. rewrite -> plus_0_r. reflexivity.
  unfold p_plus_comm. intros. rewrite <- plus_n_Sm. rewrite <- H.
  reflexivity. Qed.

Fixpoint true_upto_n__true_everywhere (n : nat) (p : nat -> Prop) : Prop :=
  match n with
  | O => (forall (m : nat), p m)
  | S n => (p (S n)) -> true_upto_n__true_everywhere n p
  end.

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity. Qed.

Inductive pal {X:Type} : (list X) -> Prop :=
  | pal1 : pal nil
  | c2 : forall x:X, pal [x]
  | c3 : forall (x:X) (l:list X), (pal l) -> pal (x :: (snoc l x)).

Inductive pal2 {X:Type} : (list X) -> Prop :=
  | c : forall ( l : list X ), ( l = rev l ) -> pal2 l.

Theorem pal_evens : forall ( X : Type ) ( l : list X ),
  pal ( l ++ rev l).
Proof.
  intros.
  induction l.
  apply pal1.
  simpl. rewrite <- snoc_with_append.
  apply c3.
  apply IHl.
  Qed.
  
Theorem pal_conv : forall ( X : Type ) ( l : list X ),
  pal l -> l = rev l.
Proof.
  intros.
  induction H.
  reflexivity.
  reflexivity.
  simpl.
  rewrite -> rev_snoc.
  simpl.
  rewrite <- IHpal.
  reflexivity.
  Qed.

Definition pal_len (n:nat) := forall (X:Type) (l : list X),
  n = length(l) -> l = rev l -> pal l.

Theorem pal_0len : pal_len 0.
Proof.
  unfold pal_len.
  intros.
  destruct l.
  apply pal1.
  inversion H.
  Qed.

Theorem pal_1len : pal_len 1.
Proof.
  unfold pal_len.
  intros.
  destruct l.
  apply pal1.
  destruct l.
  apply c2.
  inversion H.
  Qed.

Theorem snoc_inv : forall (X :Type) (l1 l2 : list X) (x:X),
  snoc l1 x = snoc l2 x -> l1 = l2.
Proof.
  intros.
  generalize dependent l2.
  induction l1.
  intros.
  destruct l2.
  reflexivity.
  inversion H. destruct l2. inversion H2. inversion H2.
  destruct l2.
  intros. simpl in H. inversion H. destruct l1. inversion H2. inversion H2.
  intros.
  simpl in H.
  inversion H.
  assert (l1 = l2).
  apply IHl1.
  apply H2.
  rewrite -> H0.
  reflexivity.
  Qed.

Theorem length_snoc : forall (X :Type) (l : list X) (x:X),
  length (snoc l x) = S (length l).
Proof.
  intros.
  induction l.
  reflexivity.
  simpl. rewrite -> IHl. reflexivity.
  Qed.

Definition palimp (n:nat) := pal_len n -> pal_len (n+1) -> pal_len (n+2).

Theorem palimptauto : forall (n:nat), palimp n.
Proof.
  intros.
  unfold palimp.
  unfold pal_len.
  intros.
  destruct l. apply pal1.
  destruct l. apply c2.
  remember (x0 :: l) as l'.
  assert (l' = rev (rev l')).
    rewrite rev_involutive. reflexivity.
  inversion H2.
  assert (x :: l' = x :: rev (rev l')).
    rewrite <- H3. reflexivity.
  rewrite H4 in H5.
  destruct (rev l').
  rewrite -> H4.
  apply c2.
  simpl in H5.
  inversion H5.
  rewrite <- H7.
  rewrite -> H4.
  simpl.
  rewrite <- H7.
  apply c3.
  rewrite -> H4 in H1.
  simpl in H1.
  assert (n + 2 = 2 + n).
    apply plus_comm.
  rewrite H6 in H1.
  inversion H1.
  rewrite -> length_snoc in H10.
  inversion H10.
  apply snoc_inv in H8.
  apply H.
  apply H11.
  rewrite -> rev_involutive.
  apply H8.
  Qed.

Theorem imp2conj : forall (p:nat->Prop) , (forall (n:nat) , (p n)->(p (n+1))->(p (n+2)))->
  (forall (n:nat), ((p n)/\(p (n+1)))->((p (n+1))/\(p (n+2)))).
Proof.
  intros.
  inversion H0.
  split.
  apply H2.
  apply H.
  apply H1.
  apply H2.
  Qed.

Definition tupn (p:nat->Prop) (n:nat) := (p n)/\(p (n+1)).

Theorem indtup : forall (p:nat->Prop) , (forall (n:nat) , (p n)->(p (n+1))->(p (n+2)))->
  (p 0)->(true_upto_n__true_everywhere 1 p).
Proof.
  unfold true_upto_n__true_everywhere.
  intros.
  assert(forall (n:nat),((p n)/\(p (n+1)))->((p (n+1))/\(p (n+2)))).
    apply imp2conj.
    apply H.
  assert(forall (n:nat), (tupn p n)).
  unfold tupn.
  induction n.
  split.
    apply H0.
    apply H1.
  replace (S n) with (n + 1).
  replace (n + 1 + 1) with (n + 2).
  apply H2.
  apply IHn.
  rewrite -> plus_comm.
  simpl. rewrite -> plus_comm. simpl. rewrite -> plus_comm. simpl. reflexivity.
  rewrite -> plus_comm.
  simpl. reflexivity.
  unfold tupn in H3.
  assert((p m)/\(p (m+1))).
    apply H3.
  decompose [and] H4.
  apply H5.
  Qed.

Theorem pal_def : forall (n:nat) ( X : Type ) ( l : list X ),
  n = (length l) -> l = rev l -> pal l.
Proof.
  assert(forall (n:nat), pal_len n).
    assert((pal_len 0)->true_upto_n__true_everywhere 1 pal_len).
      unfold true_upto_n__true_everywhere.
      intros.
      apply indtup.
      apply palimptauto.
      apply pal_0len.
      apply pal_1len.
    unfold true_upto_n__true_everywhere in H.
    apply H.
    apply pal_0len.
    apply pal_1len.
  unfold pal_len in H.
  apply H.
  Qed.

Inductive subseq : (list nat)->(list nat)->Prop :=
  | sub1 : forall (l : list nat), (subseq nil l)
  | sub3 : forall (x : nat) (l1 l2 : list nat), (subseq l1 l2) -> (subseq l1 (x::l2))
  | sub2 : forall (x : nat) (l1 l2: list nat), (subseq l1 l2)->(subseq (x::l1) (x::l2)).

Theorem nil_app2 {X:Type} : forall (l:list X),
  l ++ [] = l.
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite -> IHl.
  reflexivity.
  Qed.  

Theorem subseqrefl : forall ( l : list nat),
  (subseq l l).
Proof.
  intros.
  induction l.
  apply sub1.
  apply sub2.
  apply IHl.
  Qed.

Theorem app_con {X:Type}: forall (x:X) (l1 l2: list X),
  l1 ++ x :: l2 = (l1 ++ [x]) ++ l2.
Proof.
  induction l1.
  simpl.
  reflexivity.
  simpl.
  intros.
  assert(l1 ++ x :: l2 = (l1 ++ [x]) ++ l2).
  rewrite <- IHl1.
  reflexivity.
  rewrite -> H.
  reflexivity.
  Qed.

Theorem subin : forall ( l1 l2 l3 : list nat),
  (subseq l1 l2) -> (subseq l1 (l2++l3)).
Proof.
  intros.
  generalize dependent l1.
  induction l2.
  intros.
  inversion H.
  apply sub1.
  intros.
  induction l1.
  apply sub1.
  inversion H.
  assert(subseq l0 (l2 ++ l3)).
  apply IHl2.
  rewrite -> H1.
  apply H2.
  simpl.
  apply sub3.
  rewrite <- H1.
  apply H4.
  simpl.
  apply sub2.
  apply IHl2.
  apply H1.
  Qed.

Theorem app_left {X:Type}: forall (l1 l2 : list X),
  (l1 ++ l2 = []) -> (l1 = []).
Proof.
  intros.
  destruct l1.
  reflexivity.
  simpl in H.
  inversion H.
  Qed.

Theorem sub_trans : forall ( l1 l2 l3 : list nat),
  (subseq l1 l2) -> (subseq l2 l3) -> (subseq l1 l3).
Proof.
  intros.
  generalize dependent l1.
  generalize dependent l2.
  induction l3.
  intros.
  inversion H0.
  rewrite <- H1 in H.
  inversion H.
  apply sub1.
  intros.
  inversion H0.
  rewrite <- H1 in H.
  inversion H.
  apply sub1.
  apply sub3.
  apply IHl3 with (l2 := l2).
  assumption.
  assumption.
  rewrite <- H2 in H.
  rewrite -> H1 in H.
  inversion H.
  apply sub1.
  apply sub3.
  apply IHl3 with (l2 := l0).
  apply H3.
  apply H7.
  apply sub2.
  apply IHl3 with (l2 := l0).
  apply H3.
  apply H7.
  Qed.