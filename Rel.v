Add LoadPath "D:\sfsol".
Require Export SfLib.

Definition relation (X: Type) := X->X->Prop.

Print le.

Check le : nat->nat->Prop.

Check le : relation nat.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense.
   Case "Proof of assertion".
   apply Hc with (x := 0).
     apply le_n.
     apply le_S. apply le_n.
  inversion Nonsense. Qed.

Inductive total_relation : nat -> nat -> Prop :=
  | total : forall n1 n2, total_relation n1 n2.

Inductive empty_relation : nat -> nat -> Prop :=
  | empty : forall n1 n2, 0 = 1 -> empty_relation n1 n2.

Theorem total_not_a_partial_function :
  ~ (partial_function total_relation).
Proof.
  unfold not. unfold partial_function. intros.
  assert (0 = 1) as Nonsense.
  apply H with 0; constructor. inversion Nonsense.
  Qed.

Theorem empty_not_a_partial_function :
  (partial_function empty_relation).
Proof.
  unfold partial_function. intros.
  inversion H. inversion H1. Qed.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n. Qed.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  Case "le_n". apply Hnm.
  Case "le_S". apply le_S. apply IHHmo. Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

Theorem lt_trans' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
    apply le_S. assumption.
    apply le_S. assumption.
  Qed.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
    apply le_S. apply le_n.
    apply H. Qed.

Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros. generalize dependent n. induction m.
  intros. inversion H; try constructor. inversion H1.
  intros. inversion H; try constructor. apply IHm.
  assumption.
  Qed.

Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  induction n.
  intros H. inversion H.
  intros H. apply IHn. apply le_S_n.
  assumption.
  Qed.

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  unfold symmetric. intros H.
  assert(1<=0). apply H. constructor.
  constructor. inversion H0.
  Qed.

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  intros a b H1 H2.
  generalize dependent b. induction a; intros.
  inversion H2. reflexivity.
  destruct b. inversion H1.
  apply le_S_n in H1. apply le_S_n in H2.
  replace a with b. reflexivity.
  symmetry. apply IHa; assumption.
  Qed.

Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  intros.
  unfold lt in H.
  apply le_S_n. eapply le_trans.
  apply H. apply H0.
  Qed.

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split.
    Case "refl". apply le_reflexive.
    split.
      Case "antisym". apply le_antisymmetric.
      Case "transitive.". apply le_trans. Qed.

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step : forall x y, R x y -> clos_refl_trans R x y
    | rt_refl : forall x, clos_refl_trans R x x
    | rt_trans : forall x y z,
          clos_refl_trans R x y ->
          clos_refl_trans R y z ->
          clos_refl_trans R x z.

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
    Case "->".
      intro H. induction H.
      SCase "le_n". apply rt_refl.
      SCase "le_S".
        apply rt_trans with m. apply IHle. apply rt_step. apply nn.
    Case "<-".
      intro H. induction H.
      SCase "rt_step". inversion H. apply le_S. apply le_n.
      SCase "rt_refl". apply le_n.
      SCase "rt_trans".
        apply le_trans with y.
        apply IHclos_refl_trans1.
        apply IHclos_refl_trans2. Qed.

Inductive refl_step_closure {X:Type} (R: relation X) : relation X :=
  | rsc_refl : forall (x : X), refl_step_closure R x x
  | rsc_step : forall (x y z : X),
                    R x y ->
                    refl_step_closure R y z ->
                    refl_step_closure R x z.

Tactic Notation "rt_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rt_step" | Case_aux c "rt_refl"
  | Case_aux c "rt_trans" ].

Tactic Notation "rsc_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rsc_refl" | Case_aux c "rsc_step" ].

Theorem rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> refl_step_closure R x y.
Proof.
  intros X R x y H.
  apply rsc_step with y. apply H. apply rsc_refl. Qed.

Theorem rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      refl_step_closure R x y ->
      refl_step_closure R y z ->
      refl_step_closure R x z.
Proof.
  intros.
  induction H. assumption.
  eapply rsc_step. apply H.
  apply IHrefl_step_closure. assumption.
  Qed.

Theorem rtc_rsc_coincide :
         forall (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <-> refl_step_closure R x y.
Proof.
  split; intros; induction H.
    eapply rsc_step. apply H. apply rsc_refl.
    apply rsc_refl. apply rsc_trans with y; auto.
  apply rt_refl.
    apply rt_trans with y.
      apply rt_step; assumption.
      assumption.
  Qed.