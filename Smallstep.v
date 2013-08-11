Add LoadPath "D:\sfsol".
Require Export Imp.

Definition relation (X: Type) := X->X->Prop.

Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm.

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "C" | Case_aux c "P" ].

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P a1 a2 => evalF a1 + evalF a2
  end.

Reserved Notation " t '||' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n || n
  | E_Plus : forall t1 t2 n1 n2,
      t1 || n1 ->
      t2 || n2 ->
      P t1 t2 || (n1 + n2)

  where " t '||' n " := (eval t n).

Tactic Notation "eval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Const" | Case_aux c "E_Plus" ].

Module SimpleArith1.

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 => t1' ->
      P t1 t2 => P t1' t2
  | ST_Plus2 : forall n1 t2 t2',
      t2 => t2' ->
      P (C n1) t2 => P (C n1) t2'

  where " t '=>' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_PlusConstConst"
  | Case_aux c "ST_Plus1" | Case_aux c "ST_Plus2" ].

Example test_step_1 :
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
      =>
      P
        (C (0 + 3))
        (P (C 2) (C 4)).
Proof. apply ST_Plus1. apply ST_PlusConstConst.
  Qed.

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
      =>
      P
        (C 0)
        (P
          (C 2)
          (C (0 + 3))).
Proof. apply ST_Plus2. apply ST_Plus2. apply ST_PlusConstConst.
  Qed.

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Theorem step_deterministic:
  deterministic step.
Proof.
  intros x y z H1 H2. generalize dependent z.
  induction H1; intros. inversion H2. reflexivity. inversion H3. inversion H3.
  inversion H2. rewrite <- H0 in H1. inversion H1.
  replace (t1'0) with t1'. reflexivity. apply IHstep. assumption. rewrite <- H in H1.
  inversion H1. inversion H2; subst. inversion H1. inversion H4. replace (t2'0) with t2'.
  reflexivity. apply IHstep. apply H4.
  Qed.

End SimpleArith1.

Inductive value : tm -> Prop :=
  v_const : forall n, value (C n).

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          P (C n1) (C n2)
      => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 => t1' ->
        P t1 t2 => P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 ->
        t2 => t2' ->
        P v1 t2 => P v1 t2'

  where " t '=>' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_PlusConstConst"
  | Case_aux c "ST_Plus1" | Case_aux c "ST_Plus2" ].

Theorem step_deterministic :
  deterministic step.
Proof.
  intros x y z H. generalize dependent z.
  induction H; intros. inversion H; subst. reflexivity. inversion H3. inversion H4.
  inversion H0; subst. inversion H. replace t1'0 with t1'. reflexivity. apply IHstep. assumption.
  inversion H; subst; inversion H3.
  inversion H1; subst. inversion H0. inversion H5; subst; inversion H.
  replace t2'0 with t2'. reflexivity. apply IHstep. assumption.
  Qed.

Theorem strong_progress : forall t,
  value t \/ (exists t', t => t').
Proof.
  induction t.
  apply or_introl; constructor.
  apply or_intror; inversion IHt1.
  inversion IHt2; inversion H; inversion H0.
  apply ex_intro with (C (n + n0)). constructor.
  apply ex_intro with (P (C n) x). repeat constructor. assumption.
  inversion H. apply ex_intro with (P x t2). constructor. assumption.
  Qed.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  intros. unfold normal_form. unfold not. intros.
  inversion H0. inversion H1; subst; inversion H.
  Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof.
  intros. destruct t. constructor.
  assert(H0:(value (P t1 t2)) \/ ((exists t', (P t1 t2) => t'))); try inversion H0; try assumption.
    apply strong_progress.
  assert(contra:False);try inversion contra. apply H. assumption.
  Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split. apply nf_is_value. apply value_is_nf. Qed.

Module Temp1.

Inductive value : tm -> Prop :=
| v_const : forall n, value (C n)
| v_funny : forall t1 n2,
              value (P t1 (C n2)).

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 => t1' ->
      P t1 t2 => P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 => t2' ->
      P v1 t2 => P v1 t2'

  where " t '=>' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  exists (P (C 0) (C 0)). split. constructor.
  intros H. apply H. exists (C 0). constructor.
  Qed.

End Temp1.

Module Temp2.

Inductive value : tm -> Prop :=
| v_const : forall n, value (C n).

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,
      C n => P (C n) (C 0)
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 => t1' ->
      P t1 t2 => P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 => t2' ->
      P v1 t2 => P v1 t2'

  where " t '=>' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  exists (C 0). split. constructor.
  intros H; apply H. exists (P (C 0) (C 0)).
  constructor.
  Qed.

End Temp2.

Module Temp3.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 => t1' ->
      P t1 t2 => P t1' t2

  where " t '=>' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
  exists (P (C 0) (P (C 0) (C 0))). split;
  intros H. inversion H. inversion H.
  inversion H0; subst. inversion H4.
  Qed.

End Temp3.

Module Temp4.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_true : value ttrue
  | v_false : value tfalse.

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      tif ttrue t1 t2 => t1
  | ST_IfFalse : forall t1 t2,
      tif tfalse t1 t2 => t2
  | ST_If : forall t1 t1' t2 t3,
      t1 => t1' ->
      tif t1 t2 t3 => tif t1' t2 t3

  where " t '=>' t' " := (step t t').

Definition bool_step_prop1 :=
  tfalse => tfalse.

Theorem neg_bool_step_prop1 :
  ~ bool_step_prop1.
Proof.
  intros H. inversion H. Qed.

Definition bool_step_prop2 :=
     tif
       ttrue
       (tif ttrue ttrue ttrue)
       (tif tfalse tfalse tfalse)
  =>
     ttrue.

Theorem neg_bool_step_prop2 :
  ~ bool_step_prop2.
Proof.
  intros H. inversion H. Qed.

Definition bool_step_prop3 :=
     tif
       (tif ttrue ttrue ttrue)
       (tif ttrue ttrue ttrue)
       tfalse
   =>
     tif
       ttrue
       (tif ttrue ttrue ttrue)
       tfalse.

Theorem neg_bool_step_prop3 :
  bool_step_prop3.
Proof.
  constructor. constructor. Qed.

Theorem strong_progress : forall t,
  value t \/ (exists t', t => t').
Proof.
  induction t.
    apply or_introl; constructor.
    apply or_introl; constructor.
    apply or_intror.
      inversion IHt1; inversion H; subst.
      exists t2; constructor.
      exists t3; constructor.
      exists (tif x t2 t3); constructor. assumption.
  Qed.

Theorem step_deterministic :
  deterministic step.
Proof.
  intros x y z H. generalize dependent z.
  induction H; intros.
  inversion H; subst; try reflexivity; try inversion H4.
  inversion H; subst; try reflexivity; try inversion H4.
  inversion H0; subst. inversion H. inversion H.
  replace t1'0 with t1'. reflexivity.
  apply IHstep. assumption.
  Qed.

Module Temp5.

