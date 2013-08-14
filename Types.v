Add LoadPath "D:\sfsol".
Require Export Smallstep.

Ltac inv H := inversion H; subst; clear H.

Hint Constructors multi.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tzero : tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tiszero : tm -> tm.

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue ttrue
  | bv_false : bvalue tfalse.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : forall t, nvalue t -> nvalue (tsucc t).

Definition value (t:tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.
Hint Unfold extend.

Reserved Notation "t1 '=>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) => t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) => t2
  | ST_If : forall t1 t1' t2 t3,
      t1 => t1' ->
      (tif t1 t2 t3) => (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 => t1' ->
      (tsucc t1) => (tsucc t1')
  | ST_PredZero :
      (tpred tzero) => tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) => t1
  | ST_Pred : forall t1 t1',
      t1 => t1' ->
      (tpred t1) => (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) => ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) => tfalse
  | ST_Iszero : forall t1 t1',
      t1 => t1' ->
      (tiszero t1) => (tiszero t1')

where "t1 '=>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If"
  | Case_aux c "ST_Succ" | Case_aux c "ST_PredZero"
  | Case_aux c "ST_PredSucc" | Case_aux c "ST_Pred"
  | Case_aux c "ST_IszeroZero" | Case_aux c "ST_IszeroSucc"
  | Case_aux c "ST_Iszero" ].

Hint Constructors step.

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (tsucc ttrue); apply conj;
    intros contra; inv contra; try inv H; try inv H1.
  Qed.

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  intros t Hval contra; inv Hval;
    induction H; inv contra; try inv H0; eauto; try inv H.
  Qed.

Hint Resolve value_is_nf.

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  intros t.
  induction t; intros; inv H; inv H0; eauto.
    inv H4.
    inv H4.
    inv H5.
    inv H5.
    replace t1'0 with t1'; eauto.
    replace t1'0 with t1'; eauto.
    inv H1.
    inv H1. 
    assert (contra:False); try inversion contra.
      eapply value_is_nf; eauto.
    inv H2. 
    inv H2. 
    assert (contra:False); try inversion contra.
      eapply value_is_nf; eauto.
    replace t1'0 with t1'; eauto.
    inv H1.
    inv H1. 
    assert (contra:False); try inversion contra.
      eapply value_is_nf; eauto.
    inv H2. 
    inv H2. 
    assert (contra:False); try inversion contra.
      eapply value_is_nf; eauto.
    replace t1'0 with t1'; eauto.
  Qed.

