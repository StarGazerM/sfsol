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

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          P (C n1) (C n2)
      ==> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 ==> t1' ->
        P t1 t2 ==> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 ->
        t2 ==> t2' ->
        P v1 t2 ==> P v1 t2'

  where " t '==>' t' " := (step t t').

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
  value t \/ (exists t', t ==> t').
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
  assert(H0:(value (P t1 t2)) \/ ((exists t', (P t1 t2) ==> t'))); try inversion H0; try assumption.
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

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      tif ttrue t1 t2 => t1
  | ST_IfFalse : forall t1 t2,
      tif tfalse t1 t2 => t2
  | ST_If : forall t1 t1' t2 t3,
      t1 => t1' ->
      tif t1 t2 t3 => tif t1' t2 t3
  | ST_Short : forall t1 t2,
      value t2 ->
      tif t1 t2 t2 => t2

  where " t '=>' t' " := (step t t').

Definition bool_step_prop4 :=
         tif
            (tif ttrue ttrue ttrue)
            tfalse
            tfalse
     =>
         tfalse.

Example bool_step_prop4_holds :
  bool_step_prop4.
Proof.
  constructor. constructor.
  Qed.

Lemma negb_step_deterministic:
  ~ deterministic step.
Proof.
  intros H. unfold deterministic in H.
  assert(tif ttrue tfalse ttrue => tfalse).
    constructor.
  assert(tfalse = tif tfalse tfalse tfalse).
  apply H with (tif (tif ttrue tfalse ttrue) tfalse tfalse);
    constructor; constructor.
  inversion H1. Qed.

Theorem strong_progress : forall t,
  value t \/ (exists t', t => t').
Proof.
  induction t.
    apply or_introl; constructor.
    apply or_introl; constructor.
    apply or_intror; inversion IHt1;
      inversion H; subst.
        exists t2; constructor.
        exists t3; constructor.
      exists (tif x t2 t3); constructor.
      assumption.
  Qed.

Module Temp6.

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      tif ttrue t1 t2 => t1
  | ST_IfFalse : forall t1 t2,
      tif tfalse t1 t2 => t2
  | ST_Short : forall t1 t2,
      value t2 ->
      tif t1 t2 t2 => t2

  where " t '=>' t' " := (step t t').

Theorem strong_progress : exists t,
  ~ value t /\ ~(exists t', t => t').
Proof.
  exists (tif (tif tfalse tfalse ttrue) tfalse ttrue).
  split; intros H; inversion H. inversion H0; subst.
  inversion H4.
  Qed.

End Temp6.

End Temp5.
End Temp4.

Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Tactic Notation "multi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl" | Case_aux c "multi_step" ].

Definition multistep := multi step.
Notation " t '=>*' t' " := (multistep t t') (at level 40).

Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl. Qed.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
  intros.
  generalize dependent z.
  induction H. intros; assumption.
  intros. econstructor. apply H.
  apply IHmulti. assumption.
  Qed.

Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   =>*
      C ((0 + 3) + (2 + 4)).
Proof.
  econstructor. constructor. constructor.
  econstructor. apply ST_Plus2; constructor.
  econstructor. constructor. constructor.
  Qed.

Lemma test_multistep_2:
  C 3 =>* C 3.
Proof.
  constructor. Qed.

Lemma test_multistep_3:
      P (C 0) (C 3)
   =>*
      P (C 0) (C 3).
Proof.
  constructor. Qed.

Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  =>*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  econstructor. apply ST_Plus2. constructor.
  apply ST_Plus2. constructor. constructor.
  econstructor. apply ST_Plus2. constructor.
  constructor. econstructor.
  Qed.

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t =>* t' /\ step_normal_form t').

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  unfold deterministic. unfold normal_form_of. intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1. inversion P2 as [P21 P22]; clear P2.
  generalize dependent y2.
  induction P11.
    destruct x; intros. inversion P21.
      reflexivity.
      inversion H.
    assert(value (P x1 x2)).
      apply nf_is_value; assumption.
    inversion H.
    intros. apply IHP11; try assumption.
    inversion P21; subst. 
      destruct y2.
        inversion H.
        assert (value (P y2_1 y2_2)).
          apply nf_is_value; assumption.
        inversion H0.
        assert(y = y0).
          eapply step_deterministic.
          apply H. apply H0.
        subst. apply H1.
  Qed.

Definition normalizing {X:Type} (R:relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.

Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 =>* t1' ->
     P t1 t2 =>* P t1' t2.
Proof.
  intros.
  induction H. constructor.
  econstructor. apply ST_Plus1. apply H.
  assumption.
  Qed.

Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 =>* t2' ->
     P t1 t2 =>* P t1 t2'.
Proof.
  intros. induction H0.
  constructor.
  econstructor. apply ST_Plus2. assumption.
  apply H0. assumption.
  Qed.

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  intros. induction t.
    exists (C n).
    split; try apply value_is_nf; try constructor.
    inversion IHt1 as [t1' [H11 H12]].
    inversion IHt2 as [t2' [H21 H22]].
    assert(v1:value t1').
      apply nf_is_value. assumption.
    inversion v1.
    assert(v2:value t2').
      apply nf_is_value. assumption.
    inversion v2.
    exists(C (n + n0)). split.
    assert(Hprime:P t1 t2 =>* P t1' t2').
      eapply multi_trans.
        apply multistep_congr_1. apply H11.
        apply multistep_congr_2; assumption.
    eapply multi_trans. apply Hprime.
    subst. econstructor; constructor.
    apply value_is_nf. constructor.
  Qed.

Theorem eval__multistep : forall t n,
  t || n -> t =>* C n.
Proof.
  intros.
  induction H. constructor.
  eapply multi_trans.
  assert(P t1 t2 =>* P (C n1) t2).
    apply multistep_congr_1; assumption.
    apply H1.
  eapply multi_trans.
    apply multistep_congr_2. constructor.
    apply IHeval2.
  econstructor; constructor.
  Qed.

Lemma step__eval : forall t t' n,
     t ==> t' ->
     t' || n ->
     t || n.
Proof.
  intros t t' n Hs. generalize dependent n.
  induction Hs; intros; inversion H; subst. constructor; constructor.
  constructor. apply IHHs. assumption.
  assumption. inversion H0; subst.
  constructor. assumption. apply IHHs.
  assumption.
  Qed.

Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.
Proof.
  intros. unfold normal_form_of in H.
  inversion H.
  induction H0.
  assert(value x).
    apply nf_is_value. assumption.
  inversion H0.
  exists n. split; try reflexivity; try constructor.
  assert(exists n : nat, z = C n /\ y || n).
    apply IHmulti. split; assumption.
    assumption.
  inversion H3 as [n [H4 H5]]; clear H3.
  exists n. split. assumption.
  eapply step__eval. apply H0.
  assumption.
  Qed.

Theorem evalF_eval : forall t n,
  evalF t = n <-> t || n.
Proof.
  split; intros. generalize dependent n.
  induction t; intros. simpl in H. subst. constructor.
  simpl in H. rewrite <- H. constructor.
    apply IHt1; reflexivity.
    apply IHt2; reflexivity.
  induction H.
    reflexivity.
    simpl. subst. reflexivity.
  Qed.

Module Combined.

Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "C" | Case_aux c "P"
  | Case_aux c "ttrue" | Case_aux c "tfalse" | Case_aux c "tif" ].

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_true : value ttrue
  | v_false : value tfalse.

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
  | ST_IfTrue : forall t1 t2,
      tif ttrue t1 t2 => t1
  | ST_IfFalse : forall t1 t2,
      tif tfalse t1 t2 => t2
  | ST_If : forall t1 t1' t2 t3,
      t1 => t1' ->
      tif t1 t2 t3 => tif t1' t2 t3

  where " t '=>' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_PlusConstConst"
  | Case_aux c "ST_Plus1" | Case_aux c "ST_Plus2"
  | Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" ].

Theorem step_deterministic :
  deterministic step.
Proof.
  intros x y z H. generalize dependent z.
  induction H; intros.
    inversion H; subst. reflexivity.
    inversion H3.
    inversion H4.
    inversion H0; subst. inversion H.
    replace t1'0 with t1'. reflexivity.
    apply IHstep. assumption.
    inversion H3; subst; inversion H.
    inversion H1; subst. inversion H0.
    inversion H; subst; inversion H5.
    replace t2'0 with t2'. reflexivity.
    apply IHstep. assumption.
    inversion H; subst. reflexivity. inversion H4.
    inversion H; subst. reflexivity. inversion H4.
    inversion H0; subst. inversion H. inversion H.
    replace t1'0 with t1'. reflexivity. apply IHstep.
    assumption.
  Qed.

Theorem neg_strong_progress : exists t,
  ~ value t /\ ~ (exists t', t => t').
Proof.
  exists (P (C 0) tfalse).
  split; intros H; inversion H.
  inversion H0; subst.
  inversion H4.
  inversion H5.
  Qed.

End Combined.

Inductive aval : aexp -> Prop :=
  av_num : forall n, aval (ANum n).

Reserved Notation " t '/' st '==>a' t' " (at level 40, st at level 39).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st i, 
      AId i / st ==>a ANum (st i)
  | AS_Plus : forall st n1 n2,
      APlus (ANum n1) (ANum n2) / st ==>a ANum (n1 + n2)
  | AS_Plus1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (APlus a1 a2) / st ==>a (APlus a1' a2)
  | AS_Plus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ==>a a2' ->
      (APlus v1 a2) / st ==>a (APlus v1 a2')
  | AS_Minus : forall st n1 n2,
      (AMinus (ANum n1) (ANum n2)) / st ==>a (ANum (minus n1 n2))
  | AS_Minus1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (AMinus a1 a2) / st ==>a (AMinus a1' a2)
  | AS_Minus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ==>a a2' ->
      (AMinus v1 a2) / st ==>a (AMinus v1 a2')
  | AS_Mult : forall st n1 n2,
      (AMult (ANum n1) (ANum n2)) / st ==>a (ANum (mult n1 n2))
  | AS_Mult1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (AMult (a1) (a2)) / st ==>a (AMult (a1') (a2))
  | AS_Mult2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ==>a a2' ->
      (AMult v1 a2) / st ==>a (AMult v1 a2')

    where " t '/' st '==>a' t' " := (astep st t t').

Reserved Notation " t '/' st '==>b' t' " (at level 40, st at level 39).

Inductive bstep : state -> bexp -> bexp -> Prop :=
  | BS_Eq : forall st n1 n2,
      (BEq (ANum n1) (ANum n2)) / st ==>b 
      (if (beq_nat n1 n2) then BTrue else BFalse)
  | BS_Eq1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (BEq a1 a2) / st ==>b (BEq a1' a2)
  | BS_Eq2 : forall st v1 a2 a2',
      aval v1 -> 
      a2 / st ==>a a2' ->
      (BEq v1 a2) / st ==>b (BEq v1 a2')
  | BS_LtEq : forall st n1 n2,
      (BLe (ANum n1) (ANum n2)) / st ==>b 
               (if (ble_nat n1 n2) then BTrue else BFalse)
  | BS_LtEq1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (BLe a1 a2) / st ==>b (BLe a1' a2)
  | BS_LtEq2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ==>a a2' ->
      (BLe v1 a2) / st ==>b (BLe v1 (a2'))
  | BS_NotTrue : forall st,
      (BNot BTrue) / st ==>b BFalse
  | BS_NotFalse : forall st,
      (BNot BFalse) / st ==>b BTrue
  | BS_NotStep : forall st b1 b1',
      b1 / st ==>b b1' ->
      (BNot b1) / st ==>b (BNot b1')
  | BS_AndTrueTrue : forall st,
      (BAnd BTrue BTrue) / st ==>b BTrue
  | BS_AndTrueFalse : forall st,
      (BAnd BTrue BFalse) / st ==>b BFalse
  | BS_AndFalse : forall st b2,
      (BAnd BFalse b2) / st ==>b BFalse
  | BS_AndTrueStep : forall st b2 b2',
      b2 / st ==>b b2' ->
      (BAnd BTrue b2) / st ==>b (BAnd BTrue b2')
  | BS_AndStep : forall st b1 b1' b2,
      b1 / st ==>b b1' ->
      (BAnd b1 b2) / st ==>b (BAnd b1' b2)

  where " t '/' st '==>b' t' " := (bstep st t t').

Reserved Notation " t '/' st '==>' t' '/' st' " 
                  (at level 40, st at level 39, t' at level 39).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
      a / st ==>a a' ->
      (i ::= a) / st ==> (i ::= a') / st 
  | CS_Ass : forall st i n, 
      (i ::= (ANum n)) / st ==> SKIP / (update st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st ==> c1' / st' ->
      (c1 ;; c2) / st ==> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st ==> c2 / st
  | CS_IfTrue : forall st c1 c2,
      IFB BTrue THEN c1 ELSE c2 FI / st ==> c1 / st
  | CS_IfFalse : forall st c1 c2,
      IFB BFalse THEN c1 ELSE c2 FI / st ==> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b / st ==>b b' ->
      IFB b THEN c1 ELSE c2 FI / st ==> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
          (WHILE b DO c1 END) / st
      ==> (IFB b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st

  where " t '/' st '==>' t' '/' st' " := (cstep (t,st) (t',st')).

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CPar : com -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "PAR" ].

Notation "'SKIP'" := 
  CSkip.
Notation "x '::=' a" := 
  (CAss x a) (at level 60).
Notation "c1 ;; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI'" := 
  (CIf b c1 c2) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" := 
  (CPar c1 c2) (at level 80, right associativity).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
      a / st ==>a a' -> 
      (i ::= a) / st ==> (i ::= a') / st
  | CS_Ass : forall st i n, 
      (i ::= (ANum n)) / st ==> SKIP / (update st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st ==> c1' / st' ->
      (c1 ;; c2) / st ==> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st ==> c2 / st
  | CS_IfTrue : forall st c1 c2,
      (IFB BTrue THEN c1 ELSE c2 FI) / st ==> c1 / st
  | CS_IfFalse : forall st c1 c2,
      (IFB BFalse THEN c1 ELSE c2 FI) / st ==> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b /st ==>b b' -> 
      (IFB b THEN c1 ELSE c2 FI) / st ==> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
      (WHILE b DO c1 END) / st ==> 
               (IFB b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st ==> c1' / st' -> 
      (PAR c1 WITH c2 END) / st ==> (PAR c1' WITH c2 END) / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st ==> c2' / st' ->
      (PAR c1 WITH c2 END) / st ==> (PAR c1 WITH c2' END) / st'
  | CS_ParDone : forall st,
      (PAR SKIP WITH SKIP END) / st ==> SKIP / st
  where " t '/' st '==>' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cmultistep := multi cstep. 

Notation " t '/' st '==>*' t' '/' st' " := 
   (multi cstep  (t,st) (t',st')) 
   (at level 40, st at level 39, t' at level 39).  

Definition par_loop : com :=
  PAR
    Y ::= ANum 1
  WITH
    WHILE BEq (AId Y) (ANum 0) DO
      X ::= APlus (AId X) (ANum 1)
    END
  END.

Example par_loop_example_0:
  exists st',
       par_loop / empty_state  ==>* SKIP / st'
    /\ st' X = 0.
Proof.
  eapply ex_intro. split.
  unfold par_loop.
  eapply multi_step. apply CS_Par1.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_Eq. simpl. 
  eapply multi_step. apply CS_Par2. apply CS_IfFalse. 
  eapply multi_step. apply CS_ParDone. 
  eapply multi_refl. 
  reflexivity. Qed.

Example par_loop_example_2:
  exists st',
       par_loop / empty_state ==>* SKIP / st'
    /\ st' X = 2.
Proof.
  eapply ex_intro. split.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_Eq. simpl. 
  eapply multi_step. apply CS_Par2. apply CS_IfTrue. 
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.  
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.

  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_Eq. simpl. 
  eapply multi_step. apply CS_Par2. apply CS_IfTrue. 
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.  
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.

  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_Eq. simpl. 
  eapply multi_step. apply CS_Par2. apply CS_IfFalse. 
  eapply multi_step. apply CS_ParDone. 
  eapply multi_refl. 
  reflexivity. Qed. 

Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st ==>* par_loop / (update st X (S n)).
Proof.
  intros. inversion H as [H1 H2]. subst.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. rewrite H2. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  rewrite plus_comm. simpl.
  apply multi_refl.
  Qed.

Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  induction n; intros.
    exists st. split. apply multi_refl.
      assumption.
    assert(exists st' : state,
        par_loop / st ==>* par_loop / st' /\ st' X = n /\ st' Y = 0).
    apply IHn. assumption. inversion H0.
    exists (update x X (S n)).
    split;
    inversion H1 as [H2 H3]. 
    eapply multi_trans. apply H2.
    eapply par_body_n__Sn.
    assumption. split.
    rewrite update_eq. reflexivity.
    inversion H3 as [H4 H5].
    rewrite update_neq. assumption.
    destruct (eq_id_dec X Y) eqn:xy; inversion xy.
    assumption.
  Qed.

Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / empty_state ==>*  SKIP / st'
    /\ st' X = n.
Proof.
  intros n. 
  destruct (par_body_n n empty_state). 
    split; unfold update; reflexivity.

  rename x into st.
  inversion H as [H' [HX HY]]; clear H. 
  exists (update st Y 1). split.
  eapply multi_trans with (par_loop,st). apply H'. 
  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id. rewrite update_eq.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  apply multi_refl.

  rewrite update_neq. assumption. intro X; inversion X. 
Qed.

End CImp.

Definition stack := list nat.
Definition prog  := list sinstr.

Inductive stack_step : state -> prog * stack -> prog * stack -> Prop :=
  | SS_Push : forall st stk n p',
    stack_step st (SPush n :: p', stk)      (p', n :: stk)
  | SS_Load : forall st stk i p',
    stack_step st (SLoad i :: p', stk)      (p', st i :: stk)
  | SS_Plus : forall st stk n m p',
    stack_step st (SPlus :: p', n::m::stk)  (p', (m+n)::stk)
  | SS_Minus : forall st stk n m p',
    stack_step st (SMinus :: p', n::m::stk) (p', (m-n)::stk)
  | SS_Mult : forall st stk n m p',
    stack_step st (SMult :: p', n::m::stk)  (p', (m*n)::stk).

Theorem stack_step_deterministic : forall st, 
  deterministic (stack_step st).
Proof.
  unfold deterministic. intros st x y1 y2 H1 H2.
  induction H1; inversion H2; reflexivity.
Qed.

Definition stack_multistep st := multi (stack_step st).

Definition compiler_is_correct_statement : Prop := forall e st stck,
  stack_multistep st (s_compile e , stck) ([],(aeval st e)::stck).

Theorem compiler_app : forall st e1 e2 stck stck' stck'',
  stack_multistep st (e1 , stck) ([], stck') ->
  stack_multistep st (e2 , stck') ([], stck'') ->
  stack_multistep st (e1 ++ e2 , stck) ([],stck'').
Proof.
  intros st. induction e1; intros.
    inversion H; subst. simpl. assumption.
    inversion H1.
  inversion H; subst.
  inversion H1; subst; simpl;
  eapply multi_step; try constructor; eapply IHe1; try apply H2; apply H0.
  Qed.

Theorem compiler_is_correct : compiler_is_correct_statement.
Proof.
  unfold compiler_is_correct_statement.
  induction e; intros; simpl. 
  eapply multi_step; try constructor.
  eapply multi_step; try constructor.
  eapply multi_trans; try eapply compiler_app; try apply IHe1;
    try eapply compiler_app; try apply IHe2; econstructor; constructor.
  eapply multi_trans; try eapply compiler_app; try apply IHe1;
    try eapply compiler_app; try apply IHe2; econstructor; constructor.
  eapply multi_trans; try eapply compiler_app; try apply IHe1;
    try eapply compiler_app; try apply IHe2; econstructor; constructor.
  Qed.