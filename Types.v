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

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ==> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tpred t1) ==> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')

where "t1 '==>' t2" := (step t1 t2).

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

Ltac find_replace :=
  match goal with
    H1 : ?T ==> ?T1, H2: ?T ==> ?T2 |- _ =>
    (replace T2 with T1;eauto)
  end.

Ltac find_nvalcontra :=
  match goal with
    H1 : nvalue ?T , H2: ?T ==> ?T' |- _ =>
    (assert(contra:False); eauto; try inversion contra; try eapply value_is_nf; eauto)
  end.

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  intros t.
  induction t; intros; inv H; inv H0; eauto; 
  try solve by inversion; try find_replace; 
  try inversion H1; try inversion H2; subst;
  try find_nvalcontra.
  Qed.

Inductive ty : Type :=
  | TBool : ty
  | TNat : ty.

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True : 
       |- ttrue \in TBool
  | T_False : 
       |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T,
       |- t1 \in TBool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- tif t1 t2 t3 \in T
  | T_Zero : 
       |- tzero \in TNat
  | T_Succ : forall t1,
       |- t1 \in TNat ->
       |- tsucc t1 \in TNat
  | T_Pred : forall t1,
       |- t1 \in TNat ->
       |- tpred t1 \in TNat
  | T_Iszero : forall t1,
       |- t1 \in TNat ->
       |- tiszero t1 \in TBool

where "'|-' t '\in' T" := (has_type t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "T_Zero" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
  | Case_aux c "T_Iszero" ].

Hint Constructors has_type.

Example has_type_1 :
  |- tif tfalse tzero (tsucc tzero) \in TNat.
Proof.
  auto. Qed.

Example has_type_not :
  ~ (|- tif tfalse tzero ttrue \in TBool).
Proof. intros contra. inv contra. inv H4. Qed.

Example succ_hastype_nat__hastype_nat : forall t,
  |- tsucc t \in TNat ->
  |- t \in TNat.
Proof.
  intros. inv H. assumption. Qed.

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.
Proof with auto.
  intros t T HT.
  has_type_cases (induction HT) Case...
  Case "T_If".
    right. inversion IHHT1; clear IHHT1.
    SCase "t1 is a value". inversion H; clear H.
      SSCase "t1 is a bvalue". inversion H0; clear H0.
        SSSCase "t1 is ttrue".
          exists t2...
        SSSCase "t1 is tfalse". 
          exists t3...
      SSCase "t1 is an nvalue".
        solve by inversion 2.  (* on H and HT1 *)
    SCase "t1 can take a step".
      inversion H as [t1' H1].
      exists (tif t1' t2 t3)...
  inv IHHT; inv H. inv H0; inv HT. left... right; eexists; eauto.
  inv IHHT; inv H. inv H0; inv HT. inv H0; right; eexists; eauto. right; eexists; eauto.
  inv IHHT; inv H. inv H0; inv HT. inv H0; right; eexists; eauto. right; eexists; eauto.
  Qed.

Lemma nvalue_isnat : forall t,
  nvalue t -> |- t \in TNat.
Proof.
  intros; induction H; eauto.
  Qed.

Lemma bvalue_isbool : forall t,
  bvalue t -> |- t \in TBool.
Proof.
  intros; induction H; eauto.
  Qed.

Hint Resolve nvalue_isnat.
Hint Resolve bvalue_isbool.

Theorem preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.
Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  has_type_cases (induction HT) Case;
         intros t' HE;
         try (solve by inversion).
    Case "T_If". inversion HE; subst.
      SCase "ST_IFTrue". assumption.
      SCase "ST_IfFalse". assumption.
      SCase "ST_If". apply T_If; try assumption.
        apply IHHT1; assumption.
    inversion HE; subst; eauto.
    inversion HE; subst; eauto.
    inversion HE; subst; eauto.
  Qed.

Theorem preservation' : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.
Proof with eauto.
  intros. generalize dependent T.
  induction H0; intros; inv H; eauto; inv H0; eauto.
  Qed.

 Definition amultistep st := multi (astep st).
Notation " t '/' st '==>a*' t' " := (amultistep st t t')
  (at level 40, st at level 39).

Example astep_example1 :
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  ==>a* (ANum 15).
Proof.
  apply multi_step with (APlus (ANum 3) (ANum 12)).
    apply AS_Plus2.
      apply av_num.
      apply AS_Mult.
  apply multi_step with (ANum 15).
    apply AS_Plus.
  apply multi_refl.
Qed.

Hint Constructors astep aval.
Example astep_example1' :
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  ==>a* (ANum 15).
Proof.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  apply multi_refl.
Qed.

Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
Tactic Notation "normalize" :=
   repeat (print_goal; eapply multi_step ;
             [ (eauto 10; fail) | (instantiate; simpl)]);
   apply multi_refl.

Example astep_example1'' :
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  ==>a* (ANum 15).
Proof.
  normalize.
  Qed.

Example astep_example1''' : exists e',
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  ==>a* e'.
Proof.
  eapply ex_intro. normalize.
  Qed.

Theorem normalize_ex : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state
  ==>a* e'.
Proof.
  eapply ex_intro. normalize.
  Qed.

Theorem normalize_ex' : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state
  ==>a* e'.
Proof.
  apply ex_intro with (ANum 6).
  normalize.
  Qed.

 Definition multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |- t \in T ->
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.
  apply IHP. apply (preservation x y T HT H).
  unfold stuck. split; auto. Qed.

Theorem subject_expansion : exists t, exists t', exists T,
  t ==> t' /\ |- t' \in T /\ ~ |- t \in T.
Proof with eauto.
  apply ex_intro with (tif ttrue tzero ttrue).
  exists tzero. exists TNat. split; auto.
  split; auto. intros H. inv H. inv H6.
  Qed.

(*
  Variation1 -
    remains true
    becomes false, tsucc ttrue
    remains true.
*)

(*
  Variation2 -
    becomes false, tif ttrue ttrue ttfalse
    remains true
    remains true
*)

(*
  Variation3 -
    becomes false, tif ttrue tif ttrue ttrue ttfalse ttfalse
    remains true
    remains true
*)

(*
  Variation4 -
    becomes false, tif ttrue ttrue tpred ttfalse
    remains true
    remains true
*)

(*
  Variation5 -
    remains true
    remains true
    remains true
*)

(*
  Variation6 -
    remains true
    remains true
    becomes false, tpred tzero
*)

(*
  more variations -
    1.) Adding/Deleting a new type rule -> step deterministic property remains as is
    2.) Adding a new type for value -> Progression is un altered
    3.) Removing a type rule for value which can't step -> progression is altered, preservation isn't
    4.) Adding new step rules to create new windows for step -> step determinism affected, if step is made to same type, preservation remains, progression still remains
  combination of above 4 in non conflict manner we can achieve
  different required changes, affecting only target property.
*)

(*
  remove_predzero
     Progression would go off,
*)

(*
  prog_pres_bigstep
    progress ->
      can be broken into sequence with first command non skip,
    preservation ->
      flag like break will do.
*)