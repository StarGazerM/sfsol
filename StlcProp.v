Add LoadPath "D:\sfsol".
Require Export Stlc.

Module STLCProp.
Import STLC.

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
Proof with eauto.
  intros t T H.
  remember (@empty ty) as Gamma.
  has_type_cases (induction H) Case; subst Gamma...
    inversion H.
    right. destruct IHhas_type1...
      destruct IHhas_type2...
        inversion H; subst; try solve by inversion.
        exists ([x0:=t2]t12)...
        inversion H2 as [t2' Hstep].
        exists (tapp t1 t2')...
      inversion H1 as [t1' Hstep].
        exists (tapp t1' t2)...
    right. destruct IHhas_type1...
      inversion H2; subst...
      solve by inversion.
      inversion H2...
  Qed.

Theorem progress' : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
Proof.
  intros t.
  t_cases (induction t) Case; intros T Ht; auto.
  solve by inversion 2.
  inversion Ht; subst. right.
  assert(value t1 \/ (exists t' : tm, t1 ==> t')).
    eauto.
  assert(value t2 \/ (exists t' : tm, t2 ==> t')). eauto.
  inversion H. inversion H0. inversion H2; subst; try solve by inversion.
    exists ([x0:=t2]t12). auto.
    inversion H3. exists (tapp t1 x0). auto.
    inversion H1. exists (tapp x0 t2). auto.
  inversion Ht; subst. right.
  assert(value t1 \/ (exists t' : tm, t1 ==> t')). eauto.
  inversion H. inversion H3; subst; try solve by inversion.
    eauto.
    eauto.
    inversion H0.
    exists(tif x0 t2 t3). auto.
  Qed.

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x ->
      appears_free_in x t12 ->
      appears_free_in x (tabs y T11 t12)
  | afi_if1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tif t1 t2 t3).

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var"
  | Case_aux c "afi_app1" | Case_aux c "afi_app2"
  | Case_aux c "afi_abs"
  | Case_aux c "afi_if1" | Case_aux c "afi_if2"
  | Case_aux c "afi_if3" ].

Hint Constructors appears_free_in.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
 Proof.
  intros x t T Gamma H H0. generalize dependent Gamma.
  generalize dependent T.
  afi_cases (induction H) Case;
         intros; try solve [inversion H0; eauto].
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite extend_neq in H7; assumption.
Qed.


Corollary typable_empty__closed : forall t T,
    empty |- t \in T ->
    closed t.
Proof with auto.
  intros t T H x contra.
  apply free_in_context with (T:=T) (Gamma:=empty) in contra...
  solve by inversion 2.
  Qed.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.
Proof.
  intros.
  generalize dependent Gamma'.
  induction H; intros; eauto. econstructor. symmetry. rewrite <- H.
  apply H0. auto.
  econstructor. apply IHhas_type.
  intros. unfold extend.
  destruct (eq_id_dec x0 x1). reflexivity.
  apply H0. eauto.
  econstructor; auto.
  econstructor; auto.
  Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
     extend Gamma x U |- t \in T ->
     empty |- v \in U ->
     Gamma |- [x:=v]t \in T.
Proof.
  intros.
  generalize dependent Gamma.
  generalize dependent T.
  induction t; intros; simpl; inversion H; subst; eauto;
  destruct (eq_id_dec x0 i); subst.
  rewrite -> extend_eq in H3. inv H3.
  eapply context_invariance. apply H0.
  intros. assert (contra:False); try inversion contra.
  eapply typable_empty__closed. apply H0. apply H1.
  rewrite extend_neq in H3; eauto.
  econstructor. eapply context_invariance.
  apply H6. intros. apply extend_shadow.
  econstructor. apply IHt. eapply context_invariance.
  apply H6. intros.
  destruct (eq_id_dec i x1); subst.
  rewrite extend_eq. rewrite extend_neq; auto. rewrite extend_eq. reflexivity.
  rewrite extend_neq; auto. destruct (eq_id_dec x0 x1); subst.
  rewrite extend_eq. rewrite extend_eq. reflexivity.
  repeat rewrite extend_neq; auto.
  Qed.

Theorem preservation : forall t t' T,
     empty |- t \in T ->
     t ==> t' ->
     empty |- t' \in T.
Proof with eauto.
  intros.
  remember (@empty ty) as Gamma.
  generalize dependent t'.
  induction H; intros t' HE; subst;
  try solve [inversion HE; subst; auto].
  inversion HE; subst...
  apply substitution_preserves_typing with T11...
  inversion H...
  Qed.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty |- t \in T ->
  t ==>* t' ->
  ~(stuck t').
Proof with auto.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  assert((value x0)\/(exists t' : tm, x0 ==> t')).
    eapply progress. apply Hhas_type.
  inversion H...
  apply IHHmulti.
  eapply preservation. apply Hhas_type. assumption.
  assumption. assumption.
  Qed.

Theorem no_subject_expansion : exists t, exists t', exists T,
  (t ==> t')->(empty |- t' \in T) ->
  ~ (empty |- t \in T).
Proof with eauto.
  apply ex_intro with (tapp (tabs y TBool ttrue) (tvar z)).
  apply ex_intro with ttrue. apply ex_intro with TBool.
  intros. inversion H. subst.
  intro contra. inversion contra; subst.
  inversion H7; subst. inversion H4.
  Qed.

Theorem types_unique : forall t Gamma T1 T2,
  Gamma |- t \in T1 ->
  Gamma |- t \in T2 ->
  T1 = T2.
Proof with eauto.
  induction t; intros; inversion H; inversion H0; subst...
  rewrite H3 in H7. inversion H7...
  assert (T0 = T11)... subst.
  assert (TArrow T11 T1 = TArrow T11 T2)... inversion H1...
  assert (T12 = T3)... subst. reflexivity.
  Qed.

(*

  stlc_variation1
    determinism becomes false, trivial
    progress remains true
    preservation becomes false, trivial

  stlc_variation2
    determisim becomes false, tapp (tabs x x) (tabs x true)
    Progress remains true
    preservation becomes false, same for determinism

  stlc_variation3
    determinism remains true,
    progress becomes false, when t1 is non-value
    preservation remains true
  
  stlc_variation4
    determinism becomes false, tif true t1 t2
    progress remains true
    preservation becomes false, same as determinsim, yet t1 must have type diferent than bool

  stlc_variation5
    determinism remains true
    progress remains true
    preservation becomes false, (/\ x : Bool , /\ y : Bool y) (true)

  stlc_variation6
    determinsim remains true
    progress remains true
    preservation remains true

  stlc_variton7
    determinism remains true
    progress remains true
    preservation remains true

*)

End STLCProp.

Module STLCArith.

Inductive ty : Type :=
  | TArrow : ty -> ty -> ty
  | TNat : ty.

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | tnat : nat -> tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tmult : tm -> tm -> tm
  | tif0 : tm -> tm -> tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp"
  | Case_aux c "tabs" | Case_aux c "tnat"
  | Case_aux c "tsucc" | Case_aux c "tpred"
  | Case_aux c "tmult" | Case_aux c "tif0" ].

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_nat : forall x,
      value (tnat x).

Check value.

Hint Constructors value.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' =>
      if eq_id_dec x x' then s else t
  | tabs x' T t1 =>
      tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1))
  | tapp t1 t2 =>
      tapp ([x:=s] t1) ([x:=s] t2)
  | tnat n =>
      tnat n
  | tsucc t1 =>
      tsucc ([x:=s]t1)
  | tpred t1 =>
      tpred ([x:=s]t1)
  | tmult t1 t2 =>
      tmult ([x:=s]t1) ([x:=s]t2)
  | tif0 t1 t2 t3 =>
      tif0 ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         tapp v1 t2 ==> tapp v1 t2'
  | ST_If0 : forall t1 t2,
      (tif0 (tnat 0) t1 t2) ==> t1
  | ST_IfN0 : forall x t1 t2,
      x <> 0 -> (tif0 (tnat x) t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif0 t1 t2 t3) ==> (tif0 t1' t2 t3)
  | ST_SuccNat : forall x,
      tsucc (tnat x) ==> tnat (S x)
  | ST_Succ : forall t1 t2,
      t1 ==> t2 ->
      tsucc t1 ==> tsucc t2
  | ST_PredNat : forall x,
      tpred (tnat x) ==> tnat (pred x)
  | ST_Pred : forall t1 t2,
      t1 ==> t2 ->
      tpred t1 ==> tpred t2
  | ST_MultNatNat : forall x y,
      tmult (tnat x) (tnat y) ==> tnat (mult x y)
  | ST_MultNat : forall v t1 t2,
      value v ->
      t1 ==> t2 ->
      tmult v t1 ==> tmult v t2
  | ST_Mult : forall t1 t2 t3,
      t1 ==> t2 ->
      tmult t1 t3 ==> tmult t2 t3

where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 ->
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 ->
      Gamma |- t2 \in T11 ->
      Gamma |- tapp t1 t2 \in T12
  | T_Nat : forall Gamma x,
       Gamma |- tnat x \in TNat
  | T_Succ : forall Gamma t1,
       Gamma |- t1 \in TNat ->
       Gamma |- tsucc t1 \in TNat
  | T_Pred : forall Gamma t1,
       Gamma |- t1 \in TNat ->
       Gamma |- tpred t1 \in TNat
  | T_Mult : forall Gamma t1 t2,
       Gamma |- t1 \in TNat ->
       Gamma |- t2 \in TNat ->
       Gamma |- tmult t1 t2 \in TNat
  | T_If0 : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TNat ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif0 t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
Proof with eauto.
  intros.
  remember (@empty ty) as Gamma.
  induction H; subst Gamma...
  inversion H.
  right. destruct IHhas_type1...
    destruct IHhas_type2...
    inversion H1...
    rewrite <- H3 in H.
    inversion H.
    inversion H2...
    inversion H1...
  right.
    destruct IHhas_type...
    inversion H0... rewrite <- H1 in H.
    inversion H...
    inversion H0...
  right.
    destruct IHhas_type...
    inversion H0... rewrite <- H1 in H.
    inversion H...
    inversion H0...
  right.
    destruct IHhas_type1; eauto;
    inversion H1; subst;eauto; inversion H;
    destruct IHhas_type2; eauto;
    inversion H3; subst; eauto; inversion H0.
  right.
    destruct IHhas_type1; eauto;
    inversion H2; subst...
      inversion H.
      destruct x...
  Qed.

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x ->
      appears_free_in x t12 ->
      appears_free_in x (tabs y T11 t12)
  | afi_tsucc : forall x t,
      appears_free_in x t ->
      appears_free_in x (tsucc t)
  | afi_tpred : forall x t,
      appears_free_in x t ->
      appears_free_in x (tpred t)
  | afi_if1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tif0 t1 t2 t3)
  | afi_if2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tif0 t1 t2 t3)
  | afi_if3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tif0 t1 t2 t3)
  | afi_mult1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tmult t1 t2)
  | afi_mult2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tmult t1 t2).

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var"
  | Case_aux c "afi_app1" | Case_aux c "afi_app2"
  | Case_aux c "afi_abs"  | Case_aux c "afi_tsucc"
  | Case_aux c "afi_tpred" | Case_aux c "afi_mult1"
  | Case_aux c "afi_mult2"
  | Case_aux c "afi_if1" | Case_aux c "afi_if2"
  | Case_aux c "afi_if3" ].

Hint Constructors appears_free_in.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof.
  intros x t T Gamma H H0. generalize dependent Gamma.
  generalize dependent T.
  afi_cases (induction H) Case;
         intros; try solve [inversion H0; eauto].
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite extend_neq in H7; assumption.
Qed.


Corollary typable_empty__closed : forall t T,
    empty |- t \in T ->
    closed t.
Proof with auto.
  intros t T H x contra.
  apply free_in_context with (T:=T) (Gamma:=empty) in contra...
  solve by inversion 2.
  Qed.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.
Proof with eauto.
  intros.
  generalize dependent Gamma'.
  induction H; intros; econstructor; eauto. symmetry. rewrite <- H.
  apply H0. auto.
  apply IHhas_type.
  intros. unfold extend.
  destruct (eq_id_dec x x0). reflexivity.
  apply H0...
  Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
     extend Gamma x U |- t \in T ->
     empty |- v \in U ->
     Gamma |- [x:=v]t \in T.
Proof.
  intros.
  generalize dependent Gamma.
  generalize dependent T.
  induction t; intros; simpl; inversion H; subst; eauto.
  destruct (eq_id_dec x i); subst.
  rewrite -> extend_eq in H3. inv H3.
  eapply context_invariance. apply H0.
  intros. assert (contra:False); try inversion contra.
  eapply typable_empty__closed. apply H0. apply H1.
  rewrite extend_neq in H3; eauto.
  econstructor. auto.
  econstructor. apply IHt1. apply H4.
  apply IHt2. apply H6.
  destruct (eq_id_dec x i); subst. econstructor.
  eapply context_invariance. apply H6. intros.
  destruct (eq_id_dec x i); subst; eauto.
  rewrite extend_eq; rewrite extend_eq; auto.
  rewrite extend_neq; try rewrite extend_neq; try rewrite extend_neq; auto.
  econstructor. apply IHt. eapply context_invariance.
  apply H6. intros. destruct (eq_id_dec x x0); subst; eauto.
  rewrite extend_neq. rewrite extend_eq. rewrite extend_eq. auto. auto.
  destruct (eq_id_dec i x0); subst.
  rewrite extend_eq; auto. rewrite extend_neq. rewrite extend_eq. auto. auto.
  rewrite extend_neq; auto. rewrite extend_neq; auto.
  rewrite extend_neq; auto. rewrite extend_neq; auto.
  econstructor.
  econstructor;auto.
  econstructor;auto.
  econstructor;auto.
  econstructor; auto.
  Qed.

Theorem preservation : forall t t' T,
     empty |- t \in T ->
     t ==> t' ->
     empty |- t' \in T.
Proof with eauto.
  intros.
  remember (@empty ty) as Gamma.
  generalize dependent t'.
  induction H; intros t' HE; subst;
  try solve [inversion HE; subst; eauto; econstructor; eauto].
  inversion HE; subst...
  apply substitution_preserves_typing with T11...
  inversion H...
  econstructor...
  econstructor...
  Qed.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty |- t \in T ->
  t ==>* t' ->
  ~(stuck t').
Proof with auto.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  assert((value x)\/(exists t' : tm, x ==> t')).
    eapply progress. apply Hhas_type.
  inversion H...
  apply IHHmulti.
  eapply preservation. apply Hhas_type. assumption.
  assumption. assumption.
  Qed.

End STLCArith.