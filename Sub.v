Add LoadPath "D:\sfsol".
Require Export MoreStlc.

Inductive ty : Type :=
  | TTop   : ty
  | TBool  : ty
  | TBase  : id -> ty
  | TArrow : ty -> ty -> ty
  | TUnit  : ty
.

Tactic Notation "T_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TTop" | Case_aux c "TBool" 
  | Case_aux c "TBase" | Case_aux c "TArrow" 
  | Case_aux c "TUnit"
  ].

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tunit : tm 
.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" 
  | Case_aux c "tabs" | Case_aux c "ttrue" 
  | Case_aux c "tfalse" | Case_aux c "tif"
  | Case_aux c "tunit" 
  ].

Fixpoint subst (x:id) (s:tm)  (t:tm) : tm :=
  match t with
  | tvar y => 
      if eq_id_dec x y then s else t
  | tabs y T t1 => 
      tabs y T (if eq_id_dec x y then t1 else (subst x s t1))
  | tapp t1 t2 => 
      tapp (subst x s t1) (subst x s t2)
  | ttrue => 
      ttrue
  | tfalse => 
      tfalse
  | tif t1 t2 t3 => 
      tif (subst x s t1) (subst x s t2) (subst x s t3)
  | tunit => 
      tunit 
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_true : 
      value ttrue
  | v_false : 
      value tfalse
  | v_unit : 
      value tunit
.

Hint Constructors value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         (tapp t1 t2) ==> (tapp t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         (tapp v1 t2) ==> (tapp v1  t2')
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" 
  | Case_aux c "ST_App2" | Case_aux c "ST_IfTrue" 
  | Case_aux c "ST_IfFalse" | Case_aux c "ST_If"  
  ].

Hint Constructors step.

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
    T <: T
  | S_Trans : forall S U T,
    S <: U ->
    U <: T ->
    S <: T
  | S_Top : forall S,
    S <: TTop
  | S_Arrow : forall S1 S2 T1 T2,
    T1 <: S1 ->
    S2 <: T2 ->
    (TArrow S1 S2) <: (TArrow T1 T2)
where "T '<:' U" := (subtype T U).

Hint Constructors subtype.

Tactic Notation "subtype_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "S_Refl" | Case_aux c "S_Trans"
  | Case_aux c "S_Top" | Case_aux c "S_Arrow" 
  ].

Module Examples.

Module WithPair.

Inductive ty : Type :=
  | TTop   : ty
  | TBool  : ty
  | TBase  : id -> ty
  | TArrow : ty -> ty -> ty
  | TProd  : ty -> ty -> ty
  | TUnit  : ty
.

Tactic Notation "T_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TTop" | Case_aux c "TBool" 
  | Case_aux c "TBase" | Case_aux c "TArrow" 
  | Case_aux c "TUnit" | Case_aux c "TProd"
  ].

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tpair : tm -> tm -> tm
  | tfst : tm -> tm
  | tscnd : tm -> tm
  | tunit : tm 
.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" 
  | Case_aux c "tabs" | Case_aux c "ttrue" 
  | Case_aux c "tfalse" | Case_aux c "tif"
  | Case_aux c "tunit" | Case_aux c "tpair"
  | Case_aux c "tfst" | Case_aux c "tscnd"
  ].

Fixpoint subst (x:id) (s:tm)  (t:tm) : tm :=
  match t with
  | tvar y => 
      if eq_id_dec x y then s else t
  | tabs y T t1 => 
      tabs y T (if eq_id_dec x y then t1 else (subst x s t1))
  | tapp t1 t2 => 
      tapp (subst x s t1) (subst x s t2)
  | ttrue => 
      ttrue
  | tfalse => 
      tfalse
  | tif t1 t2 t3 => 
      tif (subst x s t1) (subst x s t2) (subst x s t3)
  | tpair t1 t2 =>
      tpair (subst x s t1) (subst x s t2)
  | tfst t =>
      tfst (subst x s t)
  | tscnd t =>
      tscnd (subst x s t)
  | tunit => 
      tunit 
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_true : 
      value ttrue
  | v_false : 
      value tfalse
  | v_unit : 
      value tunit
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value (tpair v1 v2)
.

Hint Constructors value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         (tapp t1 t2) ==> (tapp t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         (tapp v1 t2) ==> (tapp v1  t2')
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Fst : forall t t',
      t ==> t' ->
      (tfst t) ==> (tfst t')
  | ST_Scnd : forall t t',
      t ==> t' ->
      (tscnd t) ==> (tscnd t')
  | ST_Pair1 : forall t1 t1' t2,
      t1 ==> t1' ->
      (tpair t1 t2) ==> (tpair t1' t2)
  | ST_Pair2 : forall v1 t2 t2',
      (value v1) ->
      t2 ==> t2' ->
      (tpair v1 t2) ==> (tpair v1 t2')
where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" 
  | Case_aux c "ST_App2" | Case_aux c "ST_IfTrue" 
  | Case_aux c "ST_IfFalse" | Case_aux c "ST_If"  
  | Case_aux c "ST_Fst" | Case_aux c "ST_Scnd"
  | Case_aux c "ST_Pair1" | Case_aux c "ST_Pair2"
  ].

Hint Constructors step.

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
    T <: T
  | S_Trans : forall S U T,
    S <: U ->
    U <: T ->
    S <: T
  | S_Top : forall S,
    S <: TTop
  | S_Arrow : forall S1 S2 T1 T2,
    T1 <: S1 ->
    S2 <: T2 ->
    (TArrow S1 S2) <: (TArrow T1 T2)
  | S_Prod1 : forall S1 S2 T1 T2,
    S1 <: T1 ->
    S2 <: T2 ->
    (TProd S1 S2) <: (TProd T1 T2)
  | S_Prod2 : forall S1 S2 T1 T2,
    S2 <: T1 ->
    S1 <: T2 ->
    (TProd S1 S2) <: (TProd T1 T2)
  | S_Fst : forall T1 T2,
    (TProd T1 T2) <: T1
  | S_Scnd : forall T1 T2,
    (TProd T1 T2) <: T2
where "T '<:' U" := (subtype T U).

Hint Constructors subtype.

Tactic Notation "subtype_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "S_Refl" | Case_aux c "S_Trans"
  | Case_aux c "S_Top" | Case_aux c "S_Arrow" 
  | Case_aux c "S_Prod1" | Case_aux c "S_Prod1"
  | Case_aux c "S_Fst" | Case_aux c "S_Scnd"
  ].

Notation x := (Id 0).
Notation y := (Id 1).
Notation z := (Id 2).

Notation A := (TBase (Id 6)).
Notation B := (TBase (Id 7)).
Notation C := (TBase (Id 8)).

Notation String := (TBase (Id 9)).
Notation Float := (TBase (Id 10)).
Notation Integer := (TBase (Id 11)).

Definition Person : ty := 
  String.

Definition Student : ty := 
  TProd String Float.

Definition Employee : ty := 
  TProd String Integer.

Example sub_student_person :
  Student <: Person.
Proof.
  apply S_Fst. Qed.

Example sub_employee_person :
  Employee <: Person.
Proof.
  apply S_Fst. Qed.

Example subtyping_example_0 :
  (TArrow C Person) <: (TArrow C TTop).
Proof.
  apply S_Arrow.
    apply S_Refl. auto.
Qed.

Example subtyping_example_1 :
  (TArrow TTop Student) <: (TArrow (TArrow C C) Person).
Proof with eauto.
  eapply S_Arrow...
  apply sub_student_person.
  Qed.

Example subtyping_example_2 :
  (TArrow TTop Person) <: (TArrow Person TTop).
Proof with eauto.
  eapply S_Arrow... Qed.

End WithPair.

Notation x := (Id 0).
Notation y := (Id 1).
Notation z := (Id 2).

Notation A := (TBase (Id 6)).
Notation B := (TBase (Id 7)).
Notation C := (TBase (Id 8)).

Notation String := (TBase (Id 9)).
Notation Float := (TBase (Id 10)).
Notation Integer := (TBase (Id 11)).

End Examples.

Definition context := id -> (option ty).
Definition empty : context := (fun _ => None). 
Definition extend (Gamma : context) (x:id) (T : ty) :=
  fun x' => if eq_id_dec x x' then Some T else Gamma x'.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- (tvar x) \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (extend Gamma x T11) |- t12 \in T12 -> 
      Gamma |- (tabs x T11 t12) \in (TArrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (TArrow T1 T2) -> 
      Gamma |- t2 \in T1 -> 
      Gamma |- (tapp t1 t2) \in T2
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- (tif t1 t2 t3) \in T
  | T_Unit : forall Gamma,
      Gamma |- tunit \in TUnit
  | T_Sub : forall Gamma t S T,
      Gamma |- t \in S ->
      S <: T ->
      Gamma |- t \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" 
  | Case_aux c "T_App" | Case_aux c "T_True" 
  | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "T_Unit"
  | Case_aux c "T_Sub" ].

Module Examples2.
Import Examples.

Import WithPair.

Definition context := id -> (option ty).
Definition empty : context := (fun _ => None). 
Definition extend (Gamma : context) (x:id) (T : ty) :=
  fun x' => if eq_id_dec x x' then Some T else Gamma x'.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- (tvar x) \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (extend Gamma x T11) |- t12 \in T12 -> 
      Gamma |- (tabs x T11 t12) \in (TArrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (TArrow T1 T2) -> 
      Gamma |- t2 \in T1 -> 
      Gamma |- (tapp t1 t2) \in T2
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- (tif t1 t2 t3) \in T
  | T_Fst : forall t T1 T2 Gamma,
      Gamma |- t \in (TProd T1 T2)->
      Gamma |- tfst t \in T1
  | T_Scnd : forall t T1 T2 Gamma,
      Gamma |- t \in (TProd T1 T2)->
      Gamma |- tscnd t \in T2
  | T_Pair : forall t1 t2 T1 T2 Gamma,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in T2 ->
      Gamma |- tpair t1 t2 \in TProd T1 T2
  | T_Unit : forall Gamma,
      Gamma |- tunit \in TUnit
  | T_Sub : forall Gamma t S T,
      Gamma |- t \in S ->
      S <: T ->
      Gamma |- t \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" 
  | Case_aux c "T_App" | Case_aux c "T_True" 
  | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "T_Unit" | Case_aux c "T_Fst"
  | Case_aux c "T_Scnd" | Case_aux c "T_Pair"
  | Case_aux c "T_Sub" ].

Notation exampleTerm1 := (tpair (tabs z A (tvar z)) (tabs z B (tvar z))).

Example typing_example_0 :
  empty |-  exampleTerm1
          \in (TProd (TArrow A A) (TArrow B B)).
Proof.
  econstructor; econstructor; econstructor;
  eauto. Qed.

Notation exampleTerm2 := (tapp (tabs x (TProd TTop (TArrow B B)) (tscnd (tvar x)))
      exampleTerm1).

Example typing_example_1 :
  empty |-  exampleTerm2
          \in (TArrow B B).
Proof.
  econstructor; try apply typing_example_0. econstructor.
  apply T_Abs. eapply T_Scnd. eauto.
  eauto. Qed.

Notation exampleTerm3 := (tapp (tabs z (TArrow (TArrow C C) (TProd TTop (TArrow B B))) (tscnd (tapp (tvar z) (tabs x C (tvar x)))))
      (tabs z (TArrow C C) exampleTerm1)).

Example typing_example_2 :
  empty |-  exampleTerm3
          \in (TArrow B B).
Proof.
  econstructor; econstructor.
  econstructor; econstructor; econstructor.
  eauto. econstructor; eauto.
  econstructor; econstructor; eauto.
  Qed.

End Examples2.

Lemma sub_inversion_Bool : forall U,
     U <: TBool ->
       U = TBool.
Proof with auto.
  intros U Hs.
  remember TBool as V.
  induction Hs; subst...
    assert(U = TBool)... subst...
    inversion HeqV.
    inversion HeqV.
  Qed.

Lemma sub_inversion_arrow : forall U V1 V2,
     U <: (TArrow V1 V2) ->
     exists U1, exists U2,
       U = (TArrow U1 U2) /\ (V1 <: U1) /\ (U2 <: V2).
Proof with eauto.
  intros U V1 V2 Hs.
  remember (TArrow V1 V2) as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros V1 V2 HeqV.
  exists V1; exists V2...
  apply IHHs2 in HeqV. inversion HeqV as [U1 [U2 [H1 [H2 H3]]]].
  apply IHHs1 in H1. inversion H1 as [U3 [U4 [H4 [H5 H6]]]].
  exists U3; exists U4...
  inversion HeqV.
  inversion HeqV; subst. exists S1; exists S2...
  Qed.

Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  Gamma |- s \in (TArrow T1 T2) ->
  value s ->
  exists x, exists S1, exists s2,
     s = tabs x S1 s2.
Proof with eauto.
  intros.
  remember (TArrow T1 T2) as V.
  generalize dependent T1. generalize dependent T2.
  induction H; intros; eauto; try solve by inversion.
    subst.
    apply sub_inversion_arrow in H1.
    inversion H1 as [U1 [U2 [H2 [H3 H4]]]].
    eapply IHhas_type...
  Qed.

Lemma canonical_forms_of_Bool : forall Gamma s,
  Gamma |- s \in TBool ->
  value s ->
  (s = ttrue \/ s = tfalse).
Proof with eauto.
  intros Gamma s Hty Hv.
  remember TBool as T.
  has_type_cases (induction Hty) Case; try solve by inversion...
  Case "T_Sub".
    subst. apply sub_inversion_Bool in H. subst...
Qed.

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  revert HeqGamma.
  has_type_cases (induction Ht) Case;
    intros HeqGamma; subst...
  Case "T_Var".
    inversion H.
  Case "T_App".
    right.
    destruct IHHt1; subst...
    SCase "t1 is a value".
      destruct IHHt2; subst...
      SSCase "t2 is a value".
        destruct (canonical_forms_of_arrow_types empty t1 T1 T2)
          as [x [S1 [t12 Heqt1]]]...
        subst. exists ([x:=t2]t12)...
      SSCase "t2 steps".
        inversion H0 as [t2' Hstp]. exists(tapp t1 t2')...
    SCase "t1 steps".
      inversion H as [t1' Hstp]. exists(tapp t1' t2)...
  Case "T_If".
    right.
    destruct IHHt1.
    SCase "t1 is a value"...
      assert (t1 = ttrue \/ t1 = tfalse)
        by (eapply canonical_forms_of_Bool; eauto).
      inversion H0; subst...
      inversion H. rename x into t1'. eauto.
Qed.

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |- (tabs x S1 t2) \in T ->
     (exists S2, (TArrow S1 S2) <: T
              /\ (extend Gamma x S1) |- t2 \in S2).
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember (tabs x S1 t2) as t.
  has_type_cases (induction H) Case; 
    inversion Heqt; subst; intros; try solve by inversion.
  Case "T_Abs".
    exists T12...
  Case "T_Sub".
    destruct IHhas_type as [S2 [Hsub Hty]]...
  Qed.

Lemma typing_inversion_var : forall Gamma x T,
  Gamma |- (tvar x) \in T ->
  exists S,
    Gamma x = Some S /\ S <: T.
Proof with eauto.
  intros Gamma x T Hty.
  remember (tvar x) as t.
  has_type_cases (induction Hty) Case; intros; 
    inversion Heqt; subst; try solve by inversion.
  Case "T_Var".
    exists T...
  Case "T_Sub".
    destruct IHHty as [U [Hctx HsubU]]... Qed.

Lemma typing_inversion_app : forall Gamma t1 t2 T2,
  Gamma |- (tapp t1 t2) \in T2 ->
  exists T1,
    Gamma |- t1 \in (TArrow T1 T2) /\
    Gamma |- t2 \in T1.
Proof with eauto.
  intros Gamma t1 t2 T2 Hty.
  remember (tapp t1 t2) as t.
  has_type_cases (induction Hty) Case; intros;
    inversion Heqt; subst; try solve by inversion.
  Case "T_App".
    exists T1...
  Case "T_Sub".
    destruct IHHty as [U1 [Hty1 Hty2]]...
Qed.

Lemma typing_inversion_true : forall Gamma T,
  Gamma |- ttrue \in T ->
  TBool <: T.
Proof with eauto.
  intros Gamma T Htyp. remember ttrue as tu.
  has_type_cases (induction Htyp) Case;
    inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_false : forall Gamma T,
  Gamma |- tfalse \in T ->
  TBool <: T.
Proof with eauto.
  intros Gamma T Htyp. remember tfalse as tu.
  has_type_cases (induction Htyp) Case;
    inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_if : forall Gamma t1 t2 t3 T,
  Gamma |- (tif t1 t2 t3) \in T ->
  Gamma |- t1 \in TBool 
  /\ Gamma |- t2 \in T
  /\ Gamma |- t3 \in T.
Proof with eauto.
  intros Gamma t1 t2 t3 T Hty.
  remember (tif t1 t2 t3) as t.
  has_type_cases (induction Hty) Case; intros;
    inversion Heqt; subst; try solve by inversion.
  Case "T_If".
    auto.
  Case "T_Sub".
    destruct (IHHty H0) as [H1 [H2 H3]]...
Qed.

Lemma typing_inversion_unit : forall Gamma T,
  Gamma |- tunit \in T ->
    TUnit <: T.
Proof with eauto.
  intros Gamma T Htyp. remember tunit as tu.
  has_type_cases (induction Htyp) Case;
    inversion Heqtu; subst; intros...
Qed.

Lemma abs_arrow : forall x S1 s2 T1 T2, 
  empty |- (tabs x S1 s2) \in (TArrow T1 T2) ->
     T1 <: S1 
  /\ (extend empty x S1) |- s2 \in T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  inversion Hty as [S2 [Hsub Hty1]].
  apply sub_inversion_arrow in Hsub.
  inversion Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  inversion Heq; subst...  Qed.

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
        y <> x  ->
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
      appears_free_in x (tif t1 t2 t3)
.

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     Gamma' |- t \in S.
Proof with eauto.
  intros. generalize dependent Gamma'.
  has_type_cases (induction H) Case; 
    intros Gamma' Heqv...
  Case "T_Var".
    apply T_Var... rewrite <- Heqv...
  Case "T_Abs".
    apply T_Abs... apply IHhas_type. intros x0 Hafi.
    unfold extend. destruct (eq_id_dec x x0)...

  Case "T_App".
    apply T_App with T1...
  Case "T_If".
    apply T_If...

Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  has_type_cases (induction Htyp) Case; 
      subst; inversion Hafi; subst...
  Case "T_Abs".
    destruct (IHHtyp H4) as [T Hctx]. exists T.
    unfold extend in Hctx. rewrite neq_id in Hctx...  Qed.

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     (extend Gamma x U) |- t \in S  ->
     empty |- v \in U   ->
     Gamma |- ([x:=v]t) \in S.
Proof with eauto.
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent S. generalize dependent Gamma.
  t_cases (induction t) Case; intros; simpl.
  Case "tvar".
    rename i into y.
    destruct (typing_inversion_var _ _ _ Htypt) 
        as [T [Hctx Hsub]].
    unfold extend in Hctx.
    destruct (eq_id_dec x y)...
    SCase "x=y".
      subst.
      inversion Hctx; subst. clear Hctx.
      apply context_invariance with empty...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) 
          as [T' HT']...
      inversion HT'.
  Case "tapp".
    destruct (typing_inversion_app _ _ _ _ Htypt) 
        as [T1 [Htypt1 Htypt2]].
    eapply T_App...
  Case "tabs".
    rename i into y. rename t into T1.
    destruct (typing_inversion_abs _ _ _ _ _ Htypt) 
      as [T2 [Hsub Htypt2]].
    apply T_Sub with (TArrow T1 T2)... apply T_Abs...
    destruct (eq_id_dec x y).
    SCase "x=y".
      eapply context_invariance...
      subst.
      intros x Hafi. unfold extend.
      destruct (eq_id_dec y x)...
    SCase "x<>y".
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend.
      destruct (eq_id_dec y z)...
      subst. rewrite neq_id... 
  Case "ttrue".
      assert (TBool <: S) 
        by apply (typing_inversion_true _ _  Htypt)...
  Case "tfalse".
      assert (TBool <: S) 
        by apply (typing_inversion_false _ _  Htypt)...
  Case "tif".
    assert ((extend Gamma x U) |- t1 \in TBool 
            /\ (extend Gamma x U) |- t2 \in S
            /\ (extend Gamma x U) |- t3 \in S) 
      by apply (typing_inversion_if _ _ _ _ _ Htypt).
    inversion H as [H1 [H2 H3]].
    apply IHt1 in H1. apply IHt2 in H2. apply IHt3 in H3.
    auto.
  Case "tunit".
    assert (TUnit <: S) 
      by apply (typing_inversion_unit _ _  Htypt)...
Qed.

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t ==> t'  ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT.
  remember empty as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  has_type_cases (induction HT) Case; 
    intros t' HeqGamma HE; subst; inversion HE; subst...
  Case "T_App".
    inversion HE; subst...
    SCase "ST_AppAbs".
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T...
Qed.

