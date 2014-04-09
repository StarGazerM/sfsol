Add LoadPath "D:\sfsol".
Require Export Stlc.

Module STLCExtendedRecords.

Module FirstTry.

Definition alist (X : Type) := list (id * X).

Inductive ty : Type :=
  | TBase : id -> ty
  | TArrow : ty -> ty -> ty
  | TRcd : (alist ty) -> ty.

End FirstTry.

Inductive ty : Type :=
  | TBase : id -> ty
  | TArrow : ty -> ty -> ty
  | TRNil : ty
  | TRCons : id -> ty -> ty -> ty.

Tactic Notation "T_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TBase" | Case_aux c "TArrow"
  | Case_aux c "TRNil" | Case_aux c "TRCons" ].

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | tproj : tm -> id -> tm
  | trnil : tm
  | trcons : id -> tm -> tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" | Case_aux c "tabs"
  | Case_aux c "tproj" | Case_aux c "trnil" | Case_aux c "trcons" ].

Notation a := (Id 0).
Notation f := (Id 1).
Notation g := (Id 2).
Notation l := (Id 3).
Notation A := (TBase (Id 4)).
Notation B := (TBase (Id 5)).
Notation k := (Id 6).
Notation i1 := (Id 7).
Notation i2 := (Id 8).

Inductive record_ty : ty -> Prop :=
  | RTnil :
        record_ty TRNil
  | RTcons : forall i T1 T2,
        record_ty (TRCons i T1 T2).

Inductive record_tm : tm -> Prop :=
  | rtnil :
        record_tm trnil
  | rtcons : forall i t1 t2,
        record_tm (trcons i t1 t2).

Inductive well_formed_ty : ty -> Prop :=
  | wfTBase : forall i,
        well_formed_ty (TBase i)
  | wfTArrow : forall T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        well_formed_ty (TArrow T1 T2)
  | wfTRNil :
        well_formed_ty TRNil
  | wfTRCons : forall i T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        record_ty T2 ->
        well_formed_ty (TRCons i T1 T2).

Hint Constructors record_ty record_tm well_formed_ty.

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar y => if eq_id_dec x y then s else t
  | tabs y T t1 => tabs y T (if eq_id_dec x y then t1 else (subst x s t1))
  | tapp t1 t2 => tapp (subst x s t1) (subst x s t2)
  | tproj t1 i => tproj (subst x s t1) i
  | trnil => trnil
  | trcons i t1 tr1 => trcons i (subst x s t1) (subst x s tr1)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Inductive value : tm -> Prop :=
  | v_abs : forall x T11 t12,
      value (tabs x T11 t12)
  | v_rnil : value trnil
  | v_rcons : forall i v1 vr,
      value v1 ->
      value vr ->
      value (trcons i v1 vr).

Hint Constructors value.

Fixpoint Tlookup (i:id) (Tr:ty) : option ty :=
  match Tr with
  | TRCons i' T Tr' => if eq_id_dec i i' then Some T else Tlookup i Tr'
  | _ => None
  end.

Fixpoint tlookup (i:id) (tr:tm) : option tm :=
  match tr with
  | trcons i' t tr' => if eq_id_dec i i' then Some t else tlookup i tr'
  | _ => None
  end.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T11 t12 v2,
         value v2 ->
         (tapp (tabs x T11 t12) v2) ==> ([x:=v2]t12)
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         (tapp t1 t2) ==> (tapp t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         (tapp v1 t2) ==> (tapp v1 t2')
  | ST_Proj1 : forall t1 t1' i,
        t1 ==> t1' ->
        (tproj t1 i) ==> (tproj t1' i)
  | ST_ProjRcd : forall tr i vi,
        value tr ->
        tlookup i tr = Some vi ->
        (tproj tr i) ==> vi
  | ST_Rcd_Head : forall i t1 t1' tr2,
        t1 ==> t1' ->
        (trcons i t1 tr2) ==> (trcons i t1' tr2)
  | ST_Rcd_Tail : forall i v1 tr2 tr2',
        value v1 ->
        tr2 ==> tr2' ->
        (trcons i v1 tr2) ==> (trcons i v1 tr2')

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" | Case_aux c "ST_App2"
  | Case_aux c "ST_Proj1" | Case_aux c "ST_ProjRcd"
  | Case_aux c "ST_Rcd_Head" | Case_aux c "ST_Rcd_Tail" ].

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |- (tvar x) \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      well_formed_ty T11 ->
      (extend Gamma x T11) |- t12 \in T12 ->
      Gamma |- (tabs x T11 t12) \in (TArrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (TArrow T1 T2) ->
      Gamma |- t2 \in T1 ->
      Gamma |- (tapp t1 t2) \in T2
  | T_Proj : forall Gamma i t Ti Tr,
      Gamma |- t \in Tr ->
      Tlookup i Tr = Some Ti ->
      Gamma |- (tproj t i) \in Ti
  | T_RNil : forall Gamma,
      Gamma |- trnil \in TRNil
  | T_RCons : forall Gamma i t T tr Tr,
      Gamma |- t \in T ->
      Gamma |- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |- (trcons i t tr) \in (TRCons i T Tr)

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
  | Case_aux c "T_Proj" | Case_aux c "T_RNil" | Case_aux c "T_RCons" ].

Lemma typing_example_2 :
  empty |-
    (tapp (tabs a (TRCons i1 (TArrow A A)
                      (TRCons i2 (TArrow B B)
                       TRNil))
              (tproj (tvar a) i2))
            (trcons i1 (tabs a A (tvar a))
            (trcons i2 (tabs a B (tvar a))
             trnil))) \in
    (TArrow B B).
Proof with eauto.
  econstructor... econstructor...
  econstructor... apply T_Var.
  unfold extend. rewrite eq_id...
  eauto. unfold Tlookup...
  econstructor...
  Qed.

Example typing_nonexample :
  ~ exists T,
      (extend empty a (TRCons i2 (TArrow A A)
                                TRNil)) |-
               (trcons i1 (tabs a B (tvar a)) (tvar a)) \in
               T.
Proof.
  intros contra. inversion contra.
  inversion H; subst.
  inversion H8. Qed.

Example typing_nonexample_2 : forall y,
  ~ exists T,
    (extend empty y A) |-
           (tapp (tabs a (TRCons i1 A TRNil)
                     (tproj (tvar a) i1))
                   (trcons i1 (tvar y) (trcons i2 (tvar y) trnil))) \in
           T.
Proof.
  intros y contra.
  inversion contra; clear contra; inversion H; clear H; subst.
  inversion H3; subst; clear H3... inversion H8; subst; clear H8...
  inversion H3; subst... unfold extend in H0. rewrite eq_id in H0.
  inversion H0; subst; clear H0... inversion H5; subst; clear H5.
  inversion H11; subst; clear  H11.
  Qed.

Lemma wf_rcd_lookup : forall i T Ti,
  well_formed_ty T ->
  Tlookup i T = Some Ti ->
  well_formed_ty Ti.
Proof with eauto.
  intros i T.
  T_cases (induction T) Case; intros; try solve by inversion.
  Case "TRCons".
    inversion H. subst. unfold Tlookup in H0.
    destruct (eq_id_dec i i0)...
    inversion H0. subst... Qed.

Lemma step_preserves_record_tm : forall tr tr',
  record_tm tr ->
  tr ==> tr' ->
  record_tm tr'.
Proof.
  intros tr tr' Hrt Hstp.
  inversion Hrt; subst; inversion Hstp; subst; auto.
Qed.

Lemma has_type__wf : forall Gamma t T,
  Gamma |- t \in T -> well_formed_ty T.
Proof with eauto.
  intros Gamma t T Htyp.
  has_type_cases (induction Htyp) Case...
  Case "T_App".
    inversion IHHtyp1...
  Case "T_Proj".
    eapply wf_rcd_lookup...
Qed.

Lemma lookup_field_in_value : forall v T i Ti,
  value v ->
  empty |- v \in T ->
  Tlookup i T = Some Ti ->
  exists ti, tlookup i v = Some ti /\ empty |- ti \in Ti.
Proof with eauto.
  intros v T i Ti Hval Htyp Hget.
  remember (@empty ty) as Gamma.
  has_type_cases (induction Htyp) Case; subst; try solve by inversion...
  Case "T_RCons".
    simpl in Hget. simpl. destruct (eq_id_dec i i0).
    SCase "i is first".
      simpl. inversion Hget. subst.
      exists t...
    SCase "get tail".
      destruct IHHtyp2 as [vi [Hgeti Htypi]]...
      inversion Hval... Qed.

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  generalize dependent HeqGamma.
  has_type_cases (induction Ht) Case; intros HeqGamma; subst.
  Case "T_Var".
    inversion H.
  Case "T_Abs".
    left...
  Case "T_App".
    right.
    destruct IHHt1; subst...
    SCase "t1 is a value".
      destruct IHHt2; subst...
      SSCase "t2 is a value".
        inversion H; subst; try (solve by inversion).
        exists ([x:=t2]t12)...
      SSCase "t2 steps".
        destruct H0 as [t2' Hstp]. exists (tapp t1 t2')...
    SCase "t1 steps".
      destruct H as [t1' Hstp]. exists (tapp t1' t2)...
  Case "T_Proj".
    right. destruct IHHt...
    SCase "rcd is value".
      destruct (lookup_field_in_value _ _ _ _ H0 Ht H) as [ti [Hlkup _]].
      exists ti...
    SCase "rcd_steps".
      destruct H0 as [t' Hstp]. exists (tproj t' i)...
  Case "T_RNil".
    left...
  Case "T_RCons".
    destruct IHHt1...
    SCase "head is a value".
      destruct IHHt2; try reflexivity.
      SSCase "tail is a value".
        left...
      SSCase "tail steps".
        right. destruct H2 as [tr' Hstp].
        exists (trcons i t tr')...
    SCase "head steps".
      right. destruct H1 as [t' Hstp].
      exists (trcons i t' tr)... Qed.

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
  | afi_proj : forall x t i,
     appears_free_in x t ->
     appears_free_in x (tproj t i)
  | afi_rhead : forall x i ti tr,
      appears_free_in x ti ->
      appears_free_in x (trcons i ti tr)
  | afi_rtail : forall x i ti tr,
      appears_free_in x tr ->
      appears_free_in x (trcons i ti tr).

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in S.
Proof with eauto.
  intros. generalize dependent Gamma'.
  has_type_cases (induction H) Case;
    intros Gamma' Heqv...
  Case "T_Var".
    apply T_Var... rewrite <- Heqv...
  Case "T_Abs".
    apply T_Abs... apply IHhas_type. intros y Hafi.
    unfold extend. destruct (eq_id_dec x y)...
  Case "T_App".
    apply T_App with T1...
  Case "T_RCons".
    apply T_RCons... Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  has_type_cases (induction Htyp) Case; inversion Hafi; subst...
  Case "T_Abs".
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold extend in Hctx.
    rewrite neq_id in Hctx...
Qed.

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     (extend Gamma x U) |- t \in S ->
     empty |- v \in U ->
     Gamma |- ([x:=v]t) \in S.
Proof with eauto.
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent Gamma. generalize dependent S.
  t_cases (induction t) Case;
    intros S Gamma Htypt; simpl; inversion Htypt; subst...
  Case "tvar".
    simpl. rename i into y.
    destruct (eq_id_dec x y).
    SCase "x=y".
      subst.
      unfold extend in H0. rewrite eq_id in H0.
      inversion H0; subst. clear H0.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
      apply T_Var... unfold extend in H0. rewrite neq_id in H0...
  Case "tabs".
    rename i into y. rename t into T11.
    apply T_Abs...
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
  Case "trcons".
    apply T_RCons... inversion H7; subst; simpl...
Qed.

Theorem preservation : forall t t' T,
     empty |- t \in T ->
     t ==> t' ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT.
  remember (@empty ty) as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  has_type_cases (induction HT) Case;
    intros t' HeqGamma HE; subst; inversion HE; subst...
  Case "T_App".
    inversion HE; subst...
    SCase "ST_AppAbs".
      apply substitution_preserves_typing with T1...
      inversion HT1...
  Case "T_Proj".
    destruct (lookup_field_in_value _ _ _ _ H2 HT H)
      as [vi [Hget Htyp]].
    rewrite H4 in Hget. inversion Hget. subst...
  Case "T_RCons".
    apply T_RCons... eapply step_preserves_record_tm...
Qed.

End STLCExtendedRecords.