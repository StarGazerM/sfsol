Add LoadPath "D:\sfsol".
Require Export Stlc.

Module STLCExtended.

Inductive ty : Type :=
  | TArrow : ty -> ty -> ty
  | TNat : ty
  | TUnit : ty
  | TProd : ty -> ty -> ty
  | TSum : ty -> ty -> ty
  | TList : ty -> ty.

Tactic Notation "T_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TArrow" | Case_aux c "TNat"
  | Case_aux c "TProd" | Case_aux c "TUnit"
  | Case_aux c "TSum" | Case_aux c "TList" ].

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | tnat : nat -> tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tmult : tm -> tm -> tm
  | tif0 : tm -> tm -> tm -> tm
  | tpair : tm -> tm -> tm
  | tfst : tm -> tm
  | tsnd : tm -> tm
  | tunit : tm
  | tlet : id -> tm -> tm -> tm
  | tinl : ty -> tm -> tm
  | tinr : ty -> tm -> tm
  | tcase : tm -> id -> tm -> id -> tm -> tm
  | tnil : ty -> tm
  | tcons : tm -> tm -> tm
  | tlcase : tm -> tm -> id -> id -> tm -> tm
  | tfix : tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" | Case_aux c "tabs"
  | Case_aux c "tnat" | Case_aux c "tsucc" | Case_aux c "tpred"
  | Case_aux c "tmult" | Case_aux c "tif0"
  | Case_aux c "tpair" | Case_aux c "tfst" | Case_aux c "tsnd"
  | Case_aux c "tunit" | Case_aux c "tlet"
  | Case_aux c "tinl" | Case_aux c "tinr" | Case_aux c "tcase"
  | Case_aux c "tnil" | Case_aux c "tcons" | Case_aux c "tlcase"
  | Case_aux c "tfix" ].

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar y =>
      if eq_id_dec x y then s else t
  | tabs y T t1 =>
      tabs y T (if eq_id_dec x y then t1 else (subst x s t1))
  | tapp t1 t2 =>
      tapp (subst x s t1) (subst x s t2)
  | tnat x => tnat x
  | tsucc t => tsucc (subst x s t)
  | tpred t => tpred (subst x s t)
  | tmult t1 t2 => tmult (subst x s t1) (subst x s t2)
  | tif0 t1 t2 t3 => tif0 (subst x s t1) (subst x s t2)(subst x s t3)
  | tpair t1 t2 => tpair (subst x s t1) (subst x s t2)
  | tfst t1 => tfst (subst x s t1)
  | tsnd t1 => tsnd (subst x s t1)
  | tunit => tunit
  | tlet y t1 t2 => if eq_id_dec x y then 
      tlet y (subst x s t1) t2 else
      tlet y (subst x s t1) (subst x s t2)
  | tinl T t => tinl T (subst x s t)
  | tinr T t => tinr T (subst x s t)
  | tcase t x1 t1 x2 t2 => if eq_id_dec x x1 then
      if eq_id_dec x x2 then
        tcase (subst x s t) x1 t1 x2 t2 else
        tcase (subst x s t) x1 t1 x2 (subst x s t2)
      else if eq_id_dec x x2 then
        tcase (subst x s t) x1 (subst x s t1) x2 t2 else
        tcase (subst x s t) x1 (subst x s t1) x2 (subst x s t2)
  | tnil T => tnil T
  | tcons t1 t2 => tcons (subst x s t1) (subst x s t2)
  | tlcase t1 t2 x1 x2 t3 => if eq_id_dec x x1 then
      tlcase (subst x s t1) (subst x s t2) x1 x2 t3
      else if eq_id_dec x x2 then
      tlcase (subst x s t1) (subst x s t2) x1 x2 t3
      else tlcase (subst x s t1) (subst x s t2) x1 x2 (subst x s t3)
  | tfix t => tfix (subst x s t)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Inductive value : tm -> Prop :=
  | v_abs : forall x T11 t12,
      value (tabs x T11 t12)
  | v_nat : forall x,
      value (tnat x)
  | v_unit : value tunit
  | v_pair : forall t1 t2,
      value t1 ->
      value t2 ->
      value (tpair t1 t2)
  | v_inl : forall T t,
      value t ->
      value (tinl T t)
  | v_inr : forall T t,
      value t ->
      value (tinr T t)
  | v_nil : forall T,
      value (tnil T)
  | v_cons : forall t1 t2,
      value t1 ->
      value t2 ->
      value (tcons t1 t2).

Hint Constructors value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T11 t12 v2,
         value v2 ->
         (tapp (tabs x T11 t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         (tapp t1 t2) ==> (tapp t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         (tapp v1 t2) ==> (tapp v1 t2')
  | ST_Succ : forall t t',
         t ==> t' ->
         tsucc t ==> tsucc t'
  | ST_SuccNat : forall x,
         tsucc (tnat x) ==> tnat (S x)
  | ST_Pred : forall t t',
         t ==> t' ->
         tpred t ==> tpred t'
  | ST_PredNat : forall x,
         tpred (tnat x) ==> tnat (pred x)
  | ST_Mult1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tmult t1 t2 ==> tmult t1' t2
  | ST_Mult2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         tmult v1 t2 ==> tmult v1 t2'
  | ST_MultNat : forall x1 x2,
         tmult (tnat x1) (tnat x2) ==> tnat (mult x1 x2)
  | ST_IF0_Cond : forall t1 t1' t2 t3,
         t1 ==> t1' ->
         tif0 t1 t2 t3 ==> tif0 t1' t2 t3
  | ST_If0_If : forall t1 t2,
         tif0 (tnat 0) t1 t2 ==> t1
  | ST_If0_Else : forall x t1 t2,
         x <> 0 ->
         tif0 (tnat x) t1 t2 ==> t2
  | ST_Pair1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tpair t1 t2 ==> tpair t1' t2
  | ST_Pair2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         tpair v1 t2 ==> tpair v1 t2'
  | ST_First_Pair : forall t1 t2,
         tfst (tpair t1 t2) ==> t1
  | ST_Second_Pair : forall t1 t2,
         tsnd (tpair t1 t2) ==> t2
  | ST_First : forall t t',
         t ==> t' ->
         tfst t ==> tfst t'
  | ST_Second : forall t t',
         t ==> t' ->
         tsnd t ==> tsnd t'
  | ST_Let1 : forall x t1 t1' t2,
         t1 ==> t1' ->
         tlet x t1 t2 ==> tlet x t1' t2
  | ST_LetValue : forall x v1 t2,
         value v1 ->
         tlet x v1 t2 ==> [x:=v1]t2
  | ST_Inl : forall T t t',
         t ==> t' ->
         tinl T t ==> tinl T t'
  | ST_Inr : forall T t t',
         t ==> t' ->
         tinr T t ==> tinr T t'
  | ST_Case : forall t t' x1 t1 x2 t2,
         t ==> t' ->
         tcase t x1 t1 x2 t2 ==> tcase t' x1 t1 x2 t2
  | ST_CaseInl : forall T t x1 t1 x2 t2,
         tcase (tinl T t) x1 t1 x2 t2 ==> [x1:=t]t1
  | ST_CaseInr : forall T t x1 t1 x2 t2,
         tcase (tinr T t) x1 t1 x2 t2 ==> [x2:=t]t2
  | ST_Cons : forall t t' t2,
         t ==> t' ->
         tcons t t2 ==> tcons t' t2
  | ST_ConsValue : forall v1 t t',
         value v1 ->
         t ==> t' ->
         tcons v1 t ==> tcons v1 t'
  | ST_LCase1 : forall t1 t1' t2 x1 x2 t3,
         t1 ==> t1' ->
         tlcase t1 t2 x1 x2 t3 ==> tlcase t1' t2 x1 x2 t3
  | ST_LCaseNil : forall T t2 x1 x2 t3,
         tlcase (tnil T) t2 x1 x2 t3 ==> t2
  | ST_LCaseCons : forall t2 x1 x2 t3 v1 v2,
         value v1 ->
         value v2 ->
         tlcase (tcons v1 v2) t2 x1 x2 t3 ==>
         [x1:=v1]([x2:=v2]t3)
  | ST_Fix1 : forall t1 t1',
         t1 ==> t1' ->
         tfix t1 ==> tfix t1'
  | ST_FixAbs : forall x T t,
         tfix (tabs x T t) ==> [x:=tfix (tabs x T t)]t

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" | Case_aux c "ST_App2"
    | Case_aux c "ST_Succ" | Case_aux c "ST_Pred"
    | Case_aux c "ST_Mult1" | Case_aux c "ST_Mult2"
    | Case_aux c "ST_IF0_Cond" | Case_aux c "ST_IF0_If"
    | Case_aux c "ST_IF0_Else" | Case_aux c "ST_Pair1"
    | Case_aux c "ST_Pair2" | Case_aux c "ST_FirstPair"
    | Case_aux c "ST_SecondPair" | Case_aux c "ST_First"
    | Case_aux c "ST_Second" | Case_aux c "ST_Let1"
    | Case_aux c "ST_LetValue" | Case_aux c "ST_Inl"
    | Case_aux c "ST_Inr" | Case_aux c "ST_Case"
    | Case_aux c "ST_CaseInl" | Case_aux c "ST_CaseInr"
    | Case_aux c "ST_Cons" | Case_aux c "ST_ConsValue"
    | Case_aux c "ST_LCase1" | Case_aux c "ST_LCaseNil"
    | Case_aux c "ST_LCaseCons" | Case_aux c "ST_Fix1"
    | Case_aux c "ST_FixAbs"
  ].

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step.

Definition context := partial_map ty.

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
  | T_Nat : forall Gamma x,
      Gamma |- tnat x \in TNat
  | T_Succ : forall Gamma t,
      Gamma |- t \in TNat ->
      Gamma |- tsucc t \in TNat
  | T_Pred : forall Gamma t,
      Gamma |- t \in TNat ->
      Gamma |- tpred t \in TNat
  | T_Mult : forall Gamma t1 t2,
      Gamma |- t1 \in TNat ->
      Gamma |- t2 \in TNat ->
      Gamma |- tmult t1 t2 \in TNat
  | T_If : forall Gamma t1 t2 t3 T,
      Gamma |- t1 \in TNat ->
      Gamma |- t2 \in T ->
      Gamma |- t3 \in T ->
      Gamma |- tif0 t1 t2 t3 \in T
  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in T2 ->
      Gamma |- (tpair t1 t2) \in (TProd T1 T2)
  | T_First : forall Gamma t T1 T2,
      Gamma |- t \in (TProd T1 T2) ->
      Gamma |- tfst t \in T1
  | T_Second : forall Gamma t T1 T2,
      Gamma |- t \in (TProd T1 T2) ->
      Gamma |- tsnd t \in T2
  | T_Unit : forall Gamma,
      Gamma |- tunit \in TUnit
  | T_Let : forall Gamma x t1 T1 t2 T2,
      Gamma |- t1 \in T1 ->
      extend Gamma x T1 |- t2 \in T2 ->
      Gamma |- tlet x t1 t2 \in T2
  | T_Inl : forall Gamma t T1 T2,
      Gamma |- t \in T1 ->
      Gamma |- tinl T2 t \in TSum T1 T2
  | T_Inr : forall Gamma t T1 T2,
      Gamma |- t \in T2 ->
      Gamma |- tinr T1 t \in TSum T1 T2
  | T_Case : forall Gamma t0 T1 T2 x1 x2 t1 t2 T,
      Gamma |- t0 \in TSum T1 T2 ->
      extend Gamma x1 T1 |- t1 \in T ->
      extend Gamma x2 T2 |- t2 \in T ->
      Gamma |- tcase t0 x1 t1 x2 t2 \in T
  | T_Nil : forall Gamma T,
      Gamma |- tnil T \in TList T
  | T_Cons : forall Gamma t1 t2 T,
      Gamma |- t1 \in T ->
      Gamma |- t2 \in TList T ->
      Gamma |- tcons t1 t2 \in TList T
  | T_LCase : forall Gamma h t t1 t2 t3 T1 T,
      Gamma |- t1 \in TList T1 ->
      Gamma |- t2 \in T ->
      extend (extend Gamma h T1) t (TList T1) |- t3 \in T ->
      Gamma |- tlcase t1 t2 h t t3 \in T
  | T_Fix : forall Gamma t1 T1,
      Gamma |- t1 \in TArrow T1 T1 ->
      Gamma |- tfix t1 \in T1

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
    | Case_aux c "T_Nat" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
    | Case_aux c "T_Mult" | Case_aux c "T_If" | Case_aux c "T_Pair"
    | Case_aux c "T_First" | Case_aux c "T_Second" | Case_aux c "T_Unit"
    | Case_aux c "T_Let" | Case_aux c "T_Inl" | Case_aux c "T_Inr"
    | Case_aux c "T_Case" | Case_aux c "T_Nil" | Case_aux c "T_Cons"
    | Case_aux c "T_LCase" | Case_aux c "T_Fix"
].

Module Examples.

Notation a := (Id 0).
Notation f := (Id 1).
Notation g := (Id 2).
Notation l := (Id 3).
Notation k := (Id 6).
Notation i1 := (Id 7).
Notation i2 := (Id 8).
Notation x := (Id 9).
Notation y := (Id 10).
Notation processSum := (Id 11).
Notation n := (Id 12).
Notation eq := (Id 13).
Notation m := (Id 14).
Notation evenodd := (Id 15).
Notation even := (Id 16).
Notation odd := (Id 17).
Notation eo := (Id 18).

Hint Extern 2 (has_type _ (tapp _ _) _) =>
  eapply T_App; auto.

Hint Extern 2 (has_type _ (tlcase _ _ _ _ _) _) => 
  eapply T_LCase; auto.

Hint Extern 2 (_ = _) => compute; reflexivity.

Module Numtest.

Definition test :=
  tif0
    (tpred
      (tsucc
        (tpred
          (tmult
            (tnat 2)
            (tnat 0)))))
    (tnat 5)
    (tnat 6).

Example typechecks :
  (@empty ty) |- test \in TNat.
Proof.
  unfold test.
  auto 10. 
Qed.

Example numtest_reduces :
  test ==>* tnat 5.
Proof.
  unfold test. normalize.
Qed.

End Numtest.

Module Prodtest.

Definition test :=
  tsnd
    (tfst
      (tpair
        (tpair
          (tnat 5)
          (tnat 6))
        (tnat 7))).

Example typechecks :
  (@empty ty) |- test \in TNat.
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test ==>* tnat 6.
Proof. unfold test. normalize. Qed.

End Prodtest.

Module LetTest.

Definition test :=
  tlet
    x
    (tpred (tnat 6))
    (tsucc (tvar x)).

Example typechecks :
  (@empty ty) |- test \in TNat.
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test ==>* tnat 6.
Proof. unfold test. normalize. Qed.

End LetTest.

Module Sumtest1.

Definition test :=
  tcase (tinl TNat (tnat 5))
    x (tvar x)
    y (tvar y).

Example typechecks :
  (@empty ty) |- test \in TNat.
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test ==>* (tnat 5).
Proof. unfold test. normalize. Qed.

End Sumtest1.

Module Sumtest2.

Definition test :=
  tlet
    processSum
    (tabs x (TSum TNat TNat)
      (tcase (tvar x)
         n (tvar n)
         n (tif0 (tvar n) (tnat 1) (tnat 0))))
    (tpair
      (tapp (tvar processSum) (tinl TNat (tnat 5)))
      (tapp (tvar processSum) (tinr TNat (tnat 5)))).

Example typechecks :
  (@empty ty) |- test \in (TProd TNat TNat).
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test ==>* (tpair (tnat 5) (tnat 0)).
Proof. unfold test. normalize. Qed.

End Sumtest2.

Module ListTest.

Definition test :=
  tlet l
    (tcons (tnat 5) (tcons (tnat 6) (tnil TNat)))
    (tlcase (tvar l)
       (tnat 0)
       x y (tmult (tvar x) (tvar x))).

Example typechecks :
  (@empty ty) |- test \in TNat.
Proof. unfold test. eauto 20. Qed.

Example reduces :
  test ==>* (tnat 25).
Proof. unfold test. normalize. Qed.

End ListTest.

Module FixTest1.

Definition fact :=
  tfix
    (tabs f (TArrow TNat TNat)
      (tabs a TNat
        (tif0
           (tvar a)
           (tnat 1)
           (tmult
              (tvar a)
              (tapp (tvar f) (tpred (tvar a))))))).

Example fact_typechecks :
  (@empty ty) |- fact \in (TArrow TNat TNat).
Proof. unfold fact. auto 10. 
Qed.

Example fact_example: 
  (tapp fact (tnat 4)) ==>* (tnat 24).
Proof. unfold fact. normalize. Qed.

End FixTest1.

Module FixTest2.

Definition map :=
  tabs g (TArrow TNat TNat)
    (tfix
      (tabs f (TArrow (TList TNat) (TList TNat))
        (tabs l (TList TNat)
          (tlcase (tvar l)
            (tnil TNat)
            a l (tcons (tapp (tvar g) (tvar a))
                         (tapp (tvar f) (tvar l))))))).

Example map_typechecks :
  empty |- map \in 
    (TArrow (TArrow TNat TNat)
      (TArrow (TList TNat) 
        (TList TNat))).
Proof. unfold map. auto 10. Qed.

Example map_example :
  tapp (tapp map (tabs a TNat (tsucc (tvar a))))
         (tcons (tnat 1) (tcons (tnat 2) (tnil TNat)))
  ==>* (tcons (tnat 2) (tcons (tnat 3) (tnil TNat))).
Proof. unfold map. normalize. Qed.

End FixTest2.

Module FixTest3.

Definition equal :=
  tfix
    (tabs eq (TArrow TNat (TArrow TNat TNat))
      (tabs m TNat
        (tabs n TNat
          (tif0 (tvar m)
            (tif0 (tvar n) (tnat 1) (tnat 0))
            (tif0 (tvar n)
              (tnat 0)
              (tapp (tapp (tvar eq)
                              (tpred (tvar m)))
                      (tpred (tvar n)))))))).

Example equal_typechecks :
  (@empty ty) |- equal \in (TArrow TNat (TArrow TNat TNat)).
Proof. unfold equal. auto 10. 
Qed.

Example equal_example1: 
  (tapp (tapp equal (tnat 4)) (tnat 4)) ==>* (tnat 1).
Proof. unfold equal. normalize. Qed.

Example equal_example2: 
  (tapp (tapp equal (tnat 4)) (tnat 5)) ==>* (tnat 0).
Proof. unfold equal. normalize. Qed.

End FixTest3.

Module FixTest4.

Definition eotest :=
  tlet evenodd
    (tfix
      (tabs eo (TProd (TArrow TNat TNat) (TArrow TNat TNat))
        (tpair
          (tabs n TNat
            (tif0 (tvar n)
              (tnat 1)
              (tapp (tsnd (tvar eo)) (tpred (tvar n)))))
          (tabs n TNat
            (tif0 (tvar n)
              (tnat 0)
              (tapp (tfst (tvar eo)) (tpred (tvar n))))))))
  (tlet even (tfst (tvar evenodd))
  (tlet odd (tsnd (tvar evenodd))
  (tpair
    (tapp (tvar even) (tnat 3))
    (tapp (tvar even) (tnat 4))))).

Example eotest_typechecks :
  (@empty ty) |- eotest \in (TProd TNat TNat).
Proof. unfold eotest. eauto 30. 
Qed.

Example eotest_example1: 
  eotest ==>* (tpair (tnat 0) (tnat 1)).
Proof. unfold eotest. normalize. Qed.

End FixTest4.

End Examples.

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  generalize dependent HeqGamma.
  has_type_cases (induction Ht) Case; intros HeqGamma; subst...
  Case "T_Var".
    inversion H.
  Case "T_App".
    right.
    destruct IHHt1; subst...
      destruct IHHt2; subst...
        inversion H; subst; try (solve by inversion)...
      inversion H0; subst...
      inversion H;subst...
  Case "T_Succ".
    right.
    destruct IHHt; subst...
      inversion H; subst; try (solve by inversion)...
      inversion H...
  Case "T_Pred".
    right.
    destruct IHHt; subst...
      inversion H; subst; try (solve by inversion)...
      inversion H...
  Case "T_Mult".
    right.
    destruct IHHt1; subst...
      inversion H; subst; try (solve by inversion)...
      destruct IHHt2; subst...
        inversion H0; subst; try (solve by inversion)...
        inversion H0...
      inversion H...
  Case "T_If".
    right.
    destruct IHHt1; subst...
      inversion H; subst; try (solve by inversion).
      destruct x...
      inversion H...
  Case "T_Pair".
    destruct IHHt1; subst...
      destruct IHHt2; subst...
        inversion H0...
      inversion H...
  Case "T_First".
    right.
      destruct IHHt; subst...
        inversion H; subst; try (solve by inversion)...
        inversion H...
  Case "T_Second".
    right.
      destruct IHHt; subst...
        inversion H; subst; try (solve by inversion)...
        inversion H...
  Case "T_Let".
    right.
      destruct IHHt1; subst...
        inversion H...
  Case "T_Inl".
    destruct IHHt; subst...
      inversion H; subst; try (solve by inversion)...
  Case "T_Inr".
    destruct IHHt; subst...
      inversion H; subst; try (solve by inversion)...
  Case "T_Case".
    right.
      destruct IHHt1; subst...
        inversion H; subst; try (solve by inversion).
        inversion Ht1...
        inversion Ht1...
        inversion H...
  Case "T_Cons".
    destruct IHHt1; subst...
      destruct IHHt2; subst...
      inversion H0...
      inversion H...
  Case "T_LCase".
    right.
    destruct IHHt1; subst...
      inversion H; subst; try (solve by inversion)...
      inversion H...
  Case "T_Fix".
    right.
      destruct IHHt; subst...
      inversion H; subst; try (solve by inversion)...
      inversion H...
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
  | afi_succ : forall x t,
        appears_free_in x t ->
        appears_free_in x (tsucc t)
  | afi_pred : forall x t,
        appears_free_in x t ->
        appears_free_in x (tpred t)
  | afi_mult1 : forall x t1 t2,
        appears_free_in x t1 -> appears_free_in x (tmult t1 t2)
  | afi_mult2 : forall x t1 t2,
        appears_free_in x t2 -> appears_free_in x (tmult t1 t2)
  | afi_if0_0 : forall x t1 t2 t3,
        appears_free_in x t1 -> appears_free_in x (tif0 t1 t2 t3)
  | afi_if0_1 : forall x t1 t2 t3,
        appears_free_in x t2 -> appears_free_in x (tif0 t1 t2 t3)
  | afi_if0_2 : forall x t1 t2 t3,
        appears_free_in x t3 -> appears_free_in x (tif0 t1 t2 t3)
  | afi_pair1 : forall x t1 t2,
        appears_free_in x t1 -> appears_free_in x (tpair t1 t2)
  | afi_pair2 : forall x t1 t2,
        appears_free_in x t2 -> appears_free_in x (tpair t1 t2)
  | afi_first : forall x t,
        appears_free_in x t -> appears_free_in x (tfst t)
  | afi_second : forall x t,
        appears_free_in x t -> appears_free_in x (tsnd t)
  | afi_Let1 : forall x y t1 t2,
        appears_free_in x t1 -> appears_free_in x (tlet y t1 t2)
  | afi_Let2 : forall x y t1 t2,
        x<>y ->
        appears_free_in x t2 ->
        appears_free_in x (tlet y t1 t2)
  | afi_inl : forall x T t,
        appears_free_in x t -> appears_free_in x (tinl T t)
  | afi_inr : forall x T t,
        appears_free_in x t -> appears_free_in x (tinr T t)
  | afi_case1 : forall x1 x2 x3 t1 t2 t3,
        appears_free_in x1 t1 ->
        appears_free_in x1 (tcase t1 x2 t2 x3 t3)
  | afi_case2 : forall x1 x2 x3 t1 t2 t3,
        x1<>x2 ->
        appears_free_in x1 t2 ->
        appears_free_in x1 (tcase t1 x2 t2 x3 t3)
  | afi_case3 : forall x1 x2 x3 t1 t2 t3,
        x1<>x3 ->
        appears_free_in x1 t3 ->
        appears_free_in x1 (tcase t1 x2 t2 x3 t3)
  | afi_cons1 : forall x t1 t2,
        appears_free_in x t1 ->
        appears_free_in x (tcons t1 t2)
  | afi_cons2 : forall x t1 t2,
        appears_free_in x t2 ->
        appears_free_in x (tcons t1 t2)
  | afi_tlcase1 : forall x1 x2 x3 t1 t2 t3,
        appears_free_in x1 t1 ->
        appears_free_in x1 (tlcase t1 t2 x2 x3 t3)
  | afi_tlcase2 : forall x1 x2 x3 t1 t2 t3,
        appears_free_in x1 t2 ->
        appears_free_in x1 (tlcase t1 t2 x2 x3 t3)
  | afi_tlcase3 : forall x1 x2 x3 t1 t2 t3,
        x1<>x2 -> 
        x1<>x3 -> 
        appears_free_in x1 t3 ->
        appears_free_in x1 (tlcase t1 t2 x2 x3 t3)
  | afi_fix : forall x t,
        appears_free_in x t ->
        appears_free_in x (tfix t).

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
    unfold extend.
    destruct (eq_id_dec x y)...
  Case "T_Mult".
    apply T_Mult...
  Case "T_If".
    apply T_If...
  Case "T_Pair".
    apply T_Pair...
  Case "T_Let".
    eapply T_Let...
    apply IHhas_type2. intros. unfold extend.
    destruct (eq_id_dec x x0)...
  Case "T_Case".
    eapply T_Case...
    apply IHhas_type2. intros. unfold extend.
    destruct (eq_id_dec x1 x)...
    apply IHhas_type3. intros. unfold extend.
    destruct (eq_id_dec x2 x)...
  Case "T_Cons".
    apply T_Cons...
  Case "T_LCase".
    eapply T_LCase...
    apply IHhas_type3. intros. unfold extend.
    destruct (eq_id_dec t x)...
    destruct (eq_id_dec h x)...
Qed.

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
  Case "T_Let".
    apply IHHtyp2 in H4. inversion H4; subst.
    unfold extend in H. rewrite neq_id in H...
  Case "T_Case".
    apply IHHtyp2 in H6. inversion H6; subst.
    unfold extend in H6. rewrite neq_id in H6...
    apply IHHtyp3 in H6. inversion H6; subst.
    unfold extend in H6. rewrite neq_id in H6...
  Case "T_LCase".
    apply IHHtyp3 in H7. inversion H7; subst.
    unfold extend in H. rewrite neq_id in H...
    rewrite neq_id in H...
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
    simpl.
    destruct (eq_id_dec x i).
      subst. unfold extend in H1. rewrite eq_id in H1.
      inversion H1; subst. clear H1.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
      apply T_Var... unfold extend in H1. rewrite neq_id in H1...
  Case "tabs".
    apply T_Abs...
    destruct (eq_id_dec x i).
      eapply context_invariance...
      subst. intros x Hafi. unfold extend.
      destruct (eq_id_dec i x)...
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend.
      destruct (eq_id_dec i z)...
      subst. rewrite neq_id...
  Case "tlet".
    destruct (eq_id_dec x i);
    eapply T_Let; eauto; eapply context_invariance...
    intros. unfold extend. subst. destruct (eq_id_dec i x0)...
    apply IHt2. eapply context_invariance...
    intros. unfold extend. destruct (eq_id_dec i x0); eauto.
    subst. rewrite neq_id...
  Case "tcase".
    destruct (eq_id_dec x i); subst...
      destruct (eq_id_dec i i0); subst; eauto;
        eapply T_Case; eauto; eapply context_invariance; eauto;
        intros; unfold extend.
        destruct (eq_id_dec i0 x)...
        destruct (eq_id_dec i0 x)...
        destruct (eq_id_dec i x)...
      apply IHt3... eapply context_invariance...
      intros. unfold extend. destruct (eq_id_dec i0 x); subst...
      rewrite neq_id...
    destruct (eq_id_dec x i0); subst; eauto;
      eapply T_Case; eauto; eapply context_invariance...
      apply IHt2. eapply context_invariance...
      intros. unfold extend. destruct (eq_id_dec i x); subst...
      rewrite neq_id...
      intros. unfold extend. destruct (eq_id_dec i0 x); subst...
      apply IHt2. eapply context_invariance...
      intros. unfold extend. destruct (eq_id_dec i x0); subst...
      rewrite neq_id...
      apply IHt3. eapply context_invariance...
      intros. unfold extend. destruct (eq_id_dec i0 x0); subst...
      rewrite neq_id...
  Case "tlcase".
    destruct (eq_id_dec x i); subst...
      eapply T_LCase... eapply context_invariance...
      intros. unfold extend. destruct (eq_id_dec i0 x); subst...
      destruct (eq_id_dec i x)...
      destruct (eq_id_dec x i0); subst...
      eapply T_LCase... eapply context_invariance...
      intros; unfold extend. destruct (eq_id_dec i0 x); subst...
      eapply T_LCase... apply IHt3.
      eapply context_invariance... intros.
      unfold extend. destruct(eq_id_dec i0 x0); subst...
      rewrite neq_id...
      destruct (eq_id_dec i x0); subst...
      rewrite neq_id...
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
    apply substitution_preserves_typing with T1...
    inversion HT1...
  Case "T_First".
    inversion HT...
  Case "T_Second".
    inversion HT...
  Case "T_Let".
    eapply substitution_preserves_typing...
  Case "T_Case".
    eapply substitution_preserves_typing...
    inversion HT1...
    eapply substitution_preserves_typing...
    inversion HT1...
  Case "T_LCase".
    eapply substitution_preserves_typing...
    eapply substitution_preserves_typing...
    inversion HT1...
    inversion HT1...
  Case "T_Fix".
    eapply substitution_preserves_typing...
    inversion HT...
  Qed.

End STLCExtended.