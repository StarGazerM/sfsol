Add LoadPath "D:\sfsol".
Require Export Smallstep.

Module STLCRef.

Inductive ty : Type :=
  | TNat : ty
  | TUnit : ty
  | TArrow : ty -> ty -> ty
  | TRef : ty -> ty.

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | tnat : nat -> tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tmult : tm -> tm -> tm
  | tif0 : tm -> tm -> tm -> tm
  | tunit : tm
  | tref : tm -> tm
  | tderef : tm -> tm
  | tassign : tm -> tm -> tm
  | tloc : nat -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp"
  | Case_aux c "tabs" | Case_aux c "tzero"
  | Case_aux c "tsucc" | Case_aux c "tpred"
  | Case_aux c "tmult" | Case_aux c "tif0"
  | Case_aux c "tunit" | Case_aux c "tref"
  | Case_aux c "tderef" | Case_aux c "tassign"
  | Case_aux c "tloc" ].

Module ExampleVariables.

Definition x := Id 0.
Definition y := Id 1.
Definition r := Id 2.
Definition s := Id 3.

End ExampleVariables.

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_nat : forall n,
      value (tnat n)
  | v_unit :
      value tunit
  | v_loc : forall l,
      value (tloc l).

Hint Constructors value.

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' =>
      if eq_id_dec x x' then s else t
  | tapp t1 t2 =>
      tapp (subst x s t1) (subst x s t2)
  | tabs x' T t1 =>
      if eq_id_dec x x' then t else tabs x' T (subst x s t1)
  | tnat n =>
      t
  | tsucc t1 =>
      tsucc (subst x s t1)
  | tpred t1 =>
      tpred (subst x s t1)
  | tmult t1 t2 =>
      tmult (subst x s t1) (subst x s t2)
  | tif0 t1 t2 t3 =>
      tif0 (subst x s t1) (subst x s t2) (subst x s t3)
  | tunit =>
      t
  | tref t1 =>
      tref (subst x s t1)
  | tderef t1 =>
      tderef (subst x s t1)
  | tassign t1 t2 =>
      tassign (subst x s t1) (subst x s t2)
  | tloc _ =>
      t
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Definition tseq t1 t2 :=
  tapp (tabs (Id 0) TUnit t2) t1.

Definition store := list tm.

Definition store_lookup (n:nat) (st:store) :=
  nth n st tunit.

Fixpoint snoc {A:Type} (l:list A) (x:A) : list A :=
  match l with
  | nil => x :: nil
  | h :: t => h :: snoc t x
  end.

Lemma length_snoc : forall A (l:list A) x,
  length (snoc l x) = S (length l).
Proof.
  induction l; intros; [ auto | simpl; rewrite IHl; auto ]. Qed.

Lemma nth_lt_snoc : forall A (l:list A) x d n,
  n < length l ->
  nth n l d = nth n (snoc l x) d.
Proof.
  induction l as [|a l']; intros; try solve by inversion.
  Case "l = a :: l'".
    destruct n; auto.
    simpl. apply IHl'.
    simpl in H. apply lt_S_n in H. assumption.
Qed.

Lemma nth_eq_snoc : forall A (l:list A) x d,
  nth (length l) (snoc l x) d = x.
Proof.
  induction l; intros; [ auto | simpl; rewrite IHl; auto ].
Qed.

Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil => nil
  | h :: t =>
    match n with
    | O => x :: t
    | S n' => h :: replace n' x t
    end
  end.

Lemma replace_nil : forall A n (x:A),
  replace n x nil = nil.
Proof.
  destruct n; auto.
Qed.

Lemma length_replace : forall A n x (l:list A),
  length (replace n x l) = length l.
Proof with auto.
  intros A n x l. generalize dependent n.
  induction l; intros n.
    destruct n...
    destruct n...
      simpl. rewrite IHl...
Qed.

Lemma lookup_replace_eq : forall l t st,
  l < length st ->
  store_lookup l (replace l t st) = t.
Proof with auto.
  intros l t st.
  unfold store_lookup.
  generalize dependent l.
  induction st as [|t' st']; intros l Hlen.
  Case "st = []".
   inversion Hlen.
  Case "st = t' :: st'".
    destruct l; simpl...
    apply IHst'. simpl in Hlen. omega.
Qed.

Lemma lookup_replace_neq : forall l1 l2 t st,
  l1 <> l2 ->
  store_lookup l1 (replace l2 t st) = store_lookup l1 st.
Proof with auto.
  unfold store_lookup.
  induction l1 as [|l1']; intros l2 t st Hneq.
  Case "l1 = 0".
    destruct st.
    SCase "st = []". rewrite replace_nil...
    SCase "st = _ :: _". destruct l2... contradict Hneq...
  Case "l1 = S l1'".
    destruct st as [|t2 st2].
    SCase "st = []". destruct l2...
    SCase "st = t2 :: st2".
      destruct l2...
      simpl; apply IHl1'...
Qed.

Reserved Notation "t1 '/' st1 '==>' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

Inductive step : tm * store -> tm * store -> Prop :=
  | ST_AppAbs : forall x T t12 v2 st,
         value v2 ->
         tapp (tabs x T t12) v2 / st ==> [x:=v2]t12 / st
  | ST_App1 : forall t1 t1' t2 st st',
         t1 / st ==> t1' / st' ->
         tapp t1 t2 / st ==> tapp t1' t2 / st'
  | ST_App2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st ==> t2' / st' ->
         tapp v1 t2 / st ==> tapp v1 t2'/ st'
  | ST_SuccNat : forall n st,
         tsucc (tnat n) / st ==> tnat (S n) / st
  | ST_Succ : forall t1 t1' st st',
         t1 / st ==> t1' / st' ->
         tsucc t1 / st ==> tsucc t1' / st'
  | ST_PredNat : forall n st,
         tpred (tnat n) / st ==> tnat (pred n) / st
  | ST_Pred : forall t1 t1' st st',
         t1 / st ==> t1' / st' ->
         tpred t1 / st ==> tpred t1' / st'
  | ST_MultNats : forall n1 n2 st,
         tmult (tnat n1) (tnat n2) / st ==> tnat (mult n1 n2) / st
  | ST_Mult1 : forall t1 t2 t1' st st',
         t1 / st ==> t1' / st' ->
         tmult t1 t2 / st ==> tmult t1' t2 / st'
  | ST_Mult2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st ==> t2' / st' ->
         tmult v1 t2 / st ==> tmult v1 t2' / st'
  | ST_If0 : forall t1 t1' t2 t3 st st',
         t1 / st ==> t1' / st' ->
         tif0 t1 t2 t3 / st ==> tif0 t1' t2 t3 / st'
  | ST_If0_Zero : forall t2 t3 st,
         tif0 (tnat 0) t2 t3 / st ==> t2 / st
  | ST_If0_Nonzero : forall n t2 t3 st,
         tif0 (tnat (S n)) t2 t3 / st ==> t3 / st
  | ST_RefValue : forall v1 st,
         value v1 ->
         tref v1 / st ==> tloc (length st) / snoc st v1
  | ST_Ref : forall t1 t1' st st',
         t1 / st ==> t1' / st' ->
         tref t1 / st ==> tref t1' / st'
  | ST_DerefLoc : forall st l,
         l < length st ->
         tderef (tloc l) / st ==> store_lookup l st / st
  | ST_Deref : forall t1 t1' st st',
         t1 / st ==> t1' / st' ->
         tderef t1 / st ==> tderef t1' / st'
  | ST_Assign : forall v2 l st,
         value v2 ->
         l < length st ->
         tassign (tloc l) v2 / st ==> tunit / replace l v2 st
  | ST_Assign1 : forall t1 t1' t2 st st',
         t1 / st ==> t1' / st' ->
         tassign t1 t2 / st ==> tassign t1' t2 / st'
  | ST_Assign2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st ==> t2' / st' ->
         tassign v1 t2 / st ==> tassign v1 t2' / st'

where "t1 '/' st1 '==>' t2 '/' st2" := (step (t1,st1) (t2,st2)).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1"
  | Case_aux c "ST_App2" | Case_aux c "ST_SuccNat"
  | Case_aux c "ST_Succ" | Case_aux c "ST_PredNat"
  | Case_aux c "ST_Pred" | Case_aux c "ST_MultNats"
  | Case_aux c "ST_Mult1" | Case_aux c "ST_Mult2"
  | Case_aux c "ST_If0" | Case_aux c "ST_If0_Zero"
  | Case_aux c "ST_If0_Nonzero" | Case_aux c "ST_RefValue"
  | Case_aux c "ST_Ref" | Case_aux c "ST_DerefLoc"
  | Case_aux c "ST_Deref" | Case_aux c "ST_Assign"
  | Case_aux c "ST_Assign1" | Case_aux c "ST_Assign2" ].

Hint Constructors step.

Definition multistep := (multi step).
Notation "t1 '/' st '==>*' t2 '/' st'" := (multistep (t1,st) (t2,st'))
  (at level 40, st at level 39, t2 at level 39).

Definition context := partial_map ty.

Definition store_ty := list ty.

Definition store_Tlookup (n:nat) (ST:store_ty) :=
  nth n ST TUnit.

Reserved Notation "Gamma ';' ST '|-' t '\in' T" (at level 40).

Inductive has_type : context -> store_ty -> tm -> ty -> Prop :=
  | T_Var : forall Gamma ST x T,
      Gamma x = Some T ->
      Gamma; ST |- (tvar x) \in T
  | T_Abs : forall Gamma ST x T11 T12 t12,
      (extend Gamma x T11); ST |- t12 \in T12 ->
      Gamma; ST |- (tabs x T11 t12) \in (TArrow T11 T12)
  | T_App : forall T1 T2 Gamma ST t1 t2,
      Gamma; ST |- t1 \in (TArrow T1 T2) ->
      Gamma; ST |- t2 \in T1 ->
      Gamma; ST |- (tapp t1 t2) \in T2
  | T_Nat : forall Gamma ST n,
      Gamma; ST |- (tnat n) \in TNat
  | T_Succ : forall Gamma ST t1,
      Gamma; ST |- t1 \in TNat ->
      Gamma; ST |- (tsucc t1) \in TNat
  | T_Pred : forall Gamma ST t1,
      Gamma; ST |- t1 \in TNat ->
      Gamma; ST |- (tpred t1) \in TNat
  | T_Mult : forall Gamma ST t1 t2,
      Gamma; ST |- t1 \in TNat ->
      Gamma; ST |- t2 \in TNat ->
      Gamma; ST |- (tmult t1 t2) \in TNat
  | T_If0 : forall Gamma ST t1 t2 t3 T,
      Gamma; ST |- t1 \in TNat ->
      Gamma; ST |- t2 \in T ->
      Gamma; ST |- t3 \in T ->
      Gamma; ST |- (tif0 t1 t2 t3) \in T
  | T_Unit : forall Gamma ST,
      Gamma; ST |- tunit \in TUnit
  | T_Loc : forall Gamma ST l,
      l < length ST ->
      Gamma; ST |- (tloc l) \in (TRef (store_Tlookup l ST))
  | T_Ref : forall Gamma ST t1 T1,
      Gamma; ST |- t1 \in T1 ->
      Gamma; ST |- (tref t1) \in (TRef T1)
  | T_Deref : forall Gamma ST t1 T11,
      Gamma; ST |- t1 \in (TRef T11) ->
      Gamma; ST |- (tderef t1) \in T11
  | T_Assign : forall Gamma ST t1 t2 T11,
      Gamma; ST |- t1 \in (TRef T11) ->
      Gamma; ST |- t2 \in T11 ->
      Gamma; ST |- (tassign t1 t2) \in TUnit

where "Gamma ';' ST '|-' t '\in' T" := (has_type Gamma ST t T).

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
  | Case_aux c "T_Nat" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
  | Case_aux c "T_Mult" | Case_aux c "T_If0"
  | Case_aux c "T_Unit" | Case_aux c "T_Loc"
  | Case_aux c "T_Ref" | Case_aux c "T_Deref"
  | Case_aux c "T_Assign" ].

Definition store_well_typed (ST:store_ty) (st:store) :=
  length ST = length st /\
  (forall l, l < length st ->
     empty; ST |- (store_lookup l st) \in (store_Tlookup l ST)).

Inductive extends : store_ty -> store_ty -> Prop :=
  | extends_nil : forall ST',
      extends ST' nil
  | extends_cons : forall x ST' ST,
      extends ST' ST ->
      extends (x::ST') (x::ST).

Hint Constructors extends.

Lemma extends_lookup : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  store_Tlookup l ST' = store_Tlookup l ST.
Proof with auto.
  intros l ST ST' Hlen H.
  generalize dependent ST'. generalize dependent l.
  induction ST as [|a ST2]; intros l Hlen ST' HST'.
  Case "nil". inversion Hlen.
  Case "cons". unfold store_Tlookup in *.
    destruct ST'.
    SCase "ST' = nil". inversion HST'.
    SCase "ST' = a' :: ST'2".
      inversion HST'; subst.
      destruct l as [|l'].
      SSCase "l = 0"...
      SSCase "l = S l'". simpl. apply IHST2...
        simpl in Hlen; omega.
Qed.

Lemma length_extends : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  l < length ST'.
Proof with eauto.
  intros. generalize dependent l. induction H0; intros l Hlen.
    inversion Hlen.
    simpl in *.
    destruct l; try omega.
      apply lt_n_S. apply IHextends. omega.
Qed.

Lemma extends_snoc : forall ST T,
  extends (snoc ST T) ST.
Proof with auto.
  induction ST; intros T...
  simpl...
Qed.

Lemma extends_refl : forall ST,
  extends ST ST.
Proof.
  induction ST; auto.
Qed.

Definition preservation_theorem := forall ST t t' T st st',
  empty; ST |- t \in T ->
  store_well_typed ST st ->
  t / st ==> t' / st' ->
  exists ST',
    (extends ST' ST /\
     empty; ST' |- t' \in T /\
     store_well_typed ST' st').

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
  | afi_succ : forall x t1,
      appears_free_in x t1 ->
      appears_free_in x (tsucc t1)
  | afi_pred : forall x t1,
      appears_free_in x t1 ->
      appears_free_in x (tpred t1)
  | afi_mult1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tmult t1 t2)
  | afi_mult2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tmult t1 t2)
  | afi_if0_1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tif0 t1 t2 t3)
  | afi_if0_2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tif0 t1 t2 t3)
  | afi_if0_3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tif0 t1 t2 t3)
  | afi_ref : forall x t1,
      appears_free_in x t1 -> appears_free_in x (tref t1)
  | afi_deref : forall x t1,
      appears_free_in x t1 -> appears_free_in x (tderef t1)
  | afi_assign1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tassign t1 t2)
  | afi_assign2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tassign t1 t2).

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var"
  | Case_aux c "afi_app1" | Case_aux c "afi_app2" | Case_aux c "afi_abs"
  | Case_aux c "afi_succ" | Case_aux c "afi_pred"
  | Case_aux c "afi_mult1" | Case_aux c "afi_mult2"
  | Case_aux c "afi_if0_1" | Case_aux c "afi_if0_2" | Case_aux c "afi_if0_3"
  | Case_aux c "afi_ref" | Case_aux c "afi_deref"
  | Case_aux c "afi_assign1" | Case_aux c "afi_assign2" ].

Hint Constructors appears_free_in.

Lemma free_in_context : forall x t T Gamma ST,
   appears_free_in x t ->
   Gamma; ST |- t \in T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros. generalize dependent Gamma. generalize dependent T.
  afi_cases (induction H) Case;
        intros; (try solve [ inversion H0; subst; eauto ]).
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H8.
    rewrite extend_neq in H8; assumption.
Qed.

Lemma context_invariance : forall Gamma Gamma' ST t T,
  Gamma; ST |- t \in T ->
  (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
  Gamma'; ST |- t \in T.
Proof with eauto.
  intros.
  generalize dependent Gamma'.
  has_type_cases (induction H) Case; intros...
  Case "T_Var".
    apply T_Var. symmetry. rewrite <- H...
  Case "T_Abs".
    apply T_Abs. apply IHhas_type; intros.
    unfold extend.
    destruct (eq_id_dec x x0)...
  Case "T_App".
    eapply T_App.
      apply IHhas_type1...
      apply IHhas_type2...
  Case "T_Mult".
    eapply T_Mult.
      apply IHhas_type1...
      apply IHhas_type2...
  Case "T_If0".
    eapply T_If0.
      apply IHhas_type1...
      apply IHhas_type2...
      apply IHhas_type3...
  Case "T_Assign".
    eapply T_Assign.
      apply IHhas_type1...
      apply IHhas_type2...
Qed.

Lemma substitution_preserves_typing : forall Gamma ST x s S t T,
  empty; ST |- s \in S ->
  (extend Gamma x S); ST |- t \in T ->
  Gamma; ST |- ([x:=s]t) \in T.
Proof with eauto.
  intros Gamma ST x s S t T Hs Ht.
  generalize dependent Gamma. generalize dependent T.
  t_cases (induction t) Case; intros T Gamma H;
    inversion H; subst; simpl...
  Case "tvar".
    rename i into y.
    destruct (eq_id_dec x y).
    SCase "x = y".
      subst.
      rewrite extend_eq in H3.
      inversion H3; subst.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ _ _ _ Hcontra Hs) as [T' HT'].
      inversion HT'.
    SCase "x <> y".
      apply T_Var.
      rewrite extend_neq in H3...
  Case "tabs". subst.
    rename i into y.
    destruct (eq_id_dec x y).
    SCase "x = y".
      subst.
      apply T_Abs. eapply context_invariance...
      intros. apply extend_shadow.
    SCase "x <> x0".
      apply T_Abs. apply IHt.
      eapply context_invariance...
      intros. unfold extend.
      destruct (eq_id_dec y x0)...
      subst.
      rewrite neq_id...
Qed.

Lemma assign_pres_store_typing : forall ST st l t,
  l < length st ->
  store_well_typed ST st ->
  empty; ST |- t \in (store_Tlookup l ST) ->
  store_well_typed ST (replace l t st).
Proof with auto.
  intros ST st l t Hlen HST Ht.
  inversion HST; subst.
  split. rewrite length_replace...
  intros l' Hl'.
  destruct (beq_nat l' l) eqn: Heqll'.
  Case "l' = l".
    apply beq_nat_true in Heqll'; subst.
    rewrite lookup_replace_eq...
  Case "l' <> l".
    apply beq_nat_false in Heqll'.
    rewrite lookup_replace_neq...
    rewrite length_replace in Hl'.
    apply H0...
Qed.

Lemma store_weakening : forall Gamma ST ST' t T,
  extends ST' ST ->
  Gamma; ST |- t \in T ->
  Gamma; ST' |- t \in T.
Proof with eauto.
  intros. has_type_cases (induction H0) Case; eauto.
  Case "T_Loc".
    erewrite <- extends_lookup...
    apply T_Loc.
    eapply length_extends...
Qed.

Lemma store_well_typed_snoc : forall ST st t1 T1,
  store_well_typed ST st ->
  empty; ST |- t1 \in T1 ->
  store_well_typed (snoc ST T1) (snoc st t1).
Proof with auto.
  intros.
  unfold store_well_typed in *.
  inversion H as [Hlen Hmatch]; clear H.
  rewrite !length_snoc.
  split...
  Case "types match.".
    intros l Hl.
    unfold store_lookup, store_Tlookup.
    apply le_lt_eq_dec in Hl; inversion Hl as [Hlt | Heq].
    SCase "l < length st".
      apply lt_S_n in Hlt.
      rewrite <- !nth_lt_snoc...
      apply store_weakening with ST. apply extends_snoc.
      apply Hmatch...
      rewrite Hlen...
    SCase "l = length st".
      inversion Heq.
      rewrite nth_eq_snoc.
      rewrite <- Hlen. rewrite nth_eq_snoc...
      apply store_weakening with ST... apply extends_snoc.
Qed.

Theorem preservation : forall ST t t' T st st',
  empty; ST |- t \in T ->
  store_well_typed ST st ->
  t / st ==> t' / st' ->
  exists ST',
    (extends ST' ST /\
     empty; ST' |- t' \in T /\
     store_well_typed ST' st').
Proof with eauto using store_weakening, extends_refl.
    remember (@empty ty) as Gamma.
  intros ST t t' T st st' Ht.
  generalize dependent t'.
  has_type_cases (induction Ht) Case; intros t' HST Hstep;
    subst; try (solve by inversion); inversion Hstep; subst;
    try (eauto using store_weakening, extends_refl).
  Case "T_App".
    SCase "ST_AppAbs". exists ST.
      inversion Ht1; subst.
      split; try split... eapply substitution_preserves_typing...
    SCase "ST_App1".
      eapply IHHt1 in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
    SCase "ST_App2".
      eapply IHHt2 in H5...
      inversion H5 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  Case "T_Succ".
    SCase "ST_Succ".
      eapply IHHt in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  Case "T_Pred".
    SCase "ST_Pred".
      eapply IHHt in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  Case "T_Mult".
    SCase "ST_Mult1".
      eapply IHHt1 in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
    SCase "ST_Mult2".
      eapply IHHt2 in H5...
      inversion H5 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  Case "T_If0".
    SCase "ST_If0_1".
      eapply IHHt1 in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'... split...
  Case "T_Ref".
    SCase "ST_RefValue".
      exists (snoc ST T1).
      inversion HST; subst.
      split.
        apply extends_snoc.
      split.
        replace (TRef T1)
          with (TRef (store_Tlookup (length st) (snoc ST T1))).
        apply T_Loc.
        rewrite <- H. rewrite length_snoc. omega.
        unfold store_Tlookup. rewrite <- H. rewrite nth_eq_snoc...
        apply store_well_typed_snoc; assumption.
    SCase "ST_Ref".
      eapply IHHt in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  Case "T_Deref".
    SCase "ST_DerefLoc".
      exists ST. split; try split...
      inversion HST as [_ Hsty].
      replace T11 with (store_Tlookup l ST).
      apply Hsty...
      inversion Ht; subst...
    SCase "ST_Deref".
      eapply IHHt in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  Case "T_Assign".
    SCase "ST_Assign".
      exists ST. split; try split...
      eapply assign_pres_store_typing...
      inversion Ht1; subst...
    SCase "ST_Assign1".
      eapply IHHt1 in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
    SCase "ST_Assign2".
      eapply IHHt2 in H5...
      inversion H5 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
Qed.

Theorem progress : forall ST t T st,
  empty; ST |- t \in T ->
  store_well_typed ST st ->
  (value t \/ exists t', exists st', t / st ==> t' / st').
Proof with eauto.
    intros ST t T st Ht HST. remember (@empty ty) as Gamma.
  has_type_cases (induction Ht) Case; subst; try solve by inversion...
  Case "T_App".
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    SCase "t1 is a value".
      inversion Ht1p; subst; try solve by inversion.
      destruct IHHt2 as [Ht2p | Ht2p]...
      SSCase "t2 steps".
        inversion Ht2p as [t2' [st' Hstep]].
        exists (tapp (tabs x T t) t2'). exists st'...
    SCase "t1 steps".
      inversion Ht1p as [t1' [st' Hstep]].
      exists (tapp t1' t2). exists st'...
  Case "T_Succ".
    right. destruct IHHt as [Ht1p | Ht1p]...
    SCase "t1 is a value".
      inversion Ht1p; subst; try solve [ inversion Ht ].
      SSCase "t1 is a tnat".
        exists (tnat (S n)). exists st...
    SCase "t1 steps".
      inversion Ht1p as [t1' [st' Hstep]].
      exists (tsucc t1'). exists st'...
  Case "T_Pred".
    right. destruct IHHt as [Ht1p | Ht1p]...
    SCase "t1 is a value".
      inversion Ht1p; subst; try solve [inversion Ht ].
      SSCase "t1 is a tnat".
        exists (tnat (pred n)). exists st...
    SCase "t1 steps".
      inversion Ht1p as [t1' [st' Hstep]].
      exists (tpred t1'). exists st'...
  Case "T_Mult".
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    SCase "t1 is a value".
      inversion Ht1p; subst; try solve [inversion Ht1].
      destruct IHHt2 as [Ht2p | Ht2p]...
      SSCase "t2 is a value".
        inversion Ht2p; subst; try solve [inversion Ht2].
        exists (tnat (mult n n0)). exists st...
      SSCase "t2 steps".
        inversion Ht2p as [t2' [st' Hstep]].
        exists (tmult (tnat n) t2'). exists st'...
    SCase "t1 steps".
      inversion Ht1p as [t1' [st' Hstep]].
      exists (tmult t1' t2). exists st'...
  Case "T_If0".
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    SCase "t1 is a value".
      inversion Ht1p; subst; try solve [inversion Ht1].
      destruct n.
      SSCase "n = 0". exists t2. exists st...
      SSCase "n = S n'". exists t3. exists st...
    SCase "t1 steps".
      inversion Ht1p as [t1' [st' Hstep]].
      exists (tif0 t1' t2 t3). exists st'...
  Case "T_Ref".
    right. destruct IHHt as [Ht1p | Ht1p]...
    SCase "t1 steps".
      inversion Ht1p as [t1' [st' Hstep]].
      exists (tref t1'). exists st'...
  Case "T_Deref".
    right. destruct IHHt as [Ht1p | Ht1p]...
    SCase "t1 is a value".
      inversion Ht1p; subst; try solve by inversion.
      eexists. eexists. apply ST_DerefLoc...
      inversion Ht; subst. inversion HST; subst.
      rewrite <- H...
    SCase "t1 steps".
      inversion Ht1p as [t1' [st' Hstep]].
      exists (tderef t1'). exists st'...
  Case "T_Assign".
    right. destruct IHHt1 as [Ht1p|Ht1p]...
    SCase "t1 is a value".
      destruct IHHt2 as [Ht2p|Ht2p]...
      SSCase "t2 is a value".
        inversion Ht1p; subst; try solve by inversion.
        eexists. eexists. apply ST_Assign...
        inversion HST; subst. inversion Ht1; subst.
        rewrite H in H5...
      SSCase "t2 steps".
        inversion Ht2p as [t2' [st' Hstep]].
        exists (tassign t1 t2'). exists st'...
    SCase "t1 steps".
      inversion Ht1p as [t1' [st' Hstep]].
      exists (tassign t1' t2). exists st'...
Qed.

Section RefsAndNontermination.
Import ExampleVariables.

Definition loop_fun :=
  tabs x TUnit (tapp (tderef (tvar r)) tunit).

Definition loop :=
  tapp
  (tabs r (TRef (TArrow TUnit TUnit))
    (tseq (tassign (tvar r) loop_fun)
            (tapp (tderef (tvar r)) tunit)))
  (tref (tabs x TUnit tunit)).

Lemma loop_typeable : exists T, empty; nil |- loop \in T.
Proof with eauto.
  eexists. unfold loop. unfold loop_fun.
  eapply T_App...
  eapply T_Abs...
  eapply T_App...
    eapply T_Abs. eapply T_App. eapply T_Deref. eapply T_Var.
    unfold extend. simpl. reflexivity. auto.
  eapply T_Assign.
    eapply T_Var. unfold extend. simpl. reflexivity.
  eapply T_Abs.
    eapply T_App...
      eapply T_Deref. eapply T_Var. reflexivity.
Qed.

Inductive step_closure {X:Type} (R: relation X) : X -> X -> Prop :=
  | sc_one : forall (x y : X),
                R x y -> step_closure R x y
  | sc_step : forall (x y z : X),
                R x y ->
                step_closure R y z ->
                step_closure R x z.

Definition multistep1 := (step_closure step).
Notation "t1 '/' st '==>+' t2 '/' st'" := (multistep1 (t1,st) (t2,st'))
  (at level 40, st at level 39, t2 at level 39).

Ltac print_goal := match goal with |- ?x => idtac x end.
Ltac reduce :=
    repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; compute)];
            try solve [apply multi_refl]).

Lemma loop_steps_to_loop_fun :
  loop / nil ==>*
  tapp (tderef (tloc 0)) tunit / cons ([r:=tloc 0]loop_fun) nil.
Proof with eauto.
  unfold loop.
  reduce.
Qed.

Lemma loop_fun_step_self :
  tapp (tderef (tloc 0)) tunit / cons ([r:=tloc 0]loop_fun) nil ==>+
  tapp (tderef (tloc 0)) tunit / cons ([r:=tloc 0]loop_fun) nil.
Proof with eauto.
  unfold loop_fun; simpl.
  eapply sc_step. apply ST_App1...
  eapply sc_one. compute. apply ST_AppAbs...
Qed.

Definition factorial_intermediate :=
  tabs x TNat (tif0 (tvar x) (tnat 1) (tmult (tvar x) (tapp (tderef (tvar r)) (tpred (tvar x))))).

Definition factorial : tm :=
  tabs y TNat (tapp
    (tabs r (TRef (TArrow TNat TNat)) 
    ( tseq (tassign (tvar r) factorial_intermediate)
      (tapp factorial_intermediate (tvar y))))
    (tref (tabs s TNat (tnat 0)))).

Lemma factorial_type : empty; nil |- factorial \in (TArrow TNat TNat).
Proof with eauto.
  unfold factorial; repeat (econstructor;eauto).
  Qed.

Lemma factorial_4 : exists st, 
  tapp factorial (tnat 4) / nil ==>* tnat 24 / st.
Proof.
  eexists. unfold factorial. reduce.
Qed.

End RefsAndNontermination.
End STLCRef.