Add LoadPath "D:\sfsol".
Require Export SfLib.

Inductive id : Type := 
  Id : nat -> id.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
   intros id1 id2.
   destruct id1 as [n1]. destruct id2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   Case "n1 = n2".
     left. rewrite Heq. reflexivity.
   Case "n1 <> n2".
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined. 

Lemma eq_id : forall (T:Type) x (p q:T), 
              (if eq_id_dec x x then p else q) = p. 
Proof.
  intros. 
  destruct (eq_id_dec x x). 
  Case "x = x". 
    reflexivity.
  Case "x <> x (impossible)". 
    apply ex_falso_quodlibet; apply n; reflexivity. Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> 
               (if eq_id_dec x y then p else q) = q. 
Proof.
  intros. 
  destruct (eq_id_dec x y). 
  Case "x = y (impossible)". 
    subst. apply ex_falso_quodlibet; apply H; reflexivity.
  Case "x <> y". 
    reflexivity. Qed.

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Inductive val : Type :=
| VNat : nat -> val
| VList : list nat -> val.

Definition state := id -> val.

Definition empty_state : state := fun _ => VNat 0.
Definition update (st : state) (X:id) (v : val) : state :=
  fun X' => if eq_id_dec X X' then v else st X'.

Definition asnat (v : val) : nat :=
  match v with
  | VNat n => n
  | VList _ => 0
  end.

Definition aslist (v : val) : list nat :=
  match v with
  | VNat n => []
  | VList xs => xs
  end.

Inductive aexp : Type := 
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | AHead : aexp -> aexp
  | ATail : aexp -> aexp
  | ACons : aexp -> aexp -> aexp
  | ANil  : aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult"
  | Case_aux c "AHead" | Case_aux c "ATail"
  | Case_aux c "ACons" | Case_aux c "ANil" ].

Definition tail (l : list nat) :=
  match l with
  | x::xs => xs
  | [] => []
  end.

Definition head (l : list nat) :=
  match l with
  | x::xs => x
  | [] => 0
  end.

Fixpoint aeval (st : state) (e : aexp) : val :=
  match e with
  | ANum n => VNat n
  | AId i => st i
  | APlus a1 a2   => VNat (asnat (aeval st a1) + asnat (aeval st a2))
  | AMinus a1 a2  => VNat (asnat (aeval st a1) - asnat (aeval st a2))
  | AMult a1 a2   => VNat (asnat (aeval st a1) * asnat (aeval st a2))
  | ATail a => VList (tail (aslist (aeval st a)))
  | AHead a => VNat (head (aslist (aeval st a)))
  | ACons a1 a2 => VList (asnat (aeval st a1) :: aslist (aeval st a2))
  | ANil => VList []
  end. 

Inductive bexp : Type := 
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp
  | BIsCons : aexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
  | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd"
  | Case_aux c "BIsCons" ].

Fixpoint beval (st : state) (e : bexp) : bool :=
  match e with 
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (asnat (aeval st a1)) (asnat (aeval st a2))
  | BLe a1 a2   => ble_nat (asnat (aeval st a1)) (asnat (aeval st a2))
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  | BIsCons a    => match aslist (aeval st a) with
                     | _::_ => true
                     | [] => false
                   end
  end.

Theorem update_eq : forall n V st,
  (update st V n) V = n.
Proof.
  intros n V st.
  unfold update.
  rewrite eq_id. 
  reflexivity.
Qed.

Theorem update_neq : forall V2 V1 n st,
  V2 <> V1 -> 
  (update st V2 n) V1 = (st V1).
Proof.
  intros V2 V1 n st Hneq.
  unfold update.
  rewrite neq_id. 
  reflexivity. 
  assumption. Qed.

Theorem update_shadow : forall x1 x2 k1 k2 (f : state),
   (update  (update f k2 x1) k2 x2) k1 = (update f k2 x2) k1.
Proof.
  intros x1 x2 k1 k2 f.
  unfold update.
  destruct (eq_id_dec k2 k1); reflexivity.  Qed.

Theorem update_same : forall x1 k1 k2 (f : state),
  f k1 = x1 ->
  (update f k1 x1) k2 = f k2.
Proof.
  intros x1 k1 k2 f Heq.
  unfold update. subst.
  destruct (eq_id_dec k1 k2). 
  Case "k1 = k2".
    subst. reflexivity.
  Case "k1 <> k2".
    reflexivity.  Qed.

Theorem update_permute : forall x1 x2 k1 k2 k3 f,
  k2 <> k1 -> 
  (update (update f k2 x1) k1 x2) k3 = (update (update f k1 x2) k2 x1) k3.
Proof.
  intros x1 x2 k1 k2 k3 f H.
  unfold update.
  destruct (eq_id_dec k1 k3); try reflexivity.
  Case "k1 = k3".
      subst. rewrite neq_id. reflexivity. assumption. Qed.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'SKIP'" := 
  CSkip.
Notation "X '::=' a" := 
  (CAss X a) (at level 60).
Notation "c1 ; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Asgn  : forall st a1 n X,
      aeval st a1 = n ->
      (X ::= a1) / st || (update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  || st' ->
      c2 / st' || st'' ->
      (c1 ; c2) / st || st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      c1 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      c2 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      c1 / st || st' ->
      (WHILE b1 DO c1 END) / st' || st'' ->
      (WHILE b1 DO c1 END) / st || st''

  where "c1 '/' st '||' st'" := (ceval st c1 st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Asgn" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].

Definition Assertion := state -> Prop.

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', 
       c / st || st'  ->
       P st  ->
       Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
                                  (at level 90, c at next level) 
                                  : hoare_spec_scope.
Open Scope hoare_spec_scope.

Definition assn_sub X a Q : Assertion :=
  fun (st : state) =>
    Q (update st X (aeval st a)).

Theorem hoare_asgn : forall Q X a,
  {{assn_sub X a Q}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst. 
  Case "b is true".
    apply (HTrue st st'). 
      assumption. 
      split. assumption. 
             apply bexp_eval_true. assumption.
  Case "b is false".
    apply (HFalse st st'). 
      assumption. 
      split. assumption.
             apply bexp_eval_false. assumption. Qed.

Lemma hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (WHILE b DO c END) as wcom.
  ceval_cases (induction He) Case; try (inversion Heqwcom); subst.
  
  Case "E_WhileEnd".
    split. assumption. apply bexp_eval_false.  assumption.

  Case "E_WhileLoop".
    apply IHHe2.  reflexivity.
    apply (Hhoare st st'); try assumption.
      split. assumption. apply bexp_eval_true. assumption.  Qed.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q) (at level 80).
Notation "P <<->> Q" := (P ->> Q /\ Q ->> P) (at level 80).

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st'). 
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP. 
  apply Himp.
  apply (Hhoare st st'). 
  assumption. assumption. Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  intros st st' Hc HP.
  apply HQ'Q. apply (Hht st st'). assumption.
  apply HPP'. assumption. Qed.

Definition list_member :=
  WHILE BIsCons (AId X) DO
    IFB (BEq (AId Y) (AHead (AId X))) THEN
      Z ::= (ANum 1)
    ELSE
      SKIP
    FI;
    X ::= ATail (AId X)
  END.

Fixpoint snoc {X:Type} (l:list X) (v:X) : (list X) :=
  match l with
  | nil => [ v ]
  | cons h t => h :: (snoc t v)
  end.

Lemma snoc_equation : forall (A : Type) (h:A) (x y : list A),
  snoc x h ++ y = x ++ h :: y.     
Proof.
  intros A h x y.
  induction x. 
    Case "x = []". reflexivity.
    Case "x = cons". simpl. rewrite IHx. reflexivity.
Qed.

Lemma appears_in_snoc1 : forall a l,
  appears_in a (snoc l a).
Proof.
  induction l.
    Case "l = []". apply ai_here.
    Case "l = cons". simpl. apply ai_later. apply IHl.
Qed.

Lemma appears_in_snoc2 : forall a b l,
  appears_in a l ->
  appears_in a (snoc l b).
Proof.
  induction l; intros H; inversion H; subst; simpl.
    Case "l = []". apply ai_here.
    Case "l = cons". apply ai_later. apply IHl. assumption.
Qed.

Lemma appears_in_snoc3 : forall a b l,
   appears_in a (snoc l b) ->
   (appears_in a l \/ a = b).
Proof.
   induction l; intros H.
   Case "l = []". inversion H.
     SCase "ai_here". right. reflexivity.
     SCase "ai_later". left. assumption.
   Case "l = cons". inversion H; subst.
     SCase "ai_here". left. apply ai_here.
     SCase "ai_later". destruct (IHl H1).
       left. apply ai_later. assumption.
       right. assumption.
Qed.

Lemma append_singleton_equation : forall (x : nat) l l',
  (l ++ [x]) ++ l' = l ++ x :: l'.
Proof.
  intros x l l'.
  induction l.
    reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Lemma append_nil : forall (A : Type) (l : list A),
  l ++ [] = l.
Proof.
  induction l. 
    reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Theorem list_member_correct : forall l n,
  {{ fun st => aslist (st X) = l /\ asnat (st Y) = n /\ asnat (st Z) = 0 }}
  list_member
  {{ fun st => asnat (st Z) = 1 <-> appears_in n l }}.
Proof.
  intros l n.
  eapply hoare_consequence.
  apply hoare_while with (P := fun st =>
     asnat (st Y) = n 
     /\ exists p, p ++ aslist (st X) = l 
                  /\ (asnat (st Z) = 1 <-> appears_in n p)).
    (* The loop body preserves the invariant: *)
    eapply hoare_seq.
    apply hoare_asgn.
    apply hoare_if.
    Case "If taken".
      eapply hoare_consequence_pre.
      apply hoare_asgn.
      intros st [[[H1 [p [H2 H3]]] H9] H10].
      unfold assn_sub. split.
      (* (st Y) is still n *)
        rewrite update_neq; try (intro X; inversion X). 
        rewrite update_neq; try (intro X; inversion X). 
        assumption.
      (* and the interesting part of the invariant is preserved: *)
        (* X has to be a cons *)
        destruct (aslist (st X)) as [|h x'] eqn:Heqx. 
          unfold bassn in H9. unfold beval in H9. unfold aeval in H9. 
          rewrite -> Heqx in H9. inversion H9.
          
          exists (snoc p h).
          rewrite update_eq.
          unfold aeval. rewrite update_neq; try (intro X; inversion X). 
          rewrite -> Heqx.
          split.
            rewrite snoc_equation. assumption.

            rewrite update_neq; try (intro X; inversion X). 
            rewrite update_eq. 
            split. 
              simpl.
              unfold bassn in H10. unfold beval in H10.
              unfold aeval in H10. rewrite H1 in H10. 
              rewrite -> Heqx in H10. simpl in H10.
              rewrite (beq_nat_true _ _ H10).
              intros. apply appears_in_snoc1.
                
              intros. reflexivity.
    Case "If not taken".
      eapply hoare_consequence_pre. apply hoare_skip.
      unfold assn_sub.
      intros st [[[H1 [p [H2 H3]]] H9] H10].
      split.
      (* (st Y) is still n *)
        rewrite update_neq; try (intro X; inversion X). 
        assumption.
      (* and the interesting part of the invariant is preserved: *)
        (* X has to be a cons *)
        destruct (aslist (st X)) as [|h x'] eqn:Heqx.
          unfold bassn in H9. unfold beval in H9. unfold aeval in H9. 
          rewrite -> Heqx in H9. inversion H9.

          exists (snoc p h).
          split.
            rewrite update_eq.
            unfold aeval. rewrite -> Heqx.
            rewrite snoc_equation. assumption.

            rewrite update_neq; try (intro X; inversion X). 
            split.
              intros. apply appears_in_snoc2. apply H3. assumption.

              intros.  destruct (appears_in_snoc3 _ _ _ H).
              SCase "later".
                inversion H3 as [_ H3'].
                apply H3'. assumption.
              SCase "here (absurd)".
                subst.
                unfold bassn, beval, aeval in H10.
                rewrite not_true_iff_false in H10.
                apply beq_nat_false in H10. 
                rewrite -> Heqx in H10. simpl in H10.
                apply ex_falso_quodlibet. apply H10. assumption.
  (* The invariant holds at the start of the loop: *)
  intros st [H1 [H2 H3]]. 
  rewrite H1. rewrite H2. rewrite H3.
  split. 
    reflexivity.
    exists []. split.
      reflexivity.
      split; intros H; inversion H.
  (* At the end of the loop the invariant implies the right thing. *)
  simpl.   intros st [[H1 [p [H2 H3]]] H5].
  (* x must be [] *)
  unfold bassn in H5. unfold beval in H5. unfold aeval in H5.
  destruct (aslist (st X)) as [|h x'].
    rewrite append_nil in H2.
    rewrite <- H2.
    assumption.

    apply ex_falso_quodlibet. apply H5. reflexivity.
Qed.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => []
  | cons h t => snoc (rev t) h
  end.

Definition list_reverse_program :=
  Y ::= ANil;
  WHILE (BIsCons (AId X)) DO
    Y ::= ACons (AHead (AId X)) (AId Y);
    X ::= ATail (AId X)
  END.

Lemma rev_equation : forall (A : Type) (h : A) (x y : list A),
  rev (h :: x) ++ y = rev x ++ h :: y.
Proof.
  intros. simpl. apply snoc_equation.
Qed.

Theorem list_rev_correct : forall l,
  {{ fun st => aslist (st X) =  l }}
    list_reverse_program
  {{ fun st => aslist (st Y) = rev l }}.
Proof.
  intros.
  destruct (eq_id_dec X Y) eqn:eqxy; try inversion eqxy.
    unfold list_reverse_program.
    eapply hoare_seq.
      eapply hoare_consequence_post with (fun st : state => rev(aslist (st X)) ++ aslist (st Y) = rev l /\ ~ bassn (BIsCons (AId X)) st).
        apply hoare_while.
        eapply hoare_consequence_pre.
          eapply hoare_seq.
            apply hoare_asgn.
            apply hoare_asgn.
          intros st [H0 H1]. inversion H1.
          destruct (st X) eqn:stx. inversion H2.
          destruct l0. inversion H2.
          simpl in H0.
          unfold assn_sub. simpl. rewrite stx.
          simpl.
          rewrite update_neq; auto. rewrite stx. simpl.
          rewrite <- rev_equation. simpl. assumption.
        intros st [H0 H1].
          destruct (st X) eqn:stx. simpl in H0. assumption.
          destruct l0. simpl in H0. assumption.
          assert(H:False); try inversion H. apply H1. unfold bassn.
          simpl. rewrite stx. reflexivity.
      eapply hoare_consequence_post with (fun st : state => aslist (st X) = l /\ aslist (st Y) = []).
        eapply hoare_consequence_pre.
        apply hoare_asgn.
        unfold assn_sub. simpl. intros st H. split; auto.
        intros st [H0 H1]. destruct (st Y) eqn:sty; subst; simpl. apply append_nil.
        simpl in H1. rewrite H1. apply append_nil.
  Qed.

Inductive dcom : Type :=
  | DCSkip :  Assertion -> dcom
  | DCSeq : dcom -> dcom -> dcom
  | DCAsgn : id -> aexp ->  Assertion -> dcom
  | DCIf : bexp ->  Assertion -> dcom ->  Assertion -> dcom
           -> Assertion-> dcom
  | DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
  | DCPre : Assertion -> dcom -> dcom
  | DCPost : dcom -> Assertion -> dcom.

Tactic Notation "dcom_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Skip" | Case_aux c "Seq" | Case_aux c "Asgn"
  | Case_aux c "If" | Case_aux c "While"
  | Case_aux c "Pre" | Case_aux c "Post" ].

Notation "'SKIP' {{ P }}" 
      := (DCSkip P) 
      (at level 10) : dcom_scope.
Notation "l '::=' a {{ P }}" 
      := (DCAsgn l a P) 
      (at level 60, a at next level) : dcom_scope.
Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}" 
      := (DCWhile b Pbody d Ppost) 
      (at level 80, right associativity) : dcom_scope.
Notation "'IFB' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI' {{ Q }}" 
      := (DCIf b P d P' d' Q) 
      (at level 80, right associativity)  : dcom_scope.
Notation "'=>' {{ P }} d" 
      := (DCPre P d) 
      (at level 90, right associativity)  : dcom_scope.
Notation "{{ P }} d" 
      := (DCPre P d) 
      (at level 90)  : dcom_scope.
Notation "d '=>' {{ P }}" 
      := (DCPost d P) 
      (at level 91, right associativity)  : dcom_scope.
Notation " d ; d' " 
      := (DCSeq d d') 
      (at level 80, right associativity)  : dcom_scope.

Delimit Scope dcom_scope with dcom.

Example dec_while : dcom := (
  {{ fun st => True }}
  WHILE (BNot (BEq (AId X) (ANum 0))) 
  DO
    {{ fun st => True /\ bassn (BNot (BEq (AId X) (ANum 0))) st}}
    X ::= (AMinus (AId X) (ANum 1)) 
    {{ fun _ => True }}
  END
  {{ fun st => True /\ ~bassn (BNot (BEq (AId X) (ANum 0))) st}} =>
  {{ fun st => asnat (st X) = 0 }}
) % dcom.

Fixpoint extract (d:dcom) : com :=
  match d with
  | DCSkip _           => SKIP
  | DCSeq d1 d2        => (extract d1 ; extract d2) 
  | DCAsgn X a _       => X ::= a
  | DCIf b _ d1 _ d2 _ => IFB b THEN extract d1 ELSE extract d2 FI
  | DCWhile b _ d _    => WHILE b DO extract d END
  | DCPre _ d          => extract d
  | DCPost d _         => extract d
  end.

Fixpoint post (d:dcom) : Assertion :=
  match d with
  | DCSkip P                => P
  | DCSeq d1 d2             => post d2
  | DCAsgn X a Q            => Q
  | DCIf  _ _ d1 _ d2 Q     => Q
  | DCWhile b Pbody c Ppost => Ppost
  | DCPre _ d               => post d
  | DCPost c Q              => Q
  end.

Fixpoint pre (d:dcom) : Assertion :=
  match d with
  | DCSkip P                => fun st => True
  | DCSeq c1 c2             => pre c1
  | DCAsgn X a Q            => fun st => True
  | DCIf  _ _ t _ e _       => fun st => True
  | DCWhile b Pbody c Ppost => fun st => True
  | DCPre P c               => P
  | DCPost c Q              => pre c
  end.

Definition dec_correct (d:dcom) := 
  {{pre d}} (extract d) {{post d}}.

Fixpoint verification_conditions (P : Assertion) (d:dcom) : Prop :=
  match d with
  | DCSkip Q          => 
      (P ->> Q)
  | DCSeq d1 d2      => 
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q      => 
      (P ->> assn_sub X a Q)
  | DCIf b P1 d1 P2 d2 Q => 
      ((fun st => P st /\ bassn b st) ->> P1)
      /\ ((fun st => P st /\ ~ (bassn b st)) ->> P2)
      /\ (Q = post d1) /\ (Q = post d2)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost      => 
      (* post d is the loop invariant and the initial precondition *)
      (P ->> post d)  
      /\ (Pbody = (fun st => post d st /\ bassn b st))
      /\ (Ppost = (fun st => post d st /\ ~(bassn b st)))
      /\ verification_conditions Pbody d
  | DCPre P' d         => 
      (P ->> P') /\ verification_conditions P' d
  | DCPost d Q        => 
      verification_conditions P d /\ (post d ->> Q)
  end.

Theorem verification_correct : forall d P, 
  verification_conditions P d -> {{P}} (extract d) {{post d}}.
Proof.
  dcom_cases (induction d) Case; intros P H; simpl in *.
  Case "Skip".
    eapply hoare_consequence_pre.
      apply hoare_skip.
      assumption.
  Case "Seq". 
    inversion H as [H1 H2]. clear H. 
    eapply hoare_seq. 
      apply IHd2. apply H2.
      apply IHd1. apply H1.
  Case "Asgn". 
    eapply hoare_consequence_pre.
      apply hoare_asgn.
      assumption.
  Case "If".
    inversion H as [HPre1 [HPre2 [Hd1 [Hd2 [HThen HElse]]]]]; clear H.
    subst.
    apply hoare_if.
      eapply hoare_consequence_pre. apply IHd1. eassumption. assumption.
      rewrite Hd2.
      eapply hoare_consequence_pre. apply IHd2. eassumption. assumption.
  Case "While".
    inversion H as [Hpre [Hbody [Hpost Hd]]]; subst; clear H.
    eapply hoare_consequence_pre.
    apply hoare_while with (P := post d). 
      apply IHd. apply Hd. 
      assumption.
  Case "Pre".
    inversion H as [HP Hd]; clear H. 
    eapply hoare_consequence_pre. apply IHd. apply Hd. assumption.
  Case "Post".
    inversion H as [Hd HQ]; clear H.
    eapply hoare_consequence_post. apply IHd. apply Hd. assumption.
Qed.

Tactic Notation "verify" :=
  try apply verification_correct; 
  repeat split;
  simpl; unfold assert_implies; 
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat rewrite update_eq;
  repeat (rewrite update_neq; [| (intro X; inversion X)]);
  simpl in *; 
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite beq_nat_true_iff in *;
  repeat rewrite beq_nat_false_iff in *;
  try eauto; try omega.

Definition list_member_dec (n : nat) (l : list nat) : dcom := (
    {{ fun st => aslist (st X) = l /\ asnat (st Y) = n /\ asnat (st Z) = 0 }}
  WHILE BIsCons (AId X)
  DO {{ fun st => (asnat (st Y) = n 
               /\ (exists p, p ++ aslist (st X) = l 
               /\ (asnat (st Z) = 1 <-> appears_in n p)))
               /\ bassn (BIsCons (AId X)) st }}
    IFB (BEq (AId Y) (AHead (AId X))) THEN
        {{ fun st =>
          ((asnat (st Y) = n 
            /\ (exists p, p ++ aslist (st X) = l 
                /\ (asnat (st Z) = 1 <-> appears_in n p)))
          /\ bassn (BIsCons (AId X)) st)
          /\ bassn (BEq (AId Y) (AHead (AId X))) st }}
        =>
        {{ fun st => 
            asnat (st Y) = n 
            /\ (exists p, p ++ tail (aslist (st X)) = l 
                 /\ (1 = 1 <-> appears_in n p)) }}
      Z ::= ANum 1
        {{ fun st => asnat (st Y) = n 
             /\ (exists p, p ++ tail (aslist (st X)) = l 
                  /\ (asnat (st Z) = 1 <-> appears_in n p)) }}
   ELSE
        {{ fun st =>
          ((asnat (st Y) = n 
            /\ (exists p, p ++ aslist (st X) = l 
                  /\ (asnat (st Z) = 1 <-> appears_in n p)))
          /\ bassn (BIsCons (AId X)) st)
          /\ ~bassn (BEq (AId Y) (AHead (AId X))) st }}
        =>
        {{ fun st => 
          asnat (st Y) = n 
          /\ (exists p, p ++ tail (aslist (st X)) = l 
               /\ (asnat (st Z) = 1 <-> appears_in n p)) }}
      SKIP
        {{ fun st => asnat (st Y) = n 
            /\ (exists p, p ++ tail (aslist (st X)) = l 
                 /\ (asnat (st Z) = 1 <-> appears_in n p)) }}
   FI
     {{ fun st => asnat (st Y) = n 
        /\ (exists p, p ++ tail (aslist (st X)) = l 
          /\ (asnat (st Z) = 1 <-> appears_in n p)) }}
   ;
   X ::= (ATail (AId X))
     {{ fun st  =>
         asnat (st Y) = n /\
         (exists p : list nat, p ++ aslist (st X) = l 
           /\ (asnat (st Z) = 1 <-> appears_in n p)) }}
  END
   {{ fun st =>
     (asnat (st Y) = n 
       /\ (exists p, p ++ aslist (st X) = l 
            /\ (asnat (st Z) = 1 <-> appears_in n p)))
     /\ ~bassn (BIsCons (AId X)) st }}
   =>
   {{ fun st => asnat (st Z) = 1 <-> appears_in n l }}
) %dcom.

Theorem list_member_correct' : forall n l,
  dec_correct (list_member_dec n l).
Proof.
  intros n l. verify.
  Case "The loop precondition holds.".
    exists []. simpl. split.
      rewrite H. reflexivity.
      rewrite H1. split; intro Hc; inversion Hc.
  Case "IF taken".
    destruct H2 as [p [H3 H4]].
    (* We know X is non-nil. *)
    destruct (aslist (st X)) as [|h x'].
      inversion H1.
      exists (snoc p h).
      simpl. split.
         rewrite snoc_equation. assumption.
         split.
           rewrite H in H0.
           simpl in H0. rewrite H0.
           intros _. apply appears_in_snoc1.
           intros _. reflexivity.
  Case "If not taken".
    destruct H2 as [p [H3 H4]].
    (* We know X is non-nil. *)
    destruct (aslist (st X)) as [|h x'].
      inversion H1.
      exists (snoc p h).
      split. simpl.
        rewrite snoc_equation. assumption.
        split.
          intros. apply appears_in_snoc2. apply H4. assumption.
          intros Hai.  destruct (appears_in_snoc3 _ _ _ Hai).
          SCase "later". apply H4. assumption.
          SCase "here (absurd)".
            subst. simpl in H0. 
            apply ex_falso_quodlibet. apply H0. assumption.
  Case "Loop postcondition implies desired conclusion (->)".
    destruct H2 as [p [H3 H4]].
    destruct (aslist (st X)) as [|h x'].
       rewrite append_nil in H3. subst. apply H4. assumption.
       inversion H1.
  Case "loop postcondition implies desired conclusion (<-)".
    destruct H2 as [p [H3 H4]].
    destruct (aslist (st X)) as [|h x'].
       rewrite append_nil in H3. subst. apply H4. assumption.
       inversion H1.
Qed.