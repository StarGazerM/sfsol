Add LoadPath "D:\sfsol".
Require Export Hoare.

Inductive hoare_proof : Assertion -> com -> Assertion -> Type :=
  | H_Skip : forall P,
      hoare_proof P (SKIP) P
  | H_Asgn : forall Q V a,
      hoare_proof (assn_sub V a Q) (V ::= a) Q
  | H_Seq : forall P c Q d R,
      hoare_proof P c Q -> hoare_proof Q d R -> hoare_proof P (c;;d) R
  | H_If : forall P Q b c1 c2,
    hoare_proof (fun st => P st /\ bassn b st) c1 Q ->
    hoare_proof (fun st => P st /\ ~(bassn b st)) c2 Q ->
    hoare_proof P (IFB b THEN c1 ELSE c2 FI) Q
  | H_While : forall P b c,
    hoare_proof (fun st => P st /\ bassn b st) c P ->
    hoare_proof P (WHILE b DO c END) (fun st => P st /\ ~ (bassn b st))
  | H_Consequence : forall (P Q P' Q' : Assertion) c,
    hoare_proof P' c Q' ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    hoare_proof P c Q.

Tactic Notation "hoare_proof_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "H_Skip" | Case_aux c "H_Asgn" | Case_aux c "H_Seq"
  | Case_aux c "H_If" | Case_aux c "H_While" | Case_aux c "H_Consequence" ].

Lemma H_Consequence_pre : forall (P Q P': Assertion) c,
    hoare_proof P' c Q ->
    (forall st, P st -> P' st) ->
    hoare_proof P c Q.
Proof.
  intros.
  eapply H_Consequence.
  apply X. assumption. auto.
  Qed.

Lemma H_Consequence_post : forall (P Q Q': Assertion) c,
    hoare_proof P c Q' ->
    (forall st, Q' st -> Q st) ->
    hoare_proof P c Q.
Proof.
  intros.
  eapply H_Consequence.
  apply X. auto. assumption.
  Qed.

Example sample_proof
             : hoare_proof
                 (assn_sub X (APlus (AId X) (ANum 1))
                   (assn_sub X (APlus (AId X) (ANum 2))
                     (fun st => st X = 3) ))
                 (X ::= APlus (AId X) (ANum 1);; (X ::= APlus (AId X) (ANum 2)))
                 (fun st => st X = 3).
Proof.
  eapply H_Seq; apply H_Asgn.
Qed.

Theorem hoare_proof_sound : forall P c Q,
  hoare_proof P c Q -> {{P}} c {{Q}}.
Proof.
  intros. induction X.
  apply hoare_skip.
  apply hoare_asgn.
  apply hoare_seq with Q; assumption.
  apply hoare_if; assumption.
  apply hoare_while; assumption.
  eapply hoare_consequence; try apply IHX; try assumption.
  Qed.

Theorem H_Post_True_deriv:
  forall c P, hoare_proof P c (fun _ => True).
Proof.
  intro c.
  com_cases (induction c) Case; intro P.
  Case "SKIP".
    eapply H_Consequence.
    apply H_Skip.
    intros. apply H.
    (* Proof of True *)
    intros. apply I.
  Case "::=".
    eapply H_Consequence_pre.
    apply H_Asgn.
    intros. apply I.
  Case ";;".
    eapply H_Consequence_pre.
    eapply H_Seq.
    apply (IHc1 (fun _ => True)).
    apply IHc2.
    intros. apply I.
  Case "IFB".
    apply H_Consequence_pre with (fun _ => True).
    apply H_If.
    apply IHc1.
    apply IHc2.
    intros. apply I.
  Case "WHILE".
    eapply H_Consequence.
    eapply H_While.
    eapply IHc.
    intros; apply I.
    intros; apply I.
Qed.

Lemma False_and_P_imp: forall P Q,
  False /\ P -> Q.
Proof.
  intros P Q [CONTRA HP].
  destruct CONTRA.
Qed.

Tactic Notation "pre_false_helper" constr(CONSTR) :=
  eapply H_Consequence_pre;
    [eapply CONSTR | intros ? CONTRA; destruct CONTRA].

Theorem H_Pre_False_deriv:
  forall c Q, hoare_proof (fun _ => False) c Q.
Proof.
  intros c.
  com_cases (induction c) Case; intro Q.
  Case "SKIP". pre_false_helper H_Skip.
  Case "::=". pre_false_helper H_Asgn.
  Case ";;". pre_false_helper H_Seq. apply IHc1. apply IHc2.
  Case "IFB".
    apply H_If; eapply H_Consequence_pre.
    apply IHc1. intro. eapply False_and_P_imp.
    apply IHc2. intro. eapply False_and_P_imp.
  Case "WHILE".
    eapply H_Consequence_post.
    eapply H_While.
    eapply H_Consequence_pre.
      apply IHc.
      intro. eapply False_and_P_imp.
    intro. simpl. eapply False_and_P_imp.
Qed.

Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => forall s', c / s || s' -> Q s'.

Lemma wp_is_precondition: forall c Q,
  {{wp c Q}} c {{Q}}.
Proof.
  intros c Q st st' H1 H2.
  apply H2. assumption.
  Qed.

Lemma wp_is_weakest: forall c Q P',
   {{P'}} c {{Q}} -> forall st, P' st -> wp c Q st.
Proof.
  intros c Q P' H st H2. unfold wp. intros s' Hypo.
  eapply H. apply Hypo. assumption. Qed.

Lemma bassn_eval_false : forall b st, ~ bassn b st -> beval st b = false.
Proof.
  intros b st H. unfold bassn in H. destruct (beval st b).
    exfalso. apply H. reflexivity.
    reflexivity.
Qed.

Theorem hoare_proof_complete: forall P c Q,
  {{P}} c {{Q}} -> hoare_proof P c Q.
Proof.
  intros P c. generalize dependent P.
  com_cases (induction c) Case; intros P Q HT.
  Case "SKIP".
    eapply H_Consequence.
     eapply H_Skip.
      intros. eassumption.
      intro st. apply HT. apply E_Skip.
  Case "::=".
    eapply H_Consequence.
      eapply H_Asgn.
      intro st. apply HT. econstructor. reflexivity.
      intros; assumption.
  Case ";;".
    apply H_Seq with (wp c2 Q).
     eapply IHc1.
       intros st st' E1 H. unfold wp. intros st'' E2.
         eapply HT. econstructor; eassumption. assumption.
     eapply IHc2. intros st st' E1 H. apply H; assumption.
  Case "IFB".
    apply H_If. apply IHc1.
      intros st st' H [H1 H2].
      eapply HT. constructor; try apply H2; assumption. assumption.
      apply IHc2. intros st st' H [H1 H2].
      eapply HT. apply E_IfFalse; try apply bassn_eval_false; try apply H2; assumption. assumption.
  Case "WHILE".
    eapply H_Consequence with (P' := wp (WHILE b DO c END) Q).
      apply H_While.
      apply IHc. intros st st' H [H2 H3] st'' H4.
      assert((WHILE b DO c END) / st || st'').
        eapply E_WhileLoop. apply H3. apply H. apply H4.
      eapply wp_is_precondition. apply H0. assumption.
      apply wp_is_weakest. assumption.
      intros st [H1 H2]. eapply wp_is_precondition.
      assert((WHILE b DO c END) / st || st).
        apply E_WhileEnd. apply bassn_eval_false. assumption.
      apply H. assumption.
  Qed.