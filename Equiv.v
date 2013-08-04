Add LoadPath "F:\sfsol".
Require Export Imp.

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state),
    beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st || st') <-> (c2 / st || st').

(* {a}{b}{c,h}{d}{e}{f,i}{g} *)

Theorem aequiv_example:
  aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof.
  unfold aequiv.
  intros.
  unfold aeval.
  induction (st X); simpl; try reflexivity; try assumption.
  Qed.

Theorem bequiv_example:
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
Proof.
  unfold bequiv.
  intros.
  unfold beval.
  rewrite -> aequiv_example. simpl. auto.
  Qed.

Theorem skip_left: forall c,
  cequiv
     (SKIP;; c)
     c.
Proof.
  (* WORKED IN CLASS *)
  intros c st st'.
  split; intros H.
  Case "->".
    inversion H. subst.
    inversion H2. subst.
    assumption.
  Case "<-".
    apply E_Seq with st.
    apply E_Skip.
    assumption.
Qed.

Theorem skip_right: forall c,
  cequiv
    (c;; SKIP)
    c.
Proof.
  intros c st st'.
  split; intros.
    inversion H. inversion H5.
    rewrite H8 in H2. auto.
    apply E_Seq with st'. auto.
    apply E_Skip.
    Qed.

Theorem IFB_true_simple: forall c1 c2,
  cequiv
    (IFB BTrue THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros c1 c2 st st'.
  split; intros H.
  inversion H; try inversion H5; try auto.
  apply E_IfTrue; auto.
  Qed.

Theorem IFB_true: forall b c1 c2,
     bequiv b BTrue ->
     cequiv
       (IFB b THEN c1 ELSE c2 FI)
       c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  Case "->".
    inversion H; subst.
    SCase "b evaluates to true".
      assumption.
    SCase "b evaluates to false (contradiction)".
      rewrite Hb in H5.
      inversion H5.
  Case "<-".
    apply E_IfTrue; try assumption.
    rewrite Hb. reflexivity. Qed.

Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  inversion H; subst.
    rewrite Hb in H5. inversion H5.
    auto.
    apply E_IfFalse; try rewrite Hb; auto.
  Qed.

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros b e1 e2; split; intros H; inversion H; subst.
    apply E_IfFalse; simpl; try rewrite H5; try auto.
    apply E_IfTrue; simpl; try rewrite H5; try auto.
    apply E_IfFalse; inversion H5; destruct (beval st b); inversion H1; auto.
    apply E_IfTrue; inversion H5; destruct (beval st b); inversion H1; auto.
  Qed.

Theorem WHILE_false : forall b c,
     bequiv b BFalse ->
     cequiv
       (WHILE b DO c END)
       SKIP.
Proof.
  intros b c Hb st st'.
  split; intros H.
  inversion H; subst; try apply E_Skip; rewrite Hb in H2; inversion H2.
  inversion H; apply E_WhileEnd; rewrite Hb; auto.
  Qed.

Lemma WHILE_true_nonterm : forall b c st st',
     bequiv b BTrue ->
     ~( (WHILE b DO c END) / st || st' ).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw eqn:Heqcw.
  ceval_cases (induction H) Case;
    (* Most rules don't apply, and we can rule them out 
       by inversion *)
    inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for WHILE loops: *)
  Case "E_WhileEnd". (* contradictory -- b is always true! *)
    unfold bequiv in Hb.
    (* rewrite is able to instantiate the quantifier in st *)
    rewrite Hb in H. inversion H.
  Case "E_WhileLoop". (* immediate from the IH *)
    apply IHceval2. reflexivity. Qed.

Theorem WHILE_true: forall b c,
     bequiv b BTrue ->
     cequiv
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof.
  intros b c Hb st st'.
  split; intros. assert (~(WHILE b DO c END) / st || st').
    apply WHILE_true_nonterm. auto.
    apply H0 in H. inversion H.
  assert (~(WHILE BTrue DO SKIP END) / st || st').
    apply loop_stop. auto.
    apply H0 in H. inversion H.
  Qed.

Theorem loop_unrolling: forall b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  intros b c st st'.
  split; intros H.
  inversion H; subst.
    apply E_IfFalse; auto; try apply E_Skip.
    apply E_IfTrue; auto; try apply E_Seq with st'0; auto.
  inversion H; subst; inversion H6; subst.
    apply E_WhileLoop with st'0; auto.
    apply E_WhileEnd. auto.
  Qed.

Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  intros c1 c2 c3 st st'; split; intros H.
  inversion H; subst; inversion H2; subst.
    apply E_Seq with st'1; auto.
    apply E_Seq with st'0; auto.
  inversion H; subst; inversion H5; subst.
    apply E_Seq with st'1; auto.
    apply E_Seq with st'0; auto.
  Qed.

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) -> f = g.

Theorem identity_assignment : forall (X:id),
  cequiv
    (X ::= AId X)
    SKIP.
Proof.
   intros. split; intro H.
     Case "->".
       inversion H; subst. simpl.
       replace (update st X (st X)) with st.
       constructor.
       apply functional_extensionality. intro.
       rewrite update_same; reflexivity.
     Case "<-".
       inversion H; subst.
       assert (st' = (update st' X (st' X))).
          apply functional_extensionality. intro.
          rewrite update_same; reflexivity.
       rewrite H0 at 2.
       constructor. reflexivity.
Qed.

Theorem assign_aequiv : forall X e,
  aequiv (AId X) e ->
  cequiv SKIP (X ::= e).
Proof.
  intros X e He st st';
  split; intros H.
    inversion H. replace ((X ::= e) / st' || st') with ((X ::= e) / st' || update st' X (aeval st' e)).
    constructor; auto.
    replace (update st' X (aeval st' e)) with st'.
    auto. apply functional_extensionality. intro.
    rewrite update_same; auto; apply He.
  inversion H; subst.
  replace (update st X (aeval st e)) with st.
    constructor.
    apply functional_extensionality. intro.
    rewrite update_same; auto.
    apply He.
  Qed.

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  intros a st. auto. Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H st. symmetry. apply H. Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  intros a1 a2 a3 H1 H2 st. rewrite H1. auto. Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  intros b st. auto. Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  intros b1 b2 H st. auto. Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  intros b1 b2 b3 H1 H2 st. rewrite H1. auto. Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  intros c st; split; intros H; auto. Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  intros c1 c2 H st; split; apply H. Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros P1 P2 P3 H1 H2; split.
    rewrite H1. apply H2.
    rewrite <- H2. apply H1.
    Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  intros c1 c2 c3 H1 H2 st; split; intros H.
  apply H2. apply H1. apply H.
  apply H1. apply H2. apply H.
  Qed.

Theorem CAss_congruence : forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
  intros; split; intro;
  inversion H0; subst; apply E_Ass; rewrite H; auto.
  Qed.

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  (* WORKED IN CLASS *)
  unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
  Case "->".
    remember (WHILE b1 DO c1 END) as cwhile eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    SCase "E_WhileEnd".
      apply E_WhileEnd. rewrite <- Hb1e. apply H.
    SCase "E_WhileLoop".
      apply E_WhileLoop with (st' := st').
      SSCase "show loop runs". rewrite <- Hb1e. apply H.
      SSCase "body execution".
        apply (Hc1e st st'). apply Hce1.
      SSCase "subsequent loop execution".
        apply IHHce2. reflexivity.
  Case "<-".
    remember (WHILE b1' DO c1' END) as c'while eqn:Heqc'while.
    induction Hce; inversion Heqc'while; subst.
    SCase "E_WhileEnd".
      apply E_WhileEnd. rewrite -> Hb1e. apply H.
    SCase "E_WhileLoop".
      apply E_WhileLoop with (st' := st').
      SSCase "show loop runs". rewrite -> Hb1e. apply H.
      SSCase "body execution".
        apply (Hc1e st st'). apply Hce1.
      SSCase "subsequent loop execution".
        apply IHHce2. reflexivity. Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
  intros c1 c1' c2 c2' H1 H2 st st';
  split; intros H; inversion H; subst;
  apply E_Seq with st'0; try apply H1; try apply H2; auto.
  Qed.

Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
  intros; split; intros Htmp; inversion Htmp; subst.
  rewrite H in H7; apply E_IfTrue; auto; apply H0; auto.
  rewrite H in H7; apply E_IfFalse; auto; apply H1; auto.
  rewrite <- H in H7; apply E_IfTrue; auto; apply H0; auto.
  rewrite <- H in H7; apply E_IfFalse; auto; apply H1; auto.
  Qed.

Example congruence_example:
  cequiv
    (* Program 1: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= ANum 0
     ELSE
       Y ::= ANum 42
     FI)
    (* Program 2: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= AMinus (AId X) (AId X) (* <--- changed here *)
     ELSE
       Y ::= ANum 42
     FI).
Proof.
  apply CSeq_congruence.
    apply refl_cequiv.
    apply CIf_congruence.
      apply refl_bequiv.
      apply CAss_congruence. unfold aequiv. simpl.
        symmetry. apply minus_diag.
      apply refl_cequiv.
Qed.

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i => AId i
  | APlus a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (n1 + n2)
      | (a1', a2') => APlus a1' a2'
      end
  | AMinus a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (n1 - n2)
      | (a1', a2') => AMinus a1' a2'
      end
  | AMult a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (n1 * n2)
      | (a1', a2') => AMult a1' a2'
      end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp
      (AMult (APlus (ANum 1) (ANum 2)) (AId X))
  = AMult (ANum 3) (AId X).
Proof. reflexivity. Qed.

Example fold_aexp_ex2 :
    fold_constants_aexp
      (AMinus (AId X) (APlus (AMult (ANum 0) (ANum 6)) (AId Y)))
  = AMinus (AId X) (APlus (ANum 0) (AId Y)).
Proof. reflexivity. Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => if beq_nat n1 n2 then BTrue else BFalse
      | (a1', a2') => BEq a1' a2'
      end
  | BLe a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => if ble_nat n1 n2 then BTrue else BFalse
      | (a1', a2') => BLe a1' a2'
      end
  | BNot b1 =>
      match (fold_constants_bexp b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2 =>
      match (fold_constants_bexp b1, fold_constants_bexp b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Example fold_bexp_ex1 :
    fold_constants_bexp (BAnd BTrue (BNot (BAnd BFalse BTrue)))
  = BTrue.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
    fold_constants_bexp
      (BAnd (BEq (AId X) (AId Y))
            (BEq (ANum 0)
                 (AMinus (ANum 2) (APlus (ANum 1) (ANum 1)))))
  = BAnd (BEq (AId X) (AId Y)) BTrue.
Proof. reflexivity. Qed.

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP =>
      SKIP
  | i ::= a =>
      CAss i (fold_constants_aexp a)
  | c1 ;; c2 =>
      (fold_constants_com c1) ;; (fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => IFB b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.

Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    (X ::= APlus (ANum 4) (ANum 5);;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y)) (APlus (ANum 2) (ANum 4)) THEN
       SKIP
     ELSE
       Y ::= ANum 0
     FI;;
     IFB BLe (ANum 0) (AMinus (ANum 4) (APlus (ANum 2) (ANum 1))) THEN
       Y ::= ANum 0
     ELSE
       SKIP
     FI;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END)
  = (* After constant folding: *)
    (X ::= ANum 9;;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
       SKIP
     ELSE
       (Y ::= ANum 0)
     FI;;
     Y ::= ANum 0;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END).
Proof. reflexivity. Qed.

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  intros a st.
  induction a; try auto; simpl;
  remember (fold_constants_aexp a1) as af1;
  destruct af1;
  remember (fold_constants_aexp a2) as af2;
  destruct af2; rewrite IHa1; rewrite IHa2; auto.
  Qed.

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  bexp_cases (induction b) Case;
    (* BTrue and BFalse are immediate *)
    try reflexivity.
  Case "BEq".
    (* Doing induction when there are a lot of constructors makes
       specifying variable names a chore, but Coq doesn't always
       choose nice variable names.  We can rename entries in the
       context with the rename tactic: rename a into a1 will
       change a to a1 in the current goal and context. *)
    rename a into a1. rename a0 into a2. simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
      (* The only interesting case is when both a1 and a2 
         become constants after folding *)
      simpl. destruct (beq_nat n n0); reflexivity.
  Case "BLe".
    simpl.
    rewrite -> fold_constants_aexp_sound.
    replace (aeval st a0) with (aeval st (fold_constants_aexp a0)).
    remember (fold_constants_aexp a) as af;
    remember (fold_constants_aexp a0) as af0;
    destruct af; simpl; try auto.
    destruct af0; simpl; try auto.
    destruct (ble_nat n n0); auto.
    rewrite <- fold_constants_aexp_sound. auto.
  Case "BNot".
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  Case "BAnd".
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity. Qed.

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  com_cases (induction c) Case; simpl.
  Case "SKIP". apply refl_cequiv.
  Case "::=". apply CAss_congruence. apply fold_constants_aexp_sound.
  Case ";;". apply CSeq_congruence; assumption.
  Case "IFB".
    assert (bequiv b (fold_constants_bexp b)).
      SCase "Pf of assertion". apply fold_constants_bexp_sound.
    destruct (fold_constants_bexp b) eqn:Heqb;
      (* If the optimization doesn't eliminate the if, then the result
         is easy to prove from the IH and fold_constants_bexp_sound *)
      try (apply CIf_congruence; assumption).
    SCase "b always true".
      apply trans_cequiv with c1; try assumption.
      apply IFB_true; assumption.
    SCase "b always false".
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  Case "WHILE".
    assert (bequiv b (fold_constants_bexp b)).
      apply fold_constants_bexp_sound.
    destruct (fold_constants_bexp b) eqn:Heqb.
      apply WHILE_true; auto.
      apply WHILE_false; auto.
      try apply CWhile_congruence; auto.
      try apply CWhile_congruence; auto.
      try apply CWhile_congruence; auto.
      try apply CWhile_congruence; auto.
  Qed.

Fixpoint optimize_0plus_aexp (e:aexp) : aexp := 
      match e with
      | ANum n => 
          ANum n
      | AId i => AId i
      | APlus (ANum 0) e2 => 
          optimize_0plus_aexp e2
      | APlus e1 e2 => 
          APlus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
      | AMinus e1 e2 => 
          AMinus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
      | AMult e1 e2 => 
          AMult (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
      end.

Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BLe a1 a2 => BLe (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BNot b1 => BNot (optimize_0plus_bexp b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_bexp b1) (optimize_0plus_bexp b2)
  end.

Fixpoint optimize_0plus_com (c : com) : com :=
  match c with
  | SKIP =>
      SKIP
  | i ::= a =>
      CAss i (optimize_0plus_aexp a)
  | c1 ;; c2 =>
      (optimize_0plus_com c1) ;; (optimize_0plus_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      IFB (optimize_0plus_bexp b) THEN optimize_0plus_com c1
                     ELSE optimize_0plus_com c2 FI
  | WHILE b DO c END =>
      WHILE (optimize_0plus_bexp b) DO (optimize_0plus_com c) END
  end.

Theorem optimize_0plus_aexp_sound :
  atrans_sound optimize_0plus_aexp.
Proof.
  intros a st.
  induction a; simpl; try auto.
  destruct a1 eqn:Heqa1; try simpl; auto.
  destruct n; simpl; auto.
  Qed.

Theorem optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.
Proof.
  intros b st.
  induction b; try auto;
  simpl; try rewrite <- optimize_0plus_aexp_sound;
  try rewrite <- optimize_0plus_aexp_sound; auto.
  rewrite IHb; auto.
  rewrite IHb1; rewrite IHb2; auto.
  Qed.

Theorem optimize_0plus_com_sound :
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl. 
    split; auto.
    apply CAss_congruence. apply optimize_0plus_aexp_sound.
    apply CSeq_congruence; auto.
    apply CIf_congruence; auto; try apply optimize_0plus_bexp_sound.
    apply CWhile_congruence; auto; try apply optimize_0plus_bexp_sound.
  Qed.

Definition optimizer_0plus_const_com (c : com) : com :=
  optimize_0plus_com (fold_constants_com c).

Example optexam1 :
  optimizer_0plus_const_com
    (* Original program: *)
    (X ::= APlus (ANum 4) (ANum 5);;
     X ::= APlus (ANum 0) (AId X);;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y)) (APlus (ANum 2) (ANum 4)) THEN
       SKIP
     ELSE
       Y ::= ANum 0
     FI;;
     IFB BLe (ANum 0) (AMinus (ANum 4) (APlus (ANum 2) (ANum 1))) THEN
       Y ::= ANum 0
     ELSE
       SKIP
     FI;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END)
  = (* After constant folding: *)
    (X ::= ANum 9;;
     X ::= AId X;;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
       SKIP
     ELSE
       (Y ::= ANum 0)
     FI;;
     Y ::= ANum 0;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END).
Proof. reflexivity. Qed.

Theorem optimizer_0plus_const_com_sound :
  ctrans_sound optimizer_0plus_const_com.
Proof.
  unfold ctrans_sound.
  intro.
  unfold optimizer_0plus_const_com.
  split.
  intro.
  apply fold_constants_com_sound in H.
  apply optimize_0plus_com_sound in H.
  auto.
  intros.
  apply fold_constants_com_sound.
  apply optimize_0plus_com_sound.
  auto.
  Qed.

Fixpoint subst_aexp (i : id) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i' => if eq_id_dec i i' then u else AId i'
  | APlus a1 a2 => APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 => AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2 => AMult (subst_aexp i u a1) (subst_aexp i u a2)
  end.

Example subst_aexp_ex :
  subst_aexp X (APlus (ANum 42) (ANum 53)) (APlus (AId Y) (AId X)) =
  (APlus (AId Y) (APlus (ANum 42) (ANum 53))).
Proof. reflexivity. Qed.

Definition subst_equiv_property := forall i1 i2 a1 a2,
  cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.

  (* Here is the counterexample: assuming that subst_equiv_property
     holds allows us to prove that these two programs are
     equivalent... *)
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= AId X)
      as c1.
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= APlus (AId X) (ANum 1))
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).

  (* ... allows us to show that the command c2 can terminate 
     in two different final states: 
        st1 = {X |-> 1, Y |-> 1} 
        st2 = {X |-> 1, Y |-> 2}. *)
  remember (update (update empty_state X 1) Y 1) as st1.
  remember (update (update empty_state X 1) Y 2) as st2.
  assert (H1: c1 / empty_state || st1);
  assert (H2: c2 / empty_state || st2);
  try (subst;
       apply E_Seq with (st' := (update empty_state X 1));
       apply E_Ass; reflexivity).
  apply H in H1.

  (* Finally, we use the fact that evaluation is deterministic
     to obtain a contradiction. *)
  assert (Hcontra: st1 = st2)
    by (apply (ceval_deterministic c2 empty_state); assumption).
  assert (Hcontra': st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'. Qed.

Inductive var_not_used_in_aexp (X:id) : aexp -> Prop :=
  | VNUNum: forall n, var_not_used_in_aexp X (ANum n)
  | VNUId: forall Y, X <> Y -> var_not_used_in_aexp X (AId Y)
  | VNUPlus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (APlus a1 a2)
  | VNUMinus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMinus a1 a2)
  | VNUMult: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMult a1 a2).

Lemma aeval_weakening : forall i st a ni,
  var_not_used_in_aexp i a ->
  aeval (update st i ni) a = aeval st a.
Proof.
  intros.
  induction a; inversion H; simpl; try auto; try rewrite IHa1; try rewrite IHa2; auto.
  apply neq_id. auto.
  Qed.

Definition subst_equiv_property' := forall i1 i2 a1 a2,
  var_not_used_in_aexp i1 a1 ->
  cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

Theorem subst_equiv :
  subst_equiv_property'.
Proof.
  intros i1 i2 a1 a2 H.
  split; intro; inversion H0; subst.
  apply E_Seq with st'0; auto. clear H0.
  generalize dependent st'.
  induction a2. intros. simpl. auto.
  intros; inversion H6; subst; simpl; try apply E_Ass; auto; simpl; try rewrite IHa2_1.
  destruct (eq_id_dec i1 i) eqn:eqid; auto.
  inversion H3; subst.
  simpl. rewrite aeval_weakening; auto. unfold update. rewrite eq_id. auto.
  intros. inversion H6; subst.
  assert((i2 ::= subst_aexp i1 a1 a2_1) / st'0
|| update st'0 i2 (aeval st'0 a2_1)). apply IHa2_1. constructor. auto.
  assert((i2 ::= subst_aexp i1 a1 a2_2) / st'0
|| update st'0 i2 (aeval st'0 a2_2)). apply IHa2_2. constructor. auto.
  simpl. apply E_Ass. simpl.
  assert(aeval st'0 (subst_aexp i1 a1 a2_1) = aeval st'0 a2_1).
  inversion H0. rewrite H7.
  assert (update st'0 i2 n i2 = update st'0 i2 (aeval st'0 a2_1) i2).
    rewrite H8; auto.
  rewrite update_eq in H9. rewrite update_eq in H9. auto.
  assert(aeval st'0 (subst_aexp i1 a1 a2_2) = aeval st'0 a2_2).
  inversion H1. rewrite H8.
  assert (update st'0 i2 n i2 = update st'0 i2 (aeval st'0 a2_2) i2).
    rewrite H9; auto.
  rewrite update_eq in H10. rewrite update_eq in H10. auto.
  rewrite H2. rewrite H4. auto. 
  intros.
  assert((i2 ::= subst_aexp i1 a1 a2_1) / st'0
|| update st'0 i2 (aeval st'0 a2_1)). apply IHa2_1. constructor. auto.
  assert((i2 ::= subst_aexp i1 a1 a2_2) / st'0
|| update st'0 i2 (aeval st'0 a2_2)). apply IHa2_2. constructor. auto.
  inversion H6; subst. simpl. apply E_Ass. simpl.
  assert(aeval st'0 (subst_aexp i1 a1 a2_1) = aeval st'0 a2_1).
  inversion H0. rewrite H7.
  assert (update st'0 i2 n i2 = update st'0 i2 (aeval st'0 a2_1) i2).
    rewrite H8; auto.
  rewrite update_eq in H9. rewrite update_eq in H9. auto.
  assert(aeval st'0 (subst_aexp i1 a1 a2_2) = aeval st'0 a2_2).
  inversion H1. rewrite H8.
  assert (update st'0 i2 n i2 = update st'0 i2 (aeval st'0 a2_2) i2).
    rewrite H9; auto.
  rewrite update_eq in H10. rewrite update_eq in H10. auto.
  rewrite H2. rewrite H4. auto. intros.
  assert((i2 ::= subst_aexp i1 a1 a2_1) / st'0
|| update st'0 i2 (aeval st'0 a2_1)). apply IHa2_1. constructor. auto.
  assert((i2 ::= subst_aexp i1 a1 a2_2) / st'0
|| update st'0 i2 (aeval st'0 a2_2)). apply IHa2_2. constructor. auto.
  inversion H6; subst. simpl. apply E_Ass. simpl.
  assert(aeval st'0 (subst_aexp i1 a1 a2_1) = aeval st'0 a2_1).
  inversion H0. rewrite H7.
  assert (update st'0 i2 n i2 = update st'0 i2 (aeval st'0 a2_1) i2).
    rewrite H8; auto.
  rewrite update_eq in H9. rewrite update_eq in H9. auto.
  assert(aeval st'0 (subst_aexp i1 a1 a2_2) = aeval st'0 a2_2).
  inversion H1. rewrite H8.
  assert (update st'0 i2 n i2 = update st'0 i2 (aeval st'0 a2_2) i2).
    rewrite H9; auto.
  rewrite update_eq in H10. rewrite update_eq in H10. auto.
  rewrite H2. rewrite H4. auto. intros.
  apply E_Seq with st'0. auto.
  generalize dependent st'.
  induction a2; intros; inversion H6; subst; auto. destruct (eq_id_dec i1 i).
  apply E_Ass. rewrite <- e. inversion H3; subst. 
  assert(aeval (update st i (aeval st a1)) a1 = aeval st a1).
  rewrite aeval_weakening; auto.
  rewrite H1. simpl. apply update_eq.
  apply E_Ass. auto.
  assert((i2 ::= a2_1) / st'0 || update st'0 i2
     (aeval st'0 (subst_aexp i1 a1 a2_1))).
  apply IHa2_1. apply E_Seq with st'0. auto. apply E_Ass. auto. apply E_Ass. auto.
  assert((i2 ::= a2_2) / st'0 || update st'0 i2
     (aeval st'0 (subst_aexp i1 a1 a2_2))).
  apply IHa2_2. apply E_Seq with st'0. auto. apply E_Ass. auto. apply E_Ass. auto.
  inversion H1; subst. inversion H2; subst. apply E_Ass. simpl.
  assert(aeval st'0 a2_1 = aeval st'0 (subst_aexp i1 a1 a2_1)).
    symmetry. rewrite <- update_eq with (X:=i2) (st:=st'0). symmetry.
    rewrite <- update_eq with (X:=i2) (st:=st'0). rewrite H9. auto.
  assert(aeval st'0 a2_2 = aeval st'0 (subst_aexp i1 a1 a2_2)).
    symmetry. rewrite <- update_eq with (X:=i2) (st:=st'0). symmetry.
    rewrite <- update_eq with (X:=i2) (st:=st'0). rewrite H10. auto.
  rewrite <- H4. rewrite <- H5. auto.
  assert((i2 ::= a2_1) / st'0 || update st'0 i2
     (aeval st'0 (subst_aexp i1 a1 a2_1))).
  apply IHa2_1. apply E_Seq with st'0. auto. apply E_Ass. auto. apply E_Ass. auto.
  assert((i2 ::= a2_2) / st'0 || update st'0 i2
     (aeval st'0 (subst_aexp i1 a1 a2_2))).
  apply IHa2_2. apply E_Seq with st'0. auto. apply E_Ass. auto. apply E_Ass. auto.
  inversion H1; subst. inversion H2; subst. apply E_Ass. simpl.
  assert(aeval st'0 a2_1 = aeval st'0 (subst_aexp i1 a1 a2_1)).
    symmetry. rewrite <- update_eq with (X:=i2) (st:=st'0). symmetry.
    rewrite <- update_eq with (X:=i2) (st:=st'0). rewrite H9. auto.
  assert(aeval st'0 a2_2 = aeval st'0 (subst_aexp i1 a1 a2_2)).
    symmetry. rewrite <- update_eq with (X:=i2) (st:=st'0). symmetry.
    rewrite <- update_eq with (X:=i2) (st:=st'0). rewrite H10. auto.
  rewrite <- H4. rewrite <- H5. auto.
  assert((i2 ::= a2_1) / st'0 || update st'0 i2
     (aeval st'0 (subst_aexp i1 a1 a2_1))).
  apply IHa2_1. apply E_Seq with st'0. auto. apply E_Ass. auto. apply E_Ass. auto.
  assert((i2 ::= a2_2) / st'0 || update st'0 i2
     (aeval st'0 (subst_aexp i1 a1 a2_2))).
  apply IHa2_2. apply E_Seq with st'0. auto. apply E_Ass. auto. apply E_Ass. auto.
  inversion H1; subst. inversion H2; subst. apply E_Ass. simpl.
  assert(aeval st'0 a2_1 = aeval st'0 (subst_aexp i1 a1 a2_1)).
    symmetry. rewrite <- update_eq with (X:=i2) (st:=st'0). symmetry.
    rewrite <- update_eq with (X:=i2) (st:=st'0). rewrite H9. auto.
  assert(aeval st'0 a2_2 = aeval st'0 (subst_aexp i1 a1 a2_2)).
    symmetry. rewrite <- update_eq with (X:=i2) (st:=st'0). symmetry.
    rewrite <- update_eq with (X:=i2) (st:=st'0). rewrite H10. auto.
  rewrite <- H4. rewrite <- H5. auto.
  Qed.

Theorem inequiv_exercise:
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof.
  intros contra.
  unfold cequiv in contra.
  assert(forall st: state, SKIP / st || st).
    intros. apply E_Skip.
  assert(forall st: state, (WHILE BTrue DO SKIP END) / st || st).
    intros; apply contra; apply H.
  assert(forall st: state, ~((WHILE BTrue DO SKIP END) / st || st)).
    intros. apply loop_never_stops.
  assert((WHILE BTrue DO SKIP END) / empty_state || empty_state -> False).
  apply H1. apply H2. apply H0.
  Qed.

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";;"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "HAVOC" ].

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' l" := (CHavoc l) (at level 60).

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st || st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st || update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st || st' -> c2 / st' || st'' -> (c1 ;; c2) / st || st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st || st' ->
                  (WHILE b1 DO c1 END) / st' || st'' ->
                  (WHILE b1 DO c1 END) / st || st''
  | E_Havoc : forall (st : state) (n : nat) (X : id),
            (HAVOC X) / st || update st X n
  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
  | Case_aux c "E_Havoc" ].

Example havoc_example1 : (HAVOC X) / empty_state || update empty_state X 0.
Proof.
  apply E_Havoc. Qed.

Example havoc_example2 :
  (SKIP;; HAVOC Z) / empty_state || update empty_state Z 42.
Proof.
  apply E_Seq with empty_state.
    apply E_Skip.
    apply E_Havoc.
  Qed.

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  c1 / st || st' <-> c2 / st || st'.

Definition pXY :=
  HAVOC X;; HAVOC Y.

Definition pYX :=
  HAVOC Y;; HAVOC X.

Theorem update_swap: forall st X Y n n0,
  X<>Y->update (update st X n) Y n0 = update (update st Y n0) X n.
Proof.
  intros. apply functional_extensionality.
  intros. simpl.
  unfold update.
  destruct (eq_id_dec Y x); try auto.
  destruct (eq_id_dec X x); try auto; try subst.
  unfold not in H. assert (x=x).
  auto. apply H in H0. inversion H0.
  Qed.
  
Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof.
  apply or_introl.
  intros st st'; split; intros H;
  inversion H; subst; inversion H2; subst;
  inversion H5; subst;
  destruct (eq_id_dec X Y) eqn:eqid;
  inversion eqid; rewrite update_swap; auto.
  apply E_Seq with (update st Y n0);
    apply E_Havoc.
  apply E_Seq with (update st X n0);
    apply E_Havoc.
  Qed.

Definition ptwice :=
  HAVOC X;; HAVOC Y.

Definition pcopy :=
  HAVOC X;; Y ::= AId X.

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~cequiv ptwice pcopy.
Proof.
  apply or_intror.
  unfold not.
  intro. unfold cequiv in H.
  assert(ptwice / empty_state || update (update empty_state X 0) Y (S 0)
    <-> pcopy / empty_state || update (update empty_state X 0) Y (S 0)).
  apply H. clear H.
  destruct (eq_id_dec X Y) eqn:eqid.
    inversion eqid.
  inversion H0 as [H1 H2].
  clear H0.
  assert(pcopy / empty_state || update (update empty_state X 0) Y 1).
  apply H1. apply E_Seq with (update empty_state X 0);
    apply E_Havoc.
  clear H1. clear H2.
  assert((HAVOC X) / empty_state || update empty_state X 0).
    apply E_Havoc.  
  inversion H; subst. inversion H3; subst.
  inversion H6; subst. simpl in H7.
  destruct n0.
    assert(update (update empty_state X 0) Y (update empty_state X 0 X) Y = update (update empty_state X 0) Y 1 Y).
    rewrite H7. auto. rewrite update_eq in H1. rewrite update_eq in H1.
    rewrite update_eq in H1. inversion H1.
    assert(update (update empty_state X (S n0)) Y (update empty_state X (S n0) X) X = update (update empty_state X 0) Y 1 X).
    rewrite H7. auto. rewrite update_neq in H1; auto. rewrite update_eq in H1.
    rewrite update_neq in H1; auto. rewrite update_eq in H1.
    inversion H1.
  Qed.

Definition p1 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC Y;;
    X ::= APlus (AId X) (ANum 1)
  END.

Definition p2 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    SKIP
  END.

Theorem p1_p2_equiv : cequiv p1 p2.
Proof.
  intros st st'; split; intros; unfold p2.
  unfold p1 in H.
  destruct (eq_id_dec X Y) eqn:eq; inversion eq; subst.
  inversion H; subst.
  apply E_WhileEnd. auto.
  remember (WHILE BNot (BEq (AId X) (ANum 0))
      DO HAVOC Y;; X ::= APlus (AId X) (ANum 1) END) as loopdef eqn:loop.
  assert (False).
  clear H3 H6 st'0.
  induction H; try inversion loop; subst.
  rewrite H in H2. inversion H2.
  apply IHceval2; try auto.
  clear loop IHceval1 IHceval2.
  inversion H0; subst. inversion H5; subst.
  inversion H8; subst. simpl.
  rewrite update_eq. rewrite update_neq; auto.
  simpl in H2.
  destruct (st X).
    inversion H2.
    simpl. auto.
  inversion H0.
  unfold p1; unfold p2 in H.
  remember (st X) as stx.
    destruct stx.
    inversion H; subst.
    apply E_WhileEnd. auto.
    simpl in H2. rewrite <- Heqstx in H2.
    simpl in H2. inversion H2.
    assert(False).
      remember (WHILE BNot (BEq (AId X) (ANum 0)) DO SKIP END)
        as loopdef eqn:loop.
      induction H; subst; try inversion loop.
      rewrite H1 in H. simpl in H. rewrite <- Heqstx in H.
      simpl in H. inversion H.
      apply IHceval2; try auto.
      rewrite H4 in H0.
      inversion H0. subst. auto.
      inversion H0.
  Qed.

Definition p3 : com :=
  Z ::= ANum 1;;
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC X;;
    HAVOC Z
  END.

Definition p4 : com :=
  X ::= (ANum 0);;
  Z ::= (ANum 1).

Theorem p3_p4_inequiv : ~ cequiv p3 p4.
Proof.
  intro. unfold cequiv in H.
  assert(p3/update empty_state X 1||update (update (update (update empty_state X 1) Z 1) X 0) Z 0 <->
    p4/update empty_state X 1||update (update (update (update empty_state X 1) Z 1) X 0) Z 0).
  apply H. inversion H0 as [H1 H2].
  clear H H0 H2.
  assert(p3 / update empty_state X 1 || update (update (update (update empty_state X 1) Z 1) X 0) Z 0).
  apply E_Seq with (update (update empty_state X 1) Z 1).
    apply E_Ass. auto.
    apply E_WhileLoop with (update (update (update (update empty_state X 1) Z 1) X 0) Z 0).
    simpl. auto.
    apply E_Seq with (update (update (update empty_state X 1) Z 1) X 0);
      apply E_Havoc.
    apply E_WhileEnd. simpl. auto.
  apply H1 in H.
  inversion H; subst. inversion H3; subst; simpl in H3.
  simpl in H6. inversion H6; subst; simpl in H7.
  assert (update (update (update empty_state X 1) X 0) Z 1 Z=
     update (update (update (update empty_state X 1) Z 1) X 0) Z 0 Z).
  rewrite H7. auto.
  rewrite update_eq in H0. rewrite update_eq in H0.
  inversion H0.
  Qed.

Definition p5 : com :=
  WHILE (BNot (BEq (AId X) (ANum 1))) DO
    HAVOC X
  END.

Definition p6 : com :=
  X ::= ANum 1.

Theorem p5_p6_equiv : cequiv p5 p6.
Proof.
  intros st st'. unfold p5. unfold p6.
  split. intros.
  remember (WHILE BNot (BEq (AId X) (ANum 1))
      DO HAVOC X END) as loopdef eqn:loop.
  induction H; inversion loop; subst.
  inversion H.
  unfold negb in H1. destruct (beq_nat (st X) 1) eqn:stx.
  assert(st = update st X 1).
    apply functional_extensionality. intros.
    replace 1 with (st X). symmetry.
    apply update_same. auto.
    destruct (st X). inversion stx. destruct n.
    auto. inversion stx.
  assert((X ::= ANum 1) / st || update st X 1 -> (X ::= ANum 1) / st || st).
  rewrite <- H0. auto. apply H2. apply E_Ass. auto.
  inversion H1.
  assert((X ::= ANum 1) / st' || st'').
  apply IHceval2. auto. clear IHceval1 IHceval2.
  inversion H0; subst. inversion H2; subst. simpl.
  assert(update (update st X n) X 1 = update st X 1).
    apply functional_extensionality. intros.
    destruct (eq_id_dec X x) eqn:eqid; subst.
      apply update_eq.
      rewrite update_neq; auto.
      rewrite update_neq; auto.
      rewrite update_neq; auto.
    rewrite H3.
    apply E_Ass.
    auto.
  intro. inversion H; subst. simpl in H.
  remember (st X) as stx.
  destruct stx. apply E_WhileLoop with (update st X 1).
    simpl. rewrite <- Heqstx. auto.
    apply E_Havoc.
    apply E_WhileEnd. simpl. auto.
  destruct stx. simpl. replace (update st X 1) with st.
  apply E_WhileEnd. simpl. rewrite <- Heqstx. auto.
  apply functional_extensionality. intros.
  destruct (eq_id_dec X x) eqn:eqid; subst.
    rewrite update_eq. auto.
    rewrite update_neq; auto.
  apply E_WhileLoop with (update st X 1).
    simpl; rewrite <- Heqstx; auto.
    apply E_Havoc.
    apply E_WhileEnd. simpl. auto.
  Qed.

End Himp.

Definition stequiv (st1 st2 : state) : Prop :=
  forall (X:id), st1 X = st2 X.

Notation "st1 '~' st2" := (stequiv st1 st2) (at level 30).

Lemma stequiv_refl : forall (st : state),
  st ~ st.
Proof.
  intros. intro X. auto. Qed.

Lemma stequiv_sym : forall (st1 st2 : state),
  st1 ~ st2 ->
  st2 ~ st1.
Proof.
  intros. intro X. symmetry. apply H. Qed.

Lemma stequiv_trans : forall (st1 st2 st3 : state),
  st1 ~ st2 ->
  st2 ~ st3 ->
  st1 ~ st3.
Proof.
  intros. intro X. rewrite H. apply H0. Qed.

Lemma stequiv_update : forall (st1 st2 : state),
  st1 ~ st2 ->
  forall (X:id) (n:nat),
  update st1 X n ~ update st2 X n.
Proof.
  intros. intros x.
  destruct (eq_id_dec X x) eqn:eq.
    subst. rewrite update_eq. rewrite update_eq. auto.
    rewrite update_neq; auto. rewrite update_neq; auto.
  Qed.

Lemma stequiv_aeval : forall (st1 st2 : state),
  st1 ~ st2 ->
  forall (a:aexp), aeval st1 a = aeval st2 a.
Proof.
  intros.
  induction a; simpl; auto.
  Qed.

Lemma stequiv_beval : forall (st1 st2 : state),
  st1 ~ st2 ->
  forall (b:bexp), beval st1 b = beval st2 b.
Proof.
  intros.
  induction b; simpl; auto; try rewrite stequiv_aeval with (st2:=st2); auto;
  try rewrite stequiv_aeval with (st1:=st1) (st2:=st2); auto.
  rewrite IHb; auto.
  rewrite IHb1. rewrite IHb2. auto.
  Qed.

Lemma stequiv_ceval: forall (st1 st2 : state),
  st1 ~ st2 ->
  forall (c: com) (st1': state),
    (c / st1 || st1') ->
    exists st2' : state,
    ((c / st2 || st2') /\ st1' ~ st2').
Proof.
  intros st1 st2 STEQV c st1' CEV1. generalize dependent st2.
  induction CEV1; intros st2 STEQV.
  Case "SKIP".
    exists st2. split.
      constructor.
      assumption.
  Case ":=".
    exists (update st2 x n). split.
       constructor. rewrite <- H. symmetry. apply stequiv_aeval.
       assumption. apply stequiv_update. assumption.
  Case ";".
    destruct (IHCEV1_1 st2 STEQV) as [st2' [P1 EQV1]].
    destruct (IHCEV1_2 st2' EQV1) as [st2'' [P2 EQV2]].
    exists st2''. split.
      apply E_Seq with st2'; assumption.
      assumption.
  Case "IfTrue".
    destruct (IHCEV1 st2 STEQV) as [st2' [P EQV]].
    exists st2'. split.
      apply E_IfTrue. rewrite <- H. symmetry. apply stequiv_beval.
      assumption. assumption. assumption.
  Case "IfFalse".
    destruct (IHCEV1 st2 STEQV) as [st2' [P EQV]].
    exists st2'. split.
     apply E_IfFalse. rewrite <- H. symmetry. apply stequiv_beval.
     assumption. assumption. assumption.
  Case "WhileEnd".
    exists st2. split.
      apply E_WhileEnd. rewrite <- H. symmetry. apply stequiv_beval.
      assumption. assumption.
  Case "WhileLoop".
    destruct (IHCEV1_1 st2 STEQV) as [st2' [P1 EQV1]].
    destruct (IHCEV1_2 st2' EQV1) as [st2'' [P2 EQV2]].
    exists st2''. split.
      apply E_WhileLoop with st2'. rewrite <- H. symmetry.
      apply stequiv_beval. assumption. assumption. assumption.
      assumption.
Qed.

Reserved Notation "c1 '/' st '||'' st'" (at level 40, st at level 39).

Inductive ceval' : com -> state -> state -> Prop :=
  | E_equiv : forall c st st' st'',
    c / st || st' ->
    st' ~ st'' ->
    c / st ||' st''
  where "c1 '/' st '||'' st'" := (ceval' c1 st st').

Definition cequiv' (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st ||' st') <-> (c2 / st ||' st').

Lemma cequiv__cequiv' : forall (c1 c2: com),
  cequiv c1 c2 -> cequiv' c1 c2.
Proof.
  unfold cequiv, cequiv'; split; intros.
    inversion H0 ; subst. apply E_equiv with st'0.
    apply (H st st'0); assumption. assumption.
    inversion H0 ; subst. apply E_equiv with st'0.
    apply (H st st'0). assumption. assumption.
Qed.

Example identity_assignment' :
  cequiv' SKIP (X ::= AId X).
Proof.
    unfold cequiv'. intros. split; intros.
    Case "->".
      inversion H; subst; clear H. inversion H0; subst.
      apply E_equiv with (update st'0 X (st'0 X)).
      constructor. reflexivity. apply stequiv_trans with st'0.
      unfold stequiv. intros. apply update_same.
      reflexivity. assumption.
    Case "<-".
      inversion H; subst; clear H.
      apply E_equiv with st'0; auto.
      generalize H0.
      apply identity_assignment.
    Qed.

