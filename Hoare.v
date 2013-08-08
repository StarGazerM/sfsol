Add LoadPath "D:\sfsol".
Require Export Imp.

Definition Assertion := state -> Prop.

Definition as1 : Assertion := fun st => st X = 3.
Definition as2 : Assertion := fun st => st X <= st Y.
Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion := fun st => True.
Definition as6 : Assertion := fun st => False.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st || st' ->
       P st ->
       Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros. unfold hoare_triple.
  intros. apply H.
  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros. unfold hoare_triple.
  intros. apply H in H1. inversion H1.
  Qed.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple;
  intros.
  inversion H. subst.
  unfold assn_sub in H0. assumption.
  Qed.

Example assn_sub_example :
  {{(fun st => st X = 3) [X |-> ANum 3]}}
  (X ::= (ANum 3))
  {{fun st => st X = 3}}.
Proof.
  apply hoare_asgn. Qed.

Example assn_sub_example2 :
  {{(fun st => st X <= 5) [X |-> APlus (AId X) (ANum 5)]}}
  (X ::= APlus (AId X) (ANum 5))
  {{fun st => st X <= 5}}.
Proof.
  apply hoare_asgn. Qed.

Example assn_sub_example3 :
  {{(fun st => (0 <= st X)/\(st X <= 5)) [X |-> ANum 3]}}
  (X ::= (ANum 3))
  {{fun st => (0 <= st X)/\(st X <= 5)}}.
Proof.
  apply hoare_asgn. Qed.

Definition hoare_asgn2 : Prop := forall X a,
  {{fun st => True}} (X ::= a) {{fun st => st X = aeval st a}}.

Theorem hoare_asgn_wrong :
  ~ hoare_asgn2.
Proof.
  unfold not. intro.
  unfold hoare_asgn2 in H.
  assert({{fun st => True}} (X ::= APlus (AId X) (ANum 1)) 
           {{fun st => st X = aeval st (APlus (AId X) (ANum 1))}}).
  apply H. unfold hoare_triple in H0.
  assert((X ::= APlus (AId X) (ANum 1)) / empty_state || update empty_state X 1).
    apply E_Ass. auto.
  assert(update empty_state X 1 X = aeval (update empty_state X 1) (APlus (AId X) (ANum 1))).
  apply H0 with empty_state; auto.
  simpl in H2. rewrite update_eq in H2. inversion H2.
  Qed.

Theorem hoare_asgn_fwd :
  (forall {X Y: Type} {f g : X -> Y}, (forall (x: X), f x = g x) -> f = g) ->
  forall m a Q,
  {{fun st => Q st /\ st X = m}}
    X ::= a
  {{fun st => Q (update st X m) /\ st X = aeval (update st X m) a }}.
Proof.
  intros functional_extensionality v a Q.
  unfold hoare_triple. intros st st' Hass HP; inversion HP as [HP1 HP2].
  assert(st = update st' X (st X)). intros. apply functional_extensionality.
  intros. destruct (eq_id_dec X x); subst. rewrite update_eq. auto.
  rewrite update_neq; auto. inversion Hass; subst. rewrite update_neq; auto.
  apply conj. rewrite <- HP2.
  rewrite <- H. assumption.
  inversion Hass. rewrite update_eq. rewrite H3.
  rewrite <- HP2. rewrite <- H. symmetry. assumption.
  Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple. intros. apply H with st; auto.
  Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple. intros. apply H0. apply H with st; auto.
  Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros.
  apply hoare_consequence_post with Q'; auto.
  apply hoare_consequence_pre with P'; auto.
  Qed.

Example hoare_asgn_example1' :
  {{fun st => True}}
  (X ::= (ANum 1))
  {{fun st => st X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H. reflexivity. Qed.

Lemma silly1 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (forall x y : nat, P x y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. apply HP. Abort.

Lemma silly2 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. destruct HP as [y HP'].
  Abort.

Lemma silly2_fixed : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ.
  Abort.

Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  unfold hoare_triple. intros. inversion H; subst.
  assumption. Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' Hseq Hpre.
  inversion Hseq; subst. apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); try assumption.
  Qed.

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}}
  (X ::= a;; SKIP)
  {{fun st => st X = n}}.
Proof.
  intros a n.
  eapply hoare_seq.
    apply hoare_skip.
    eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. subst. reflexivity. Qed.

Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1);; Y ::= (ANum 2))
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  eapply hoare_seq.
    apply hoare_asgn.
    eapply hoare_consequence.
      apply hoare_asgn.
      intros st H. assert(((fun st : state => st X = 1) [X |-> ANum 1]) st).
      reflexivity. apply H0.
    intros st H. unfold assn_sub.
    destruct (eq_id_dec X Y) eqn:eq.
    inversion e. apply conj. rewrite update_neq; auto.
      rewrite update_eq; auto.
  Qed.

Definition swap_program : com :=
  Z ::= AId X;; X ::= AId Y;; Y ::= AId Z.

Theorem swap_exercise :
  {{fun st => st X <= st Y}}
  swap_program
  {{fun st => st Y <= st X}}.
Proof.
  unfold swap_program.
  eapply hoare_seq.
    eapply hoare_seq.
      apply hoare_asgn.
      apply hoare_asgn.
    eapply hoare_consequence_pre.
      apply hoare_asgn.
      intros st H.
      apply H.
  Qed.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros. apply H. Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof. unfold not. intros. inversion H0. rewrite H2 in H.
  inversion H. Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros.
  unfold hoare_triple.
  intros st st' H1 H2.
  inversion H1. eapply H. apply H9. apply conj; auto.
  eapply H0. apply H9. apply conj; auto.
  apply bexp_eval_false; auto.
  Qed.

Example if_example :
    {{fun st => True}}
  IFB (BEq (AId X) (ANum 0))
    THEN (Y ::= (ANum 2))
    ELSE (Y ::= APlus (AId X) (ANum 1))
  FI
    {{fun st => st X <= st Y}}.
Proof.
  eapply hoare_if;
    eapply hoare_consequence_pre;
      try apply hoare_asgn;
      intros st H; inversion H as [H0 H1].
      inversion H1. symmetry in H3. apply beq_nat_eq in H3.
      assert (st X <= 2).
        rewrite H3. auto.
      apply H2.
      assert (st X <= (st X) + 1).
        rewrite plus_comm. repeat constructor.
      apply H2.
      Qed.

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}.
Proof.
  eapply hoare_if;
    eapply hoare_consequence_pre;
      try apply hoare_asgn;
      intros st H; inversion H as [H0 H1].
      inversion H1.
      assert(forall n1 n2, n1<=n2 -> n2 = n1 + (n2 - n1)).
        induction n1; intros. simpl. destruct n2; auto.
        destruct n2. inversion H2.
        simpl. rewrite <- IHn1; auto.
        apply le_S_n. auto.
      apply H2.
      destruct (eq_id_dec Z X) eqn:idzx; try inversion idzx.
      rewrite update_neq; auto.
      destruct (eq_id_dec Z Y) eqn:idzy; try inversion idzy.
      rewrite update_neq; auto.
      apply ble_nat_true; auto.
      reflexivity.
  Qed.

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "CIF1" ].

Notation "'SKIP'" := 
  CSkip.
Notation "c1 ;; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" := 
  (CAss X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'IF1' b 'THEN' c 'FI'" := 
  (CIf1 b c) (at level 80, right associativity).

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
  | E_If1True : forall (st st' : state) (b : bexp) (c : com),
               beval st b = true ->
               c / st || st' -> (IF1 b THEN c FI) / st || st'
   | E_If1False : forall (st : state) (b : bexp) (c : com),
               beval st b = false ->
               (IF1 b THEN c FI) / st || st

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
  | Case_aux c "E_If1True" | Case_aux c "E_If1False"
  ].

