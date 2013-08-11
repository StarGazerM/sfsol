Add LoadPath "D:\sfsol".
Require Export Hoare.

Definition reduce_to_zero' : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem reduce_to_zero_correct' :
  {{fun st => True}}
  reduce_to_zero'
  {{fun st => st X = 0}}.
Proof.
  unfold reduce_to_zero'.
  (* First we need to transform the postcondition so
     that hoare_while will apply. *)
  eapply hoare_consequence_post.
  apply hoare_while.
  Case "Loop body preserves invariant".
    (* Need to massage precondition before hoare_asgn applies *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    (* Proving trivial implication (2) ->> (3) *)
    intros st [HT Hbp]. unfold assn_sub. apply I.
  Case "Invariant and negated guard imply postcondition".
    intros st [Inv GuardFalse].
    unfold bassn in GuardFalse. simpl in GuardFalse.
    (* SearchAbout helps to find the right lemmas *)
    SearchAbout [not true].
    rewrite not_true_iff_false in GuardFalse.
    SearchAbout [negb false].
    rewrite negb_false_iff in GuardFalse.
    SearchAbout [beq_nat true].
    apply beq_nat_true in GuardFalse.
    apply GuardFalse. Qed.

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  intros. destruct x. inversion H. destruct x. inversion H. inversion H1.
  simpl. rewrite <- minus_n_O. reflexivity.
  Qed.

Lemma parity_lt_2 : forall x,
  ~ 2 <= x ->
  parity (x) = x.
Proof.
  intros. destruct x; auto. destruct x; auto.
  assert (False).
  apply H. apply le_n_S. apply le_n_S. induction x;
  constructor. auto. inversion H0.
  Qed.

Theorem parity_correct : forall m,
    {{ fun st => st X = m }}
  WHILE BLe (ANum 2) (AId X) DO
    X ::= AMinus (AId X) (ANum 2)
  END
    {{ fun st => st X = parity m }}.
Proof.
  intros.
  eapply hoare_consequence_post.
    apply hoare_consequence_pre with (fun st => parity (st X) = parity m).
      apply hoare_while.
      eapply hoare_consequence_pre.
        apply hoare_asgn.
        intros st [H1 H2].
        unfold assn_sub. simpl. rewrite update_eq.
        rewrite parity_ge_2. assumption. 
        apply ble_nat_true. apply H2.
      intros st H; rewrite H; reflexivity.
    intros st [H1 H2]. symmetry. rewrite <- parity_lt_2.
      symmetry. assumption.
      unfold not. intro. apply H2.
      apply bexp_eval_true. simpl. destruct (st X); inversion H; auto.
      destruct n. inversion H3. reflexivity.
  Qed.

Definition is_wp P c Q :=
  {{P}} c {{Q}} /\
  forall P', {{P'}} c {{Q}} -> (P' ->> P).

Theorem is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).
Proof.
  unfold is_wp.
  split. eapply hoare_consequence_pre.
  apply hoare_asgn. intros st H. unfold assn_sub.
  rewrite update_eq. simpl. rewrite plus_comm.
  apply le_n_S; auto.
  intros. unfold hoare_triple in H.
  intros st H1.
  assert (update st X ((st Y) + 1 ) X <= 5).
    eapply H.
    constructor. auto. auto.
  rewrite update_eq in H0. rewrite plus_comm in H0.
  apply le_S_n. auto.
  Qed.

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
  intros. unfold is_wp; split.
  apply hoare_asgn.
  unfold hoare_triple.
  intros P H st H1.
  assert(Q (update st X (aeval st a))).
    eapply H; auto; try constructor; auto.
  apply H0.
  Qed.

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "HAVOC" ].

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' X" := (CHavoc X) (at level 60).

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
  | E_Havoc : forall (st : state) (X : id) (n : nat),
              (HAVOC X) / st || update st X n

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
  | Case_aux c "E_Havoc" ].

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', c / st || st' -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
                                  (at level 90, c at next level) 
                                  : hoare_spec_scope.

Definition havoc_pre (X : id) (Q : Assertion) : Assertion :=
  fun st => forall n, Q[X|->ANum n] st.

Theorem hoare_havoc : forall (Q : Assertion) (X : id),
  {{ havoc_pre X Q }} HAVOC X {{ Q }}.
Proof.
  intros Q X st st' Heval Hpre.
  inversion Heval; subst.
  apply Hpre.
  Qed.

Lemma hoare_havoc_weakest : forall (P Q : Assertion) (X : id),
  {{ P }} HAVOC X {{ Q }} ->
  P ->> havoc_pre X Q.
Proof.
  intros P Q X H st H1.
  unfold havoc_pre. intros n.
  unfold hoare_triple in H.
  assert(Q (update st X n)).
    eapply H; try constructor; auto.
  apply H0.
  Qed.

End Himp.

Inductive dcom : Type :=
  | DCSkip : Assertion -> dcom
  | DCSeq : dcom -> dcom -> dcom
  | DCAsgn : id -> aexp -> Assertion -> dcom
  | DCIf : bexp -> Assertion -> dcom -> Assertion -> dcom
           -> Assertion -> dcom
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
      (at level 80, right associativity) : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
      (at level 90, right associativity) : dcom_scope.
Notation "{{ P }} d"
      := (DCPre P d)
      (at level 90) : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
      (at level 80, right associativity) : dcom_scope.
Notation " d ;; d' "
      := (DCSeq d d')
      (at level 80, right associativity) : dcom_scope.

Delimit Scope dcom_scope with dcom.

Example dec_while : dcom := (
  {{ fun st => True }}
  WHILE (BNot (BEq (AId X) (ANum 0)))
  DO
    {{ fun st => True /\ st X <> 0}}
    X ::= (AMinus (AId X) (ANum 1))
    {{ fun _ => True }}
  END
  {{ fun st => True /\ st X = 0}} ->>
  {{ fun st => st X = 0 }}
) % dcom.

Fixpoint extract (d:dcom) : com :=
  match d with
  | DCSkip _ => SKIP
  | DCSeq d1 d2 => (extract d1 ;; extract d2)
  | DCAsgn X a _ => X ::= a
  | DCIf b _ d1 _ d2 _ => IFB b THEN extract d1 ELSE extract d2 FI
  | DCWhile b _ d _ => WHILE b DO extract d END
  | DCPre _ d => extract d
  | DCPost d _ => extract d
  end.

Fixpoint post (d:dcom) : Assertion :=
  match d with
  | DCSkip P => P
  | DCSeq d1 d2 => post d2
  | DCAsgn X a Q => Q
  | DCIf _ _ d1 _ d2 Q => Q
  | DCWhile b Pbody c Ppost => Ppost
  | DCPre _ d => post d
  | DCPost c Q => Q
  end.

Fixpoint pre (d:dcom) : Assertion :=
  match d with
  | DCSkip P => fun st => True
  | DCSeq c1 c2 => pre c1
  | DCAsgn X a Q => fun st => True
  | DCIf _ _ t _ e _ => fun st => True
  | DCWhile b Pbody c Ppost => fun st => True
  | DCPre P c => P
  | DCPost c Q => pre c
  end.

Definition dec_correct (d:dcom) :=
  {{pre d}} (extract d) {{post d}}.

Fixpoint verification_conditions (P : Assertion) (d:dcom) : Prop :=
  match d with
  | DCSkip Q =>
      (P ->> Q)
  | DCSeq d1 d2 =>
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn l a Q =>
      (P ->> Q [l |-> a])
  | DCIf b P1 d1 P2 d2 Q =>
      ((fun st => P st /\ bassn b st) ->> P1)
      /\ ((fun st => P st /\ ~ (bassn b st)) ->> P2)
      /\ (Q <<->> post d1) /\ (Q <<->> post d2)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost =>
      (P ->> post d)
      /\ (Pbody <<->> (fun st => post d st /\ bassn b st))
      /\ (Ppost <<->> (fun st => post d st /\ ~(bassn b st)))
      /\ verification_conditions Pbody d
  | DCPre P' d =>
      (P ->> P') /\ verification_conditions P' d
  | DCPost d Q =>
      verification_conditions P d /\ (post d ->> Q)
  end.

Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} (extract d) {{post d}}.
Proof.
  induction d; intros P H; simpl in *.
    eapply hoare_consequence_pre.
      apply hoare_skip. assumption.
    eapply hoare_seq;
      inversion H as [H1 H2]. apply IHd2.
      apply H2. apply IHd1. apply H1.
    eapply hoare_consequence_pre.
      apply hoare_asgn. assumption.
    eapply hoare_if; inversion H as [H0 [H1 [H2 [H3 [H4 H5]]]]];
      eapply hoare_consequence.
        apply IHd1. apply H4. auto. apply H2.
        apply IHd2. apply H5. auto. apply H3.
    inversion H as [H1 [H2 [H3 H4]]].
    eapply hoare_consequence.
      apply hoare_while.
      eapply hoare_consequence_pre.
      apply IHd. apply H4. apply H2.
      assumption.
      apply H3.
    inversion H. eapply hoare_consequence_pre. apply IHd. apply H1.
    assumption.
    inversion H. eapply hoare_consequence_post. apply IHd. assumption.
    assumption.
    Qed.

Lemma ble_nat_true_iff : forall n m : nat,
  ble_nat n m = true <-> n <= m.
Proof.
  split. apply ble_nat_true.
  destruct (ble_nat n m) eqn:lenm.
    reflexivity.
    intros.
    apply ble_nat_false in H. inversion H. assumption.
  Qed.

Lemma ble_nat_false_iff : forall n m : nat,
  ble_nat n m = false <-> ~(n <= m).
Proof.
  split. apply ble_nat_false.
  destruct (ble_nat n m) eqn:lenm; intros.
  unfold not in H.
  assert (n <= m).
    apply ble_nat_true; assumption.
  apply H in H0. inversion H0.
  reflexivity.
  Qed.

Tactic Notation "verify" :=
  apply verification_correct;
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
  repeat rewrite ble_nat_true_iff in *;
  repeat rewrite ble_nat_false_iff in *;
  try subst;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
          [H : st _ = _ |- _] => rewrite -> H in *; clear H
        | [H : _ = st _ |- _] => rewrite -> H in *; clear H
        end
    end;
  try eauto; try omega.

Theorem dec_while_correct :
  dec_correct dec_while.
Proof. verify. Qed.

Example subtract_slowly_dec (m:nat) (p:nat) : dcom := (
    {{ fun st => st X = m /\ st Z = p }} ->>
    {{ fun st => st Z - st X = p - m }}
  WHILE BNot (BEq (AId X) (ANum 0))
  DO {{ fun st => st Z - st X = p - m /\ st X <> 0 }} ->>
       {{ fun st => (st Z - 1) - (st X - 1) = p - m }}
     Z ::= AMinus (AId Z) (ANum 1)
       {{ fun st => st Z - (st X - 1) = p - m }} ;;
     X ::= AMinus (AId X) (ANum 1)
       {{ fun st => st Z - st X = p - m }}
  END
    {{ fun st => st Z - st X = p - m /\ st X = 0 }} ->>
    {{ fun st => st Z = p - m }}
) % dcom.

Theorem subtract_slowly_dec_correct : forall m p,
  dec_correct (subtract_slowly_dec m p).
Proof. intros m p. verify. Qed.

Example slow_assignment_dec (m:nat) : dcom :=
  ({{ fun st => st X = m }} ->>
  {{ fun st => st X = m /\ 0 = 0 }}
    Y ::= ANum 0
  {{ fun st => st X = m /\ st Y = 0}} ->>
  {{ fun st => st X + st Y = m}};;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      {{ fun st => st X + st Y = m /\ st X <> 0 }} ->>
      {{ fun st => (st X - 1) + (st Y + 1) = m}}
      X ::= AMinus (AId X) (ANum 1)
      {{ fun st => st X + (st Y + 1) = m}};;
      Y ::= APlus (AId Y) (ANum 1)
      {{ fun st => st X + st Y = m }}
    END
   {{ fun st => st X + st Y = m /\ st X = 0 }} ->>
      {{ fun st => st Y = m }}) %dcom.
Theorem slow_asignment_dec_correct : forall m,
  dec_correct (slow_assignment_dec m).
Proof. intros m. verify. Qed.

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

Example slow_factorial_dec (m:nat) : dcom :=
  ({{ fun st => st X = m }} ->>
  {{ fun st => st X = m /\ 1 = 1 }}
    Y ::= ANum 1
  {{ fun st => st X = m /\ st Y = 1}} ->>
  {{ fun st => (st Y) * (real_fact (st X)) = (real_fact m)}};;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      {{ fun st => (st Y) * (real_fact (st X)) = (real_fact m) /\ st X <> 0 }} ->>
      {{ fun st => ((st Y) * (st X)) * (real_fact (st X - 1)) = (real_fact m)}}
      Y ::= AMult (AId Y) (AId X)
      {{ fun st => (st Y) * (real_fact (st X - 1)) = (real_fact m)}};;
      X ::= AMinus (AId X) (ANum 1)
      {{ fun st => (st Y) * (real_fact (st X)) = (real_fact m) }}
    END
   {{ fun st => (st Y) * (real_fact (st X)) = (real_fact m) /\ st X = 0 }} ->>
      {{ fun st => st Y = real_fact m }}) %dcom.
Theorem slow_factorial_dec_correct : forall m,
  dec_correct (slow_factorial_dec m).
Proof. intros m. verify.
  destruct (st X) eqn:stx.
    assert(False); try apply H0; auto.
  inversion H1. simpl in *.
  rewrite <- H. rewrite mult_assoc_reverse.
  rewrite <- minus_n_O. simpl. reflexivity.
  simpl in H. rewrite mult_comm in H. simpl in H.
  rewrite plus_0_r in H. assumption.
  Qed.