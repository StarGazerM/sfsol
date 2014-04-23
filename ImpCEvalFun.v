Add LoadPath "D:\sfsol".
Require Import Imp.

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_state
  | S i' =>
    match c with
      | SKIP =>
          st
      | l ::= a1 =>
          update st l (aeval st a1)
      | c1 ;; c2 =>
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.

Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (update st l (aeval st a1))
      | c1 ;; c2 =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (update st l (aeval st a1))
      | c1 ;; c2 =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.

Eval compute in 
     (test_ceval empty_state 
         (X ::= ANum 2;;
          IFB BLe (AId X) (ANum 1)
            THEN Y ::= ANum 3 
            ELSE Z ::= ANum 4
          FI)).

Example pup_to_n_1 : 
  test_ceval (update empty_state X 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.

Definition peven : com :=
  Z ::= ANum 0;;
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    Z ::= AMinus (ANum 1) (AId Z) ;;
    X ::= AMinus (AId X) (ANum 1) 
  END.

Example peven_1 : 
  test_ceval (update empty_state X 5) peven
  = Some (0, 0, 1).
Proof. reflexivity. Qed.

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      c / st || st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].

  Case "i = 0 -- contradictory".
    intros c st st' H. inversion H.

  Case "i = S i'".
    intros c st st' H.
    com_cases (destruct c) SCase;
           simpl in H; inversion H; subst; clear H.
      SCase "SKIP". apply E_Skip.
      SCase "::=". apply E_Ass. reflexivity.

      SCase ";;".
        destruct (ceval_step st c1 i') eqn:Heqr1.
        SSCase "Evaluation of r1 terminates normally".
          apply E_Seq with s.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H1. assumption.
        SSCase "Otherwise -- contradiction".
          inversion H1.

      SCase "IFB".
        destruct (beval st b) eqn:Heqr.
        SSCase "r = true".
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        SSCase "r = false".
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      SCase "WHILE". destruct (beval st b) eqn :Heqr.
        SSCase "r = true".
         destruct (ceval_step st c i') eqn:Heqr1.
          SSSCase "r1 = Some s".
            apply E_WhileLoop with s. rewrite Heqr. reflexivity.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H1. assumption.
          SSSCase "r1 = None".
            inversion H1.
        SSCase "r = false".
          inversion H1.
          apply E_WhileEnd.
          rewrite <- Heqr. subst. reflexivity. Qed.

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  Case "i1 = 0".
    simpl in Hceval. inversion Hceval.
  Case "i1 = S i1'".
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by omega.
    com_cases (destruct c) SCase.
    SCase "SKIP".
      simpl in Hceval. inversion Hceval.
      reflexivity.
    SCase "::=".
      simpl in Hceval. inversion Hceval.
      reflexivity.
    SCase ";;".
      simpl in Hceval. simpl.
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      SSCase "st1'o = Some".
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      SSCase "st1'o = None".
        inversion Hceval.

    SCase "IFB".
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval; assumption.

    SCase "WHILE".
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      SSCase "st1'o = Some".
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      SSCase "i1'o = None".
        simpl in Hceval. inversion Hceval. Qed.

Theorem le_temp: forall i1 i2,
  i1 <= i1 + i2.
Proof.
  intros.
  rewrite -> plus_comm.
  induction i2.
  apply le_n.
  apply le_S. auto.
  Qed.

Theorem ceval__ceval_step: forall c st st',
      c / st || st' ->
      exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  ceval_cases (induction Hce) Case.
  apply ex_intro with 1; reflexivity.
  apply ex_intro with 1; simpl; rewrite H; auto.
  inversion IHHce1 as [i1 IHHce1'];inversion IHHce2 as [i2 IHHce2']; apply ex_intro with (S i1+i2).
  assert(ceval_step st c1 (i1+i2) = Some st').
    apply ceval_step_more with i1. apply le_temp.
    assumption.
  assert(ceval_step st' c2 (i1+i2) = Some st'').
    apply ceval_step_more with i2. rewrite plus_comm. apply le_temp.
    assumption.
  simpl. rewrite H. rewrite H0. reflexivity.
  inversion IHHce as [i IHHce1].
  apply ex_intro with (S i).
  unfold ceval_step. rewrite H. assumption.
  inversion IHHce as [i IHHce1].
  apply ex_intro with (S i).
  unfold ceval_step. rewrite H. assumption.
  apply ex_intro with 1.
  unfold ceval_step. rewrite H. reflexivity.
  inversion IHHce1 as [i1 IHHce1'];inversion IHHce2 as [i2 IHHce2']; apply ex_intro with (S i1+i2).
  assert(ceval_step st c (i1+i2) = Some st').
    apply ceval_step_more with i1. apply le_temp.
    assumption.
  assert(ceval_step st' (WHILE b DO c END) (i1+i2) = Some st'').
    apply ceval_step_more with i2. rewrite plus_comm. apply le_temp.
    assumption. simpl. rewrite H.
    rewrite H0. apply H1.
  Qed.

Theorem ceval_deterministic' : forall c st st1 st2,
     c / st || st1 ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  omega. omega. Qed.