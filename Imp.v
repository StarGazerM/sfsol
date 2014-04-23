Add LoadPath "D:\sfsol".
Require Export SfLib.

Module AExp.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (e : aexp) : nat :=
  match e with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Fixpoint beval (e : bexp) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2 => ble_nat (aeval a1) (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (e:aexp) : aexp :=
  match e with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound: forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e. induction e.
  Case "ANum". reflexivity.
  Case "APlus". destruct e1.
    SCase "e1 = ANum n". destruct n.
      SSCase "n = 0". simpl. apply IHe2.
      SSCase "n <> 0". simpl. rewrite IHe2. reflexivity.
    SCase "e1 = APlus e1_1 e1_2".
      simpl. simpl in IHe1. rewrite IHe1.
      rewrite IHe2. reflexivity.
    SCase "e1 = AMinus e1_1 e1_2".
      simpl. simpl in IHe1. rewrite IHe1.
      rewrite IHe2. reflexivity.
    SCase "e1 = AMult e1_1 e1_2".
      simpl. simpl in IHe1. rewrite IHe1.
      rewrite IHe2. reflexivity.
  Case "AMinus".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  Case "AMult".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity. Qed.

Theorem ev100 : ev 100.
Proof.
  repeat (apply ev_SS).
  apply ev_0.
Qed.

Theorem ev100' : ev 100.
Proof.
  repeat (apply ev_0). (* doesn't fail, applies ev_0 zero times *)
  repeat (apply ev_SS). apply ev_0. (* we can continue the proof *)
Qed.

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. (* this just does reflexivity *) Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* just reflexivity would have failed *)
  apply HP. (* we can still finish the proof in some other way *)
Qed.

Lemma foo : forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n.
    (* Leaves two subgoals...  *)
    Case "n=0". simpl. reflexivity.
    Case "n=Sn'". simpl. reflexivity.
    (* ... which are discharged similarly *)
Qed.

Lemma foo' : forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n; (* destruct the current goal *)
  simpl; (* then simpl each resulting subgoal *)
  reflexivity. (* then do reflexivity on each resulting subgoal *)
Qed.

Theorem optimize_0plus_sound': forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  induction e;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity).
  (* The remaining cases -- ANum and APlus -- are more
     interesting... *)
  Case "ANum". reflexivity.
  Case "APlus".
    destruct e1;
      (* Again, most cases follow directly by the IH *)
      try (simpl; simpl in IHe1; rewrite IHe1;
           rewrite IHe2; reflexivity).
    (* The interesting case, on which the try... does nothing, 
       is when e1 = ANum n. In this case, we have to destruct 
       n (to see whether the optimization applies) and rewrite 
       with the induction hypothesis. *)
    SCase "e1 = ANum n". destruct n;
      simpl; rewrite IHe2; reflexivity. Qed.

Theorem optimize_0plus_sound'': forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  induction e;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when e = APlus e1 e2. *)
  Case "APlus".
    destruct e1; try (simpl; simpl in IHe1; rewrite IHe1;
                      rewrite IHe2; reflexivity).
    SCase "e1 = ANum n". destruct n;
      simpl; rewrite IHe2; reflexivity. Qed.

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

Theorem optimize_0plus_sound''': forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  aexp_cases (induction e) Case;
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
    try reflexivity.
  (* At this point, there is already an "APlus" case name
     in the context.  The Case "APlus" here in the proof 
     text has the effect of a sanity check: if the "Case" 
     string in the context is anything _other_ than "APlus"
     (for example, because we added a clause to the definition
     of aexp and forgot to change the proof) we'll get a 
     helpful error at this point telling us that this is now
     the wrong case. *)
  Case "APlus".
    aexp_cases (destruct e1) SCase;
      try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
    SCase "ANum". destruct n;
      simpl; rewrite IHe2; reflexivity. Qed.

Fixpoint optimize_0plus_b (e:bexp) : bexp :=
  match e with
  | BTrue => BTrue
  | BFalse => BFalse
  | (BEq e1 e2) => (BEq (optimize_0plus e1) (optimize_0plus e2))
  | (BLe e1 e2) => (BLe (optimize_0plus e1) (optimize_0plus e2))
  | (BNot e1) => (BNot e1)
  | (BAnd e1 e2) => (BAnd e1 e2)
  end.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse"
  | Case_aux c "BEq" | Case_aux c "BLe"
  | Case_aux c "BNot" | Case_aux c "BAnd" ].

Theorem optimize_0plus__b_sound: forall e,
  beval (optimize_0plus_b e) = beval e.
Proof.
  intros.
  bexp_cases (destruct e) Case;
    try (simpl;repeat rewrite -> optimize_0plus_sound''';reflexivity).
    Qed.

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n: nat),
      aevalR (ANum n) n
  | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Notation "e || n" := (aevalR e n) : type_scope.

End aevalR_first_try.

Reserved Notation "e || n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) ||  n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)

  where "e || n" := (aevalR e n) : type_scope.

Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_ANum" | Case_aux c "E_APlus"
  | Case_aux c "E_AMinus" | Case_aux c "E_AMult" ].

Theorem aeval_iff_aevalR : forall a n,
  (a || n) <-> aeval a = n.
Proof.
 split.
 Case "->".
   intros H.
   aevalR_cases (induction H) SCase; simpl.
   SCase "E_ANum".
     reflexivity.
   SCase "E_APlus".
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
   SCase "E_AMinus".
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
   SCase "E_AMult".
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
 Case "<-".
   generalize dependent n.
   aexp_cases (induction a) SCase;
      simpl; intros; subst.
   SCase "ANum".
     apply E_ANum.
   SCase "APlus".
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   SCase "AMinus".
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   SCase "AMult".
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

Theorem aeval_iff_aevalR' : forall a n,
  (a || n) <-> aeval a = n.
Proof.
  (* WORKED IN CLASS *)
  split.
  Case "->".
    intros H; induction H; subst; reflexivity.
  Case "<-".
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

Reserved Notation "e |b n" (at level 50, left associativity).

Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue : (bevalR BTrue true)
  | E_BFalse : (bevalR BFalse false)
  | E_BEq : forall (e1 e2:aexp) (n1 n2:nat), (aevalR e1 n1) -> (aevalR e2 n2) -> (bevalR (BEq e1 e2) (beq_nat n1 n2))
  | E_BLe : forall (e1 e2:aexp) (n1 n2:nat), (aevalR e1 n1) -> (aevalR e2 n2) -> (bevalR (BLe e1 e2) (ble_nat n1 n2))
  | E_BNot : forall (e:bexp) (b:bool), (bevalR e b) -> (bevalR (BNot e) (negb b))
  | E_BAnd : forall (e1 e2:bexp) (b1 b2:bool), (bevalR e1 b1) -> (bevalR e2 b2) -> (bevalR (BAnd e1 e2) (andb b1 b2))

  where "e |b b" := (bevalR e b) : type_scope.

Tactic Notation "bevalR_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_BTrue" | Case_aux c "E_BFalse"
  | Case_aux c "E_BEq" | Case_aux c "E_BLe"
  | Case_aux c "E_BNot" | Case_aux c "E_BAnd" ].

Theorem beval_iff_bevalR : forall a b,
  (a |b b) <-> beval a = b.
Proof.
  split.
  Case "->".
    intros H; induction H; subst; simpl; try rewrite -> aeval_iff_aevalR' in H; try rewrite -> aeval_iff_aevalR' in H0; try constructor; auto.
  Case "<-".
    generalize dependent b.
    induction a; simpl; intros; subst; constructor; try apply aeval_iff_aevalR'; try apply IHa; try apply IHa1; try apply IHa2; try reflexivity.
    Qed.

End AExp.

Module Id.

Inductive id : Type :=
  Id : nat -> id.

Definition beq_id X1 X2 :=
  match (X1, X2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall X,
  true = beq_id X X.
Proof.
  intros. destruct X.
  apply beq_nat_refl. Qed.

Theorem beq_id_eq : forall i1 i2,
  true = beq_id i1 i2 -> i1 = i2.
Proof.
  intros; destruct i1; destruct i2. unfold beq_id in H.
  apply beq_nat_eq in H; subst; reflexivity.
  Qed.

Theorem beq_id_false_not_eq : forall i1 i2,
  beq_id i1 i2 = false -> i1 <> i2.
Proof.
  intros. destruct i1; destruct i2.
  unfold beq_id in H. unfold not. intros H2.
  inversion H2. subst. rewrite <- beq_nat_refl in H. inversion H.
  Qed.

Theorem not_eq_beq_id_false : forall i1 i2,
  i1 <> i2 -> beq_id i1 i2 = false.
Proof.
  intros. unfold not in H.
  remember (beq_id i1 i2) as tmp.
  destruct tmp. apply beq_id_eq in Heqtmp.
  contradiction. reflexivity.
  Qed.

Theorem beq_id_sym: forall i1 i2,
  beq_id i1 i2 = beq_id i2 i1.
Proof.
  intros. remember (beq_id i1 i2) as b12.
  destruct b12.
  apply beq_id_eq in Heqb12. subst. apply beq_id_refl.
  symmetry in Heqb12. apply beq_id_false_not_eq in Heqb12.
  symmetry. apply not_eq_beq_id_false. auto. Qed.

End Id.

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st : state) (X:id) (n : nat) : state :=
  fun X' => if eq_id_dec X X' then n else st X'.

Theorem update_eq : forall n X st,
  (update st X n) X = n.
Proof.
  intros.
  unfold update. apply eq_id.
  Qed.

Theorem update_neq : forall x2 x1 n st,
  x2 <> x1 ->
  (update st x2 n) x1 = (st x1).
Proof.
  intros.
  unfold update.
  apply neq_id. auto.
  Qed.

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  intros.
  unfold update.
  simpl.
  reflexivity. Qed.

Theorem update_shadow : forall x1 x2 k1 k2 (f : state),
   (update (update f k2 x1) k2 x2) k1 = (update f k2 x2) k1.
Proof.
  intros.
  unfold update.
  destruct (eq_id_dec k2 k1); reflexivity.
  Qed.

Theorem update_same : forall x1 k1 k2 (f : state),
  f k1 = x1 ->
  (update f k1 x1) k2 = f k2.
Proof.
  intros; unfold update; remember (eq_id_dec k1 k2) as b12.
  destruct b12. subst. auto.
  reflexivity.
  Qed.

Theorem update_permute : forall n1 n2 x1 x2 x3 st,
  x2 <> x1 ->
  (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
Proof.
  intros.
  unfold update.
  remember (eq_id_dec x1 x3) as b13.
  destruct b13.
  rewrite e in H; rewrite neq_id; auto.
  reflexivity.
  Qed.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
  | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd" ].

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => ble_nat (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Example aexp1 :
  aeval (update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
  beval (update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.
Proof. reflexivity. Qed.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";;"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1).

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
  Z ::= ANum 5 ;;
  subtract_slowly.

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st || (update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st || st' ->
      c2 / st' || st'' ->
      (c1 ;; c2) / st || st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st || st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st || st' ->
      (WHILE b DO c END) / st' || st'' ->
      (WHILE b DO c END) / st || st''

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Check ceval_ind.

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].

Example ceval_example1:
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   || (update (update empty_state X 2) Z 4).
Proof.
  apply E_Seq with (update empty_state X 2).
  Case "assignment command".
    apply E_Ass. reflexivity.
  Case "if command".
    apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity. Qed.

Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
  apply E_Seq with (update empty_state X 0).
    apply E_Ass. reflexivity.
  apply E_Seq with (update (update empty_state X 0) Y 1).
    apply E_Ass. reflexivity.
  apply E_Ass. reflexivity.
  Qed.

Definition pup_to_n : com :=
  Y ::= ANum 0;;
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    Y ::= APlus (AId Y) (AId X) ;;
    X ::= AMinus (AId X) (ANum 1) 
  END.

Theorem pup_to_2_ceval :
  pup_to_n / (update empty_state X 2) ||
    update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  apply E_Seq with (update (update empty_state X 2) Y 0).
    apply E_Ass. auto.
  apply E_WhileLoop with (update (update (update (update empty_state X 2) Y 0) Y 2) X 1).
    auto.
    apply E_Seq with (update (update (update empty_state X 2) Y 0) Y 2);
      apply E_Ass; auto.
    apply E_WhileLoop with (update (update (update (update (update (update empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0).
      auto.
      apply E_Seq with (update (update (update (update (update empty_state X 2) Y 0) Y 2) X 1) Y 3);
      apply E_Ass; auto.
      apply E_WhileEnd; auto.
  Qed.

Theorem ceval_deterministic: forall c st st1 st2,
     c / st || st1 ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  ceval_cases (induction E1) Case;
           intros st2 E2; inversion E2; subst.
  Case "E_Skip". reflexivity.
  Case "E_Ass". reflexivity.
  Case "E_Seq".
    assert (st' = st'0) as EQ1.
      SCase "Proof of assertion". apply IHE1_1; assumption.
    subst st'0.
    apply IHE1_2. assumption.
  Case "E_IfTrue".
    SCase "b1 evaluates to true".
      apply IHE1. assumption.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H5. inversion H5.
  Case "E_IfFalse".
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H5. inversion H5.
    SCase "b1 evaluates to false".
      apply IHE1. assumption.
  Case "E_WhileEnd".
    SCase "b1 evaluates to false".
      reflexivity.
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H2. inversion H2.
  Case "E_WhileLoop".
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H4. inversion H4.
    SCase "b1 evaluates to true".
      assert (st' = st'0) as EQ1.
        SSCase "Proof of assertion". apply IHE1_1; assumption.
      subst st'0.
      apply IHE1_2. assumption. Qed.

Theorem loop_stop : forall b c st1 st2,
  (beval st2 b) = true ->
  ~ (WHILE b DO c END / st1 || st2).
Proof.
  intros.
  unfold not.
  intros.
  remember (WHILE b DO c END) as loopdef.
  induction H0; try inversion Heqloopdef.
  rewrite H2 in H0. rewrite H0 in H. inversion H.
  apply IHceval2. assumption. auto. Qed.

Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st || st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst. clear Heval. simpl.
  apply update_eq. Qed.

Example XtimesYinZ_Example :
    (X ::= ANum 3;; Y ::= ANum 2;; XtimesYinZ) / empty_state ||
    (update (update (update empty_state X 3) Y 2) Z 6).
Proof.
  apply E_Seq with (update empty_state X 3).
  apply E_Ass; reflexivity.
  apply E_Seq with (update (update empty_state X 3) Y 2);
  apply E_Ass; reflexivity.
  Qed.

Theorem loop_never_stops : forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef eqn:Heqloopdef.
  induction contra;
  try inversion Heqloopdef.
  rewrite -> H1 in H; inversion H.
  apply IHcontra2.
  auto. Qed.

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP => true
  | _ ::= _ => true
  | c1 ;; c2 => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END => false
  end.

Inductive no_whilesR: com -> Prop :=
  | nw1 : no_whilesR SKIP
  | nw2 : forall (x:id) (e:aexp), no_whilesR (x::=e)
  | nw3 : forall (c1 c2:com), no_whilesR c1 -> no_whilesR c2 -> no_whilesR (c1;;c2)
  | nw4 : forall (b:bexp) (c1 c2:com), no_whilesR c1 -> no_whilesR c2 -> no_whilesR (IFB b THEN c1 ELSE c2 FI).

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  split.
  intros.
  induction c; try constructor;try inversion H;
  destruct (no_whiles c1);inversion H1;try apply IHc1; try destruct (no_whiles c2);try apply IHc2;try reflexivity; try assumption.
  intros.
  induction H; try reflexivity; try simpl; rewrite -> IHno_whilesR1; try rewrite -> IHno_whilesR2; auto.
  Qed.

Theorem terminates_no_while:
  forall c,
  (no_whilesR c) -> (forall st, exists st', c / st || st').
Proof.
  intros c H.
  induction H; intros.
  try apply ex_intro with st; try constructor.
  try apply ex_intro with (update st x (aeval st e)); try constructor; try reflexivity.
  try assert( exists st'' : state, c1 / st || st'');
    try apply IHno_whilesR1;
  try inversion H1;
  try assert( exists st' : state, c2 / x || st');
    try apply IHno_whilesR2;
  try inversion H3.
  try apply ex_intro with x0; apply E_Seq with x; auto.
  remember (beval st b) as bval.
  destruct bval.
  try assert( exists st'' : state, c1 / st || st'');
    try apply IHno_whilesR1;
  try inversion H1;
  try apply ex_intro with x; apply E_IfTrue; auto.
  try assert( exists st'' : state, c2 / st || st'');
    try apply IHno_whilesR2;
  try inversion H1;
  try apply ex_intro with x; apply E_IfFalse; auto.
  Qed.

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
  match prog with
  | [] => stack
  | x::xs => match x with
    | (SPush num) => (s_execute st (num::stack) xs)
    | (SLoad id) => (s_execute st ((st id)::stack) xs)
    | SPlus => match stack with
      | [] => (s_execute st [] xs)
      | [y] => (s_execute st [y] xs)
      | y1::y2::ys => (s_execute st ((y2+y1)::ys) xs)
      end
    | SMinus => match stack with
      | [] => (s_execute st [] xs)
      | [y] => (s_execute st [y] xs)
      | y1::y2::ys => (s_execute st ((y2-y1)::ys) xs)
      end
    | SMult => match stack with
      | [] => (s_execute st [] xs)
      | [y] => (s_execute st [y] xs)
      | y1::y2::ys => (s_execute st ((y2*y1)::ys) xs)
      end
    end
  end.

Example s_execute1 :
     s_execute empty_state []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
Proof.
  simpl. reflexivity. Qed.

Example s_execute2 :
     s_execute (update empty_state X 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
Proof. simpl. reflexivity. Qed.

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [(SPush n)]
  | AId x => [(SLoad x)]
  | APlus a1 a2 => (s_compile a1)++(s_compile a2)++[SPlus]
  | AMinus a1 a2 => (s_compile a1)++(s_compile a2)++[SMinus]
  | AMult a1 a2 => (s_compile a1)++(s_compile a2)++[SMult]
  end.

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. reflexivity. Qed.

Theorem s_execute_app : forall x y st stck,
  s_execute st stck (x++y) = s_execute st (s_execute st stck x) y.
Proof.
  intros x.
  induction x.
  reflexivity.
  intros.
  destruct a; try simpl; try apply IHx;
  try destruct stck; try destruct stck; try apply IHx.
  Qed.

Lemma s_compile_correct_strong : forall (st : state) (e : aexp) stck,
  s_execute st stck (s_compile e) = (aeval st e)::stck .
Proof.
  intros st e.
  induction e; try simpl; try reflexivity;
  try intros; rewrite -> s_execute_app; rewrite -> IHe1; rewrite -> s_execute_app; rewrite -> IHe2; reflexivity.
  Qed.
  
Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros.
  apply s_compile_correct_strong.
  Qed.

Module BreakImp.

Inductive com : Type :=
  | CSkip : com
  | CBreak : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "BREAK" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Inductive status : Type :=
  | SContinue : status
  | SBreak : status.

Reserved Notation "c1 '/' st '||' s '/' st'"
                  (at level 40, st, s at level 39).

Inductive ceval : com -> state -> status -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || SContinue / st
  | E_Break : forall st,
      BREAK / st || SBreak / st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st || SContinue / (update st x n)
  | E_SeqCont : forall c1 c2 st st' st'' b1,
      c1 / st || SContinue / st' ->
      c2 / st' || b1 / st'' ->
      (c1 ; c2) / st || b1 / st''
  | E_SeqBr : forall c1 c2 st st',
      c1 / st || SBreak / st' ->
      (c1 ; c2) / st || SBreak / st'
  | E_IfTrue : forall st st' b c1 c2 b1,
      beval st b = true ->
      c1 / st || b1 / st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || b1 / st'
  | E_IfFalse : forall st st' b c1 c2 b1,
      beval st b = false ->
      c2 / st || b1 / st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || b1 / st'
  | E_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st || SContinue / st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st || SContinue / st' ->
      (WHILE b DO c END) / st' || SContinue / st'' ->
      (WHILE b DO c END) / st || SContinue / st''
  | E_WhileLoopBr : forall st st' b c,
      beval st b = true ->
      c / st || SBreak / st' ->
      (WHILE b DO c END) / st || SContinue / st'

  where "c1 '/' st '||' s '/' st'" := (ceval c1 st s st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Break" | Case_aux c "E_Ass" | Case_aux c "E_SeqBr"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse" | Case_aux c "E_SeqCont"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" | Case_aux c "E_WhileLoopBr" ].

Theorem break_ignore : forall c st st' s,
     (BREAK; c) / st || s / st' ->
     st = st'.
Proof.
  intros.
  inversion H. inversion H2.
  inversion H5. auto.
  Qed.

Theorem while_continue : forall b c st st' s,
  (WHILE b DO c END) / st || s / st' ->
  s = SContinue.
Proof.
  intros.
  inversion H; try auto.
  Qed.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  c / st || SBreak / st' ->
  (WHILE b DO c END) / st || SContinue / st'.
Proof.
  intros.
  apply E_WhileLoopBr; assumption.
  Qed.

Theorem while_break_true : forall b c st st',
  (WHILE b DO c END) / st || SContinue / st' ->
  beval st' b = true ->
  exists st'', c / st'' || SBreak / st'.
Proof.
  intros.
  remember (WHILE b DO c END) as lp.
  induction H; try inversion Heqlp.
  rewrite H2 in H. rewrite H0 in H. inversion H.
  apply IHceval2. auto. auto.
  apply ex_intro with st. rewrite <- H4. auto.
  Qed.

Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     c / st || s1 / st1 ->
     c / st || s2 / st2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  intros.
  generalize dependent st2.
  generalize dependent s2.
  induction H; intros. inversion H0; try auto.
  inversion H0; try auto.
  inversion H0. rewrite H6 in H. rewrite H. try auto.
  inversion H1. subst.
    assert(st'=st'0/\SContinue=SContinue).
      apply IHceval1. auto.
    inversion H2 as [Hn1 Hn2].
    assert(st''=st2/\b1=s2).
      apply IHceval2. rewrite -> Hn1. auto. auto.
    subst. assert(st'=st2/\SContinue=SBreak).
    apply IHceval1. auto. inversion H2. inversion H4.
  inversion H0. assert(st'=st'0/\SBreak=SContinue).
    apply IHceval. auto. inversion H8. inversion H10.
    assert(st'=st2/\SBreak=SBreak).
    apply IHceval. auto. auto.
  inversion H1; subst; try apply IHceval; try auto; try rewrite H8 in H; try inversion H.
  inversion H1; subst; try apply IHceval; try auto; try rewrite H8 in H; try inversion H.
  inversion H0;subst; try auto; try rewrite H3 in H; try inversion H.
  inversion H2; subst; try (rewrite H8 in H; inversion H); try apply IHceval2. assert (st'=st'0/\SContinue=SContinue).
    apply IHceval1; auto. inversion H3 as [Hn1 Hn2]. rewrite Hn1. auto.
    assert (st'=st2/\SContinue=SBreak). apply IHceval1. auto. inversion H3 as [Hn1 Hn2]. inversion Hn2.
  inversion H1; subst. rewrite H7 in H; inversion H.
    assert (st'=st'0/\SBreak=SContinue); try apply IHceval; auto. inversion H2 as [Hn1 Hn2]; inversion Hn2.
    split; auto. assert(st' = st2/\SBreak=SBreak). apply IHceval; auto. inversion H2. auto.
  Qed.

End BreakImp.

Fixpoint beval2 (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => ble_nat (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => if (beval st b1) then (beval st b2) else false
  end.

Theorem beval_eq : forall st b,
  beval st b = beval2 st b.
Proof.
  induction b; try reflexivity.
  Qed.

Inductive comf : Type :=
  | CFSkip : comf
  | CFAss : id -> aexp -> comf
  | CFSeq : comf -> comf -> comf
  | CFIf : bexp -> comf -> comf -> comf
  | CFWhile : bexp -> comf -> comf
  | CFFor : comf -> bexp -> comf -> comf -> comf.

Notation "'FSKIP'" :=
  CFSkip.
Notation "x 'F=' a" :=
  (CFAss x a) (at level 60).
Notation "c1 'F;' c2" :=
  (CFSeq c1 c2) (at level 80, right associativity).
Notation "'WHILEF' b 'DO' c 'END'" :=
  (CFWhile b c) (at level 80, right associativity).
Notation "'IFBF' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CFIf c1 c2 c3) (at level 80, right associativity).
Notation "'FOR' '(' c1 ',' b ',' c2 ')' 'DO' c3 'END'" :=
  (CFFor c1 b c2 c3) (at level 80, right associativity).

Reserved Notation "c1 '/f' st '||' st'"
                  (at level 40, st at level 39).

Inductive cevalf : comf -> state -> state -> Prop :=
  | F_Skip : forall st,
      FSKIP /f st || st
  | F_Ass : forall st a1 n x,
      aeval st a1 = n ->
      (x F= a1) /f st || (update st x n)
  | F_Seq : forall c1 c2 st st' st'',
      c1 /f st || st' ->
      c2 /f st' || st'' ->
      (c1 F; c2) /f st || st''
  | F_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 /f st || st' ->
      (IFBF b THEN c1 ELSE c2 FI) /f st || st'
  | F_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 /f st || st' ->
      (IFBF b THEN c1 ELSE c2 FI) /f st || st'
  | F_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILEF b DO c END) /f st || st
  | F_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c /f st || st' ->
      (WHILEF b DO c END) /f st' || st'' ->
      (WHILEF b DO c END) /f st || st''
  | F_ForEnd :  forall st st' c1 b c2 c3,
      c1 /f st || st' ->
      beval st' b = false ->
      (FOR (c1, b, c2) DO c3 END) /f st || st'
  | F_ForLoop : 
      forall st st' st'' st''' c1 b c2 c3,
      c1 /f st || st' ->
      beval st' b = true ->
      (c3 F; c2) /f st' || st'' ->
      (FOR (FSKIP, b, c2) DO c3 END) /f st'' || st''' ->
      (FOR (c1, b, c2) DO c3 END) /f st || st'''

  where "c1 '/f' st '||' st'" := (cevalf c1 st st').
