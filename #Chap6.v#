Add LoadPath "F:\sfsol".
Require Export Chap5.

Definition funny_prop1 :=
  forall n, forall (E : beautiful n), beautiful (n+3).

Definition funny_prop1' :=
  forall n, forall (_ : beautiful n), beautiful (n+3).

Definition funny_prop1'' :=
  forall n, beautiful n -> beautiful (n+3).

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Check conj.

Theorem and_example :
  (beautiful 0) /\ (beautiful 3).
Proof.
  apply conj.
  apply b_0.
  apply b_3.
  Qed.

Print and_example.

Theorem and_example' :
  (ev 0) /\ (ev 4).
Proof.
  split.
    Case "left". apply ev_0.
    Case "right". apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP. Qed.

Theorem proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HQ. Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros.
  inversion H as [HP HQ].
  split.
  assumption.
  assumption.
  Qed.

Print and_commut.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.
  split.
  assumption.
  assumption.
  assumption.
  Qed.
  
Theorem even__ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  intros.
  induction n.
  split.
  intros. apply ev_0.
  intros. inversion H.
  inversion IHn as [IHn1 IHn2].
  split.
  apply IHn2.
  intros.
  apply ev_SS. unfold even in H. unfold evenb in H.
  assert (even n). unfold even. apply H.
  apply IHn1. apply H0.
  Qed.

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) (H : P /\ Q) =>
    match H with
    | conj HP HQ => (
      fun (H2 : Q /\ R) =>
        match H2 with
        | conj HQ HR => conj P R HP HR
        end
    )
    end.

Print conj_fact.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity) : type_scope.

Theorem iff_implies : forall P Q : Prop,
  (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  inversion H as [HAB HBA]. apply HAB. Qed.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q H.
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB. Qed.


Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  split.
  intros. assumption.
  intros. assumption.
  Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros.
  inversion H as [HPQ HQP].
  inversion H0 as [HQR HRQ].
  split.
  intros. apply HQR. apply HPQ. apply H1.
  intros. apply HQP. apply HRQ. apply H1.
  Qed.

SearchAbout gorgeous.

Definition beautiful_iff_gorgeous :
  forall n, beautiful n <-> gorgeous n :=
    fun (n:nat) => conj (beautiful n -> gorgeous n) (gorgeous n -> beautiful n) (beautiful__gorgeous n) (gorgeous__beautiful n).

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ. Qed.

Definition or_comm_defn : forall P Q : Prop, P \/ Q -> Q \/ P :=
  fun (P Q : Prop) (H : P \/ Q) =>
    match H with
    | or_introl P1 => or_intror Q P P1
    | or_intror Q1 => or_introl Q P Q1
    end.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. intros H. inversion H as [HP | [HQ HR]].
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR. Qed.

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros.
  inversion H.
  destruct H0.
  apply or_introl.
  apply H0.
  destruct H1.
  apply or_introl.
  apply H1.
  apply or_intror.
  split.
  assumption.
  assumption.
  Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros.
  split.
  apply or_distributes_over_and_1.
  apply or_distributes_over_and_2.
  Qed.

Theorem andb_true__and : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H. Qed.

Theorem and__andb_true : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros.
  destruct b.
  simpl in H.
  apply or_intror.
  apply H.
  apply or_introl. reflexivity.
  Qed.

Theorem orb_true : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros.
  destruct b.
  apply or_introl. reflexivity.
  simpl in H.
  apply or_intror. apply H.
  Qed.

Theorem orb_false : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof.
  intros.
  destruct b.
  inversion H.
  simpl in H.
  split.
  reflexivity.
  apply H.
  Qed.

Inductive False : Prop := .

Check False_ind.

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof.
  intros contra.
  inversion contra. Qed.

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra. Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros.
  inversion H.
  Qed.

Inductive True : Prop := 
  | evidence : forall (P : Prop), P -> True.

Check True_ind.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. inversion H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA.
  apply HNA in HP. inversion HP. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. unfold not. intros G. apply G. apply H. Qed.

Theorem double_neg_inf : forall (P : Prop),
  P -> ~~P.
Proof.
  intros.
  unfold not.
  intros.
  apply H0.
  apply H.
  Qed.

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros.
  unfold not in H0.
  unfold not.
  intros.
  apply H0. apply H. apply H1.
  Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  unfold not.
  intros.
  inversion H.
  apply H1. apply H0.
  Qed.

Theorem five_not_even :
  ~ ev 5.
Proof.
  unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn].
  inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1. Qed.

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof.
  unfold not. intros n H. induction H.
  intros.
  inversion H.
  intros.
  inversion H0.
  apply IHev.
  apply H2.
  Qed.

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.
Definition classic := forall P:Prop,
  ~~P -> P.
Definition excluded_middle := forall P:Prop,
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P/\~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

Theorem peirce__classic : ( forall P Q: Prop,
  ((P->Q)->P)->P ) -> ( forall P:Prop,
  ~~P -> P ).
Proof.
  intros.
  unfold not in H0.
  apply H with (Q := False).
  intros.
  assert(H2 : False).
    apply H0.
    apply H1.
  inversion H2.
  Qed.

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity. Qed.

Theorem inv_inequal : forall n n' : nat,
  S n <> S n' -> n <> n'.
Proof.
  unfold not.
  intros. apply H. rewrite -> H0.
  reflexivity. Qed.

Theorem not_eq_beq_false : forall n n' : nat,
     n <> n' ->
     beq_nat n n' = false.
Proof.
  intros.
  generalize dependent n'.
  induction n.
  intros. unfold not in H.
  destruct n'. apply ex_falso_quodlibet.
  apply H. reflexivity.
  reflexivity.
  destruct n'. reflexivity.
  intros.
  simpl. apply IHn.
  apply inv_inequal. apply H.
  Qed.

Theorem beq_false_not_eq : forall n m,
  false = beq_nat n m -> n <> m.
Proof.
  intros.
  unfold not.
  destruct n.
  destruct m.
  inversion H.
  intros.
  inversion H0.
  intros.
  destruct m.
  inversion H0.
  inversion H0.
  simpl in H.
  rewrite -> H2 in H.
  rewrite <- beq_nat_refl in H.
  inversion H.
  Qed.

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall(witness:X), P witness -> ex X P.

Definition some_nat_is_even : Prop :=
  ex nat ev.

Definition snie : some_nat_is_even :=
  ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2).
  reflexivity. Qed.

Example exists_example_1' : exists n,
  n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity. Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm].
  exists (2 + m).
  apply Hm. Qed.

Definition p : ex nat (fun n => beautiful (S n)) :=
  ex_intro nat (fun n:nat => beautiful (S n)) 2 b_3.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros.
  unfold not.
  intros.
  inversion H0.
  apply H1.
  apply H.
  Qed.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle.
  intros.
  unfold not in H.
  assert((P x) \/ (~ P x)).
  apply H.
  inversion H1.
  apply H2.
  assert(False).
  apply H0.
  apply ex_intro with (witness := x).
  apply H2.
  inversion H3.
  Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  split.
  intros.
  inversion H.
  inversion H0.
  apply or_introl.
  apply ex_intro with (witness := witness).
  apply H1.
  apply or_intror.
  apply ex_intro with (witness := witness).
  apply H1.
  intros.
  inversion H.
  inversion H0.
  apply ex_intro with (witness := witness).
  apply or_introl. apply H1.
  inversion H0.
  apply ex_intro with (witness := witness).
  apply or_intror. apply H1.
  Qed.

Module MyEquality.

Inductive eq (X:Type) : X -> X -> Prop :=
  refl_equal : forall x, eq X x x.

Notation "x = y" := (eq _ x y)
                    (at level 70, no associativity) : type_scope.

Inductive eq' (X:Type) (x:X) : X -> Prop :=
    refl_equal' : eq' X x x.

Notation "x =' y" := (eq' _ x y)
                     (at level 70, no associativity) : type_scope.

Theorem two_defs_of_eq_coincide : forall (X:Type) (x y : X),
  x = y <-> x =' y.
Proof.
  intros.
  split.
  intros.
  inversion H.
  apply refl_equal'.
  intros.
  inversion H.
  apply refl_equal.
  Qed.

Definition four : 2 + 2 = 1 + 3 :=
  refl_equal nat 4.

Definition singleton : forall (X:Set) (x:X), []++[x] = x::[] :=
  fun (X:Set) (x:X) => refl_equal (list X) [x].

End MyEquality.

Module LeFirstTry.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

End LeFirstTry.

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Check le_ind.

Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n. Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 :
  ~ (2 <= 1).
Proof.
  intros H. inversion H. inversion H1. Qed.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : ev (S n) -> next_even n (S n)
  | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

Inductive total_relation (n m:nat) : Prop :=
  | tr_1 : total_relation n m.

Inductive empty_relation (n m:nat) : Prop :=
  | er_1 : ~ (total_relation n m) -> (empty_relation n m).

Module R.

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

Inductive R' : nat -> nat -> nat -> Prop :=
   | d1 : R' 0 0 0
   | d2 : forall m n o, R' m n o -> R' (S m) n (S o)
   | d3 : forall m n o, R' m n o -> R' m (S n) (S o)
   | d4 : forall m n o, R' m n o -> R' n m o.

Inductive R'' : nat -> nat -> nat -> Prop :=
   | e1 : R'' 0 0 0
   | e2 : forall m n o, R'' m n o -> R'' (S m) n (S o)
   | e3 : forall m n o, R'' m n o -> R'' m (S n) (S o).

Theorem e3_R'' : forall (m n o:nat),
  (R'' m (S n) (S o)) <-> (R'' m n o).
Proof.
  split.
  generalize dependent n.
  generalize dependent o.
  induction m.
  intros.
  inversion H.
  apply H3.
  intros.
  inversion H.
  destruct o.
  inversion H3.
  apply e2.
  apply IHm.
  apply H3.
  apply H3.
  intros.
  apply e3.
  apply H.
  Qed.

Theorem e2_R'' : forall (m n o:nat),
  (R'' (S m) n (S o)) <-> (R'' m n o).
Proof.
  split.
  generalize dependent m.
  generalize dependent o.
  induction n.
  intros.
  inversion H.
  apply H3.
  intros.
  inversion H.
  apply H3.
  destruct o.
  inversion H3.
  apply e3.
  apply IHn.
  apply H3.
  intros.
  apply e2.
  apply H.
  Qed.

Theorem e3_e2_R'' : forall (m n o:nat),
  (R'' (S m) n o) <-> (R'' m (S n) o).
Proof.
  split.
  intros.
  destruct o.
  inversion H.
  apply e3.
  apply e2_R''.
  apply H.
  intros.
  destruct o.
  inversion H.
  apply e2.
  apply e3_R''.
  apply H.
  Qed.

Theorem symm_R'' : forall (m n o:nat),
  (R'' m n o) -> (R'' n m o).
Proof.
  induction m.
  induction n.
  intros. apply H.
  intros.
  destruct o.
  inversion H.
  inversion H.
  apply e2.
  apply IHn.
  apply H3.
  intros.
  apply e3_e2_R''.
  apply IHm.
  apply e3_e2_R''.
  apply H.
  Qed.

Theorem eq_R_R'' : forall (m n o:nat),
  (R m n o) <-> (R'' m n o).
Proof.
  split.
  apply R_ind.
  apply e1.
  intros.
  apply e2.
  apply H0.
  intros.
  apply e3.
  apply H0.
  intros.
  apply e2_R''.
  apply e3_R''.
  apply H0.
  intros.
  apply symm_R''.
  apply H0.
  apply R''_ind.
  apply c1.
  intros.
  apply c2.
  apply H0.
  intros.
  apply c3.
  apply H0.
  Qed.

Definition sum_eq (m n o:nat) : Prop :=
  m + n = o.

Theorem eq_R : forall (m n o:nat),
  (R m n o) <-> (sum_eq m n o).
Proof.
  split.
  assert ((R'' m n o) -> (sum_eq m n o)).
  apply R''_ind.
  unfold sum_eq. reflexivity.
  intros.
  unfold sum_eq in H0.
  unfold sum_eq.
  rewrite <- H0.
  reflexivity.
  intros.
  unfold sum_eq in H0.
  unfold sum_eq.
  rewrite <- H0.
  rewrite -> plus_n_Sm.
  reflexivity.
  intros.
  apply H.
  apply eq_R_R''.
  apply H0.
  unfold sum_eq.
  generalize dependent o.
  generalize dependent n.
  induction m.
  intros.
  simpl in H.
  rewrite -> H.
  generalize dependent n.
  induction o.
  intros.
  apply c1.
  intros.
  apply c3.
  destruct n.
  inversion H.
  inversion H.
  apply IHo with (n:=n).
  apply H1.
  intros.
  destruct o.
  inversion H.
  apply c2.
  inversion H.
  apply IHm.
  reflexivity.
  Qed.

End R.

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  | all1 : all X P []
  | all2 : forall (x:X) (l:list X), (P x) -> (all X P l) -> (all X P (x::l)).

Theorem all_forallb : forall (X:Type) (P: X ->bool) (l:list X),
  all X (fun x:X => (P x)=true) l -> (forallb P l = true).
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  inversion H.
  rewrite -> H2.
  apply IHl.
  apply H3.
  Qed.

Inductive in_merge (X:Type) : list X->list X->list X->Prop :=
  | in1 : in_merge X [] [] []
  | in2 : forall (hx:X) (x y xy:list X) , in_merge X x y xy -> in_merge X (hx::x) y (hx::xy)
  | in3 : forall (hy:X) (x y xy:list X) , in_merge X x y xy -> in_merge X x (hy::y) (hy::xy).

Theorem filter_challenge : forall (X:Set) (l1 l2 l:list X) (test:X->bool),
  (all X (fun x:X => (test x)=true) l1)->(all X (fun x:X => (test x)=false) l2)
  ->(in_merge X l1 l2 l)
  -> filter test l=l1.
Proof.
  intros.
  generalize dependent l.
  generalize dependent l2.
  induction l1.
  induction l2.
  intros.
  inversion H1.
  reflexivity.
  intros.
  inversion H1.
  inversion H0.
  unfold filter.
  rewrite -> H9.
  apply IHl2.
  apply H10.
  apply H6.
  intros.
  generalize dependent l.
  generalize dependent l2.
  induction l2.
  intros.
  inversion H1.
  inversion H.
  assert(filter test xy = l1).
  apply IHl1 with (l2:=[]).
  apply H10.
  apply H0.
  apply H6.
  rewrite <- H11.
  unfold filter.
  rewrite -> H9.
  reflexivity.
  intros.
  inversion H.
  inversion H1.
  assert(filter test xy = l1).
  apply IHl1 with (l2:=(x0::l2)).
  apply H5.
  apply H0.
  apply H10.
  rewrite <- H11.
  unfold filter.
  rewrite -> H4.
  reflexivity.
  inversion H0.
  assert(filter test (x0::xy) = filter test xy).
  unfold filter.
  rewrite -> H13.
  reflexivity.
  rewrite -> H15.
  apply IHl2.
  apply H14.
  apply H10.
  Qed.

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

Lemma appears_in_app : forall {X:Type} (xs ys : list X) (x:X),
  appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros X.
  induction xs.
  intros.
  simpl in H.
  apply or_intror.
  apply H.
  intros.
  inversion H.
  apply or_introl.
  apply ai_here.
  assert (appears_in x0 xs \/ appears_in x0 ys).
    apply IHxs.
    apply H1.
  inversion H3 as [ H4 | H5].
    apply or_introl.
    apply ai_later.
    apply H4.
    apply or_intror.
    apply H5.
  Qed.

Lemma app_appears_in : forall {X:Type} (xs ys : list X) (x:X),
  appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros.
  inversion H as [H1 | H2].
  induction xs.
  inversion H1.
  inversion H1.
  apply ai_here.
  apply ai_later.
  apply IHxs.
  apply or_introl.
  apply H2.
  apply H2.
  induction xs.
  apply H2.
  apply ai_later.
  apply IHxs.
  apply or_intror.
  apply H2.
  Qed.

Definition disjoint (X:Type) (l1 l2:list X) :=
  forall (x:X), ((appears_in x l1)/\ ~(appears_in x l2))\/(~(appears_in x l1)/\ (appears_in x l2)).

Inductive no_repeats (X:Type) : list X->Prop :=
  | nr1 : no_repeats X []
  | nr2 : forall (x:X) (l:list X), ~ (appears_in x l) -> no_repeats X (x::l).

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros.
  induction n.
  apply le_n.
  apply le_S.
  apply IHn.
  Qed.  

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros.
  generalize dependent m.
  induction n.
  intros.
  induction m.
  apply le_n.
  apply le_S.
  apply IHm.
  apply O_le_n.
  induction m.
  intros.
  inversion H.
  intros.
  inversion H.
  apply le_n.
  apply le_S.
  apply IHm.
  apply H1.
  Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m. generalize dependent n. induction m.
  intros.
  inversion H.
  apply le_n.
  inversion H1.
  intros.
  inversion H.
  apply le_n.
  apply le_S.
  apply IHm.
  apply H1.
  Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b.
  induction b.
  rewrite -> plus_0_r.
  apply le_n.
  rewrite <- plus_n_Sm.
  apply le_S.
  apply IHb.
  Qed.

Theorem plus_lt_l : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m .
Proof.
  intros.
  generalize dependent m.
  induction n2.
  intros.
  rewrite -> plus_0_r in H.
  apply H.
  intros.
  inversion H.
  unfold lt.
  apply n_le_m__Sn_le_Sm.
  apply le_plus_l.
  rewrite <- H1 in H.
  unfold lt in H.
  apply Sn_le_Sm__n_le_m in H.
  rewrite <- plus_n_Sm in H.
  apply le_S.
  apply IHn2.
  apply H.
  Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros.
  apply conj.
  apply plus_lt_l with (n2:=n2).
  apply H.
  rewrite -> plus_comm in H.
  apply plus_lt_l with (n2:=n1).
  apply H.
  Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  intros.
  apply le_S.
  apply H.
  Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  intros.
  generalize dependent m.
  induction n.
  intros.
  apply O_le_n.
  intros.
  inversion H.
  destruct m.
  inversion H1.
  apply n_le_m__Sn_le_Sm.
  apply IHn.
  apply H1.
  Qed.

Theorem ble_nat_n_Sn_false : forall n m,
  ble_nat n (S m) = false ->
  ble_nat n m = false.
Proof.
  intros.
  generalize dependent m.
  induction n.
  intros.
  inversion H.
  intros.
  inversion H.
  destruct m.
  rewrite -> H1.
  unfold ble_nat.
  reflexivity.
  rewrite -> H1.
  unfold ble_nat.
  apply IHn.
  apply H1.
  Qed.

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  intros.
  generalize dependent n.
  induction m.
  intros.
  unfold not.
  intros.
  inversion H0.
  rewrite -> H1 in H.
  inversion H.
  induction n.
  intros.
  inversion H.
  intros.
  unfold not.
  intros.
  apply Sn_le_Sm__n_le_m in H0.
  generalize H0.
  apply IHm.
  inversion H.
  reflexivity.
  Qed.

Inductive nostutter: list nat -> Prop :=
  | ns1 : nostutter []
  | ns2 : forall (x:nat), (nostutter [x])
  | ns3 : forall (x y:nat) (l:list nat),~(x=y) -> (nostutter (y::l)) -> (nostutter (x::y::l)).

Example test_nostutter_1: nostutter [3,1,4,1,5,6].
Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_2: nostutter [].
Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_3: nostutter [5].
Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_4: not (nostutter [3,1,1,4]).
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.

Lemma app_length : forall {X:Type} (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  generalize dependent l2.
  induction l1.
  auto.
  intros.
  simpl.
  auto.
  Qed.

Lemma appears_in_app_split : forall {X:Type} (x:X) (l:list X),
  appears_in x l ->
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros.
  induction l.
  inversion H.
  inversion H.
  apply ex_intro with (witness:=[]).
  apply ex_intro with (witness:=l).
  reflexivity.
  assert(exists l1 : list X, exists l2 : list X, l = l1 ++ x :: l2).
  auto.
  inversion H3.
  inversion H4.
  apply ex_intro with (witness:=(x0::witness)).
  apply ex_intro with (witness:=witness0).
  rewrite -> H5. reflexivity.
  Qed.

Inductive repeats {X:Type} : list X -> Prop :=
  | rp1 : forall (x:X) (l:list X),(appears_in x l)->(repeats (x::l))
  | rp2 : forall (x:X) (l:list X),(repeats l)->(repeats (x::l)).

Theorem remove_one: forall (X:Type) (x:X) (l l1 l2:list X),
  (forall (x1:X), (appears_in x1 (x::l)) -> (appears_in x1 (l1++(x::l2)))) ->
  (forall (x2:X), ~(x2=x) -> (appears_in x2 l) -> (appears_in x2 (l1++l2))).
Proof.
  intros.
  assert(appears_in x2 (l1++x::l2)).
  apply H.
  apply ai_later.
  apply H1.
  apply appears_in_app in H2.
  inversion H2 as [H3 | H4].
  apply app_appears_in.
  apply or_introl.
  apply H3.
  inversion H4.
  assert(False).
  apply H0. apply H5.
  inversion H3.
  apply app_appears_in.
  apply or_intror.
  apply H5.
  Qed.

Theorem pigeonhole_principle: forall {X:Type} (l1 l2:list X),
  excluded_middle ->
  (forall x, appears_in x l1 -> appears_in x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof. intros X l1. induction l1.
  intros.
  inversion H1.
  intros.
  assert((appears_in x l1)\/~(appears_in x l1)).
  apply H.
  inversion H2 as [H3 | H4].
  apply rp1. apply H3.
  apply rp2.
  assert(appears_in x l2).
  apply H0. apply ai_here.
  apply appears_in_app_split in H3.
  inversion H3.
  inversion H5.
  assert((forall x1 : X, (~x1=x) -> appears_in x1 l1 -> appears_in x1 (witness++witness0))).
  apply remove_one.
  rewrite <- H6.
  apply H0.
  assert(forall x1 : X, appears_in x1 l1 -> appears_in x1 (witness ++ witness0)).
  intros.
  apply H7.
  assert(forall (y y1:X) (l:list X),~(appears_in y l)->(appears_in y1 l)->~(y=y1)).
    induction l.
    intros.
    inversion H10.
    intros.
    inversion H10.
    rewrite <- H12 in H9.
    unfold not in H9.
    unfold not. intros.
    apply H9.
    rewrite -> H12.
    rewrite -> H11.
    apply ai_here.
    apply IHl.
    unfold not.
    intros.
    apply H9.
    apply ai_later.
    apply H14.
    apply H12.
  assert(x<>x1).
  apply H9 with (l:=l1).
  auto.
  auto.
  unfold not.
  auto.
  apply H8.
  apply IHl1 with (l2:=(witness ++ witness0)).
  apply H.
  assumption.
  rewrite -> H6 in H1.
  rewrite -> app_length.
  rewrite -> app_length in H1.
  unfold lt in H1.
  unfold lt.
  apply Sn_le_Sm__n_le_m.
  assert(forall (l:list X), length(x::l)=S (length l)).
    intros.
    unfold length.
    reflexivity.
  rewrite -> H9 in H1.
  rewrite -> H9 in H1.
  rewrite <- plus_n_Sm in H1.
  assumption.
  Qed.