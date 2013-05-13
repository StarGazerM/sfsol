Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Example test_negb1: (negb true) = false.
Proof. simpl. reflexivity. Qed.
Example test_negb2: (negb false) = true.
Proof. simpl. reflexivity. Qed.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Example test_andb1: (andb true false) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb2: (andb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb3: (andb false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb4: (andb true true) = true.
Proof. simpl. reflexivity. Qed.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

(* Excercise nandb*)

Definition nandb (b1 : bool) (b2 : bool) : bool :=
 match b1 with
 | true =>  negb(b2)
 | false => true
 end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise andb3*)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
 match b1 with
 | false => false
 | true => (andb b2 b3)
 end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.

Check (negb true).

Check negb.

Module Playground1.

Inductive nat : Type :=
 | O : nat
 | S : nat -> nat.

Definition pred (n:nat) : nat :=
 match n with
 | O => O
 | S n' => n'
 end.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S (S O)))).

Eval simpl in (minustwo 4).

Check S.

Check pred.

Check minustwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. simpl. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Eval simpl in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

(* Excercise factorial *)

Fixpoint factorial (n:nat) : nat := 
  match n with
    | O => 1
    | S n' => mult (S n') (factorial n')
end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Excercise blt_nat*)

Fixpoint blt_nat (n m : nat) : bool :=
  match m with
  | O => false
  | S m' =>
    match n with
      | O => true
      | S n' => blt_nat n' m'
    end
  end.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof. simpl. reflexivity. Qed.

(* Excercise optional simpl_plus *)

Eval simpl in (forall n:nat, n + 0 = n).

Eval simpl in (forall n:nat, 0 + n = n).

Theorem plus_O_n'' : forall n:nat, 0+n = n.
Proof. intros n. reflexivity. Qed.

Theorem plus_1_1 : forall n:nat, 1+n = S n.
Proof. intros n. reflexivity. Qed.

Theorem mult_0_1 : forall n:nat, 0*n = 0.
Proof. intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat,
  n = m ->
  n + n = m + m.

Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.

(* Excercise plus_id_excercise *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m ->
  m = o ->
  n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite <- H2.
  rewrite <- H1.
  reflexivity.
  Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. Qed.

(* Excercise mult_1_plus *)

Theorem mult_1_plus : forall n m : nat,
  (1 + n) * m = m + n * m.
Proof.
  intros n m.
  rewrite -> plus_1_1.
  reflexivity.
  Qed.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity. Qed.

(* Excercise zero_nbeq_plus_1*)

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 ( n + 1 ) = false.
Proof.
  intros n. destruct n as [| n'].
  reflexivity.
  reflexivity.
  Qed.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity. Qed.

(* andb_true_elim2 *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  Case "c = true".
    reflexivity.
  Case "c = false".
    rewrite <- H.
  destruct b.
  SCase "b = true".
    reflexivity.
  SCase "b = false".
    reflexivity.

Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite IHn'. reflexivity. Qed.

(* What about double induction i.e. like one with two basis or two branches*)

(* Excercise basic_induction *)

Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S ( n + m ) = n + ( S m ).
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0".
    simpl. rewrite -> plus_0_r. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S ( S ( double n' ) )
  end.

(* Ecercise double_plus *)

Lemma double_plus : forall n,
  double n = n + n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
  simpl. reflexivity.
  Case "n = S n'".
  simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. Qed.

(* destruct a simple case handling while induction
 follows all cases by PMI *)

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity. Qed.

(* Excercise plus_comm_informal *)

(*

Theorem for any n and m,
  n + m = m + n.
Proof. By induction on n.
  o First suppose n = 0. We must show
      0 + m = m + 0.
    From definition of + we must show
      m = m + 0.
    This follows from theorem plus_0_r : forall n: nat,
      n + 0 = n.
  o Next suppose n = S n'. We must show
      (S n') + m = m + ( S n')
    From definition of +
      S (n' + m) = m + ( S n')
    From Induction Hypothesis.
      S (m + n') = m + ( S n')
    Which is immediate from theorem plus_n_Sm.

*)

(* Excercise beq_nat_refl_informal *)

(*

Theorem for any n,
  true = beq_nat n n.
Proof. By induction on n.
  o When n = 0. We must show
      true = beq_nat 0 0.
    This follows from definition of beq_nat.
  o When n = S n' We must show
      true = beq_nat (S n') (S n').
    Using definition of beq_nat we must show
      true = beq_nat n' n'.
    This directly comes from induction hypothesis.

*)

(* Excercise beq_nat_refl *)

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity. Qed.

(* Excercise mult_comm *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_comm.
  rewrite <- plus_assoc.
  assert (H: p + n = n + p).
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity. Qed.

Theorem mult_n_Sm : forall n m : nat,
  n * S m = n + n * m.
Proof.
  intros n m.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    rewrite -> plus_swap.
    reflexivity.
    Qed.
  


Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m.
  induction m as [| m'].
  Case "m = 0".
    simpl. rewrite mult_0_r. reflexivity.
  Case "m = S m'".
    simpl.
    rewrite <- IHm'.
    rewrite <- mult_n_Sm.
    reflexivity.
    Qed.

(* Excercise evenb_n_oddb_Sn *)

Theorem evenb_n_oddb_Sn : forall n : nat,
  evenb n = negb ( evenb ( S n )).
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    assert (H : evenb n' = evenb (S (S n'))).
      reflexivity.
    rewrite <- H.
    assert (H' : negb (negb (evenb (S n'))) = evenb (S n')).
      rewrite -> negb_involutive. reflexivity.
    rewrite -> IHn'.
    rewrite -> H'.
    reflexivity.
    Qed.

(* Excercise more_excercises *)

Theorem ble_nat_refl : forall n : nat,
  true = ble_nat n n.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem zero_nbeq_S : forall n : nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n.
  reflexivity. Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b.
  destruct b as [].
  Case "b = true".
    reflexivity.
  Case "b = false".
    reflexivity.
  Qed.

Theorem plus_ble_compat_1 : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p H.
  induction p as [| p'].
  Case "p = 0".
    simpl. rewrite -> H. reflexivity.
  Case "p = S p'".
    simpl. rewrite -> IHp'. reflexivity.
  Qed.

Theorem S_nbeq_0 : forall n : nat,
  beq_nat (S n) 0 = false.
Proof.
  intros n.
  reflexivity.
  Qed.

Theorem mult_1_1 : forall n : nat, 1 * n = n.
Proof.
  intros n.
  simpl.
  rewrite -> plus_0_r.
  reflexivity.
  Qed.

Theorem all3_spec : forall b c : bool,
  orb (andb b c)
    (orb (negb b) (negb c)) = true.
Proof.
  intros b c.
  destruct b as [].
  assert(or_neg : orb c (negb c) = true).
    destruct c as [].
    SCase "c = true".
      reflexivity.
    SCase "c = false".
      reflexivity.
  Case "b = true".
    simpl.
    rewrite -> or_neg.
    reflexivity.
  Case "b = false".
    reflexivity.
  Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction p as [| p'].
  Case "p = 0".
    rewrite -> mult_0_r.
    rewrite -> mult_0_r.
    rewrite -> mult_0_r.
    reflexivity.
  Case "p = p'".
    rewrite -> mult_n_Sm.
    rewrite -> mult_n_Sm.
    rewrite -> mult_n_Sm.
    rewrite -> IHp'.
    rewrite -> plus_comm.
    rewrite -> plus_swap.
    assert( H : n * p' + m * p' + m =
      n * p' + (m + m * p')).
      rewrite -> plus_swap.
      rewrite -> plus_comm.
      reflexivity.
    rewrite -> H.
    rewrite -> plus_assoc.
    reflexivity.
  Qed.

Theorem mult_assoc : forall n m p : nat,
  n * ( m * p ) = ( n * m ) * p.
Proof.
  intros n m p.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> mult_plus_distr_r.
    rewrite -> IHn'.
    reflexivity.
  Qed.

Theorem plus_swap' : forall n m p,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  replace (m + p) with (p + m).
  rewrite -> plus_assoc.
  rewrite -> plus_comm.
  reflexivity.
  rewrite -> plus_comm.
  reflexivity.
  Qed.

Theorem bool_fn_applied_thrice : 
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b.
  Case "b = true".
  remember (f true) as ftrue.
    destruct ftrue.
    SCase "f true = true".
      rewrite <- Heqftrue.
      symmetry.
      apply Heqftrue.
    SCase "f true = false".
      remember (f false) as ffalse.
      destruct ffalse.
      SSCase "f false = true".
        symmetry.
        apply Heqftrue.
      SSCase "f false = false".
        symmetry.
        apply Heqffalse.
  remember (f false) as ffalse.
    destruct ffalse.
    SCase "f false = true".
      remember (f true) as ftrue.
      destruct ftrue.
      SSCase "f true = true".
        symmetry.
        apply Heqftrue.
      SSCase "f true = false".
        symmetry.
        apply Heqffalse.
    SCase "f false = false".
      rewrite <- Heqffalse.
      symmetry.
      apply Heqffalse.
Qed.

(* Excercise binary *)

Inductive bin : Type :=
  | O : bin
  | Tn : bin -> bin
  | T1n : bin -> bin.

Fixpoint inc (n : bin) : bin :=
  match n with
  | O => T1n O
  | T1n n => Tn (inc n)
  | Tn n => T1n n
  end.

Fixpoint bin_unary (n : bin) : nat :=
  match n with
  | O => 0
  | (T1n n) => S ( double ( bin_unary n))
  | (Tn n) => double (bin_unary n)
  end.

Theorem inc_comm : forall n,
  bin_unary( inc n) = S ( bin_unary n).
Proof.
  intros n.
  induction n as [| n'| n'].
  Case "n = 0".
    simpl.
    reflexivity.
  Case "n = Tn n'".
    simpl.
    reflexivity.
  Case "n = T1n n'".
    simpl.
    rewrite -> IHn'.
    simpl.
    reflexivity.
  Qed.

(* Excercise binary_inverse *)

Fixpoint nat_bin (n : nat) : bin :=
  match n with
  | 0 => O
  | S n' => inc ( nat_bin n')
  end.

Theorem eq_bin_nat : forall n : nat,
  bin_unary ( nat_bin n ) = n.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> inc_comm.
    rewrite -> IHn'.
    reflexivity.
Qed.

(*

Since bin_unary is many one. while nat_bin is
one one function. Also nat_bin is inverse of
bin_unary hence bin_unary(nat_bin(n)) = n.
But bin_unary isn't inverse of nat_bin being
many one so nat_bin(bin_unary(n)) = n isn't 
true. For example. Take two binary numbers
O and Tn O. Both convert to 0 in nat. But from
nat 0 converts only to O not Tn O.

*)

Fixpoint normalize (b : bin) : bin :=
  match b with
  | O => O
  | T1n b' => T1n ( normalize b' )
  | Tn b' => match ( normalize b' ) with
    | O => O
    | _ => Tn b'
    end
  end.

Theorem norm_unorm_nat : forall b : bin,
  bin_unary b = bin_unary ( normalize b).
Proof.
  intros b.
  induction b as [| b' | b'].
  Case "b = O".
    reflexivity.
  Case "b = 2*b'".
    simpl.
    remember (normalize b') as normb'.
    destruct normb' as [| n' | n'].
    SCase "b' = 0".
      rewrite -> IHb'.
      simpl.
      reflexivity.
    SCase "b' = 2*n'".
      rewrite -> IHb'.
      simpl.
      rewrite -> IHb'.
      reflexivity.
    SCase "b' = 2*n + 1".
      rewrite IHb'.
      simpl.
      rewrite IHb'.
      reflexivity.
  simpl.
  rewrite -> IHb'.
  reflexivity.
  Qed.

Theorem norm_dub : forall b : bin,
  normalize ( normalize b ) = normalize b.
Proof.
  intros b.
  induction b as [| b'|b'].
  reflexivity.
  remember (normalize b') as normb.
  destruct normb.
    simpl. rewrite <- Heqnormb. reflexivity.
    simpl. rewrite <- Heqnormb. simpl. rewrite <- Heqnormb. reflexivity.
    simpl. rewrite <- Heqnormb. simpl. rewrite <- Heqnormb. reflexivity.
  remember (normalize b') as normb.
  destruct normb.
    simpl. rewrite <- Heqnormb. reflexivity.
    simpl. rewrite <- Heqnormb. rewrite -> IHb'. reflexivity.
    simpl. rewrite <- Heqnormb. rewrite -> IHb'. reflexivity.
  Qed.

Theorem norm_norm : forall b b' : bin,
  normalize b = b' -> normalize b' = b'.
Proof.
  intros b b' H.
  rewrite <- H.
  rewrite -> norm_dub.
  reflexivity.
  Qed.

Theorem norm_T1n : forall b : bin,
  normalize (T1n b) = T1n (normalize b).
Proof.
  intros b.
  destruct b as [| b2| b2].
  reflexivity.
  reflexivity.
  reflexivity.
  Qed.

Theorem norm_Tn : forall b b' : bin,
  normalize b = Tn b' -> Tn ( normalize b) = normalize (Tn b).
Proof.
  intros b b'.
  induction b as [| b2| b2].
  simpl.
  induction b' as [| b3 | b3].
  intros H. rewrite <- H. reflexivity.
  intros H. symmetry. rewrite -> H. assert(H2:Tn (Tn (Tn b3)) = Tn O).
    rewrite <- H. reflexivity.
  rewrite -> H2. rewrite <- IHb3.

Theorem double_nat : forall n : nat,
  nat_bin ( double n ) = normalize (Tn (nat_bin n)).
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    assert( H : Tn (nat_bin (S n')) = Tn ( inc (nat_bin n'))).
      reflexivity.
    rewrite -> H.
    simpl.
    rewrite -> IHn'.
    remember (nat_bin n') as nprime.
    destruct nprime as [| n''| n''].
    SCase "n'' = 0".
      reflexivity.
    SCase "n'' = Tn b''".
      simpl. reflexivity.
    SCase "n'' = T1n b''".
      reflexivity.
  Qed.

Theorem eq_nat_bin_norm : forall b : bin,
  nat_bin ( bin_unary b) = normalize b.
Proof.
  intros b.
  induction b as [| b'| b'].
  Case "b = 0".
    reflexivity.
  Case "b = Tn b'".
    simpl.
    remember (normalize b') as normb'.
    destruct normb' as [| b''| b''].
    SCase "b'' = 0".
    simpl. simpl.

Theorem norm_inc : forall b : bin,
  normalize (inc b) = inc (normalize b).
Proof.
  intros b.
  induction b as [| b2| b2].
  reflexivity.
  simpl. 
  remember (normalize b2) as normb.
  destruct normb as [| nb2| nb2].
    reflexivity.
    reflexivity.
    reflexivity.

Theorem nat_double : forall n : nat,
  nat_bin ( double n) = normalize (Tn nat_bin n)      

Theorem norm_Tn_norm : forall b : bin,
  normalize ( Tn b ) = normalize ( Tn ( normalize b ) ).
Proof.
  intros b.
  induction b as [| b' | b'].
  Case "b = 0".
    reflexivity.
  Case "b = 2b'".
    remember (Tn b') as b.
    simpl.
    rewrite -> IHb'.
    replace (normalize (normalize (Tn (normalize b')))) 
      with (normalize ( Tn b )).
    simpl.
    reflexivity.
    reflexivity.
    reflexivity.