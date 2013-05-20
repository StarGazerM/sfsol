Add LoadPath "D:\sfsol".
Require Export Chap2.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check nil.

Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil => 0
  | cons h t => S (length X t)
  end.

Example test_length1 :
    length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.

Example test_length2 :
    length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil => nil X
  | cons h t => snoc X (rev X t) h
  end.

Example test_rev1 :
    rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.

Example test_rev2:
  rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.

Fixpoint app' X l1 l2 : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons X h (app' X t l2)
  end.

Check app'.
Check app.

Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
  | nil => 0
  | cons h t => S (length' _ t)
  end.

Definition list123 :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Check list123.

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
  | nil => 0
  | cons h t => S (length'' t)
  end.

Definition mynil : list nat := nil.

Check @nil.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1, 2, 3].

Check list123'''.

Fixpoint repeat (X : Type) (n : X) (count : nat) : list X := 
  match count with
  | 0 => nil
  | S count' => n :: (repeat X n count')
  end.

Example test_repeat1:
  repeat bool true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app : forall (X : Type) (l : list X),
  app [] l = l.
Proof.
  reflexivity. Qed.

Theorem rev_snoc : forall (X : Type) (v : X) (s : list X),
  rev (snoc s v) = v :: (rev s).
Proof.
  induction s.
  reflexivity.
  simpl. rewrite -> IHs. simpl. reflexivity.
  Qed.

Theorem rev_involutive : forall (X : Type) (l : list X),
  rev (rev l) = l.
Proof.
  induction l.
  reflexivity.
  simpl. rewrite -> rev_snoc. rewrite -> IHl.
  reflexivity. Qed.

Theorem snoc_with_append : forall (X : Type)
   (l1 l2 : list X) (v : X),
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros X l1 l2 v.
  induction l1.
  reflexivity.
  simpl. rewrite -> IHl1.
  reflexivity.
  Qed.

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Implicit Arguments pair [[X] [Y]].

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match (lx,ly) with
  | ([],_) => []
  | (_,[]) => []
  | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.

Fixpoint combine' {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx,ly with
  | [],_ => []
  | _,[] => []
  | x::tx, y::ty => (x,y) :: (combine' tx ty)
  end.

Eval simpl in (combine [1,2] [false,false,true,true]).

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X)*(list Y) :=
  match l with
  | [] => ([],[])
  | (x,y) :: rem => match (split rem) with
    | (xrem,yrem) => ((x::xrem),(y::yrem))
    end
  end.

Example test_split:
  split [(1,false),(2,false)] = ([1,2],[false,false]).
Proof. reflexivity.  Qed.

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Implicit Arguments Some [[X]].
Implicit Arguments None [[X]].

Fixpoint index {X : Type} (n : nat)
               (l : list X) : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n 0 then Some a else index (pred n) l'
  end.

Example test_index1 : index 0 [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 1 [[1],[2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3 : index 2 [true] = None.
Proof. reflexivity. Qed.

Definition hd_opt {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | x :: y => Some x
  end.

Check @hd_opt.

Example test_hd_opt1 : hd_opt [1,2] = Some 1.
  Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [[1],[2]] = Some [1].
  Proof. reflexivity. Qed.

Definition doit3times {X:Type} (f:X -> X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Check plus.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := (f (fst p) (snd p)).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  remember (prod_uncurry f) as f'.
  assert (prod_curry f' x y = f' (x,y)).
    reflexivity.
  rewrite -> H.
  rewrite -> Heqf'.
  reflexivity.
  Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                               (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  remember (prod_curry f) as f'.
  assert (prod_uncurry f' p = f' (fst p) (snd p)).
    reflexivity.
  rewrite -> H.
  rewrite -> Heqf'.
  assert (p = ((fst p),(snd p))).
    destruct p.
    reflexivity.
  assert (f p = f ((fst p),(snd p))).
    rewrite <- H0.
    reflexivity.
  rewrite -> H1.
  reflexivity.
  Qed.

Fixpoint filter {X:Type} (test: X -> bool) (l:list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.

Example test_filter1: filter evenb [1,2,3,4] = [2,4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0,2,4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
    filter (fun l => andb (ble_nat 8 l) (evenb l)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5,2,6,19,129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type} (test : X -> bool) (l : list X)
                     : list X * list X :=
   ((filter test l),(filter (fun x => negb (test x)) l)).

Example test_partition1: partition oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5,9,0] = ([], [5,9,0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y:Type} (f:X -> Y) (l:list X)
             : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (plus 3) [2,0,2] = [5,3,5].
Proof. reflexivity. Qed.

Example test_map2: map oddb [2,1,2,5] = [false,true,false,true].
Proof. reflexivity. Qed.

Example test_map3:
    map (fun n => [evenb n,oddb n]) [2,1,2,5]
  = [[true,false],[false,true],[true,false],[false,true]].
Proof. reflexivity. Qed.

Theorem map_app_distr : forall (X Y: Type) (x y : list X) (f : X -> Y), map f (x ++ y) = (map f x) ++ (map f y).
Proof.
    intros X Y x y f.
    induction x.
    reflexivity.
    simpl. rewrite <- IHx. reflexivity.
    Qed.

Theorem snoc_app : forall (X:Type) (l:list X) (x: X) , snoc l x = l ++ [x] .
Proof.
    intros X l x.
    induction l.
    reflexivity.
    simpl. rewrite -> IHl. reflexivity.
    Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l.
  reflexivity.
  simpl. rewrite <- IHl.
  rewrite -> snoc_app.
  rewrite -> snoc_app.
  apply map_app_distr.
  Qed.

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y) := 
  match l with
  | nil => nil
  | x :: xs => (f x) ++ (flat_map f xs)
  end.

Example test_flat_map1:
  flat_map (fun n => [n,n,n]) [1,5,4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

Fixpoint fold {X Y:Type} (f: X -> Y -> Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Check (fold plus).
Eval simpl in (fold plus [1,2,3,4] 0).

Example fold_example1 : fold mult [1,2,3,4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true,true,false,true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 : fold app [[1],[],[2,3],[4]] [] = [1,2,3,4].
Proof. reflexivity. Qed.

Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition override {X:Type} (f:nat->X) (k:nat) (x:X) : nat->X :=
  fun (k':nat) => if beq_nat k k' then x else f k'.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

Theorem override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.
Proof.
  destruct b.
  reflexivity.
  reflexivity.
  Qed.

Inductive boollist : nat -> Type :=
  boollnil : boollist 0
  | boollcons : forall n, bool -> boollist n -> boollist (S n).

Check boollist.

Implicit Arguments boollcons [[n]].

Check (boollcons true (boollcons false (boollcons true boollnil))).


Fixpoint blapp {n1} (l1: boollist n1)
               {n2} (l2: boollist n2)
             : boollist (n1 + n2) :=
  match l1 with
  | boollnil => l2
  | boollcons _ h t => boollcons h (blapp t l2)
  end.

Inductive llist (X:Type) : nat -> Type :=
  lnil : llist X 0
| lcons : forall n, X -> llist X n -> llist X (S n).

Implicit Arguments lnil [[X]].
Implicit Arguments lcons [[X] [n]].

Check (lcons true (lcons false (lcons true lnil))).

Fixpoint lapp (X:Type)
              {n1} (l1: llist X n1)
              {n2} (l2: llist X n2)
            : llist X (n1 + n2) :=
  match l1 with
  | lnil => l2
  | lcons _ h t => lcons h (lapp X t l2)
  end.

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n,o] = [n,p] ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
  Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q,o] = [r,p]) ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall(q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros H.
  apply H.
  Qed.

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H. Qed.

Theorem rev_exercise1 : forall(l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H.
  destruct l'.
  rewrite -> H. reflexivity.
  rewrite -> H.
  rewrite -> rev_involutive.
  reflexivity.
  Qed.

Theorem unfold_example : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite -> H.
  reflexivity. Qed.

Theorem override_eq : forall {X:Type} x k (f:nat->X),
  (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity. Qed.

Theorem override_neq : forall {X:Type} x1 x2 k1 k2 (f : nat->X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
  intros X x1 x2 k1 k2 f H1 H2.
  unfold override.
  rewrite -> H2.
  apply H1.
  Qed.


Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity. Qed.

Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n o eq. inversion eq. reflexivity. Qed.

Theorem silly5 : forall (n m o : nat),
     [n,m] = [o,o] ->
     [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.

Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
     intros X x y z l j H1 H2.
     inversion H1.
     inversion H2.
     rewrite <- H0.
     reflexivity.
     Qed.

Theorem silly6 : forall (n : nat),
     S n = 0 ->
     2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra. inversion contra. Qed.

Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
     intros X x y z l j H.
     inversion H.
     Qed.

Lemma eq_remove_S : forall n m,
  n = m -> S n = S m.
Proof. intros n m eq. rewrite -> eq. reflexivity. Qed.

Theorem length_snoc' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros X v l. induction l as [| v' l'].
  Case "l = []". intros n eq. rewrite <- eq. reflexivity.
  Case "l = v' :: l'". intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply eq_remove_S. apply IHl'. inversion eq. reflexivity. Qed.

Theorem beq_nat_eq : forall n m,
  true = beq_nat n m -> n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    intros m. destruct m as [| m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". simpl. intros contra. inversion contra.
  Case "n = S n'".
    intros m. destruct m as [| m'].
    SCase "m = 0". simpl. intros contra. inversion contra.
    SCase "m = S m'". simpl. intros H.
      apply eq_remove_S. apply IHn'. apply H. Qed.

(* Informal proof needs to be inserted *)

Theorem beq_nat_eq' : forall m n,
  beq_nat n m = true -> n = m.
Proof.
  intros m. induction m as [| m'].
  destruct n.
  reflexivity.
  intros H. inversion H.
  destruct n.
  intros H. inversion H.
  simpl. intros H.
  assert (n=m').
  apply IHm'.
  rewrite -> H. reflexivity.
  rewrite <- H0.
  reflexivity.
  Qed.

Theorem beq_nat_0_r : forall n,
  true = beq_nat 0 n -> 0 = n.
Proof.
  intros n.
  induction n.
  reflexivity.
  simpl.
  intros H.
  inversion H.
  Qed.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n. induction n as [| n'].
  destruct m.
  reflexivity.
  simpl. reflexivity.
  destruct m.
  simpl. reflexivity.
  simpl. apply IHn'.
  Qed.

(* beq_nat_sym informal to be written *)

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b ->
     beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5 ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.

Theorem insert_S : forall n m,
  S n = S m -> n = m.
Proof.
  intros n m H.
  replace n with (pred (S n)).
  replace m with (pred (S m)).
  rewrite <- H. reflexivity.
  reflexivity. reflexivity.
  Qed.
  

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n.
  induction n.
  simpl. intros m.
  intros H.
  destruct m.
  reflexivity.
  inversion H.
  destruct m.
  intros H. inversion H.
  simpl. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm.
  intros H.
  apply insert_S in H.
  apply insert_S in H.
  apply IHn in H.
  rewrite -> H.
  reflexivity.
  Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity. Qed.

Theorem override_shadow : forall {X:Type} x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f.
  unfold override.
  destruct (beq_nat k1 k2).
  reflexivity.
  reflexivity.
  Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| [x y] l'].
  intros l1 l2 H.
  inversion H.
  reflexivity.
  intros l1 l2 H.
  simpl in H.
  destruct (split l').
  inversion H.
  simpl.
  rewrite -> IHl'.
  reflexivity.
  reflexivity.
  Qed.

Theorem split_combine : forall X Y (l1 : list X) (l2 : list Y),
  length(l1) = length(l2) -> split ( combine l1 l2 ) = ( l1 , l2 ).
Proof.
  intros X Y l1.
  induction l1.
  destruct l2.
  intros H.
  reflexivity.
  intros H.
  inversion H.
  destruct l2.
  intros H.
  inversion H.
  intros H.
  inversion H.
  simpl.
  rewrite -> IHl1.
  reflexivity.
  apply H1.
  Qed.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  remember (beq_nat n 3) as e3.
  destruct e3.
  Case "e3 = true". apply beq_nat_eq in Heqe3.
    rewrite -> Heqe3. reflexivity.
  Case "e3 = false".
    remember (beq_nat n 5) as e5. destruct e5.
    SCase "e5 = true".
      apply beq_nat_eq in Heqe5.
      rewrite -> Heqe5. reflexivity.
    SCase "e5 = false". inversion eq. Qed.

Theorem override_same : forall{X:Type} x1 k1 k2 (f : nat->X),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f.
  unfold override.
  remember (beq_nat k1 k2) as eq12.
  destruct eq12.
  intros H.
  apply beq_nat_eq in Heqeq12.
  rewrite <- H.
  rewrite -> Heqeq12.
  reflexivity.
  reflexivity.
  Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
  intros X test x l lf.
  induction l.
  intros H. simpl in H. inversion H.
  intros H. simpl in H.
  remember (test x0) as t0.
  destruct t0.
  inversion H.
  rewrite <- H1.
  rewrite <- Heqt0.
  reflexivity.
  apply IHl.
  apply H.
  Qed.

Theorem trans_eq : forall {X:Type} (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n k o p eq1 eq2.
  apply trans_eq with (m:=k).
  apply eq2.
  apply eq1.
  Qed.

Theorem beq_nat_trans : forall n m p,
  true = beq_nat n m ->
  true = beq_nat m p ->
  true = beq_nat n p.
Proof.
  intros n k p H1 H2.
  apply beq_nat_eq in H1.
  apply beq_nat_eq in H2.
  assert (n = p).
  apply trans_eq with (m:=k).
  apply H1.
  apply H2.
  rewrite -> H.
  apply beq_nat_refl.
  Qed.

Theorem override_permute : forall {X:Type} x1 x2 k1 k2 k3 (f : nat->X),
  false = beq_nat k2 k1 ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros X x1 x2 k1 k2 k3 f.
  unfold override.
  intros H.
  remember (beq_nat k1 k3) as e13.
  remember (beq_nat k2 k3) as e23.
  destruct e13.
  destruct e23.
  rewrite -> beq_nat_sym in Heqe13.
  assert (true = beq_nat k2 k1).
    apply beq_nat_trans with (m:=k3).
    apply Heqe23.
    apply Heqe13.
  rewrite <- H0 in H.
  inversion H.
  reflexivity.
  destruct e23.
  reflexivity.
  reflexivity.
  Qed.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4,7,0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l.
  induction l.
  reflexivity.
  simpl.
  assert (fold_length (x::l) = S (fold_length l)).
    unfold fold_length. reflexivity.
  rewrite -> H.
  rewrite -> IHl.
  reflexivity.
  Qed.

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x ys => (f x)::ys) l [].
Theorem fold_map_eq : forall {X Y : Type} (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  intros X Y f l.
  induction l.
  reflexivity.
  assert (fold_map f (x::l) = (f x) :: (fold_map f l)).
  unfold fold_map. reflexivity.
  rewrite -> H.
  rewrite -> IHl.
  reflexivity.
  Qed.

Module MumbleBaz.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(*
    d (b a 5)           False
    d mumble (b a 5)    True
    d bool (b a 5)      True
    e bool true         True
    e mumble (b c 0)    True
    e bool (b c 0)      False
    c                   False

*)

Inductive baz : Type :=
   | x : baz -> baz
   | y : baz -> bool -> baz.

(*

baz_num_elts = 0

*)

End MumbleBaz.

Fixpoint forallb {X:Type} (f:X->bool) (l:list X) : bool :=
  match l with
  | [] => true
  | x :: xs => if (f x) then (forallb f xs) else false
  end.

Fixpoint existsb {X:Type} (f:X->bool) (l:list X) : bool :=
  match l with
  | nil => false
  | x :: xs => if (f x) then true else (existsb f xs)
  end.

Example forallb1 : forallb oddb [1,3,5,7,9] = true.
Proof. reflexivity. Qed.

Example forallb2 : forallb (beq_nat 5) [] = true.
Proof. reflexivity. Qed.

Example forallb3 : forallb negb [false,false] = true.
Proof. reflexivity. Qed.

Example forallb4 : forallb evenb [0,2,4,5] = false.
Proof. reflexivity. Qed.

Example existsb1 : existsb (beq_nat 5) [0,2,3,6] = false.
Proof. reflexivity. Qed.

Example existsb2 : existsb oddb [1,0,0,0,0,3] = true.
Proof. reflexivity. Qed.

Example existsb3 : existsb (andb true) [true,true,false] = true.
Proof. reflexivity. Qed.

Example existsb4 : existsb evenb [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X:Type} (f:X->bool) (l:list X) : bool :=
  negb (forallb (fun x:X => negb (f x)) l).

Theorem eq_existsb_existsb' : forall (X:Type) (f:X->bool) (l:list X),
  existsb f l = existsb' f l.
Proof.
  intros X f l.
  induction l.
  reflexivity.
  simpl. unfold existsb'.
  simpl.
  remember (f x) as fx.
  destruct fx.
  reflexivity.
  rewrite -> IHl.
  unfold existsb'.
  simpl.
  reflexivity.
  Qed.

(* Informal proof yet to write for ∀ X n l, length l = n → @index X (S n) l = None. *)
