Add LoadPath "D:\sfsol".
Require Export Chap3.

Theorem double_injective' : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". simpl. intros m eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'".
    intros m eq.
    destruct m as [| m'].
    SCase "m = O". inversion eq.
    SCase "m = S m'".
      assert (n' = m') as H.
      SSCase "Proof of assertion". apply IHn'.
        inversion eq. reflexivity.
      rewrite -> H. reflexivity. Qed.

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  Case "m = O". simpl. intros n eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros n eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'".
      assert (n' = m') as H.
      SSCase "Proof of assertion".
        apply IHm'. inversion eq. reflexivity.
      rewrite -> H. reflexivity. Qed.

Theorem plus_n_n_injective_take2 : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  destruct n.
    reflexivity.
    intros H. inversion H.
  destruct n.
    intros H. inversion H.
    rewrite <- plus_n_Sm.
    rewrite <- plus_n_Sm.
    intros H. inversion H.
    assert (n = m). apply IHm.
    apply H1.
    rewrite -> H0.
    reflexivity.
    Qed.

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index (S n) l = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l.
    intros n H.
    destruct n.
      reflexivity.
      inversion H.
    intros n H.
    destruct n.
      inversion H.
      simpl.
      inversion H.
      apply IHl.
      reflexivity.
  Qed.

(* index_after_last_informal yet to write *)

Theorem length_snoc''' : forall (n : nat) (X : Type)
                              (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros n X v l.
  generalize dependent n.
  induction l.
  intros n.
  destruct n.
    reflexivity.
    intros H. inversion H.
  intros n H.
  destruct n.
    inversion H.
    simpl in H. inversion H.
    simpl.
    assert (length (snoc l v) = S n).
    apply IHl. apply H1.
    rewrite -> H.
    rewrite -> H0.
    reflexivity.
  Qed.

Theorem length_snoc'''' : forall (n : nat) (X : Type)
                              (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros n X v l.
  generalize dependent n.
  induction l.
  intros n H.
  destruct n.
    reflexivity.
    inversion H.
  intros n H.
  destruct n.
    inversion H.
    simpl in H. inversion H.
    simpl.
    assert (length (snoc l v) = S n).
      apply IHl.
      apply H1.
    rewrite -> H0.
    rewrite -> H.
    reflexivity.
  Qed.

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X)
                                  (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  intros X l1 l2 x n.
  generalize dependent n.
  induction l1.
  intros n H.
  rewrite <- H.
  reflexivity.
  intros n H.
  destruct n.
    inversion H.
    simpl in H.
    inversion H.
    simpl.
    rewrite -> H1.
    assert(S (length (l1 ++ l2)) = n).
      apply IHl1.
    apply H1.
    rewrite -> H0.
    reflexivity.
  Qed.

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  intros X n l.
  generalize dependent n.
  induction l.
  intros n H.
  simpl in H.
  rewrite <- H.
  reflexivity.
  intros n H.
  destruct n.
    inversion H.
    simpl.
    assert (length (l ++ x :: l) = S (n + n)).
    inversion H.
    assert (length (l ++ l) = n + n).
    apply IHl. apply H1.
    rewrite -> H1.
    rewrite <- H0.
    remember (length (l ++ x :: l)) as len.
    symmetry.
    apply app_length_cons with (x:=x).
    symmetry.
    apply Heqlen.
    rewrite -> H0.
    rewrite -> plus_n_Sm.
    reflexivity.
  Qed.