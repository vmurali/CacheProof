Require Import Tree List Omega.

Inductive BaseTree := B: list BaseTree -> BaseTree.

Section ListProp.
  Context {A: Type}.
  Context (def: A).
  Theorem appLastNth: forall {l i} a, i = length l -> nth i (l ++ (a :: nil)) def = a.
  Proof.
    intros l.
    induction l.
    intros i a i_len.
    simpl in *.
    rewrite i_len.
    auto.
    intros i a0 i_len.
    unfold length in i_len.
    fold (length l) in i_len.
    rewrite i_len.
    unfold app.
    fold (app l (a0 :: nil)).
    simpl.
    specialize (IHl (length l) a0).
    assert (length l = length l) by auto.
    specialize (IHl H).
    assumption.
  Qed.

  Theorem appNotLastNth: forall {l i} a, i < length l -> nth i (l ++ (a :: nil)) def = nth i l def.
  Proof.
    intros l.
    induction l.
    intros i a i_len.
    simpl in *.
    omega.
    intros i a0 i_len.
    unfold app.
    fold (app l (a0::nil)).
    destruct i.
    simpl.
    auto.
    simpl.
    simpl in i_len.
    assert (i < length l) by omega.
    specialize (IHl i a0 H).
    assumption.
  Qed.

  Theorem appLen: forall (l: list A) a, length (l ++ a :: nil) = S (length l).
  Proof.
    intros l a.
    induction l.
    simpl.
    auto.
    unfold app.
    fold (app l (a :: nil)).
    simpl.
    omega.
  Qed.

  Theorem revLen: forall (l: list A), length l = length (rev l).
  Proof.
    intros l.
    induction l.
    simpl.
    auto.
    simpl.
    pose proof (appLen (rev l) a).
    rewrite H; clear H.
    omega.
  Qed.

  Theorem revProp: forall {l i}, i < length l -> nth i l def = nth (length l - S i) (rev l) def.
  Proof.
    intros l.
    induction l.
    intros i i_lt_len.
    simpl in *.
    omega.
    intros i i_lt_len.
    unfold rev.
    fold (rev l).
    unfold length.
    fold (length l).
    assert (S (length l) - S i = (length l) - i) by omega.
    rewrite H.
    clear H.
    destruct i.
    simpl.
    assert (length l - 0 = length l) by omega.
    rewrite H; clear H.
    pose proof (revLen l) as H.
    rewrite H; clear H.
    assert (length (rev l) = length (rev l)) by reflexivity.
    pose proof (appLastNth a H).
    rewrite H0.
    auto.
    simpl in i_lt_len.
    pose proof (revLen l) as H.
    assert (length l - S i < length (rev l)) by omega.
    pose proof (appNotLastNth a H0).
    rewrite H1.
    simpl.
    assert (i < length l) by omega.
    specialize (IHl i H2).
    assumption.
  Qed.
End ListProp.

Fixpoint makeList l :=
  match l with
    | 0 => nil
    | S n => n :: (makeList n)
  end.

Theorem makeListLength l: length (makeList l) = l.
Proof.
  induction l.
  simpl.
  auto.
  simpl.
  f_equal.
  auto.
Qed.

Theorem isRevN: forall {l i}, i < l -> nth i (makeList l) 0 = l - S i.
Proof.
  intros l.
  induction l.
  intros i i_lt_l.
  omega.
  intros i i_lt_l.
  unfold makeList.
  fold makeList.
  destruct i.
  simpl.
  omega.
  simpl.
  assert (i < l) by omega.
  apply (IHl i H).
Qed.
  
Theorem isN: forall {n i}, i < n -> nth (n - S i) (rev (makeList n)) 0 = (n - S i).
Proof.
  intros n i i_lt_n.
  pose proof (isRevN i_lt_n) as gdOne.
  pose proof (makeListLength n) as t1.
  rewrite <- t1 in i_lt_n.
  pose proof (revProp 0 i_lt_n) as bdOne.
  rewrite t1 in bdOne.
  rewrite gdOne in bdOne.
  auto.
Qed.

Theorem isN2: forall {n i}, i < n -> nth i (rev (makeList n)) 0 = i.
Proof.
  intros n i i_lt_n.
  assert (sth: n - S i < n) by omega.
  pose proof (isN sth) as sth2.
  assert (n - S (n - S i) = i) by omega.
  rewrite H in sth2.
  assumption.
Qed.
  

Fixpoint getX b nm :=
  match b with
    | B bs => fold_left (
                  fun x y =>
                    (getX y ((fst x)::nm)) :: (snd x))

Fixpoint getX b nm :=
  match b with
    | B bs => (fst (fold_left (
                        fun (x: (list Tree * nat)) y =>
                          let (cs, next) := x in
                          ((C (next :: nm) (getX y (next :: nm)))::cs, next - 1)
                      ) bs (nil, (length bs - 1))))
  end.

Definition getC b nm := C nm (getX b nm).

Theorem treeNameHelp b nm:
  match getC b nm with
    | C x ls => treeNthName x ls
  end.
Proof.
  unfold treeNthName.
  unfold getC.
  intros n n_lt_len.
  induction n.
  destruct b.
  destruct l.
  simpl in *.
  omega.
  unfold getX.
  fold getX.
  admit.
  simpl.
  simpl.
  fold
  simpl.
  unfold
  simpl.
  unfold nth.
  destruct b.
  induction 
  simpl.

Theorem treeName2 {b} {p} (desc: descendent p (getC b nil)):
  match p with
    | C x ls => treeNthName x ls
  end.
Proof.
  unfold treeNthName.
  remember (getC b nil) as hier.
  induction desc.
  admit.
  admit.
  rewrite Heqhier in H; clear Heqhier.
  unfold parent in H.
  destruct desc.
  destruct p as [nm cs].
  intros n n_lt_csLen.
  remember (C nm cs) as p.
  remember (getC b nil) as orig.
  induction desc.
  unfold parent in H.
  destruct y as [nm' cs'].
  unfold getC in Heqorig.
  destruct b.
  simpl in Heqorig.
  induction desc.
  dependent desc.
*)
