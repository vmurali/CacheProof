Require Import Rules DataTypes Omega Useful List Coq.Logic.Classical.
Import mkDataTypes.

Theorem enqGreater':
  forall {s p c t i}, In i (labelCh t s p c) -> t > i.
Proof.
  intros s p c t i inI.
  induction t.
  unfold labelCh in *.
  unfold In in inI.
  firstorder.
  unfold labelCh in inI; fold labelCh in inI.
  destruct (trans oneBeh t).
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.

  destruct s.
  specialize (IHt inI); omega.
  destruct (decTree c0 p).
  destruct (decTree p0 c).
  unfold In in inI.
  destruct inI as [mu1|mu2]; [ | specialize (IHt mu2)]; omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.

  destruct s.
  destruct (decTree c0 c).
  destruct (decTree p0 p).
  unfold In in inI.
  destruct inI as [mu1|mu2]; [ | specialize (IHt mu2)]; omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  destruct (decTree p0 c).
  destruct (decTree c0 p).
  pose proof (notInRemove i (labelCh t rch p c) inI) as f.
  specialize (IHt f); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.


  destruct s.
  destruct (decTree p0 p).
  destruct (decTree c0 c).
  pose proof (notInRemove i (labelCh t mch p c) inI) as f.
  specialize (IHt f); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.

  destruct s.
  destruct (decTree p0 p).
  destruct (decTree c0 c).
  unfold In in inI.
  destruct inI as [mu1|mu2]; [ | specialize (IHt mu2)]; omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.

  destruct s.
  destruct (decTree p0 p).
  destruct (decTree c0 c).
  pose proof (notInRemove i (labelCh t mch p c) inI) as f.
  specialize (IHt f); omega.
  destruct (decTree p0 c).
  destruct (decTree c0 p).
  unfold In in inI.
  destruct inI as [mu1|mu2]; [ | specialize (IHt mu2)]; omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  destruct (decTree c0 c) as [e1|e2].
  rewrite <- e1 in *.
  destruct (decTree p0 c) as [e3|e4].
  rewrite <- e3 in *.
  pose proof (noParentChild e1 p1); firstorder.
  destruct (decTree p0 c0) as [e5|e6].
  assert (H: c0 = p0) by auto.
  pose proof (noParentChild H p1); firstorder.
  specialize (IHt inI); omega.
  destruct (decTree p0 c) as [e3|e4].
  rewrite <- e3 in *.
  destruct (decTree c0 p) as [e5|e6].
  rewrite <- e5 in *.
  unfold In in inI.
  destruct inI as [mu1|mu2]; [ | specialize (IHt mu2)]; omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.

  
  destruct s.
  destruct (decTree c0 p).
  destruct (decTree p0 c).
  pose proof (notInRemove i (labelCh t mch p c) inI) as f.
  specialize (IHt f); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.


  destruct s.
  destruct (decTree c0 p).
  destruct (decTree p0 c).
  unfold In in inI.
  destruct inI as [mu1|mu2]; [ | specialize (IHt mu2)]; omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.

  destruct s.
  destruct (decTree p0 p).
  destruct (decTree c0 c).
  pose proof (notInRemove i (labelCh t mch p c) inI) as f.
  specialize (IHt f); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
Qed.


Theorem posGreater:
  forall {s p c t n},
    n < length (labelCh t s p c) ->
    forall {i}, i < n ->
                nth n (labelCh t s p c) 0 < nth i (labelCh t s p c) 0.
Proof.
  intros s p c t.
  induction t.
  intros n n_lt i i_lt.
  unfold labelCh in n_lt.
  simpl in n_lt.
  assert False by omega; firstorder.

  intros n n_lt i i_lt.
  unfold labelCh in n_lt; fold labelCh in n_lt. unfold labelCh; fold labelCh.

  assert (one: n < length (t :: labelCh t s p c) ->
               nth n (t :: labelCh t s p c) 0 < nth i (t :: labelCh t s p c) 0).
  intros n_lt'.
  destruct n.
  assert False by omega; firstorder.
  assert (n_lt'': n < length (labelCh t s p c)) by
      (unfold length in n_lt'; fold (length (labelCh t s p c)) in n_lt'; omega).
  unfold nth.
  fold (nth n (labelCh t s p c) 0).
  destruct i.
  pose proof (enqGreater' (nth_In (labelCh t s p c) 0 n_lt'')).
  assumption.
  assert (H: i < n) by omega.
  apply (IHt n n_lt'' i H).

  destruct (trans oneBeh t).

  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  specialize (IHt n n_lt i i_lt); assumption.
  destruct (decTree c0 p).
  destruct (decTree p0 c).
  apply (one n_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree c0 c).
  destruct (decTree p0 p).
  apply (one n_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct (decTree p0 c).
  destruct (decTree c0 p).
  apply (listNoShift IHt n_lt i_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree p0 p).
  destruct (decTree c0 c).
  apply (listNoShift IHt n_lt i_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree p0 p).
  destruct (decTree c0 c).
  apply (one n_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree c0 c).
  destruct (decTree p0 p).
  apply (listNoShift IHt n_lt i_lt).
  destruct (decTree p0 c).
  destruct (decTree c0 p).
  apply (one n_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  destruct (decTree p0 c).
  destruct (decTree c0 p).
  apply (one n_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree c0 p).
  destruct (decTree p0 c).
  apply (listNoShift IHt n_lt i_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree c0 p).
  destruct (decTree p0 c).
  apply (one n_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree p0 p).
  destruct (decTree c0 c).
  apply (listNoShift IHt n_lt i_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
Qed.

Theorem msgIdTime: forall {s p c m t}, mark s p c t m -> msgId m = t.
Proof.
  intros s p c m t markm.
  unfold mark in markm.
  destruct (trans oneBeh t);firstorder.
Qed.

Theorem enqGreater: forall {s p c m t i s'}, mark s p c t m ->
                                             In i (labelCh t s' p c) -> msgId m > i.
Proof.
  intros s p c m t i s' markm ini.
  pose proof (enqGreater' ini) as H.
  pose proof (msgIdTime markm).
  rewrite H0.
  assumption.
Qed.

Theorem lenEq: forall {s p c t}, length (ch (sys oneBeh t) s p c) = length (labelCh t s p c).
Proof.
  intros s p c t.
  induction t.
  unfold labelCh.
  pose proof (init oneBeh) as initi.
  rewrite initi.
  unfold initGlobalState; reflexivity.
  unfold labelCh; fold labelCh.
  destruct (trans oneBeh t).
  assumption.
  assumption.
  simpl.
  destruct s.
  assumption.
  destruct (decTree p c0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c p0) as [y|ny].
  rewrite <- y in *.
  destruct (decTree p p).
  destruct (decTree c c).
  unfold length; f_equal; assumption.
  firstorder.
  firstorder.
  destruct (decTree p0 c).
  assert (c = p0) by auto; firstorder.
  destruct (decTree p p).
  assumption.
  firstorder.
  destruct (decTree c0 p).
  assert (p = c0) by auto; firstorder.
  firstorder.

  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [y|ny].
  rewrite <- y in *.
  destruct (decTree p p).
  destruct (decTree c c).
  unfold length; f_equal; assumption.
  firstorder.
  firstorder.
  destruct (decTree c0 c).
  assert (c = c0) by auto; firstorder.
  firstorder.
  destruct (decTree p0 p).
  assert (p = p0) by auto; firstorder.
  destruct (decTree c0 c); firstorder.
  destruct (decTree p c0) as [ez | hd].
  rewrite <- ez in *.
  destruct (decTree c p0) as [y | ny].
  rewrite <- y in *.
  destruct (decTree p p).
  destruct (decTree c c).
  apply (eqLen (ch (sys oneBeh t) rch p c) (labelCh t rch p c) IHt).
  firstorder.
  firstorder.
  destruct (decTree p0 c).
  assert (c = p0) by auto; firstorder.
  assumption.
  destruct (decTree c0 p).
  assert (p = c0) by auto; firstorder.
  destruct (decTree p0 c).
  firstorder.
  firstorder.


  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [y|ny].
  rewrite <- y in *.
  destruct (decTree p p).
  destruct (decTree c c).
  apply (eqLen (ch (sys oneBeh t) mch p c) (labelCh t mch p c) IHt).
  firstorder.
  firstorder.
  destruct (decTree c0 c).
  assert (c = c0) by auto; firstorder.
  firstorder.
  destruct (decTree p p); firstorder.
  destruct (decTree p0 p).
  assert (p = p0) by auto; firstorder.
  firstorder.
  firstorder.

  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [y|ny].
  rewrite <- y in *.
  destruct (decTree p p).
  destruct (decTree c c).
  unfold length; firstorder.
  firstorder.
  firstorder.
  destruct (decTree c0 c).
  assert (c = c0) by auto; firstorder.
  destruct (decTree p p).
  firstorder.
  firstorder.
  destruct (decTree p0 p).
  assert (p = p0) by auto; firstorder.
  firstorder.
  firstorder.



  simpl in *.
  destruct s.
  destruct (decTree p c0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c p0) as [y|ny].
  rewrite <- y in *.
  destruct (decTree p c).
  pose proof (noParentChild e0 p1); firstorder.
  destruct (decTree c c).
  destruct (decTree p p).
  unfold length; firstorder.
  firstorder.
  firstorder.
  destruct (decTree p p0) as [ex|hx].
  pose proof (noParentChild ex p1); firstorder.
  destruct (decTree p c).
  destruct (decTree p0 p).
  assert (p = p0) by auto; firstorder.
  destruct (decTree p0 c).
  assert (c = p0) by auto; firstorder.
  firstorder.
  destruct (decTree p0 c).
  assert (c = p0) by auto; firstorder.
  firstorder.
  destruct (decTree p p0).
  destruct (decTree c c0).
  destruct (decTree c0 c).
  destruct (decTree p0 p).
  apply (eqLen (ch (sys oneBeh t) mch p c) (labelCh t mch p c) IHt).
  assert (p0 = p) by auto; firstorder.
  assert (c0 = c) by auto; firstorder.
  destruct (decTree c0 c).
  assert (c = c0) by auto; firstorder.
  destruct (decTree p0 c).
  destruct (decTree c0 p).
  rewrite e0 in e2.
  pose proof (noParentChild e2 p1); firstorder.
  firstorder.
  firstorder.
  destruct (decTree c0 c).
  destruct (decTree p0 p).
  assert (p = p0) by auto; firstorder.
  destruct (decTree p0 c).
  rewrite <- e1 in e0.
  pose proof (noParentChild e0 p1); firstorder.
  firstorder.
  destruct (decTree p0 c).
  destruct (decTree c0 p).
  assert (p = c0) by auto; firstorder.
  firstorder.
  firstorder.
  firstorder.


  simpl in *.
  destruct s.
  destruct (decTree p c0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c p0) as [y|ny].
  rewrite <- y in *.
  destruct (decTree p p).
  destruct (decTree c c).
  apply (eqLen (ch (sys oneBeh t) mch p c) (labelCh t mch p c) IHt).
  firstorder.
  firstorder.
  destruct (decTree p0 c).
  assert (c = p0) by auto.
  firstorder.
  destruct (decTree p p); firstorder.
  destruct (decTree c0 p).
  assert (p = c0) by auto.
  firstorder.
  firstorder.
  firstorder.


  simpl in *.
  destruct s.
  destruct (decTree p c0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c p0) as [y|ny].
  rewrite <- y in *.
  destruct (decTree p p).
  destruct (decTree c c).
  unfold length; firstorder.
  firstorder.
  firstorder.
  destruct (decTree p0 c).
  assert (c = p0) by auto; firstorder.
  destruct (decTree p p); firstorder.
  destruct (decTree c0 p).
  assert (p = c0) by auto; firstorder.
  firstorder.
  firstorder.


  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [y|ny].
  rewrite <- y in *.
  destruct (decTree p p).
  destruct (decTree c c).
  apply (eqLen (ch (sys oneBeh t) mch p c) (labelCh t mch p c) IHt).
  firstorder.
  firstorder.
  destruct (decTree c0 c).
  assert (c = c0) by auto; firstorder.
  destruct (decTree p p); firstorder.
  destruct (decTree p0 p).
  assert (p = p0) by auto; firstorder.
  firstorder.
  firstorder.
Qed.

Theorem inImpSend: forall {s p c b l t},
                     In (b, l) (combine (ch (sys oneBeh (S t)) s p c)
                                        (labelCh (S t) s p c)) ->
                     ~ In (b, l) (combine (ch (sys oneBeh t) s p c)
                                          (labelCh t s p c)) ->
                     mark (type b) p c t (Build_Mesg (fromB b) (toB b) (addrB b)
                                                     (dataBM b) l) /\
                     (combine (ch (sys oneBeh (S t)) s p c) (labelCh (S t) s p c)) =
                     (b,l) :: (combine (ch (sys oneBeh t) s p c) (labelCh t s p c)).
Proof.
  intros s p c b l t inComb notInComb.
  unfold mark; simpl in *.
  destruct (trans oneBeh t).
  firstorder.
  firstorder.

  simpl in *.
  destruct s. firstorder.
  destruct (decTree p c0) as [pEq | pNeq].
  rewrite <- pEq in *.
  destruct (decTree c p0) as [cEq | cNeq].
  rewrite <- cEq in *.
  destruct (decTree p p) as [peq | pneq].
  destruct (decTree c c) as [ceq | cneq].
  unfold combine in inComb.
  unfold In in inComb.
  assert (L: (b, l) = ({|
                          fromB := st (sys oneBeh t) p a;
                          toB := x;
                          addrB := a;
                          dataBM := Initial; type := rch |}, t)) by firstorder.
  pose proof (eachProd L) as [L1 L2].
  rewrite L1; rewrite L2; simpl; firstorder.
  firstorder.
  firstorder.
  destruct (decTree p0 c) as [ceq | cneq].
  assert   (c = p0) by auto; firstorder.
  destruct (decTree p p) as [easy | hard]; firstorder.
  destruct (decTree c0 p); [assert (p = c0) by auto; firstorder| firstorder].

  simpl in *.
  assert (rew: r = last (ch (sys oneBeh t) rch c0 p0) dmy) by auto;
    rewrite <- rew in *.
  destruct s.
  destruct (decTree p p0) as [pEq | pNeq].
  rewrite <- pEq in *.
  destruct (decTree c c0) as [cEq | cNeq].
  rewrite <- cEq in *.
  destruct (decTree p p) as [peq | pneq].
  destruct (decTree c c) as [ceq | cneq].
  unfold combine in inComb.
  unfold In in inComb.
  assert (L: (b, l) = ({|
                          fromB := dirSt (sys oneBeh t) p c a;
                          toB := toB r;
                          addrB := a;
                          dataBM := dt (sys oneBeh t) p a; type := mch |}, t)) by firstorder.
  pose proof (eachProd L) as [L1 L2]; clear L.
  rewrite L1; rewrite L2; simpl; firstorder.
  firstorder.
  firstorder.
  destruct (decTree c0 c) as [easy|hard].
  assert (c = c0) by auto; firstorder.
  firstorder.
  destruct (decTree c0 c) as [sth | easy].
  destruct (decTree p0 p) as [ez | hd].
  assert (p = p0) by auto; firstorder.
  firstorder.
  firstorder.

  destruct (decTree p c0) as [pEq | pNeq].
  rewrite <- pEq in *.
  destruct (decTree c p0) as [cEq | cNeq].
  rewrite <- cEq in *.
  destruct (decTree c c) as [peq | pneq].
  destruct (decTree p p) as [ceq | cneq].
  pose proof (removeCombine (ch (sys oneBeh t) rch p c) (labelCh t rch p c))
    as sthEq.
  rewrite <- sthEq in inComb.
  pose proof (notInRemove (b, l) (combine (ch (sys oneBeh t) rch p c) (labelCh t rch p c))
                          inComb) as H.
  firstorder.
  firstorder.
  firstorder.
  destruct (decTree p0 c) as [ez|hd].
  assert (c = p0) by auto; firstorder.
  firstorder.
  destruct (decTree p0 c) as [ez|hd].
  destruct (decTree c0 p) as [yay|nay].
  assert (p = c0) by auto; firstorder.
  firstorder.
  firstorder.


  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [yay|nay].
  rewrite <- yay in *.
  destruct (decTree p p).
  destruct (decTree c c).
  pose proof (removeCombine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)) as sthEq.
  rewrite <- sthEq in inComb.
  pose proof (notInRemove (b, l) (combine (ch (sys oneBeh t) mch p c) (labelCh t mch p c))
                          inComb) as H.
  firstorder.
  firstorder.
  firstorder.
  destruct (decTree c0 c) as [m1 | m2].
  assert (c = c0) by auto; firstorder.
  destruct (decTree p p) as [k1 | k2].
  firstorder.
  firstorder.
  destruct (decTree p0 p).
  assert (p = p0) by auto; firstorder.
  firstorder.
  firstorder.


  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [yay|nay].
  rewrite <- yay in *.
  destruct (decTree p p).
  destruct (decTree c c).
  unfold combine in inComb.
  unfold In in inComb.
  assert (L: (b, l) = ({|
                          fromB := dirSt (sys oneBeh t) p c a;
                          toB := x;
                          addrB := a;
                          dataBM := Initial; type := rch |}, t)) by firstorder.
  pose proof (eachProd L) as [L1 L2]; clear L.
  rewrite L1; rewrite L2; simpl; firstorder.
  firstorder.
  firstorder.
  destruct (decTree p p).
  destruct (decTree c0 c).
  assert (c = c0) by auto; firstorder.
  firstorder.
  firstorder.
  destruct (decTree p0 p).
  assert (p = p0) by auto; firstorder.
  firstorder.
  firstorder.

  simpl in *.
  assert (rew: r = last (ch (sys oneBeh t) mch p0 c0) dmy) by auto;
    rewrite <- rew in *.
  destruct s.
  destruct (decTree p c0) as [pEq | pNeq].
  rewrite pEq in *.
  destruct (decTree c p0) as [cEq | cNeq].
  rewrite cEq in *.
  destruct (decTree c0 p0).
  pose proof (noParentChild e0 p1); firstorder.
  destruct (decTree p0 p0) as [peq | pneq].
  destruct (decTree c0 c0) as [ceq | cneq].
  unfold combine in inComb.
  unfold In in inComb.
  assert (L: (b, l) = ({|
                          fromB := st (sys oneBeh t) c0 a;
                          toB := toB r;
                          addrB := a;
                          dataBM := dt (sys oneBeh t) c0 a; type := mch |}, t)) by firstorder.
  pose proof (eachProd L) as [L1 L2]; clear L.
  rewrite L1; rewrite L2; simpl; firstorder.
  firstorder.
  firstorder.

  destruct (decTree c0 p0) as [peq | pneq].
  pose proof (noParentChild peq p1); firstorder.
  destruct (decTree c0 c) as [ceq | cneq].
  rewrite ceq in *.
  destruct (decTree p0 c).
  assert (c = p0) by auto; firstorder.
  firstorder.
  destruct (decTree p0 c).
  assert (c = p0) by auto; firstorder.
  firstorder.

  destruct (decTree p p0) as [ez|hd].
  rewrite ez in *.
  destruct (decTree c0 c) as [mu|su].
  rewrite mu in *.
  destruct (decTree c c).
  destruct (decTree p0 p0).
  pose proof (removeCombine (ch (sys oneBeh t) mch p0 c) (labelCh t mch p0 c)) as H.
  rewrite <- H in inComb.
  pose proof (notInRemove (b,l) (combine (ch (sys oneBeh t) mch p0 c) (labelCh t mch p0 c)) inComb) as H2.
  firstorder.
  firstorder.
  firstorder.
  destruct (decTree c c0).
  assert (c0 = c) by auto; firstorder.
  destruct (decTree p0 c).
  destruct (decTree c0 p0).
  assert (p0 = c0) by auto; firstorder.
  firstorder.
  firstorder.
  destruct (decTree c0 c) as [ea|ec].
  rewrite ea in *.
  destruct (decTree p0 p).
  assert (p = p0) by auto; firstorder.
  destruct (decTree p0 c) as [ef|eg].
  assert (xxx: c = p0) by auto.
  pose proof (noParentChild xxx p1); firstorder.
  firstorder.
  destruct (decTree p0 c) as [ef|eg].
  rewrite ef in *.
  destruct (decTree c0 p) as [eh|ej].
  rewrite eh in *.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  

  simpl in *.
  destruct s.
  destruct (decTree p c0) as [pEq | pNeq].
  rewrite <- pEq in *.
  destruct (decTree c p0) as [cEq | cNeq].
  rewrite <- cEq in *.
  destruct (decTree p p).
  destruct (decTree c c).
  pose proof (removeCombine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)) as H.
  rewrite <- H in inComb.
  pose proof (notInRemove (b,l) (combine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)) inComb) as H2.
  firstorder.
  firstorder.
  firstorder.
  destruct (decTree p0 c).
  assert (c = p0) by auto; firstorder.
  destruct (decTree p p); firstorder.
  destruct (decTree c0 p).
  assert (p = c0) by auto; firstorder.
  firstorder.
  firstorder.

  simpl in *.
  destruct s.
  destruct (decTree p c0) as [pEq | pNeq].
  rewrite <- pEq in *.
  destruct (decTree c p0) as [cEq | cNeq].
  rewrite <- cEq in *.
  destruct (decTree p p) as [peq | pneq].
  destruct (decTree c c) as [ceq | cneq].
  unfold combine in inComb.
  unfold In in inComb.
  assert (L: (b, l) = ({|
                          fromB := st (sys oneBeh t) p a;
                          toB := x;
                          addrB := a;
                          dataBM := dt (sys oneBeh t) p a; type := mch |}, t)) by firstorder.
  pose proof (eachProd L) as [L1 L2]; clear L.
  rewrite L1; rewrite L2; simpl; firstorder.
  firstorder.
  firstorder.
  destruct (decTree p0 c) as [easy|hard].
  assert (c = p0) by auto; firstorder.
  destruct (decTree p p);
    firstorder.
  destruct (decTree c0 p) as [sth | easy].
  destruct (decTree p0 c) as [ez | hd].
  assert (p = c0) by auto; firstorder.
  firstorder.
  firstorder.
  firstorder.

  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez | hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [m1 | m2].
  rewrite <- m1 in *.
  destruct (decTree p p).
  destruct (decTree c c).
  pose proof (removeCombine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)) as H.
  rewrite <- H in inComb.
  pose proof (notInRemove (b,l) (combine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)) inComb) as H2.
  firstorder.
  firstorder.
  firstorder.
  destruct (decTree c0 c).
  assert (c = c0) by auto; firstorder.
  destruct (decTree p p); firstorder.
  destruct (decTree p0 p).
  assert (p = p0) by auto; firstorder.
  firstorder.
  firstorder.
Qed.

Theorem inImpSent: forall {s p c b l t1 t2}, t1 < t2 ->
                     In (b, l) (combine (ch (sys oneBeh t2) s p c) (labelCh t2 s p c)) ->
                     ~ In (b, l) (combine (ch (sys oneBeh t1) s p c) (labelCh t1 s p c)) ->
                     exists ti, t1 <= ti < t2 /\ mark (type b) p c ti
                                                      (Build_Mesg (fromB b) (toB b)
                                                                  (addrB b) (dataBM b) l) /\
                     (combine (ch (sys oneBeh (S ti)) s p c) (labelCh (S ti) s p c)) =
                     (b,l) :: (combine (ch (sys oneBeh ti) s p c) (labelCh ti s p c)).
Proof.
  intros s p c b l t1 t2 cond isIn notIn.
  remember (t2 - t1 - 1) as td.
  assert (t2 = t1 + S td) by omega.
  rewrite H in *; clear Heqtd H cond.
  induction td.
  assert (rew: t1 + 1 = S t1) by omega.
  rewrite rew in *; clear rew.
  assert (cond2: t1 <= t1 < S t1) by omega.
  pose proof (inImpSend isIn notIn) as use.
  exists t1; generalize cond2 use; clear.
  constructor; assumption.
  destruct (classic (In (b, l) (combine (ch (sys oneBeh (t1 + S td)) s p c)
                                        (labelCh (t1 + S td) s p c)))) as
      [easy | hard].
  destruct (IHtd easy) as [ti [cond use]].
  assert (ez: t1 <= ti < t1 + S (S td)) by omega.
  generalize ez use; clear.
  intros; exists ti; constructor; assumption.
  assert (h: t1 + S (S td) = S (t1 + S td)) by omega.
  rewrite h in *; clear h.
  pose proof (inImpSend isIn hard) as use.
  exists (t1 + S td).
  assert (t1 <= t1 + S td < S ( t1 + S td)) by omega.
  generalize H use; clear; intros; constructor; assumption.
Qed.

Theorem recvImpIn: forall {s p c m t},
                     recv s p c t m ->
                     In (Build_BaseMesg (from m) (to m) (addr m) (dataM m) s,
                         msgId m) (combine (ch (sys oneBeh t) (recvc t) p c)
                                             (labelCh t (recvc t) p c)).
Proof.
  unfold recv.
  intros s p c m t recvm. unfold recvc.
  destruct (trans oneBeh t).
  firstorder.
  firstorder.
  firstorder.
  destruct recvm as [u1 [u2 [u3 [use1 [use2 [use3 [use4 use5]]]]]]].
  pose proof (@lenEq rch p c t) as H.
  rewrite <- u1 in *; rewrite <- u2 in *.
  assert (lft: Build_BaseMesg (from m) (to m) (addr m) (dataM m) s = 
               last (ch (sys oneBeh t) rch c0 p0) dmy) by (
                rewrite use1; rewrite use2; rewrite use3; rewrite use4; rewrite u3;
                destruct (last (ch (sys oneBeh t) rch c0 p0) dmy); simpl in *; reflexivity).
  pose proof (lenEqLastCombine _ _ dmy n lft (msgId m)
                               (labelCh t rch c0 p0) 0 H use5) as almost.
  assumption.
  destruct recvm as [u1 [u2 [u3 [use1 [use2 [use3 [use4 use5]]]]]]].
  pose proof (@lenEq mch p c t) as H.
  rewrite <- u1 in *; rewrite <- u2 in *.
  assert (lft: Build_BaseMesg (from m) (to m) (addr m) (dataM m) s = last (ch (sys oneBeh t) mch p0 c0) dmy) by (
                rewrite use1; rewrite use2; rewrite use3; rewrite use4; rewrite u3;
                destruct (last (ch (sys oneBeh t) mch p0 c0) dmy); reflexivity).
  pose proof (lenEqLastCombine _ _ dmy n lft (msgId m)
                               (labelCh t mch p0 c0) 0 H use5) as almost.
  assumption.
  firstorder.
  destruct recvm as [u1 [u2 [u3 [use1 [use2 [use3 [use4 use5]]]]]]].
  pose proof (@lenEq mch p c t) as H.
  rewrite <- u1 in *; rewrite <- u2 in *.
  assert (lft: Build_BaseMesg (from m) (to m) (addr m) (dataM m) s = last (ch (sys oneBeh t) mch p0 c0) dmy) by (
                rewrite use1; rewrite use2; rewrite use3; rewrite use4; rewrite u3;
                destruct (last (ch (sys oneBeh t) mch p0 c0) dmy); reflexivity).
  pose proof (lenEqLastCombine _ _ dmy n lft (msgId m)
                               (labelCh t mch p0 c0) 0 H use5) as almost.
  assumption.
  destruct recvm as [u1 [u2 [u3 [use1 [use2 [use3 [use4 use5]]]]]]].
  pose proof (@lenEq mch p c t) as H.
  rewrite <- u1 in *; rewrite <- u2 in *.
  assert (lft: Build_BaseMesg (from m) (to m) (addr m) (dataM m) s = last (ch (sys oneBeh t) mch c0 p0) dmy) by (
                rewrite use1; rewrite use2; rewrite use3; rewrite use4; rewrite u3;
                destruct (last (ch (sys oneBeh t) mch c0 p0) dmy); reflexivity).
  pose proof (lenEqLastCombine _ _ dmy n lft (msgId m)
                               (labelCh t mch c0 p0) 0 H use5) as almost.
  assumption.
  firstorder.
  destruct recvm as [u1 [u2 [u3 [use1 [use2 [use3 [use4 use5]]]]]]].
  pose proof (@lenEq mch p c t) as H.
  rewrite <- u1 in *; rewrite <- u2 in *.
  assert (lft: Build_BaseMesg (from m) (to m) (addr m) (dataM m) s = last (ch (sys oneBeh t) mch p0 c0) dmy) by (
            rewrite use1; rewrite use2; rewrite use3; rewrite use4; rewrite u3;
            destruct (last (ch (sys oneBeh t) mch p0 c0) dmy); reflexivity).
  pose proof (lenEqLastCombine _ _ dmy n lft (msgId m)
                                    (labelCh t mch p0 c0) 0 H use5) as almost.
  assumption.
Qed.

Theorem recvImpSend: forall {s p c m t}, recv s p c t m -> exists t', t' <= t /\ send s p c t' m.
Proof.
  intros s p c m t recvm.
  pose proof (recvImpIn recvm) as gdIn.
  destruct t.
  pose proof (init oneBeh) as sth.
  rewrite sth in *; clear sth.
  unfold initGlobalState in *; simpl in *.
  firstorder.
  assert (sth: 0 < S t) by omega.
  assert (sth3: ~ In ({|
            fromB := from m;
            toB := to m;
            addrB := addr m;
            dataBM := dataM m;
            type := s |}, msgId m)
            (combine (ch (sys oneBeh 0) (recvc (S t)) p c)
                     (labelCh 0 (recvc (S t)) p c))).
  pose proof (init oneBeh) as sth2.
  rewrite sth2 in *; clear sth2.
  unfold initGlobalState; simpl.
  unfold not; intro; assumption.
  pose proof (inImpSent sth gdIn sth3) as [ti [cond rest]].
  simpl in *.
  exists ti.
  assert (ti <= S t) by omega.
  unfold send.
  destruct rest as [useful _].
  assert (great: mark s p c ti m).
  destruct m.
  simpl in *.
  assumption.
  constructor; assumption.
Qed.

Theorem enqC2P: forall {s p c t}, parent c p -> ch (sys oneBeh t) s c p <> nil ->
                                  type (last (ch (sys oneBeh t) s c p) dmy) = s.
Proof.
  intros s p c t c_p notNil.
  assert (gd: last (ch (sys oneBeh t) s c p) dmy = fst (last (combine (ch (sys oneBeh t) s c p)                                                                  (labelCh t s c p)) (dmy, 0)))
  by apply (lastCombine dmy 0 (@lenEq s c p t)).
  rewrite gd; clear gd.
  assert (gd2: combine (ch (sys oneBeh t) s c p) (labelCh t s c p) <> nil).
  pose proof (@lenEq s c p t) as gd.
  destruct (ch (sys oneBeh t) s c p).
  firstorder.
  destruct (labelCh t s c p).
  simpl in *.
  discriminate.
  simpl.
  unfold not; intros; discriminate.
  firstorder.
  pose proof (@lastIn (BaseMesg * nat) (combine (ch (sys oneBeh t) s c p) (labelCh t s c p))
             (dmy, 0) gd2) as use.
  destruct t.
  pose proof (init oneBeh) as sth.
  rewrite sth in *; clear sth.
  unfold initGlobalState in *; simpl in *.
  firstorder.
  assert (sth: 0 < S t) by omega.
  assert (sth3: ~ In (last (combine (ch (sys oneBeh (S t)) s c p) (labelCh (S t) s c p))
             (dmy, 0))
            (combine (ch (sys oneBeh 0) s c p)
                     (labelCh 0 s c p))).
  pose proof (init oneBeh) as sth2.
  rewrite sth2 in *; clear sth2.
  unfold initGlobalState; simpl.
  unfold not; intro; assumption.
  assert (L: 0 < S t) by omega.
  remember (last (combine (ch (sys oneBeh (S t)) s c p) (labelCh (S t) s c p))
             (dmy, 0)) as lt.
  assert (rew: lt = (fst lt, snd lt)).
  destruct lt.
  reflexivity.
  rewrite rew in *.
  pose proof (@inImpSent s c p (fst lt) (snd lt) 0 (S t) L use sth3) as use2.
  unfold mark in use2.
  simpl in use2.
  destruct use2 as [x [y stf]].
  destruct (trans oneBeh x).
  intuition.
  intuition.

  simpl in *.
  destruct s.
  destruct (decTree c c0).
  destruct (decTree p p0).
  destruct stf as [_ u1].
  pose proof (listNeq _ _ (eq_sym u1)); intuition.
  destruct stf as [_ u1].
  pose proof (listNeq _ _ (eq_sym u1)); intuition.
  destruct stf as [_ u1].
  pose proof (listNeq _ _ (eq_sym u1)); intuition.
  destruct stf as [[_ [_ [u2 _]]] _].
  assumption.

  simpl in *.
  destruct s.
  destruct stf as [[_ [_ [u2 _]]] _].
  assumption.
  destruct stf as [[u1 [u2 _]] _].
  rewrite u1 in *; rewrite u2 in *.
  pose proof (noCycle c_p p1); intuition.


  intuition.

  destruct stf as [[u1 [u2 _]] _].
  rewrite u1 in *; rewrite u2 in *.
  pose proof (noCycle c_p p1); intuition.


  simpl in *.
  destruct s.
  destruct stf as [[_ [_ [u2 _]]] _].
  assumption.
  destruct stf as [_ u1].
  pose proof (listNeq _ _ (eq_sym u1)); intuition.


  intuition.


  simpl in *.
  destruct s.
  destruct stf as [[_ [_ [u2 _]]] _].
  assumption.
  destruct stf as [_ u1].
  pose proof (listNeq _ _ (eq_sym u1)); intuition.

  intuition.
Qed.

Theorem noEnqDeq: forall {s p c t m1 m2}, recv s p c t m1 -> mark s p c t m2 -> False.
Proof.
  intros s p c t m1 m2 recvm1 markm2.
  unfold recv in *. unfold mark in *.
  destruct (trans oneBeh t).
  firstorder.
  firstorder.
  firstorder.
  pose proof (enqC2P p1 n) as ty; rewrite ty in recvm1.
  destruct recvm1 as [_ [_ [u1 _]]]; destruct markm2 as [_ [_ [u2 _]]].
  rewrite u1 in u2; discriminate.
  firstorder.
  firstorder.
  assert (H: r = last (ch (sys oneBeh t) mch p0 c0) dmy) by auto.
  rewrite <- H in recvm1; rewrite e in recvm1.
  destruct recvm1 as [_ [_ [u1 _]]]; destruct markm2 as [_ [_ [u2 _]]].
  rewrite u1 in u2; discriminate.
  firstorder.
  firstorder.
  firstorder.
Qed.

Theorem useful: forall {s p c t1 t2 m1 m2},
                  recv s p c t1 m1 -> recv s p c t2 m2 -> recvc t1 = recvc t2.
  intros s p c t1 t2 m1 m2 recv1 recv2.
  unfold recv in *.
  unfold recvc in *.
  destruct (trans oneBeh t1); destruct (trans oneBeh t2); intuition.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3;
  pose proof (noCycle p1 p3).
  pose proof (noCycle p1 p3).
  pose proof (noCycle p1 p3).
  intuition.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3;
  pose proof (noCycle p1 p3).
  intuition.
  pose proof (enqC2P p1 n).
  pose proof (enqC2P p3 n0).
  rewrite <- H2 in *; rewrite H16 in *; rewrite H13 in *; discriminate.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3;
  pose proof (noCycle p1 p3).
  intuition.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3;
  pose proof (noCycle p1 p3).
  intuition.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3;
  pose proof (noCycle p1 p3).
  firstorder.
  pose proof (enqC2P p1 n).
  pose proof (enqC2P p3 n0).
  rewrite <- H2 in *; rewrite H16 in *; rewrite H13 in *; discriminate.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3;
  pose proof (noCycle p1 p3).
  firstorder.
Qed.

Theorem recvNotIn: forall {s p c t m}, recv s p c t m ->
                                       In (Build_BaseMesg (from m) (to m) (addr m) (dataM m)
                                                          s, msgId m)
                                          (combine (ch (sys oneBeh (S t)) (recvc t) p c)
                                                   (labelCh (S t) (recvc t) p c)) -> False.
Proof.
  intros s p c t m recvm isIn.
  unfold recv in recvm. unfold recvc in isIn.
  destruct (trans oneBeh t).
  intuition.
  intuition.
  intuition.
  admit.
  admit.
  intuition.
  admit.
  admit.
  intuition.
  admit.
Qed.

Theorem uniqRecv2: forall {s p c t1 t2 m1 m2},
                     recv s p c t1 m1 -> recv s p c t2 m2 -> t1 < t2 ->
                     msgId m1 < msgId m2.
Proof.
  intros s p c t1 t2 m1 m2 recvm1 recvm2 t1_lt_t2.
  pose proof (recvImpIn recvm1) as H1.
  pose proof (recvImpIn recvm2) as H2.
  destruct (classic (In ({|
          fromB := from m2;
          toB := to m2;
          addrB := addr m2;
          dataBM := dataM m2;
          type := s |}, msgId m2) ( (combine (ch (sys oneBeh t1) (recvc t2) p c)
            (labelCh t1 (recvc t2) p c))))) as [pos|enq].
  pose proof (useful recvm1 recvm2) as H.
  rewrite <- H in pos.
  assert (mDec: {m1 = m2} + {m1 <> m2}).
  repeat (decide equality).
  apply (decLabel).
  apply (decAddr).
  destruct mDec as [same|diff];
  admit.
  pose proof (inImpSent t1_lt_t2 H2 enq) as [ti [cond [markm rest]]].
  simpl in markm.
  assert (cond2: t1 = ti \/ t1 < ti) by (unfold Time in *; omega).
  destruct cond2 as [eq | lt].
  rewrite eq in *.
  pose proof (noEnqDeq recvm1 markm).
  intuition.
  pose proof (inComb H1) as use2.
  pose proof (enqGreater' use2) as g1.
  pose proof (msgIdTime markm) as id.
  simpl in id.
  omega.
Qed.

