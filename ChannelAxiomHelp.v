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
  destruct (decTree p c0).
  destruct (decTree c p0).
  unfold In in inI.
  destruct inI as [mu1|mu2]; [ | specialize (IHt mu2)]; omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.

  destruct s.
  destruct (decTree c c0).
  destruct (decTree p p0).
  unfold In in inI.
  destruct inI as [mu1|mu2]; [ | specialize (IHt mu2)]; omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  destruct (decTree c p0).
  destruct (decTree p c0).
  pose proof (notInRemove i (labelCh t rch p c) inI) as f.
  specialize (IHt f); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.


  destruct s.
  destruct (decTree p p0).
  destruct (decTree c c0).
  pose proof (notInRemove i (labelCh t mch p c) inI) as f.
  specialize (IHt f); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.

  destruct s.
  destruct (decTree p p0).
  destruct (decTree c c0).
  unfold In in inI.
  destruct inI as [mu1|mu2]; [ | specialize (IHt mu2)]; omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.

  destruct s.
  destruct (decTree c p0).
  destruct (decTree p c0).
  unfold In in inI.
  destruct inI as [mu1|mu2]; [ | specialize (IHt mu2)]; omega.
  specialize (IHt inI); omega.
  destruct (decTree c c0).
  destruct (decTree p p0).
  pose proof (notInRemove i (labelCh t mch p c) inI) as f.
  specialize (IHt f); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.

  
  destruct s.
  destruct (decTree p c0).
  destruct (decTree c p0).
  pose proof (notInRemove i (labelCh t mch p c) inI) as f.
  specialize (IHt f); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.


  destruct s.
  destruct (decTree p c0).
  destruct (decTree c p0).
  unfold In in inI.
  destruct inI as [mu1|mu2]; [ | specialize (IHt mu2)]; omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.

  destruct s.
  destruct (decTree p p0).
  destruct (decTree c c0).
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
  destruct (decTree p c0).
  destruct (decTree c p0).
  apply (one n_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree c c0).
  destruct (decTree p p0).
  apply (one n_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct (decTree c p0).
  destruct (decTree p c0).
  apply (listNoShift IHt n_lt i_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree p p0).
  destruct (decTree c c0).
  apply (listNoShift IHt n_lt i_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree p p0).
  destruct (decTree c c0).
  apply (one n_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree c p0).
  destruct (decTree p c0).
  apply (one n_lt).
  specialize (IHt n n_lt i i_lt); assumption.  
  destruct (decTree c c0).
  destruct (decTree p p0).
  apply (listNoShift IHt n_lt i_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree p c0).
  destruct (decTree c p0).
  apply (listNoShift IHt n_lt i_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree p c0).
  destruct (decTree c p0).
  apply (one n_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree p p0).
  destruct (decTree c c0).
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
  unfold length; f_equal; assumption.
  firstorder.
  firstorder.

  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [y|ny].
  rewrite <- y in *.
  unfold length; f_equal; assumption.
  firstorder.
  destruct (decTree c c0); firstorder.
  destruct (decTree p c0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c p0) as [y|ny].
  rewrite <- y in *.
  apply (eqLen (ch (sys oneBeh t) rch p c) (labelCh t rch p c) IHt).
  firstorder.
  destruct (decTree c p0); firstorder.


  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [y|ny].
  rewrite <- y in *.
  apply (eqLen (ch (sys oneBeh t) mch p c) (labelCh t mch p c) IHt).
  firstorder.
  firstorder.
  firstorder.

  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [y|ny].
  rewrite <- y in *.
  unfold length; firstorder.
  firstorder.
  firstorder.
  firstorder.



  simpl in *.
  destruct s.
  destruct (decTree p c0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c p0) as [y|ny].
  rewrite <- y in *.
  unfold length; firstorder.
  destruct (decTree c p).
  rewrite <- e0 in *.
  destruct (decTree c p0);
  firstorder.
  firstorder.
  destruct (decTree p p0).
  rewrite <- e0 in *.
  destruct (decTree c c0).
  rewrite <- e1 in *.
  destruct (decTree c p).
  rewrite <- e2 in *.
  firstorder.
  apply (eqLen (ch (sys oneBeh t) mch p c) (labelCh t mch p c) IHt).
  destruct (decTree c p);
  firstorder.
  destruct (decTree c p0).
  firstorder.
  destruct (decTree c c0); firstorder.
  firstorder.
  


  simpl in *.
  destruct s.
  destruct (decTree p c0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c p0) as [y|ny].
  rewrite <- y in *.
  apply (eqLen (ch (sys oneBeh t) mch p c) (labelCh t mch p c) IHt).
  firstorder.
  firstorder.
  firstorder.


  simpl in *.
  destruct s.
  destruct (decTree p c0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c p0) as [y|ny].
  rewrite <- y in *.
  unfold length; firstorder.
  firstorder.
  firstorder.
  firstorder.


  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [y|ny].
  rewrite <- y in *.
  apply (eqLen (ch (sys oneBeh t) mch p c) (labelCh t mch p c) IHt).
  firstorder.
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



  simpl in *.
  assert (rew: r = last (ch (sys oneBeh t) rch c0 p0) dmy) by auto.
  rewrite <- rew in *.
  destruct s.
  destruct (decTree p p0) as [pEq | pNeq].
  rewrite <- pEq in *.
  destruct (decTree c c0) as [cEq | cNeq].
  rewrite <- cEq in *.
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
  destruct (decTree c c0) as [easy|hard]; firstorder.

  destruct (decTree p c0) as [pEq | pNeq].
  rewrite <- pEq in *.
  destruct (decTree c p0) as [cEq | cNeq].
  rewrite <- cEq in *.
  pose proof (removeCombine (ch (sys oneBeh t) rch p c) (labelCh t rch p c))
    as sthEq.
  rewrite <- sthEq in inComb.
  pose proof (notInRemove (b, l) (combine (ch (sys oneBeh t) rch p c) (labelCh t rch p c))
                          inComb) as H.
  firstorder.
  firstorder.
  destruct (decTree c p0) as [ez|hd]; firstorder.


  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [yay|nay].
  rewrite <- yay in *.
  pose proof (removeCombine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)) as sthEq.
  rewrite <- sthEq in inComb.
  pose proof (notInRemove (b, l) (combine (ch (sys oneBeh t) mch p c) (labelCh t mch p c))
                          inComb) as H.
  firstorder.
  firstorder.
  firstorder.
  firstorder.


  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [yay|nay].
  rewrite <- yay in *.
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
  firstorder.

  simpl in *.
  assert (rew: r = last (ch (sys oneBeh t) mch p0 c0) dmy) by auto;
    rewrite <- rew in *.
  destruct s.
  destruct (decTree p c0) as [pEq | pNeq].
  rewrite pEq in *.
  destruct (decTree c p0) as [cEq | cNeq].
  rewrite cEq in *.
  unfold combine in inComb.
  unfold In in inComb.
  assert (L: (b, l) = ({|
                          fromB := st (sys oneBeh t) c0 a;
                          toB := toB r;
                          addrB := a;
                          dataBM := dt (sys oneBeh t) c0 a; type := mch |}, t)) by firstorder.
  pose proof (eachProd L) as [L1 L2]; clear L.
  rewrite L1; rewrite L2; simpl; firstorder.
  destruct (decTree c c0) as [ceq | cneq].
  destruct (decTree c0 p0) as [peq | pneq].
  rewrite <- pEq in *; rewrite ceq in *; rewrite peq in *.
  firstorder.
  firstorder.
  firstorder.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [mu|su].
  rewrite <- mu in *.
  destruct (decTree c p) as [alf|bet].
  rewrite alf in *.
  firstorder.
  pose proof (removeCombine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)) as sthEq.
  rewrite <- sthEq in inComb.
  pose proof (notInRemove (b, l) (combine (ch (sys oneBeh t) mch p c) (labelCh t mch p c))
                          inComb) as H.
  firstorder.
  destruct (decTree c p) as [yes|no]; firstorder.

  destruct (decTree c p0).
  firstorder.
  destruct (decTree c c0);
  firstorder.
  firstorder.
  

  simpl in *.
  destruct s.
  destruct (decTree p c0) as [pEq | pNeq].
  rewrite <- pEq in *.
  destruct (decTree c p0) as [cEq | cNeq].
  rewrite <- cEq in *.
  pose proof (removeCombine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)) as H.
  rewrite <- H in inComb.
  pose proof (notInRemove (b,l) (combine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)) inComb) as H2.
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
  firstorder.

  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez | hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [m1 | m2].
  rewrite <- m1 in *.
  pose proof (removeCombine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)) as H.
  rewrite <- H in inComb.
  pose proof (notInRemove (b,l) (combine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)) inComb) as H2.
  firstorder.
  firstorder.
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

Theorem inImpSent2: forall {s p c b l t},
                      In (b, l) (combine (ch (sys oneBeh t) s p c) (labelCh t s p c)) ->
                      exists ti, ti < t /\ mark (type b) p c ti
                                    (Build_Mesg (fromB b) (toB b) (addrB b) (dataBM b) l) /\
                                    (combine (ch (sys oneBeh (S ti)) s p c) (labelCh (S ti) s p c)) =
                                 (b, l) :: combine (ch (sys oneBeh ti) s p c) (labelCh ti s p c).
Proof.
  intros s p c b l t isIn.
  assert (zero: ~ In (b, l) (combine (ch (sys oneBeh 0) s p c) (labelCh 0 s p c))).
  pose proof (init oneBeh).
  rewrite H.
  unfold initGlobalState.
  simpl.
  intuition.
  destruct t.
  intuition.
  assert (0 < S t) by omega.
  pose proof (inImpSent H isIn zero) as [ti [cond rest]].
  assert (ti < S t) by omega.
  exists ti.
  intuition.
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

Section Local.
  Context {s: ChannelType}.
  Context {p c: Cache}.
  Context {t: Time}.
  Definition comb := combine (ch (sys oneBeh t) s p c) (labelCh t s p c).
  Theorem posGreaterFull: forall {n}, n < length (ch (sys oneBeh t) s p c) ->
                                      forall {i}, i < n -> snd (nth n comb (dmy, 0)) <
                                                           snd (nth i comb (dmy, 0)).
  Proof.
    intros n n_lt i i_lt.
    pose proof (@lenEq s p c t) as lEq.
    rewrite lEq in n_lt.
    pose proof (posGreater n_lt i_lt) as almost.
    pose proof (eqComb dmy 0 n lEq) as bestn.
    pose proof (eqComb dmy 0 i lEq) as besti.
    unfold snd.
    unfold comb.
    rewrite bestn; rewrite besti.
    assumption.
  Qed.

  Theorem posNeq: In (last (ch (sys oneBeh t) s p c) dmy, last (labelCh t s p c) 0)
                     (combine (removelast (ch (sys oneBeh t) s p c))
                              (removelast (labelCh t s p c))) -> False.
  Proof.
    intros isIn.
    pose proof (removeCombine (ch (sys oneBeh t) s p c) (labelCh t s p c)) as eq.
    rewrite <- eq in isIn; clear eq.
    pose proof (lastCombineDist (ch (sys oneBeh t) s p c) dmy (labelCh t s p c) 0 (@lenEq s p c t)) as use1.
    rewrite <- use1 in isIn.
    pose proof (lastInRemove isIn) as [i [cond1 cond2]].
    pose proof (last_nth comb (dmy, 0)) as cond3.
    pose proof (@lenEq s p c t) as H.
    pose proof (combLength H) as H0.
    fold comb in H0.
    rewrite <- H0 in cond3.
    assert (length (ch (sys oneBeh t) s p c) <> 0).
    unfold comb in *; rewrite <- H0 in cond1.
    unfold not; intro K.
    rewrite K in cond1.
    omega.
    assert (one: length (ch (sys oneBeh t) s p c) - 1 < length (ch (sys oneBeh t) s p c)) by
           omega.
    unfold comb in H0.
    rewrite <- H0 in cond1.
    pose proof (posGreaterFull one cond1).
    rewrite cond3 in H2.
    unfold comb in H2.
    rewrite cond2 in H2.
    omega.
  Qed.
End Local.

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
  unfold recv in recvm. unfold recvc in isIn. unfold labelCh in isIn; fold labelCh in isIn.
  destruct (trans oneBeh t).
  intuition.
  intuition.
  intuition.

  simpl in isIn.
  destruct (decTree p c0).
  rewrite <- e0 in *.
  destruct (decTree c p0).
  rewrite <- e1 in *.
  assert (gd: In (last (ch (sys oneBeh t) rch p c) dmy, last (labelCh t rch p c) 0)
                 (combine (removelast (ch (sys oneBeh t) rch p c)) (removelast (labelCh t rch p c)))).
  destruct recvm as [_ [_ [u1 [u2 [u3 [u4 [ u5 u6]]]]]]].
  rewrite u1 in isIn; rewrite u2 in isIn; rewrite u3 in isIn; rewrite u4 in isIn;
  rewrite u5 in isIn; rewrite u6 in isIn;
  destruct (last (ch (sys oneBeh t) rch p c) dmy).
  simpl in *.
  assumption.
  pose proof (posNeq gd).
  firstorder.
  firstorder.
  destruct (decTree c p0); firstorder.

  simpl in isIn.
  destruct (decTree p p0).
  rewrite <- e0 in *.
  destruct (decTree c c0).
  rewrite <- e1 in *.
  assert (gd: In (last (ch (sys oneBeh t) mch p c) dmy, last (labelCh t mch p c) 0)
                 (combine (removelast (ch (sys oneBeh t) mch p c)) (removelast (labelCh t mch p c)))).
  destruct recvm as [_ [_ [u1 [u2 [u3 [u4 [ u5 u6]]]]]]].
  rewrite u1 in isIn; rewrite u2 in isIn; rewrite u3 in isIn; rewrite u4 in isIn;
  rewrite u5 in isIn; rewrite u6 in isIn;
  destruct (last (ch (sys oneBeh t) mch p c) dmy).
  simpl in *.
  assumption.
  pose proof (posNeq gd).
  firstorder.
  firstorder.
  firstorder.

  intuition.

  simpl in isIn.
  destruct (decTree p c0).
  rewrite <- e0 in *.
  destruct (decTree c p0).
  rewrite <- e1 in *.
  destruct recvm as [u1 [u2 _]].
  pose proof (noParentChild u2 p1).
  firstorder.
  destruct (decTree c p).
  rewrite <- e1 in *.
  destruct (decTree p p0).
  rewrite <- e2 in *.
  firstorder.
  destruct (decTree c p0).
  firstorder.
  firstorder.
  firstorder.
  destruct (decTree p p0).
  rewrite <- e0 in *.
  destruct (decTree c c0).
  rewrite <- e1 in *.
  destruct (decTree c p).
  rewrite <- e2 in *.
  pose proof (noParentChild eq_refl p1).
  firstorder.
  assert (gd: In (last (ch (sys oneBeh t) mch p c) dmy, last (labelCh t mch p c) 0)
                 (combine (removelast (ch (sys oneBeh t) mch p c)) (removelast (labelCh t mch p c)))).
  destruct recvm as [_ [_ [u1 [u2 [u3 [u4 [ u5 u6]]]]]]].
  rewrite u1 in isIn; rewrite u2 in isIn; rewrite u3 in isIn; rewrite u4 in isIn;
  rewrite u5 in isIn; rewrite u6 in isIn;
  destruct (last (ch (sys oneBeh t) mch p c) dmy).
  simpl in *.
  assumption.
  pose proof (posNeq gd).
  firstorder.
  destruct (decTree c p).
  firstorder.
  firstorder.
  destruct (decTree c p0); destruct (decTree c c0); firstorder.

  simpl in isIn.
  destruct (decTree p c0).
  rewrite <- e in *.
  destruct (decTree c p0).
  rewrite <- e0 in *.
  assert (gd: In (last (ch (sys oneBeh t) mch p c) dmy, last (labelCh t mch p c) 0)
                 (combine (removelast (ch (sys oneBeh t) mch p c)) (removelast (labelCh t mch p c)))).
  destruct recvm as [_ [_ [u1 [u2 [u3 [u4 [ u5 u6]]]]]]].
  rewrite u1 in isIn; rewrite u2 in isIn; rewrite u3 in isIn; rewrite u4 in isIn;
  rewrite u5 in isIn; rewrite u6 in isIn;
  destruct (last (ch (sys oneBeh t) mch p c) dmy).
  simpl in *.
  assumption.
  pose proof (posNeq gd).
  firstorder.
  firstorder.
  firstorder.


  intuition.

  simpl in *.
  destruct (decTree p p0).
  rewrite <- e0 in *.
  destruct (decTree c c0).
  rewrite <- e1 in *.
  assert (gd: In (last (ch (sys oneBeh t) mch p c) dmy, last (labelCh t mch p c) 0)
                 (combine (removelast (ch (sys oneBeh t) mch p c)) (removelast (labelCh t mch p c)))).
  destruct recvm as [_ [_ [u1 [u2 [u3 [u4 [ u5 u6]]]]]]].
  rewrite u1 in isIn; rewrite u2 in isIn; rewrite u3 in isIn; rewrite u4 in isIn;
  rewrite u5 in isIn; rewrite u6 in isIn;
  destruct (last (ch (sys oneBeh t) mch p c) dmy).
  simpl in *.
  assumption.
  pose proof (posNeq gd).
  firstorder.
  firstorder.
  firstorder.
Qed.

Theorem recvLast: forall {s p c t m}, recv s p c t m ->
                                      last (combine (ch (sys oneBeh t) (recvc t) p c)
                                                    (labelCh t (recvc t) p c)) (dmy, 0) =
                                      (Build_BaseMesg (from m) (to m) (addr m) (dataM m) s,
                                      msgId m).
Proof.
  intros s p c t m recvm.
  unfold recv in *.
  unfold recvc in *.
  destruct (trans oneBeh t).
  intuition.
  intuition.
  intuition.
  destruct recvm as [u1 [u2 [u3 [u4 [u5 [u6 [u7 u8]]]]]]].
  assert (rew: r = last (ch (sys oneBeh t) rch c0 p0) dmy) by auto.
  rewrite <- rew in *.
  rewrite <- u1 in *; rewrite <- u2 in *. rewrite u3 in *; rewrite u4 in *; rewrite u5 in *;
  rewrite u6 in *; rewrite u7 in *; rewrite u8 in *.
  destruct r.
  simpl in *.
  rewrite rew.
  pose proof (lastCombineDist _ dmy _ 0 (@lenEq rch c0 p0 t)) as r2.
  auto.
  destruct recvm as [u1 [u2 [u3 [u4 [u5 [u6 [u7 u8]]]]]]].
  assert (rew: m0 = last (ch (sys oneBeh t) mch p0 c0) dmy) by auto.
  rewrite <- rew in *.
  rewrite <- u1 in *; rewrite <- u2 in *. rewrite u3 in *; rewrite u4 in *; rewrite u5 in *;
  rewrite u6 in *; rewrite u7 in *; rewrite u8 in *.
  destruct m0.
  simpl in *.
  rewrite rew.
  pose proof (lastCombineDist _ dmy _ 0 (@lenEq mch p0 c0 t)) as r2.
  auto.
  intuition.
  destruct recvm as [u1 [u2 [u3 [u4 [u5 [u6 [u7 u8]]]]]]].
  assert (rew: r = last (ch (sys oneBeh t) mch p0 c0) dmy) by auto.
  rewrite <- rew in *.
  rewrite <- u1 in *; rewrite <- u2 in *. rewrite u3 in *; rewrite u4 in *; rewrite u5 in *;
  rewrite u6 in *; rewrite u7 in *; rewrite u8 in *.
  destruct r.
  simpl in *.
  rewrite rew.
  pose proof (lastCombineDist _ dmy _ 0 (@lenEq mch p0 c0 t)) as r2.
  auto.
  destruct recvm as [u1 [u2 [u3 [u4 [u5 [u6 [u7 u8]]]]]]].
  assert (rew: m0 = last (ch (sys oneBeh t) mch c0 p0) dmy) by auto.
  rewrite <- rew in *.
  rewrite <- u1 in *; rewrite <- u2 in *. rewrite u3 in *; rewrite u4 in *; rewrite u5 in *;
  rewrite u6 in *; rewrite u7 in *; rewrite u8 in *.
  destruct m0.
  simpl in *.
  rewrite rew.
  pose proof (lastCombineDist _ dmy _ 0 (@lenEq mch c0 p0 t)) as r2.
  auto.
  intuition.
  destruct recvm as [u1 [u2 [u3 [u4 [u5 [u6 [u7 u8]]]]]]].
  assert (rew: r = last (ch (sys oneBeh t) mch p0 c0) dmy) by auto.
  rewrite <- rew in *.
  rewrite <- u1 in *; rewrite <- u2 in *. rewrite u3 in *; rewrite u4 in *; rewrite u5 in *;
  rewrite u6 in *; rewrite u7 in *; rewrite u8 in *.
  destruct r.
  simpl in *.
  rewrite rew.
  pose proof (lastCombineDist _ dmy _ 0 (@lenEq mch p0 c0 t)) as r2.
  auto.
Qed.

Theorem uniqRecv2': forall {s1 s2 p c t1 t2 m1 m2},
                     recv s1 p c t1 m1 -> recv s2 p c t2 m2 -> t1 < t2 -> recvc t1 = recvc t2 ->
                     msgId m1 < msgId m2.
Proof.
  intros s1 s2 p c t1 t2 m1 m2 recvm1 recvm2 t1_lt_t2 eq_recv.
  pose proof (recvImpIn recvm1) as H1.
  pose proof (recvImpIn recvm2) as H2.
  destruct (classic (In ({|
          fromB := from m2;
          toB := to m2;
          addrB := addr m2;
          dataBM := dataM m2;
          type := s2 |}, msgId m2) ( (combine (ch (sys oneBeh t1) (recvc t2) p c)
            (labelCh t1 (recvc t2) p c))))) as [pos|enq].
  rewrite <- eq_recv in pos.
  assert (mDec: {(Build_BaseMesg (from m1) (to m1) (addr m1) (dataM m1) s1, msgId m1) =
                (Build_BaseMesg (from m2) (to m2) (addr m2) (dataM m2) s2, msgId m2)} +
               {(Build_BaseMesg (from m1) (to m1) (addr m1) (dataM m1) s1, msgId m1) <>
                (Build_BaseMesg (from m2) (to m2) (addr m2) (dataM m2) s2, msgId m2)}).
  repeat decide equality.
  apply decLabel.
  apply decAddr.
  destruct mDec as [same|diff].
  rewrite <- same in *.
  pose proof (recvNotIn recvm1) as notIn.
  assert (S t1 = t2 \/ S t1 < t2) by omega.
  destruct H as [easy | hard].
  rewrite easy in *.
  rewrite eq_recv in *.
  intuition.
  rewrite eq_recv in *.
  pose proof (inImpSent hard H2 notIn) as [t2i [cond2 [mark2 rest2]]].
  simpl in mark2.
  pose proof (msgIdTime mark2) as gt.
  simpl in gt.
  pose proof (inImpSent2 H1) as [t1i [cond1 [mark1 rest1]]].
  simpl in mark1.
  pose proof (msgIdTime mark1) as lt.
  simpl in lt.
  omega.

  pose proof (last_nth (combine (ch (sys oneBeh t1) (recvc t1) p c) (labelCh t1 (recvc t1) p c)) (dmy, 0)) as isLast.
  pose proof (in_nth (dmy, 0) pos) as [i [i_lt eq]].

  assert (i = length (combine (ch (sys oneBeh t1) (recvc t1) p c)
                              (labelCh t1 (recvc t1) p c)) - 1 \/
         i < length (combine (ch (sys oneBeh t1) (recvc t1) p c)
                    (labelCh t1 (recvc t1) p c)) - 1) by omega.
  destruct H as [isEq | neq].
  rewrite isEq in eq.
  rewrite isLast in eq.

  pose proof (recvLast recvm1) as H.
  rewrite H in eq.
  firstorder.


  pose proof (combLength (@lenEq (recvc t1) p c t1)) as H0.
  rewrite <- H0 in neq.
  rewrite <- H0 in i_lt.

  assert (la: length (ch (sys oneBeh t1) (recvc t1) p c) - 1 < length (ch (sys oneBeh t1)
                                                                      (recvc t1) p c))
    by omega.
  pose proof (posGreaterFull la neq) as almost.
  rewrite <- H0 in isLast.
  unfold comb in almost.
  rewrite isLast in almost.
  rewrite eq in almost.
  pose proof (recvLast recvm1) as K.
  rewrite K in almost.
  simpl in almost.
  assumption.


  pose proof (inImpSent t1_lt_t2 H2 enq) as [t2i [cond2 [mark2 rest2]]].
  simpl in mark2.
  pose proof (inImpSent2 H1) as [t1i [cond1 [mark1 rest1]]].
  simpl in mark1.

  pose proof (msgIdTime mark1) as lt.
  pose proof (msgIdTime mark2) as gt.
  simpl in *.
  rewrite lt; rewrite gt; omega.
Qed.

Theorem uniqRecv2: forall {s p c t1 t2 m},
                     recv s p c t1 m -> recv s p c t2 m -> t1 = t2.
Proof.
  intros s p c t1 t2 m recv1 recv2.
  pose proof (useful recv1 recv2).
  unfold Time in *.
  assert (t1 = t2 \/ t1 < t2 \/ t2 < t1) by omega.
  destruct H0 as [eq | [lt | gt]].
  assumption.
  pose proof (uniqRecv2' recv1 recv2 lt H).
  omega.
  assert (recvc t2 = recvc t1) by auto.
  pose proof (uniqRecv2' recv2 recv1 gt H0).
  omega.
Qed.
