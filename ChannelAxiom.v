Require Import Rules DataTypes Channel Omega Useful List Coq.Logic.Classical.

Module mkChannel: Channel mkDataTypes.
  Import mkDataTypes.
  Section local.
    Context {s: ChannelType}.
    Context {p c: Cache}.

    Theorem uniqMark1: forall {m n t}, mark s p c t m -> mark s p c t n -> m = n.
    Proof.
      intros m n t markm markn.
      unfold mark in *.
      destruct (trans oneBeh t).
      firstorder.
      firstorder.

      destruct markm as [_ [_ [_ [fromm [tom [addrm [datam idm]]]]]]].
      destruct markn as [_ [_ [_ [fromn [ton [addrn [datan idn]]]]]]].
      rewrite <- fromm in fromn;
        rewrite <- tom in ton;
        rewrite <- addrm in addrn;
        rewrite <- datam in datan;
        rewrite <- idm in idn.
      destruct m; destruct n; simpl in *.
      rewrite fromn; rewrite ton; rewrite addrn; rewrite datan; rewrite idn.
      reflexivity.

      destruct markm as [_ [_ [_ [fromm [tom [addrm [datam idm]]]]]]].
      destruct markn as [_ [_ [_ [fromn [ton [addrn [datan idn]]]]]]].
      rewrite <- fromm in fromn;
        rewrite <- tom in ton;
        rewrite <- addrm in addrn;
        rewrite <- datam in datan;
        rewrite <- idm in idn.
      destruct m; destruct n; simpl in *.
      rewrite fromn; rewrite ton; rewrite addrn; rewrite datan; rewrite idn.
      reflexivity.

      firstorder.

      destruct markm as [_ [_ [_ [fromm [tom [addrm [datam idm]]]]]]].
      destruct markn as [_ [_ [_ [fromn [ton [addrn [datan idn]]]]]]].
      rewrite <- fromm in fromn;
        rewrite <- tom in ton;
        rewrite <- addrm in addrn;
        rewrite <- datam in datan;
        rewrite <- idm in idn.
      destruct m; destruct n; simpl in *.
      rewrite fromn; rewrite ton; rewrite addrn; rewrite datan; rewrite idn.
      reflexivity.

      destruct markm as [_ [_ [_ [fromm [tom [addrm [datam idm]]]]]]].
      destruct markn as [_ [_ [_ [fromn [ton [addrn [datan idn]]]]]]].
      rewrite <- fromm in fromn;
        rewrite <- tom in ton;
        rewrite <- addrm in addrn;
        rewrite <- datam in datan;
        rewrite <- idm in idn.
      destruct m; destruct n; simpl in *.
      rewrite fromn; rewrite ton; rewrite addrn; rewrite datan; rewrite idn.
      reflexivity.

      firstorder.

      destruct markm as [_ [_ [_ [fromm [tom [addrm [datam idm]]]]]]].
      destruct markn as [_ [_ [_ [fromn [ton [addrn [datan idn]]]]]]].
      rewrite <- fromm in fromn;
        rewrite <- tom in ton;
        rewrite <- addrm in addrn;
        rewrite <- datam in datan;
        rewrite <- idm in idn.
      destruct m; destruct n; simpl in *.
      rewrite fromn; rewrite ton; rewrite addrn; rewrite datan; rewrite idn.
      reflexivity.

      firstorder.
    Qed.

    Definition uniqSend1 {m n t} := @uniqMark1 m n t.

    Theorem uniqMark2: forall {m t1 t2}, mark s p c t1 m -> mark s p c t2 m -> t1 = t2.
    Proof.
      intros m t1 t2 markm1 markm2.
      unfold mark in *.

      destruct (trans oneBeh t1).
      firstorder.
      firstorder.

      destruct (trans oneBeh t2).
      firstorder.
      firstorder.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      firstorder.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      firstorder.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.

      firstorder.

      destruct (trans oneBeh t2).
      firstorder.
      firstorder.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.

      firstorder.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      firstorder.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      firstorder.

      firstorder.

      destruct (trans oneBeh t2).
      firstorder.
      firstorder.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      firstorder.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      firstorder.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      firstorder.

      destruct (trans oneBeh t2).
      firstorder.
      firstorder.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      firstorder.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      firstorder.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      firstorder.

      firstorder.

      destruct (trans oneBeh t2).
      firstorder.
      firstorder.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      firstorder.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      firstorder.
      destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
      destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
      rewrite u1 in u2; assumption.
      firstorder.

      firstorder.
    Qed.

    Definition uniqSend2 {m t1 t2} := @uniqMark2 m t1 t2.

    Theorem uniqRecv1: forall {m n t}, recv s p c t m -> recv s p c t n -> m = n.
    Proof.
      intros m n t markm markn.
      unfold recv in *.
      destruct (trans oneBeh t).
      firstorder.
      firstorder.
      firstorder.

      destruct markm as [_ [_ [_ [fromm [tom [addrm [datam idm]]]]]]].
      destruct markn as [_ [_ [_ [fromn [ton [addrn [datan idn]]]]]]].
      rewrite <- fromm in fromn;
        rewrite <- tom in ton;
        rewrite <- addrm in addrn;
        rewrite <- datam in datan;
        rewrite <- idm in idn.
      destruct m; destruct n; simpl in *.
      rewrite fromn; rewrite ton; rewrite addrn; rewrite datan; rewrite idn.
      reflexivity.

      destruct markm as [_ [_ [_ [fromm [tom [addrm [datam idm]]]]]]].
      destruct markn as [_ [_ [_ [fromn [ton [addrn [datan idn]]]]]]].
      rewrite <- fromm in fromn;
        rewrite <- tom in ton;
        rewrite <- addrm in addrn;
        rewrite <- datam in datan;
        rewrite <- idm in idn.
      destruct m; destruct n; simpl in *.
      rewrite fromn; rewrite ton; rewrite addrn; rewrite datan; rewrite idn.
      reflexivity.

      firstorder.

      destruct markm as [_ [_ [_ [fromm [tom [addrm [datam idm]]]]]]].
      destruct markn as [_ [_ [_ [fromn [ton [addrn [datan idn]]]]]]].
      rewrite <- fromm in fromn;
        rewrite <- tom in ton;
        rewrite <- addrm in addrn;
        rewrite <- datam in datan;
        rewrite <- idm in idn.
      destruct m; destruct n; simpl in *.
      rewrite fromn; rewrite ton; rewrite addrn; rewrite datan; rewrite idn.
      reflexivity.

      destruct markm as [_ [_ [_ [fromm [tom [addrm [datam idm]]]]]]].
      destruct markn as [_ [_ [_ [fromn [ton [addrn [datan idn]]]]]]].
      rewrite <- fromm in fromn;
        rewrite <- tom in ton;
        rewrite <- addrm in addrn;
        rewrite <- datam in datan;
        rewrite <- idm in idn.
      destruct m; destruct n; simpl in *.
      rewrite fromn; rewrite ton; rewrite addrn; rewrite datan; rewrite idn.
      reflexivity.

      firstorder.

      destruct markm as [_ [_ [_ [fromm [tom [addrm [datam idm]]]]]]].
      destruct markn as [_ [_ [_ [fromn [ton [addrn [datan idn]]]]]]].
      rewrite <- fromm in fromn;
        rewrite <- tom in ton;
        rewrite <- addrm in addrn;
        rewrite <- datam in datan;
        rewrite <- idm in idn.
      destruct m; destruct n; simpl in *.
      rewrite fromn; rewrite ton; rewrite addrn; rewrite datan; rewrite idn.
      reflexivity.
    Qed.

    Definition uniqProc1 {m n t} := @uniqRecv1 m n t.
    Definition uniqDeq1 {m n t} := @uniqRecv1 m n t.

    Axiom uniqRecv2: forall {m t1 t2}, recv s p c t1 m -> recv s p c t2 m -> t1 = t2.
    Definition uniqProc2 {m t1 t2} := @uniqRecv2 m t1 t2.
    Definition uniqDeq2 {m t1 t2} := @uniqRecv2 m t1 t2.

    Theorem sendImpMark: forall {m t}, send s p c t m -> exists t', t' <= t /\ mark s p c t' m.
    Proof.
      intros m t sendm.
      exists t.
      assert (H: t <= t) by omega.
      firstorder.
    Qed.

    Theorem inImpSend: forall {b l t},
                         In (b, l) (combine (ch (sys oneBeh (S t)) s p c)
                                            (labelCh (S t) s p c)) ->
                         ~ In (b, l) (combine (ch (sys oneBeh t) s p c)
                                              (labelCh t s p c)) ->
                         mark s p c t (Build_Mesg (fromB b) (toB b) (addrB b)
                                                  (dataBM b) l).
    Proof.
      intros b l t inComb notInComb.
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
        dataBM := Initial |}, t)) by firstorder.
      pose proof (eachProd L) as [L1 L2]; clear L.
      rewrite L1; simpl; firstorder.
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
        dataBM := dt (sys oneBeh t) p a |}, t)) by firstorder.
      pose proof (eachProd L) as [L1 L2]; clear L.
      rewrite L1; simpl; firstorder.
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
      firstorder.
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
        dataBM := Initial |}, t)) by firstorder.
      pose proof (eachProd L) as [L1 L2]; clear L.
      rewrite L1; simpl; firstorder.
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


      simpl in *.
      assert (rew: r = last (ch (sys oneBeh t) rch p0 c0) dmy) by auto;
      rewrite <- rew in *.
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
        toB := toB r;
        addrB := a;
        dataBM := dt (sys oneBeh t) p a |}, t)) by firstorder.
      pose proof (eachProd L) as [L1 L2]; clear L.
      rewrite L1; simpl; firstorder.
      firstorder.
      firstorder.
      destruct (decTree p0 c) as [easy|hard].
      assert (c = p0) by auto; firstorder.
      firstorder.
      destruct (decTree p0 c) as [sth | easy].
      destruct (decTree c0 p) as [ez | hd].
      assert (p = c0) by auto; firstorder.
      firstorder.
      firstorder.

      destruct (decTree p p0) as [pEq | pNeq].
      rewrite <- pEq in *.
      destruct (decTree c c0) as [cEq | cNeq].
      rewrite <- cEq in *.
      destruct (decTree c c).
      destruct (decTree p p).
      pose proof (removeCombine (ch (sys oneBeh t) rch p c) (labelCh t rch p c)) as H.
      rewrite <- H in inComb.
      pose proof (notInRemove (b,l) (combine (ch (sys oneBeh t) rch p c) (labelCh t rch p c)) inComb) as H2.
      firstorder.
      firstorder.
      firstorder.
      destruct (decTree c0 c).
      assert (c = c0) by auto; firstorder.
      firstorder.
      destruct (decTree p0 p).
      assert (p = p0) by auto; firstorder.
      destruct (decTree c0 c); firstorder.


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
        dataBM := dt (sys oneBeh t) p a |}, t)) by firstorder.
      pose proof (eachProd L) as [L1 L2]; clear L.
      rewrite L1; simpl; firstorder.
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
      firstorder.
      destruct (decTree p p0) as [ez | hd].
      rewrite <- ez in *.
      destruct (decTree c c0) as [m1 | m2].
      rewrite <- m1 in *.
      destruct (decTree p p).
      destruct (decTree c c).
      pose proof (removeCombine (ch (sys oneBeh t) rch p c) (labelCh t rch p c)) as H.
      rewrite <- H in inComb.
      pose proof (notInRemove (b,l) (combine (ch (sys oneBeh t) rch p c) (labelCh t rch p c)) inComb) as H2.
      firstorder.
      firstorder.
      firstorder.
      destruct (decTree c0 c).
      assert (c = c0) by auto; firstorder.
      destruct (decTree p p); firstorder.
      destruct (decTree p0 p).
      assert (p = p0) by auto; firstorder.
      firstorder.
    Qed.

    Theorem inImpSent: forall {b l t},
                         In (b, l) (combine (ch (sys oneBeh t) s p c) (labelCh t s p c)) ->
                         exists t', t' <= t /\ mark s p c t' (Build_Mesg (fromB b) (toB b) (addrB b)
                                                                         (dataBM b) l).
    Proof.
      intros b l t inComb.
      pose proof @inImpSend as inImpSend.

      induction t.
      unfold labelCh in inComb.
      pose proof (combNil nat (ch (sys oneBeh 0) s p c)) as gd.
      rewrite gd in inComb.
      unfold In in inComb.
      firstorder.

      destruct (classic (In (b, l) (combine (ch (sys oneBeh t) s p c) (labelCh t s p c)))) as
      [easy | hard].
      pose proof (IHt easy) as [t' [cond rest]].
      assert (t' <= S t) by omega; exists t'; firstorder.
      
      pose proof (inImpSend b l t inComb hard) as H.
      exists t.
      assert (t <= S t) by omega.
      firstorder.
    Qed.
  End local.

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
      firstorder.
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
      firstorder.
      destruct (decTree c0 p).
      assert (p = c0) by auto; firstorder.
      destruct (decTree p0 c); firstorder.
      destruct (decTree p p0) as [ez|hd].
      rewrite <- ez in *.
      destruct (decTree c c0) as [y|ny].
      rewrite <- y in *.
      destruct (decTree p p).
      destruct (decTree c c).
      apply (eqLen (ch (sys oneBeh t) rch p c) (labelCh t rch p c) IHt).
      firstorder.
      firstorder.
      destruct (decTree c0 c).
      assert (c = c0) by auto; firstorder.
      firstorder.
      destruct (decTree p0 p).
      assert (p = p0) by auto; firstorder.
      destruct (decTree c0 c).
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
      firstorder.
      destruct (decTree p p0) as [ez|hd].
      rewrite <- ez in *.
      destruct (decTree c c0) as [y|ny].
      rewrite <- y in *.
      destruct (decTree p p).
      destruct (decTree c c).
      apply (eqLen (ch (sys oneBeh t) rch p c) (labelCh t rch p c) IHt).
      firstorder.
      firstorder.
      destruct (decTree c0 c).
      assert (c = c0) by auto; firstorder.
      destruct (decTree p p); firstorder.
      destruct (decTree p0 p).
      assert (p = p0) by auto; firstorder.
      firstorder.
    Qed.

    Section Local.
      Context {s: ChannelType}.
      Context {p: Cache}.
      Context {c: Cache}.
    Theorem recvImpIn: forall {m t}, recv s p c t m ->
                                     In (Build_BaseMesg (from m) (to m) (addr m) (dataM m),
                                         msgId m) (combine (ch (sys oneBeh t) s p c)
                                                           (labelCh t s p c)).
    Proof.
      unfold recv.
      intros m t recvm.
      destruct (trans oneBeh t).
      firstorder.
      firstorder.
      firstorder.
      destruct recvm as [u1 [u2 [u3 [use1 [use2 [use3 [use4 use5]]]]]]].
      pose proof (@lenEq rch p c t) as H.
      rewrite <- u1 in *; rewrite <- u2 in *; rewrite u3 in *.
      assert (lft: Build_BaseMesg (from m) (to m) (addr m) (dataM m) = last (ch (sys oneBeh t) rch c0 p0) dmy) by (
            rewrite use1; rewrite use2; rewrite use3; rewrite use4; 
            destruct (last (ch (sys oneBeh t) rch c0 p0) dmy); reflexivity).
      pose proof (lenEqLastCombine {|
        fromB := from m;
        toB := to m;
        addrB := addr m;
        dataBM := dataM m |} (ch (sys oneBeh t) rch c0 p0) dmy n lft (msgId m)
                                    (labelCh t rch c0 p0) 0 H use5) as almost.
      assumption.
      destruct recvm as [u1 [u2 [u3 [use1 [use2 [use3 [use4 use5]]]]]]].
      pose proof (@lenEq mch p c t) as H.
      rewrite <- u1 in *; rewrite <- u2 in *; rewrite u3 in *.
      assert (lft: Build_BaseMesg (from m) (to m) (addr m) (dataM m) = last (ch (sys oneBeh t) mch p0 c0) dmy) by (
            rewrite use1; rewrite use2; rewrite use3; rewrite use4; 
            destruct (last (ch (sys oneBeh t) mch p0 c0) dmy); reflexivity).
      pose proof (lenEqLastCombine {|
        fromB := from m;
        toB := to m;
        addrB := addr m;
        dataBM := dataM m |} (ch (sys oneBeh t) mch p0 c0) dmy n lft (msgId m)
                                    (labelCh t mch p0 c0) 0 H use5) as almost.
      assumption.
      firstorder.
      destruct recvm as [u1 [u2 [u3 [use1 [use2 [use3 [use4 use5]]]]]]].
      pose proof (@lenEq rch p c t) as H.
      rewrite <- u1 in *; rewrite <- u2 in *; rewrite u3 in *.
      assert (lft: Build_BaseMesg (from m) (to m) (addr m) (dataM m) = last (ch (sys oneBeh t) rch p0 c0) dmy) by (
            rewrite use1; rewrite use2; rewrite use3; rewrite use4; 
            destruct (last (ch (sys oneBeh t) rch p0 c0) dmy); reflexivity).
      pose proof (lenEqLastCombine {|
        fromB := from m;
        toB := to m;
        addrB := addr m;
        dataBM := dataM m |} (ch (sys oneBeh t) rch p0 c0) dmy n lft (msgId m)
                                    (labelCh t rch p0 c0) 0 H use5) as almost.
      assumption.
      destruct recvm as [u1 [u2 [u3 [use1 [use2 [use3 [use4 use5]]]]]]].
      pose proof (@lenEq mch p c t) as H.
      rewrite <- u1 in *; rewrite <- u2 in *; rewrite u3 in *.
      assert (lft: Build_BaseMesg (from m) (to m) (addr m) (dataM m) = last (ch (sys oneBeh t) mch c0 p0) dmy) by (
            rewrite use1; rewrite use2; rewrite use3; rewrite use4; 
            destruct (last (ch (sys oneBeh t) mch c0 p0) dmy); reflexivity).
      pose proof (lenEqLastCombine {|
        fromB := from m;
        toB := to m;
        addrB := addr m;
        dataBM := dataM m |} (ch (sys oneBeh t) mch c0 p0) dmy n lft (msgId m)
                                    (labelCh t mch c0 p0) 0 H use5) as almost.
      assumption.
      firstorder.
      destruct recvm as [u1 [u2 [u3 [use1 [use2 [use3 [use4 use5]]]]]]].
      pose proof (@lenEq rch p c t) as H.
      rewrite <- u1 in *; rewrite <- u2 in *; rewrite u3 in *.
      assert (lft: Build_BaseMesg (from m) (to m) (addr m) (dataM m) = last (ch (sys oneBeh t) rch p0 c0) dmy) by (
            rewrite use1; rewrite use2; rewrite use3; rewrite use4; 
            destruct (last (ch (sys oneBeh t) rch p0 c0) dmy); reflexivity).
      pose proof (lenEqLastCombine {|
        fromB := from m;
        toB := to m;
        addrB := addr m;
        dataBM := dataM m |} (ch (sys oneBeh t) rch p0 c0) dmy n lft (msgId m)
                                    (labelCh t rch p0 c0) 0 H use5) as almost.
      assumption.
    Qed.

    Theorem recvImpSend: forall {m t}, recv s p c t m -> exists t', t' <= t /\ send s p c t' m.
    Proof.
      intros m t recvm.
      pose proof (recvImpIn recvm) as gdIn.
      apply (inImpSent gdIn).
    Qed.

    Theorem procImpRecv: forall {m t}, proc s p c t m -> exists t', t' <= t /\ recv s p c t' m.
    Proof.
      intros m t procm.
      exists t.
      assert (H: t <= t) by omega.
      firstorder.
    Qed.

    Definition deqImpProc {m t} := @procImpRecv m t.
    Theorem deqImpRecv: forall {m t}, deq s p c t m -> exists t', t' <= t /\ recv s p c t' m.
    Proof.
      intros m t deqm.
      pose proof (deqImpProc deqm) as [t' [t'LeT procm]].
      pose proof (procImpRecv procm) as [t'' [t''LeT' recvm]].
      assert (t''LeT: t'' <= t) by omega.
      firstorder.
    Qed.
    Theorem deqImpSend: forall {m t}, deq s p c t m -> exists t', t' <= t /\ send s p c t' m.
    Proof.
      intros m t deqm.
      pose proof (deqImpRecv deqm) as [t' [t'LeT recvm]].
      pose proof (recvImpSend recvm) as [t'' [t''LeT' sendm]].
      assert (t''LeT: t'' <= t) by omega.
      firstorder.
    Qed.
    Theorem deqImpMark: forall {m t}, deq s p c t m -> exists t', t' <= t /\ mark s p c t' m.
    Proof.
      intros m t deqm.
      pose proof (deqImpSend deqm) as [t' [t'LeT sendm]].
      pose proof (sendImpMark sendm) as [t'' [t''LeT' markm]].
      assert (t''LeT: t'' <= t) by omega.
      firstorder.
    Qed.
    Theorem procImpSend: forall {m t}, proc s p c t m -> exists t', t' <= t /\ send s p c t' m.
    Proof.
      intros m t procm.
      pose proof (procImpRecv procm) as [t' [t'LeT recvm]].
      pose proof (recvImpSend recvm) as [t'' [t''LeT' sendm]].
      assert (t''LeT: t'' <= t) by omega.
      firstorder.
    Qed.
    Theorem procImpMark: forall {m t}, proc s p c t m -> exists t', t' <= t /\ mark s p c t' m.
    Proof.
      intros m t procm.
      pose proof (procImpSend procm) as [t' [t'LeT sendm]].
      pose proof (sendImpMark sendm) as [t'' [t''LeT' markm]].
      assert (t''LeT: t'' <= t) by omega.
      firstorder.
    Qed.
    Theorem recvImpMark: forall {m t}, recv s p c t m -> exists t', t' <= t /\ mark s p c t' m.
    Proof.
      intros m t recvm.
      pose proof (recvImpSend recvm) as [t' [t'LeT sendm]].
      pose proof (sendImpMark sendm) as [t'' [t''LeT' markm]].
      assert (t''LeT: t'' <= t) by omega.
      firstorder.
    Qed.
    Theorem procImpMarkBefore: forall {m ts tr}, proc s p c tr m -> mark s p c ts m -> ts <= tr.
    Proof.
      intros m ts tr procm markm.
      pose proof (procImpMark procm) as [t' [t'_le_tr markm']].
      pose proof uniqMark2 markm markm' as ts_eq_t'.
      omega.
    Qed.
    Theorem recvImpMarkBefore: forall {m ts tr}, recv s p c tr m -> mark s p c ts m -> ts <= tr.
    Proof.
      intros m ts tr recvm markm.
      pose proof (recvImpMark recvm) as [t' [t'_le_tr markm']].
      pose proof uniqMark2 markm markm' as ts_eq_t'.
      omega.
    Qed.

  End Local.
End mkChannel.