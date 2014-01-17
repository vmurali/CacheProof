Require Import Rules DataTypes Channel Omega Useful List Coq.Logic.Classical ChannelAxiomHelp.

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

    Theorem sendImpMark: forall {m t}, send s p c t m -> exists t', t' <= t /\ mark s p c t' m.
    Proof.
      intros m t sendm.
      exists t.
      assert (H: t <= t) by omega.
      firstorder.
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


    Axiom recvImpSend: forall {m t}, recv s p c t m -> exists t', t' <= t /\ send s p c t' m.
    Axiom uniqRecv2: forall {m t1 t2}, recv s p c t1 m -> recv s p c t2 m -> t1 = t2.

    Definition uniqProc2 {m t1 t2} := @uniqRecv2 m t1 t2.
    Definition uniqDeq2 {m t1 t2} := @uniqRecv2 m t1 t2.


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
  End local.
End mkChannel.