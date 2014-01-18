Require Import Rules DataTypes Channel Omega Useful List Coq.Logic.Classical ChannelAxiomHelp.

Module mkChannel: Channel mkDataTypes.
  Import mkDataTypes.
  Section local.
    Context {s: ChannelType}.
    Context {p c: Cache}.

    Definition uniqMark1 {m n t}  := @ChannelAxiomHelp.uniqMark1 s p c m n t.

    Definition uniqMark2 {m n t}  := @ChannelAxiomHelp.uniqMark2 s p c m n t.

    Definition uniqSend1 {m n t} := @uniqMark1 m n t.

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


    Definition recvImpSend {m t} := @ChannelAxiomHelp.recvImpSend s p c m t.
    Definition uniqRecv2 {m : Mesg} {t1 t2: Time} := @ChannelAxiomHelp.uniqRecv2 s p c t1 t2 m.

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