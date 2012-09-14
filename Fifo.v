Require Import CpdtTactics.

Load Classical.

Module Type Mesg.
  Parameter mesg: Type.
End Mesg.

Module Type FifoHighLevelBasic (mesg: Mesg).
  Import mesg.

  Axiom enq: mesg -> nat -> Prop.

  Axiom deq: mesg -> nat -> Prop.

  Axiom uniqueEnq1: forall {m n t1 t2}, enq m t1 -> enq n t2 -> m = n -> t1 = t2.

  Axiom uniqueEnq2: forall {m n t1 t2}, enq m t1 -> enq n t2 -> t1 = t2 -> m = n.

  Axiom uniqueDeq1: forall {m n t1 t2}, deq m t1 -> deq n t2 -> m = n -> t1 = t2.

  Axiom uniqueDeq2: forall {m n t1 t2}, deq m t1 -> deq n t2 -> t1 = t2 -> m = n.

  Axiom deqImpEnq: forall {m t}, deq m t -> exists t', t' <= t /\ enq m t'.

  Axiom fifo:
    forall {m te td m' te'}, enq m te -> deq m td -> enq m' te' -> te' < te -> exists td', deq m' td' /\ td' < td.
End FifoHighLevelBasic.

Module Type FifoHighLevel (mesg: Mesg).
  Import mesg.

  Declare Module f : FifoHighLevelBasic mesg.
  Import f.

  Axiom fifo1: 
      forall {m te td}, enq m te -> deq m td -> forall {m' te' td'}, enq m' te' -> deq m' td' -> te' < te -> td' < td.

  Axiom fifo2:
      forall {m te td}, enq m te -> deq m td -> forall {m' te' td'}, enq m' te' -> deq m' td' -> td' < td -> te' < te.

  Axiom fifo1':
    forall {m te td}, enq m te -> deq m td -> forall {m' te' td'}, enq m' te' -> deq m' td' -> te' <= te -> td' <= td.

  Axiom fifo2':
    forall {m te td}, enq m te -> deq m td -> forall {m' te' td'}, enq m' te' -> deq m' td' -> td' <= td -> te' <= te.

  Axiom enq0First: forall {m t}, enq m 0 -> deq m t -> forall t', t' < t -> forall m', deq m' t' -> False.
End FifoHighLevel.

Module GetFifoHighLevel (m: FifoHighLevelBasic) (mesg: Mesg) : FifoHighLevel mesg.
  Module f := m mesg.
  Import f.

  Theorem fifo1 {m te td} (enqm: enq m te) (deqm: deq m td) {m' te' td'} (enqm': enq m' te') (deqm': deq m' td') (lt: te' < te): td' < td.
    pose proof (fifo enqm deqm enqm' lt) as fifo.
    destruct fifo as [td'' [deqm'' ltd]].
    assert (td'' = td') by (apply (uniqueDeq1 deqm'' deqm'); crush).
    crush.
  Qed.

  Theorem fifo2 {m te td} (enqm: enq m te) (deqm: deq m td) {m' te' td'} (enqm': enq m' te') (deqm': deq m' td') (lt: td' < td): te' < te.
    pose proof (fifo1 enqm' deqm' enqm deqm) as fifo.
    assert (rew: (te' >= te -> False) -> te' < te) by crush.
    apply rew; intro te'LeTe; clear rew.
    assert (notEqOrEq: te' <> te \/ te' = te) by decide equality.
    destruct notEqOrEq as [notEq | eq].
    assert (gt: te < te') by crush.
    crush.
    assert (mEq: m' = m) by (apply (uniqueEnq2 enqm' enqm); crush).
    assert (tdEq: td' = td) by (apply (uniqueDeq1 deqm' deqm); crush).
    crush.
  Qed.

  Theorem fifo1' {m te td} (enqM: enq m te) (deqM: deq m td) {m' te' td'} (enqM': enq m' te') (deqM': deq m' td'): te' <= te -> td' <= td.
  Proof.
    intro te'LeTe.
    assert (cases: te' = te \/ te' < te) by crush.
    destruct cases as [te'EqTe | te'LtTe].
    assert (m' = m) by (apply (uniqueEnq2 enqM' enqM); crush).
    assert (td' = td) by (apply (uniqueDeq1 deqM' deqM); crush).
    crush.
    assert (td' < td) by (apply (fifo1 enqM deqM enqM' deqM'); crush).
    crush.
  Qed.

  Theorem fifo2' {m te td} (enqM: enq m te) (deqM: deq m td) {m' te' td'} (enqM': enq m' te') (deqM': deq m' td'): td' <= td -> te' <= te.
  Proof.
    intro td'LeTe.
    assert (cases: td' = td \/ td' < td) by crush.
    destruct cases as [td'EqTd | td'LtTd].
    assert (m' = m) by (apply (uniqueDeq2 deqM' deqM); crush).
    assert (te' = te) by (apply (uniqueEnq1 enqM' enqM); crush).
    crush.
    assert (te' < te) by (apply (fifo2 enqM deqM enqM' deqM'); crush).
    crush.
  Qed.

  Theorem enq0First {m t} (enq0: enq m 0) (deqT: deq m t) t' (lt: t' < t) m' (deqM': deq m' t'): False.
  Proof.
    pose proof (deqImpEnq deqM') as exEnq.
    destruct exEnq as [t'' rest].
    destruct rest as [leEnq enqM'].
    pose proof (fifo2 enq0 deqT enqM' deqM' lt).
    crush.
  Qed.
End GetFifoHighLevel.

Module Type FifoMidLevelBasic (mesg: Mesg).
  Import mesg.

  Axiom available: mesg -> nat -> Prop.
  Axiom space: nat -> Prop.
  Axiom enq: mesg -> nat -> Prop.
  Axiom deq: mesg -> nat -> Prop.

  Axiom uniqueEnq1: forall {m n t1 t2}, enq m t1 -> enq n t2 -> m = n -> t1 = t2.

  Axiom uniqueEnq2: forall {m n t1 t2}, enq m t1 -> enq n t2 -> t1 = t2 -> m = n.

  Axiom deqImpAvailable: forall {m t}, deq m t -> available m t.

  Axiom enqImpSpace: forall {m t}, enq m t -> space t.

  Axiom enqImpEvenAvailable:
    (forall m t, available m t -> exists t', t' >= t /\ deq m t') ->
    forall {m t}, enq m t -> exists t', t' >= t /\ available m t'.

  Axiom availableImpEnqBefore:
    forall {m t}, available m t -> exists t', t' <= t /\ enq m t'.

  Axiom deqImpEvenSpace: forall {m t}, deq m t -> exists t', t' >= t /\ space t'.

  Axiom neverAvailImpEvenSpace: forall {t}, (forall t', t' >= t -> forall m, ~ available m t) -> (exists t', t' >= t /\ space t').

  Axiom available2ImpNotDeq: forall {m t}, available m t -> available m (S t) -> ~ deq m t.
  Axiom availableNotDeqImpAvail: forall {m t}, available m t -> ~ deq m t -> available m (S t).

  Axiom uniqueAvailable: forall {m t}, available m t -> forall {n}, available n t -> m = n.

  Axiom uniqueDeq1: forall {m n t1 t2}, deq m t1 -> deq n t2 -> m = n -> t1 = t2.

  Axiom fifoAvailable:
    forall {m te td m' te'}, enq m te -> available m td -> enq m' te' -> te' < te -> exists td', available m' td' /\ td' < td.
End FifoMidLevelBasic.

Module FifoMidBasicToHighBasic (m: FifoMidLevelBasic) (mesg: Mesg) : FifoHighLevelBasic mesg.
  Import Classical.

  Module f := m mesg.
  Import mesg.
  Import f.

  Definition enq := enq.
  Definition deq := deq.
  Definition uniqueEnq1 {m n t1 t2} := @uniqueEnq1 m n t1 t2.
  Definition uniqueEnq2 {m n t1 t2} := @uniqueEnq2 m n t1 t2.
  Definition uniqueDeq1 {m n t1 t2} := @uniqueDeq1 m n t1 t2.

  Theorem uniqueDeq2 {m n t1 t2}: deq m t1 -> deq n t2 -> t1 = t2 -> m = n.
  Proof.
    intros deqM deqN t1Eqt2.
    pose proof (deqImpAvailable deqM) as availM.
    pose proof (deqImpAvailable deqN) as availN.
    rewrite t1Eqt2 in availM.
    apply (uniqueAvailable availM availN).
  Qed.

  Theorem deqImpEnq {m t}: deq m t -> exists t', t' <= t /\ enq m t'.
  Proof.
    intros deqM.
    pose proof (deqImpAvailable deqM) as availM.
    apply (availableImpEnqBefore availM).
  Qed.

  Lemma availAgain {m t} (availm: available m t) t1 (noDeq: forall t2, t <= t2 < t1 + t -> ~ deq m t2): available m (t1 + t).
    induction t1.
    crush.
    assert (noDeqPrev: forall t2, t <= t2 < t1 + t -> ~ deq m t2) by (
      intros t2 cond; assert (cond2: t <= t2 < S t1 + t) by crush; firstorder).
    specialize (IHt1 noDeqPrev).
    assert (nowNoDeq: ~ deq m (t1 + t)) by (assert (t <= t1 + t < S t1 + t) by crush; firstorder).
    assert (eq: S t1 + t = S (t1 + t)) by crush.
    rewrite eq.
    apply availableNotDeqImpAvail; crush.
  Qed.

  Theorem fifo:
    forall {m te td m' te'}, enq m te -> deq m td -> enq m' te' -> te' < te -> exists td', deq m' td' /\ td' < td.
  Proof.
    intros m te td m' te' enqm deqm enqm' teLt.
    assert (availm: available m td) by (apply deqImpAvailable; crush).
    assert (availm': exists td'', available m' td'' /\ td'' < td) by (apply (fifoAvailable enqm availm enqm'); crush).
    destruct availm' as [td' [availm' tdLt]].
    pose proof (availAgain availm' (td - td')) as availm'Real.
    assert (eq: td - td' + td' = td) by crush.
    rewrite eq in availm'Real; clear eq.
    destruct (dec (forall t2, td' <= t2 < td -> ~ deq m' t2)) as [complex|triv].
    specialize (availm'Real complex).
    assert (mEq: m' = m) by (apply (uniqueAvailable availm'Real availm); crush).
    pose proof (uniqueEnq1 enqm' enqm mEq) as teEq.
    crush.
    destruct (dec (exists tf, deq m' tf /\ td' <= tf < td)) as [case1|case2].
    destruct case1 as [tf rest].
    exists tf; crush.
    assert (forall tf, td' <= tf < td -> ~ deq m' tf) by firstorder.
    crush.
  Qed.
End FifoMidBasicToHighBasic.
