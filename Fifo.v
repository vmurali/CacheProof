Require Import CpdtTactics.

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

  Axiom fifo1: 
      forall {m te td}, enq m te -> deq m td -> forall {m' te' td'}, enq m' te' -> deq m' td' -> te' < te -> td' < td.

  Axiom fifo2:
      forall {m te td}, enq m te -> deq m td -> forall {m' te' td'}, enq m' te' -> deq m' td' -> td' < td -> te' < te.
End FifoHighLevelBasic.

Module Type FifoHighLevel (mesg: Mesg).
  Import mesg.

  Declare Module f : FifoHighLevelBasic mesg.
  Import f.

  Axiom fifo1':
    forall {m te td}, enq m te -> deq m td -> forall {m' te' td'}, enq m' te' -> deq m' td' -> te' <= te -> td' <= td.

  Axiom fifo2':
    forall {m te td}, enq m te -> deq m td -> forall {m' te' td'}, enq m' te' -> deq m' td' -> td' <= td -> te' <= te.

  Axiom enq0First: forall {m t}, enq m 0 -> deq m t -> forall t', t' < t -> forall m', deq m' t' -> False.
End FifoHighLevel.

Module GetFifoHighLevel (m: FifoHighLevelBasic) (mesg: Mesg) : FifoHighLevel mesg.
  Module f := m mesg.
  Import f.

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

  Axiom fifoAvail1:
    forall {m te td}, enq m te -> available m td -> forall {m' te' td'}, enq m' te' -> available m' td' -> te' < te -> td' < td.

  Axiom fifoAvail2:
    forall {m te td}, enq m te -> available m td -> forall {m' te' td'}, enq m' te' -> available m' td' -> td' < td -> m <> m' -> te' < te.
End FifoMidLevelBasic.

Module FifoMidBasicToHighBasic (m: FifoMidLevelBasic) (mesg: Mesg) : FifoHighLevelBasic mesg.
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

  Theorem fifo1: 
      forall {m te td}, enq m te -> deq m td -> forall {m' te' td'}, enq m' te' -> deq m' td' -> te' < te -> td' < td.
  Proof.
    intros m te td enqM deqM m' te' td' enqM' deqM' te'LtTe.
    pose proof (deqImpAvailable deqM) as availM.
    pose proof (deqImpAvailable deqM') as availM'.
    apply (fifoAvail1 enqM availM enqM' availM' te'LtTe).
  Qed.

  Theorem fifo2:
      forall {m te td}, enq m te -> deq m td -> forall {m' te' td'}, enq m' te' -> deq m' td' -> td' < td -> te' < te.
  Proof.
    intros m te td enqM deqM m' te' td' enqM' deqM' te'LtTe.
    pose proof (deqImpAvailable deqM) as availM.
    pose proof (deqImpAvailable deqM') as availM'.
    apply (fifoAvail2 enqM availM enqM' availM' te'LtTe).
    pose proof (uniqueDeq1 deqM' deqM) as uniqueDeq.
    crush.
  Qed.
  
End FifoMidBasicToHighBasic.
