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