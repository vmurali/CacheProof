Require Import DataTypes.
Require Import Omega.

Module Type Channel (dt: DataTypes).
  Import dt.

  Parameter marksend: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
  Parameter send: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
  Parameter recv: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
  Parameter proc: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
  Parameter deq: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.

  Section local.
    Context {s: ChannelType}.
    Context {p c : Cache}.
    Axiom uniqMarksend1: forall {m n t}, marksend s p c t m -> marksend s p c t n -> m = n.
    Axiom uniqMarksend2: forall {m t1 t2}, marksend s p c t1 m -> marksend s p c t2 m -> t1 = t2.
    Axiom uniqSend1: forall {m n t}, send s p c t m -> send s p c t n -> m = n.
    Axiom uniqSend2: forall {m t1 t2}, send s p c t1 m -> send s p c t2 m -> t1 = t2.
    Axiom uniqRecv1: forall {m n t}, recv s p c t m -> recv s p c t n -> m = n.
    Axiom uniqRecv2: forall {m t1 t2}, recv s p c t1 m -> recv s p c t2 m -> t1 = t2.
    Axiom uniqProc1: forall {m n t}, proc s p c t m -> proc s p c t n -> m = n.
    Axiom uniqProc2: forall {m t1 t2}, proc s p c t1 m -> proc s p c t2 m -> t1 = t2.
    Axiom uniqDeq1: forall {m n t}, deq s p c t m -> deq s p c t n -> m = n.
    Axiom uniqDeq2: forall {m t1 t2}, deq s p c t1 m -> deq s p c t2 m -> t1 = t2.
    Axiom sendImpMarksend: forall {m t}, send s p c t m -> exists t', t' <= t /\ marksend s p c t' m.
    Axiom recvImpSend: forall {m t}, recv s p c t m -> exists t', t' <= t /\ send s p c t' m.
    Axiom procImpRecv: forall {m t}, proc s p c t m -> exists t', t' <= t /\ recv s p c t' m.
    Axiom deqImpProc: forall {m t}, deq s p c t m -> exists t', t' <= t /\ proc s p c t' m.
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
    Theorem deqImpMarksend: forall {m t}, deq s p c t m -> exists t', t' <= t /\ marksend s p c t' m.
    Proof.
      intros m t deqm.
      pose proof (deqImpSend deqm) as [t' [t'LeT sendm]].
      pose proof (sendImpMarksend sendm) as [t'' [t''LeT' marksendm]].
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
    Theorem procImpMarksend: forall {m t}, proc s p c t m -> exists t', t' <= t /\ marksend s p c t' m.
    Proof.
      intros m t procm.
      pose proof (procImpSend procm) as [t' [t'LeT sendm]].
      pose proof (sendImpMarksend sendm) as [t'' [t''LeT' marksendm]].
      assert (t''LeT: t'' <= t) by omega.
      firstorder.
    Qed.
    Theorem recvImpMarksend: forall {m t}, recv s p c t m -> exists t', t' <= t /\ marksend s p c t' m.
    Proof.
      intros m t recvm.
      pose proof (recvImpSend recvm) as [t' [t'LeT sendm]].
      pose proof (sendImpMarksend sendm) as [t'' [t''LeT' marksendm]].
      assert (t''LeT: t'' <= t) by omega.
      firstorder.
    Qed.
  End local.
End Channel.

Module Type ChannelPerAddr (dt: DataTypes).
  Import dt.

  Parameter marksend: ChannelType -> Cache -> Cache -> Addr -> Time -> Mesg -> Prop.
  Parameter send: ChannelType -> Cache -> Cache -> Addr -> Time -> Mesg -> Prop.
  Parameter recv: ChannelType -> Cache -> Cache -> Addr -> Time -> Mesg -> Prop.
  Parameter proc: ChannelType -> Cache -> Cache -> Addr -> Time -> Mesg -> Prop.
  Parameter deq: ChannelType -> Cache -> Cache -> Addr -> Time -> Mesg -> Prop.

  Section local.
    Context {s: ChannelType}.
    Context {p c : Cache} {a: Addr}.
    Axiom uniqMarksend1: forall {m n t}, marksend s p c a t m -> marksend s p c a t n -> m = n.
    Axiom uniqMarksend2: forall {m t1 t2}, marksend s p c a t1 m -> marksend s p c a t2 m -> t1 = t2.
    Axiom uniqSend1: forall {m n t}, send s p c a t m -> send s p c a t n -> m = n.
    Axiom uniqSend2: forall {m t1 t2}, send s p c a t1 m -> send s p c a t2 m -> t1 = t2.
    Axiom uniqRecv1: forall {m n t}, recv s p c a t m -> recv s p c a t n -> m = n.
    Axiom uniqRecv2: forall {m t1 t2}, recv s p c a t1 m -> recv s p c a t2 m -> t1 = t2.
    Axiom uniqProc1: forall {m n t}, proc s p c a t m -> proc s p c a t n -> m = n.
    Axiom uniqProc2: forall {m t1 t2}, proc s p c a t1 m -> proc s p c a t2 m -> t1 = t2.
    Axiom uniqDeq1: forall {m n t}, deq s p c a t m -> deq s p c a t n -> m = n.
    Axiom uniqDeq2: forall {m t1 t2}, deq s p c a t1 m -> deq s p c a t2 m -> t1 = t2.
    Axiom sendImpMarksend: forall {m t}, send s p c a t m -> exists t', t' <= t /\ marksend s p c a t' m.
    Axiom recvImpSend: forall {m t}, recv s p c a t m -> exists t', t' <= t /\ send s p c a t' m.
    Axiom procImpRecv: forall {m t}, proc s p c a t m -> exists t', t' <= t /\ recv s p c a t' m.
    Axiom deqImpProc: forall {m t}, deq s p c a t m -> exists t', t' <= t /\ proc s p c a t' m.
    Axiom deqImpRecv: forall {m t}, deq s p c a t m -> exists t', t' <= t /\ recv s p c a t' m.
    Axiom deqImpSend: forall {m t}, deq s p c a t m -> exists t', t' <= t /\ send s p c a t' m.
    Axiom deqImpMarksend: forall {m t}, deq s p c a t m -> exists t', t' <= t /\ marksend s p c a t' m.
    Axiom procImpSend: forall {m t}, proc s p c a t m -> exists t', t' <= t /\ send s p c a t' m.
    Axiom procImpMarksend: forall {m t}, proc s p c a t m -> exists t', t' <= t /\ marksend s p c a t' m.
    Axiom recvImpMarksend: forall {m t}, recv s p c a t m -> exists t', t' <= t /\ marksend s p c a t' m.
  End local.
End ChannelPerAddr.

Module mkChannelPerAddr (dt: DataTypes) (ch: Channel dt) : ChannelPerAddr dt.
  Import dt.
  Definition marksend ch p c a t m := ch.marksend ch p c t m /\ addr m = a.
  Definition send ch p c a t m := ch.send ch p c t m /\ addr m = a.
  Definition recv ch p c a t m := ch.recv ch p c t m /\ addr m = a.
  Definition proc ch p c a t m := ch.proc ch p c t m /\ addr m = a.
  Definition deq ch p c a t m := ch.deq ch p c t m /\ addr m = a.

  Set Implicit Arguments.
  Section local.
    Variable s: ChannelType.
    Variable p c : Cache.
    Variable a: Addr.
    Definition uniqMarksend1 {m n t} (sendm : marksend s p c a t m) (sendn : marksend s p c a t n) :=
      ch.uniqMarksend1 (proj1 sendm) (proj1 sendn).
    Definition uniqMarksend2 {m t1 t2} (sendm1: marksend s p c a t1 m) (sendm2: marksend s p c a t2 m) :=
      ch.uniqMarksend2 (proj1 sendm1) (proj1 sendm2).
    Definition uniqSend1 {m n t} (sendm : send s p c a t m) (sendn : send s p c a t n) :=
      ch.uniqSend1 (proj1 sendm) (proj1 sendn).
    Definition uniqSend2 {m t1 t2} (sendm1: send s p c a t1 m) (sendm2: send s p c a t2 m) :=
      ch.uniqSend2 (proj1 sendm1) (proj1 sendm2).
    Definition uniqRecv1 {m n t} (sendm : recv s p c a t m) (sendn : recv s p c a t n) :=
      ch.uniqRecv1 (proj1 sendm) (proj1 sendn).
    Definition uniqRecv2 {m t1 t2} (sendm1: recv s p c a t1 m) (sendm2: recv s p c a t2 m) :=
      ch.uniqRecv2 (proj1 sendm1) (proj1 sendm2).
    Definition uniqProc1 {m n t} (sendm : proc s p c a t m) (sendn : proc s p c a t n) :=
      ch.uniqProc1 (proj1 sendm) (proj1 sendn).
    Definition uniqProc2 {m t1 t2} (sendm1: proc s p c a t1 m) (sendm2: proc s p c a t2 m) :=
      ch.uniqProc2 (proj1 sendm1) (proj1 sendm2).
    Definition uniqDeq1 {m n t} (deqm: deq s p c a t m) (deqn: deq s p c a t n) :=
      ch.uniqDeq1 (proj1 deqm) (proj1 deqn).
    Definition uniqDeq2 {m t1 t2} (deqm1: deq s p c a t1 m) (deqm2: deq s p c a t2 m) :=
      ch.uniqDeq2 (proj1 deqm1) (proj1 deqm2).

    Definition sendImpMarksend {m t} (deqm: send s p c a t m) :=
      match ch.sendImpMarksend (proj1 deqm) with
          | ex_intro x Px => 
              ex_intro (fun t' =>
                          t' <= t /\ marksend s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition recvImpSend {m t} (deqm: recv s p c a t m) :=
      match ch.recvImpSend (proj1 deqm) with
          | ex_intro x Px => 
              ex_intro (fun t' =>
                          t' <= t /\ send s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition procImpRecv {m t} (deqm: proc s p c a t m) :=
      match ch.procImpRecv (proj1 deqm) with
          | ex_intro x Px => 
              ex_intro (fun t' =>
                          t' <= t /\ recv s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition deqImpProc {m t} (deqm: deq s p c a t m) :=
      match ch.deqImpProc (proj1 deqm) with
          | ex_intro x Px => 
              ex_intro (fun t' =>
                          t' <= t /\ proc s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition deqImpRecv {m t} (deqm: deq s p c a t m) :=
      match ch.deqImpRecv (proj1 deqm) with
          | ex_intro x Px =>
              ex_intro (fun t' =>
                          t' <= t /\ recv s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition deqImpSend {m t} (deqm: deq s p c a t m) :=
      match ch.deqImpSend (proj1 deqm) with
          | ex_intro x Px =>
              ex_intro (fun t' =>
                          t' <= t /\ send s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition deqImpMarksend {m t} (deqm: deq s p c a t m) :=
      match ch.deqImpMarksend (proj1 deqm) with
          | ex_intro x Px => 
              ex_intro (fun t' =>
                          t' <= t /\ marksend s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition procImpSend {m t} (deqm: proc s p c a t m) :=
      match ch.procImpSend (proj1 deqm) with
          | ex_intro x Px =>
              ex_intro (fun t' =>
                          t' <= t /\ send s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition procImpMarksend {m t} (deqm: proc s p c a t m) :=
      match ch.procImpMarksend (proj1 deqm) with
          | ex_intro x Px => 
              ex_intro (fun t' =>
                          t' <= t /\ marksend s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition recvImpMarksend {m t} (deqm: recv s p c a t m) :=
      match ch.recvImpMarksend (proj1 deqm) with
          | ex_intro x Px =>
              ex_intro (fun t' =>
                          t' <= t /\ marksend s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.
  End local.
End mkChannelPerAddr.
