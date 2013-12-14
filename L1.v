Require Import DataTypes.

Require Import StoreAtomicity.

Module Type L1Axioms (d: DataTypes).
  Import d.

  Parameter deqR: forall c, leaf c -> Label -> Addr -> Desc -> Index -> Time -> Prop.
  Parameter enqLd: forall c, leaf c -> Label -> StLabel -> Time -> Prop.
  Parameter enqSt: forall c, leaf c -> Label -> Time -> Prop.

  Axiom deqOrder: forall {c leafC l1 a1 d1 i1 t1 l2 a2 d2 i2 t2},
                    deqR c leafC l1 a1 d1 i1 t1 -> deqR c leafC l2 a2 d2 i2 t2 -> i1 < i2 -> t1 < t2.

  Axiom loadS: forall {c leafC l a i t}, deqR c leafC l a Ld i t -> state c a t >= 1.
  Axiom storeM: forall {c leafC l a i t}, deqR c leafC l a St i t -> state c a t = 3.
  Axiom reqImpEnq: forall {c leafC l a d i t}, deqR c leafC l a d i t ->
                                               match d with
                                                 | Ld => enqLd c leafC l (data c a t) t
                                                 | St => enqSt c leafC l t
                                               end.
  Axiom enqLdImpReq: forall {c leafC l t v}, enqLd c leafC l v t -> exists a i d, deqR c leafC l a d i t.
  Axiom enqStImpReq: forall {c leafC l t}, enqSt c leafC l t -> exists a i d, deqR c leafC l a d i t.
  Axiom deqUniqMesg: forall {c leafC t l1 a1 d1 i1 l2 a2 d2 i2},
                       deqR c leafC l1 a1 d1 i1 t -> deqR c leafC l2 a2 d2 i2 t ->
                       l1 = l2 /\ a1 = a2 /\ d1 = d2 /\ i1 = i2.
End L1Axioms.

Module Type L1Theorems (d: DataTypes) (l1: L1Axioms d).
  Import d l1.

  Parameter latestValue:
  forall {c a t},
    leaf c -> state c a t >= 1 ->
    match data c a t with
      | Initial => forall ti, 0 <= ti <= t -> forall ci leafCi li ii, ~ deqR ci leafCi li a St ii ti
      | Store lb =>
          exists cb leafCb tb ib, tb < t /\ deqR cb leafCb lb a St ib tb /\
                                     forall ti, tb <= ti <= t ->
                                                forall ci leafCi li ii, ~ deqR ci leafCi li a St ii ti
    end.

  Parameter uniqM:
  forall {c a t},
    state c a t > 2 -> forall {co}, state co a t = 0.
End L1Theorems.

Module mkInputTypes (d: DataTypes) (l1: L1Axioms d) <: InputTypes d.
  Import d l1.
  Record Req' :=
    { proc: Cache;
      l1Pf: leaf proc;
      label: Label;
      loc: Addr;
      desc: Desc;
      index: Index;
      deqTime: Time;
      deqDone: deqR proc l1Pf label loc desc index deqTime
    }.

  Definition Req := Req'.

  Record RespLd :=
    { ldL1: Cache;
      ldL1Pf: leaf ldL1;
      ldLabel: Label;
      ldStl: StLabel;
      ldTime: Time;
      ldEnq: enqLd ldL1 ldL1Pf ldLabel ldStl ldTime
    }.

  Record RespSt :=
    { stL1: Cache;
      stL1Pf: leaf stL1;
      stLabel: Label;
      stTime: Time;
      stEnq: enqSt stL1 stL1Pf stLabel stTime
    }.

  Definition Resp := (RespLd + RespSt)%type.

  Definition procR r := match r with
                          | inl x => ldL1 x
                          | inr x => stL1 x
                        end.

  Definition origLabel r := match r with
                              | inl x => ldLabel x
                              | inr x => stLabel x
                            end.

  Definition stl (r: Resp) := match r with
                                | inl x => ldStl x
                                | inr x => Initial
                              end.

  Definition time (r: Resp) := match r with
                                 | inl x => ldTime x
                                 | inr x => stTime x
                               end.

  Print Resp.
  Print RespLd.
End mkInputTypes.

Axiom cheat: forall t, t.

Module mkSAShell (d: DataTypes) (l1: L1Axioms d) (l1t: L1Theorems d l1).
  Module it := mkInputTypes d l1.
  Declare Module mkInput : Input d it.
  Import d l1 l1t it mkInput.
  Print it.Resp.

  Module mkStoreAtomicity: StoreAtomicity d it mkInput.
    Theorem respProc:
      forall {r q}, origLabel r = label q -> procR r = proc q.
    Proof.
      intros r q lEq.
      destruct q.
      simpl in *.
      destruct desc0.
      pose proof (reqImpEnq deqDone0) as enq'.
      simpl in *.
      unfold procR in *.
      destruct r.
      destruct r.
      simpl in *.
      pose proof (enqLdImpReq ldEnq0) as [a [i [d deq']]].
      assert (label 
      pose proof (uniqReqLabels ) as dEq.
      
      destruct r.
      simpl in *.
      destruct desc0.
      destruct r.
      simpl in *.
      
      destruct 
      simpl in *.
      auto.
      unfold procR in *.
      simpl in *.
      unfold origLabel in *.
      destruct q.
      unfold origLabel in *.
      unfold procR in *.
      apply cheat.
    Qed.

    Theorem uniqRespLabels:
      forall {r1 r2}, origLabel r1 = origLabel r2 -> r1 = r2.
    Proof.
      apply cheat.
    Qed.

    Theorem uniqRespTimes:
      forall {r1 r2}, time r1 = time r2 ->
                      forall {q1 q2}, origLabel r1 = label q1 -> origLabel r2 = label q2 ->
                                      loc q1 = loc q2 -> desc q1 = St -> q1 = q2.
    Proof.
      apply cheat.
    Qed.

    Theorem localOrdering:
      forall {r1 r2 q1 q2}, origLabel r1 = label q1 -> origLabel r2 = label q2 -> proc q1 = proc q2 ->
                            loc q1 = loc q2 -> index q1 < index q2 -> ~ time r2 > time r1.
    Proof.
      apply cheat.
    Qed.

    Theorem storeAtomicity:
      forall {r q}, origLabel r = label q -> desc q = Ld ->
                    match stl r with
                      | Initial => forall {r' q'}, origLabel r' = label q' ->
                                                   0 <= time r' <= time r -> ~ (loc q = loc q' /\ desc q' = St)
                      | Store st =>
                          exists qst rst ,
                            label qst = st /\ origLabel rst = st /\ 
                            time rst < time r /\ loc q = loc qst /\ desc qst = St /\
                            forall {r' q'}, origLabel r' = label q' ->
                                            time rst < time r' <= time r ->
                                            ~ (loc q = loc q' /\ desc q' = St)
                    end.
    Proof.
      apply cheat.
    Qed.
  End mkStoreAtomicity.
End mkSAShell.
    
  Theorem respProc:
    forall {r q}, origLabel r = label q -> procR r = proc q.
  Proof.
    intros r q lEq.
    destruct r.
    elim r with (a:=). inly].
    destruct r.
  Qed.


  Definition 
  Theorem uniqRespTimes:
    forall {l1 l2}, time l1 = time l2 -> loc l1 = loc l2 -> desc l1 = St -> l1 = l2.
  Proof.
    intros l1 l2 t1Eqt2 a1Eqa2 l1S.
    
  Qed.
End mkStoreAtomicity.