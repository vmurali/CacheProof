Require Import DataTypes StoreAtomicity Omega Coq.Logic.Classical.

Module Type L1Axioms (dt: DataTypes).
  Import dt.
  Axiom deqLeaf: forall {c l a d i t}, deqR c l a d i t -> leaf c.
  Axiom deqDef: forall {c l a d i t}, deqR c l a d i t -> defined c.
  Axiom uniqDeqProc: forall {c l1 a1 d1 i1 t l2 a2 d2 i2},
                       deqR c l1 a1 d1 i1 t -> deqR c l2 a2 d2 i2 t ->
                       l1 = l2.
  Axiom deqOrder: forall {c l1 a1 d1 i1 t1 l2 a2 d2 i2 t2},
                    deqR c l1 a1 d1 i1 t1 -> deqR c l2 a2 d2 i2 t2 ->
                    i1 < i2 -> ~ t1 > t2.
  Axiom processDeq: forall {c l a d i t}, deqR c l a d i t ->
                                          match d with
                                            | Ld => sle Sh (state c a t)
                                            | St => state c a t = Mo
                                          end.
  Axiom deqImpEnq: forall {c l a d i t}, deqR c l a d i t ->
                                         match d with
                                           | Ld => enqLd c l (data c a t) t
                                           | St => enqSt c l t
                                         end.
  Axiom enqLdImpDeq: forall {c l st t}, enqLd c l st t -> exists a i, deqR c l a Ld i t
                                                                      /\ data c a t = st.
  Axiom enqStImpDeq: forall {c l t}, enqSt c l t -> exists a i, deqR c l a St i t.
End L1Axioms.

Module Type L1InputAxioms (dt: DataTypes).
  Import dt.
  Axiom uniqDeqLabels:
  forall {c1 l1 a1 d1 i1 t1 c2 l2 a2 d2 i2 t2},
    deqR c1 l1 a1 d1 i1 t1 -> deqR c2 l2 a2 d2 i2 t2 -> l1 = l2 ->
    c1 = c2 /\ a1 = a2 /\ d1 = d2 /\ i1 = i2 /\ t1 = t2.

  Axiom uniqDeqIndicesPerProc:
  forall {c1 l1 a1 d1 i1 t1 c2 l2 a2 d2 i2 t2},
    deqR c1 l1 a1 d1 i1 t1 -> deqR c2 l2 a2 d2 i2 t2 -> c1 = c2 -> i1 = i2 ->
    l1 = l2 /\ a1 = a2 /\ d1 = d2 /\ t1 = t2.
End L1InputAxioms.

Module Type L1Theorems (dt: DataTypes).
  Import dt.
  Parameter latestValue:
  forall {c a t},
    defined c ->
    leaf c ->
    sle Sh (state c a t) ->
    match data c a t with
      | Initial => forall {ti}, 0 <= ti < t -> forall {ci li ii}, defined ci ->
                                                                  ~ deqR ci li a St ii ti
      | Store lb =>
        exists cb ib tb, defined cb /\ tb < t /\ deqR cb lb a St ib tb /\
                         forall {ti}, tb < ti < t -> forall {ci li ii}, defined ci ->
                                                                        ~ deqR ci li a St ii ti
    end.

  Parameter uniqM:
  forall {c a t}, defined c -> leaf c ->
    state c a t = Mo -> forall {co}, defined co -> leaf co -> c <> co -> state co a t = In.
End L1Theorems.

Module Type L1StoreAtomicity (dt: DataTypes).
  Import dt.
  Parameter enqHasDeq:
    forall {c1 l1 st1 t1}, enqLd c1 l1 st1 t1 + enqSt c1 l1 t1 ->
                       exists c2 l2 a2 d2 i2 t2, deqR c2 l2 a2 d2 i2 t2 /\ l1 = l2.

  Parameter enqProc:
    forall {c1 l1 st1 t1},
      enqLd c1 l1 st1 t1 + enqSt c1 l1 t1 ->
      forall {c2 l2 a2 d2 i2 t2}, deqR c2 l2 a2 d2 i2 t2 -> l1 = l2 -> c1 = c2.

  Parameter uniqEnqLabels:
    forall {rc1 rl1 rs1 rt1 rc2 rl2 rs2 rt2},
      enqLd rc1 rl1 rs1 rt1 + enqSt rc1 rl1 rt1 ->
      enqLd rc2 rl2 rs2 rt2 + enqSt rc2 rl2 rt2 ->
      rl1 = rl2 -> rc1 = rc2 /\ rt1 = rt2 /\
                   forall {qc1 ql1 qa1 qd1 qi1 qt1}, deqR qc1 ql1 qa1 qd1 qi1 qt1 ->
                     ql1 = rl1 -> qd1 = Ld -> rs1 = rs2.

  Parameter uniqEnqTimes:
    forall {rc1 rl1 rst1 rt1 rc2 rl2 rst2 rt2}
      (enq1: enqLd rc1 rl1 rst1 rt1 + enqSt rc1 rl1 rt1)
      (enq2: enqLd rc2 rl2 rst2 rt2 + enqSt rc2 rl2 rt2),
      rt1 = rt2 ->
      forall {c1 l1 a1 d1 i1 t1 c2 l2 a2 d2 i2 t2},
        deqR c1 l1 a1 d1 i1 t1 ->
        deqR c2 l2 a2 d2 i2 t2 ->
        rl1 = l1 -> rl2 = l2 -> a1 = a2 -> d1 = St -> rl1 = rl2.

  Parameter localOrdering':
    forall {rc1 rl1 rs1 rt1 rc2 rl2 rs2 rt2 qc1 ql1 qa1 qd1 qi1 qt1 qc2 ql2 qa2 qd2 qi2 qt2},
      enqLd rc1 rl1 rs1 rt1 + enqSt rc1 rl1 rt1 -> enqLd rc2 rl2 rs2 rt2 + enqSt rc2 rl2 rt2 ->
      deqR qc1 ql1 qa1 qd1 qi1 qt1 -> deqR qc2 ql2 qa2 qd2 qi2 qt2 ->
      rl1 = ql1 -> rl2 = ql2 -> qc1 = qc2 -> qa1 = qa2 -> qi1 < qi2 -> ~ rt1 > rt2.
    
  Parameter storeAtomicity':
    forall {rc rl rs rt qc ql qa qd qi qt},
      enqLd rc rl rs rt + enqSt rc rl rt ->
      rl = ql -> qd = Ld ->
      deqR qc ql qa qd qi qt ->
      match rs with
        | Initial => forall {rc' rl' rs' rt' qc' ql' qa' qd' qi' qt'},
                       enqLd rc' rl' rs' rt' + enqSt rc' rl' rt' ->
                       deqR qc' ql' qa' qd' qi' qt' ->
                       rl' = ql' -> 0 <= rt' < rt -> ~ (qa = qa' /\ qd' = St)
        | Store m =>
          exists rmc rml rms rmt qmc qml qma qmd qmi qmt
            (enqm: enqLd rmc rml rms rmt + enqSt rmc rml rmt),
            deqR qmc qml qma qmd qmi qmt /\
            rml = m /\ qml = m /\
            rmt < rt /\ qma = qa /\ qmd = St /\
            forall {rc' rl' rs' rt' qc' ql' qa' qd' qi' qt'},
              enqLd rc' rl' rs' rt' + enqSt rc' rl' rt' -> deqR qc' ql' qa' qd' qi' qt' ->
              rl' = ql' -> rmt < rt' < rt ->
              ~ (qa = qa' /\ qd' = St)
      end.
End L1StoreAtomicity.

Module mkL1StoreAtomicity (dt: DataTypes) (l1: L1Axioms dt) (l1In: L1InputAxioms dt) (l1T: L1Theorems dt): L1StoreAtomicity dt.
  Import dt l1 l1In l1T.

  Theorem enqHasDeq:
    forall {c1 l1 st1 t1}, enqLd c1 l1 st1 t1 + enqSt c1 l1 t1 ->
                       exists c2 l2 a2 d2 i2 t2, deqR c2 l2 a2 d2 i2 t2 /\ l1 = l2.
  Proof.
    intros c l st t [enqL | enqS].
    pose proof (enqLdImpDeq enqL) as [a [i [deq _]]].
    exists c; exists l; exists a; exists Ld; exists i; exists t.
    constructor; auto.
    pose proof (enqStImpDeq enqS) as [a [i deq]].
    exists c; exists l; exists a; exists St; exists i; exists t.
    constructor; auto.
  Qed.

  Theorem enqProc:
    forall {c1 l1 st1 t1},
      enqLd c1 l1 st1 t1 + enqSt c1 l1 t1 ->
      forall {c2 l2 a2 d2 i2 t2}, deqR c2 l2 a2 d2 i2 t2 -> l1 = l2 -> c1 = c2.
  Proof.
    intros.
    destruct H as [enqL|enqS].
    pose proof (enqLdImpDeq enqL) as [a [i [deq _]]].
    pose proof (uniqDeqLabels deq H0 H1).
    firstorder.
    pose proof (enqStImpDeq enqS) as [a [i deq]].
    pose proof (uniqDeqLabels deq H0 H1).
    firstorder.
  Qed.

  Theorem uniqEnqLabels:
    forall {rc1 rl1 rs1 rt1 rc2 rl2 rs2 rt2},
      enqLd rc1 rl1 rs1 rt1 + enqSt rc1 rl1 rt1 ->
      enqLd rc2 rl2 rs2 rt2 + enqSt rc2 rl2 rt2 ->
      rl1 = rl2 -> rc1 = rc2 /\ rt1 = rt2 /\
                   forall {qc1 ql1 qa1 qd1 qi1 qt1}, deqR qc1 ql1 qa1 qd1 qi1 qt1 ->
                     ql1 = rl1 -> qd1 = Ld -> rs1 = rs2.
  Proof.
    intros.
    destruct H as [enqL1|enqS1].
    pose proof (enqLdImpDeq enqL1) as [a1 [i1 [deq1 st1Eq]]].
    destruct H0 as [enqL2|enqS2].
    pose proof (enqLdImpDeq enqL2) as [a2 [i2 [deq2 st2Eq]]].
    pose proof (uniqDeqLabels deq1 deq2 H1).
    firstorder.
    rewrite H in *; rewrite H0 in *; rewrite H3 in *; rewrite H4 in *.
    rewrite st1Eq in st2Eq.
    assumption.
    pose proof (enqStImpDeq enqS2) as [a2 [i2 deq2]].
    pose proof (uniqDeqLabels deq1 deq2 H1).
    firstorder.
    discriminate.
    pose proof (enqStImpDeq enqS1) as [a1 [i1 deq1]].
    destruct H0 as [enqL2|enqS2].
    pose proof (enqLdImpDeq enqL2) as [a2 [i2 [deq2 st2Eq]]].
    pose proof (uniqDeqLabels deq1 deq2 H1).
    firstorder.
    discriminate.
    pose proof (enqStImpDeq enqS2) as [a2 [i2 deq2]].
    pose proof (uniqDeqLabels deq1 deq2 H1).
    firstorder.
    rewrite H in *; rewrite H0 in *; rewrite H3 in *; rewrite H4 in *.
    pose proof (uniqDeqLabels H5 deq1 H6).
    firstorder.
    rewrite H7 in H10.
    discriminate.
  Qed.

  Theorem uniqEnqTimes:
    forall {rc1 rl1 rst1 rt1 rc2 rl2 rst2 rt2}
      (enq1: enqLd rc1 rl1 rst1 rt1 + enqSt rc1 rl1 rt1)
      (enq2: enqLd rc2 rl2 rst2 rt2 + enqSt rc2 rl2 rt2),
      rt1 = rt2 ->
      forall {c1 l1 a1 d1 i1 t1 c2 l2 a2 d2 i2 t2},
        deqR c1 l1 a1 d1 i1 t1 ->
        deqR c2 l2 a2 d2 i2 t2 ->
        rl1 = l1 -> rl2 = l2 -> a1 = a2 -> d1 = St -> rl1 = rl2.
  Proof.
    intros.
    destruct enq1 as [enqL1|enqS1].
    pose proof (enqLdImpDeq enqL1) as [at1 [it1 [deqt1 _]]].
    pose proof (uniqDeqLabels deqt1 H0 H2).
    assert (tEq: Ld = St) by (rewrite H5 in H6; firstorder).
    discriminate.
    pose proof (enqStImpDeq enqS1) as [at1 [it1 deqt1]].
    pose proof (uniqDeqLabels deqt1 H0 H2).
    destruct enq2 as [ld2|st2].
    pose proof (enqLdImpDeq ld2) as [at2 [it2 [deqt2 _]]].
    pose proof (uniqDeqLabels deqt2 H1 H3).
    assert (tEq: t1 = t2) by (
                              rewrite H in *;
                              assert (sth: rt2 = t1 /\ rt2 = t2) by firstorder;
                              destruct sth as [one two]; rewrite one in two; assumption).
    destruct (classic (c1 = c2)) as [eq | nEq].
    rewrite tEq in *; rewrite eq in *.
    pose proof (uniqDeqProc H0 H1).
    pose proof (uniqDeqLabels H0 H1 H8).
    assert (temp: St = d1 /\ Ld = d2 /\ d1 = d2) by firstorder.
    destruct temp as [one [two three]].
    rewrite <- one in three; rewrite <- two in three.
    discriminate.
    pose proof (deqLeaf H0) as leaf1.
    pose proof (processDeq H0) as stM.
    rewrite H5 in stM.
    pose proof (deqLeaf H1) as leaf2.
    pose proof uniqM (deqDef H0) leaf1 stM (deqDef H1) leaf2 nEq.
    pose proof (processDeq H1) as someC2.
    rewrite H4 in *.
    rewrite tEq in *.
    rewrite H8 in *.
    unfold sle in *.
    unfold slt in *.
    destruct d2. firstorder.
    discriminate.
    pose proof (enqStImpDeq st2) as [at2 [it2 deqt2]].
    pose proof (uniqDeqLabels deqt2 H1 H3).
    assert (tEq: t1 = t2) by (
                              rewrite H in *;
                              assert (sth: rt2 = t1 /\ rt2 = t2) by firstorder;
                              destruct sth as [one two]; rewrite one in two; assumption).
    destruct (classic (c1 = c2)) as [eq | nEq].
    rewrite tEq in *; rewrite eq in *.
    pose proof (uniqDeqProc H0 H1).
    pose proof (uniqDeqLabels H0 H1 H8).
    assert (temp: rc1 = c2 /\ rc2 = c2) by firstorder.
    destruct temp as [one two].
    rewrite <- two in one.
    rewrite H8 in H2.
    rewrite <- H3 in H2.
    firstorder.
    pose proof (deqLeaf H0) as leaf1.
    pose proof (processDeq H0) as stM.
    rewrite H5 in stM.
    pose proof (deqLeaf H1) as leaf2.
    pose proof uniqM (deqDef H0) leaf1 stM (deqDef H1) leaf2 nEq.
    pose proof (processDeq H1) as someC2.
    rewrite H4 in *.
    rewrite tEq in *.
    rewrite H8 in someC2.
    unfold sle in *; unfold slt in *.
    destruct d2.
    firstorder. discriminate.
  Qed.

  Theorem localOrdering':
    forall {rc1 rl1 rs1 rt1 rc2 rl2 rs2 rt2 qc1 ql1 qa1 qd1 qi1 qt1 qc2 ql2 qa2 qd2 qi2 qt2},
      enqLd rc1 rl1 rs1 rt1 + enqSt rc1 rl1 rt1 -> enqLd rc2 rl2 rs2 rt2 + enqSt rc2 rl2 rt2 ->
      deqR qc1 ql1 qa1 qd1 qi1 qt1 -> deqR qc2 ql2 qa2 qd2 qi2 qt2 ->
      rl1 = ql1 -> rl2 = ql2 -> qc1 = qc2 -> qa1 = qa2 -> qi1 < qi2 -> ~ rt1 > rt2.
  Proof.
    intros.
    destruct H as [ld1|st1].
    pose proof (enqLdImpDeq ld1) as [a1 [i1 [deq1 _]]].
    pose proof (uniqDeqLabels deq1 H1 H3).
    assert (t1: rc1 = qc1 /\ rt1 = qt1) by firstorder; clear deq1 H.
    destruct t1 as [e1 o1].
    destruct H0 as [ld2|st2].
    pose proof (enqLdImpDeq ld2) as [a2 [i2 [deq2 _]]].
    pose proof (uniqDeqLabels deq2 H2 H4).
    assert (t2: rc2 = qc2 /\ rt2 = qt2) by firstorder; clear deq2 H.
    destruct t2 as [e2 o2].
    rewrite <- e1 in H1.
    rewrite <- o1 in H1.
    rewrite <- e2 in H2.
    rewrite <- o2 in H2.
    assert (damn: rc1 = rc2) by (
                                 rewrite <- e1 in H5; rewrite <- e2 in H5; assumption).
    rewrite <- damn in H2.
    apply (deqOrder H1 H2 H7).
    pose proof (enqStImpDeq st2) as [a2 [i2 deq2]].
    pose proof (uniqDeqLabels deq2 H2 H4).
    assert (t2: rc2 = qc2 /\ rt2 = qt2) by firstorder; clear deq2 H.
    destruct t2 as [e2 o2].
    rewrite <- e1 in H1.
    rewrite <- o1 in H1.
    rewrite <- e2 in H2.
    rewrite <- o2 in H2.
    assert (damn: rc1 = rc2) by (
                                 rewrite <- e1 in H5; rewrite <- e2 in H5; assumption).
    rewrite <- damn in H2.
    apply (deqOrder H1 H2 H7).
    pose proof (enqStImpDeq st1) as [a1 [i1 deq1]].
    pose proof (uniqDeqLabels deq1 H1 H3).
    assert (t1: rc1 = qc1 /\ rt1 = qt1) by firstorder; clear deq1 H.
    destruct t1 as [e1 o1].
    destruct H0 as [ld2|st2].
    pose proof (enqLdImpDeq ld2) as [a2 [i2 [deq2 _]]].
    pose proof (uniqDeqLabels deq2 H2 H4).
    assert (t2: rc2 = qc2 /\ rt2 = qt2) by firstorder; clear deq2 H.
    destruct t2 as [e2 o2].
    rewrite <- e1 in H1.
    rewrite <- o1 in H1.
    rewrite <- e2 in H2.
    rewrite <- o2 in H2.
    assert (damn: rc1 = rc2) by (
                                 rewrite <- e1 in H5; rewrite <- e2 in H5; assumption).
    rewrite <- damn in H2.
    apply (deqOrder H1 H2 H7).
    pose proof (enqStImpDeq st2) as [a2 [i2 deq2]].
    pose proof (uniqDeqLabels deq2 H2 H4).
    assert (t2: rc2 = qc2 /\ rt2 = qt2) by firstorder; clear deq2 H.
    destruct t2 as [e2 o2].
    rewrite <- e1 in H1.
    rewrite <- o1 in H1.
    rewrite <- e2 in H2.
    rewrite <- o2 in H2.
    assert (damn: rc1 = rc2) by (
                                 rewrite <- e1 in H5; rewrite <- e2 in H5; assumption).
    rewrite <- damn in H2.
    apply (deqOrder H1 H2 H7).
  Qed.
    
  Theorem storeAtomicity':
    forall {rc rl rs rt qc ql qa qd qi qt},
      enqLd rc rl rs rt + enqSt rc rl rt ->
      rl = ql -> qd = Ld ->
      deqR qc ql qa qd qi qt ->
      match rs with
        | Initial => forall {rc' rl' rs' rt' qc' ql' qa' qd' qi' qt'},
                       enqLd rc' rl' rs' rt' + enqSt rc' rl' rt' ->
                       deqR qc' ql' qa' qd' qi' qt' ->
                       rl' = ql' -> 0 <= rt' < rt -> ~ (qa = qa' /\ qd' = St)
        | Store m =>
          exists rmc rml rms rmt qmc qml qma qmd qmi qmt
            (enqm: enqLd rmc rml rms rmt + enqSt rmc rml rmt),
            deqR qmc qml qma qmd qmi qmt /\
            rml = m /\ qml = m /\
            rmt < rt /\ qma = qa /\ qmd = St /\
            forall {rc' rl' rs' rt' qc' ql' qa' qd' qi' qt'},
              enqLd rc' rl' rs' rt' + enqSt rc' rl' rt' -> deqR qc' ql' qa' qd' qi' qt' ->
              rl' = ql' -> rmt < rt' < rt ->
              ~ (qa = qa' /\ qd' = St)
      end.
  Proof.
    intros.
    destruct H as [ld|st].
    pose proof (enqLdImpDeq ld) as [a [i [deq dt]]].
    pose proof (processDeq deq) as sth.
    simpl in *.
    pose proof (latestValue (deqDef deq) (deqLeaf deq) sth) as lv.
    rewrite dt in *.
    pose proof (uniqDeqLabels deq H2 H0) as [_ [aEq _]].
    rewrite aEq in *. clear aEq.
    destruct rs.
    intros.
    unfold not; intros [aEq dIsSt].
    rewrite dIsSt in H3.
    rewrite <- aEq in H3.
    destruct H as [ld2|st2].
    pose proof (enqLdImpDeq ld2) as [a2 [i2 [deq2 _]]].
    pose proof (uniqDeqLabels deq2 H3 H4) as [_ [_ [_ [_ tEq]]]].
    rewrite tEq in *. clear tEq.
    apply (lv qt' H5 qc' ql' qi' (deqDef H3) H3).
    pose proof (enqStImpDeq st2) as [a2 [i2 deq2]].
    pose proof (uniqDeqLabels deq2 H3 H4) as [_ [_ [_ [_ tEq]]]].
    rewrite tEq in *. clear tEq.
    apply (lv qt' H5 qc' ql' qi' (deqDef H3) H3).
    destruct lv as [cb [ib [tb [cbDef [tbLtRt [deqb noDeq]]]]]].
    pose proof (deqImpEnq deqb) as hope.
    simpl in *.
    exists cb.
    exists l.
    exists Initial.
    exists tb.
    exists cb.
    exists l.
    exists qa.
    exists St.
    exists ib.
    exists tb.
    exists (inr hope).
    constructor.
    assumption.
    constructor. auto.
    constructor. auto.
    constructor. assumption.
    constructor. auto.
    constructor. auto.
    intros.
    unfold not.
    intros [aEq store].
    rewrite store in H3.
    rewrite <- aEq in H3.
    clear aEq store.
    destruct H as [ld2|st2].
    pose proof (enqLdImpDeq ld2) as [a2 [i2 [deq2 _]]].
    pose proof (uniqDeqLabels deq2 H3 H4) as [_ [_ [_ [_ tEq]]]].
    rewrite tEq in *. clear tEq.
    apply (noDeq qt' H5 qc' ql' qi' (deqDef H3) H3).
    pose proof (enqStImpDeq st2) as [a2 [i2 deq2]].
    pose proof (uniqDeqLabels deq2 H3 H4) as [_ [_ [_ [_ tEq]]]].
    rewrite tEq in *. clear tEq.
    apply (noDeq qt' H5 qc' ql' qi' (deqDef H3) H3).
    pose proof (enqStImpDeq st) as [a2 [i2 deq2]].
    pose proof (uniqDeqLabels deq2 H2 H0) as [cEq [aEq [dEq [iEq tEq]]]].
    rewrite H1 in dEq.
    discriminate.
  Qed.
End mkL1StoreAtomicity.

Module mkL1InputTypes (d: DataTypes) (l1: L1Axioms d) <: L1InputTypes d.
  Import d l1.
  Record ReqSet: Set :=
    { procQ: Cache;
      labelQ: Label;
      loc: Addr;
      desc: Desc;
      index: Index;
      timeQ: Time;
      defQ: deqR procQ labelQ loc desc index timeQ
    }.
  Definition Req := ReqSet.

  Record RespSet: Set :=
    { procR: Cache;
      labelR: Label;
      stl: StLabel;
      timeR: Time;
      defR: enqLd procR labelR stl timeR + enqSt procR labelR timeR
    }.
  Definition Resp := RespSet.
End mkL1InputTypes.

Module mkL1InputAxioms (dt: DataTypes) (l1A: L1Axioms dt).
  Module li := mkL1InputTypes dt l1A.
  Export li.
  Module mkRealL1InputAxioms (lb: L1BaseInputAxioms dt li): L1InputAxioms dt.
    Import lb li dt l1A.
    Theorem uniqDeqLabels:
      forall {c1 l1 a1 d1 i1 t1 c2 l2 a2 d2 i2 t2},
        deqR c1 l1 a1 d1 i1 t1 -> deqR c2 l2 a2 d2 i2 t2 -> l1 = l2 ->
        c1 = c2 /\ a1 = a2 /\ d1 = d2 /\ i1 = i2 /\ t1 = t2.
    Proof.
      intros.
      pose (Build_ReqSet c1 l1 a1 d1 i1 t1 H) as q1.
      pose (Build_ReqSet c2 l2 a2 d2 i2 t2 H0) as q2.
      assert (t: labelQ q1 = labelQ q2) by (unfold labelQ; simpl in *; auto).
      pose proof uniqReqLabels t as eq.
      assert (procQ q1 = procQ q2) by (f_equal; assumption); unfold procQ in *.
      assert (loc q1 = loc q2) by (f_equal; assumption); unfold loc in *.
      assert (desc q1 = desc q2) by (f_equal; assumption); unfold desc in *.
      assert (index q1 = index q2) by (f_equal; assumption); unfold index in *.
      assert (timeQ q1 = timeQ q2) by (f_equal; assumption); unfold timeQ in *.
      simpl in *.
      firstorder.
    Qed.

    Theorem uniqDeqIndicesPerProc:
      forall {c1 l1 a1 d1 i1 t1 c2 l2 a2 d2 i2 t2},
        deqR c1 l1 a1 d1 i1 t1 -> deqR c2 l2 a2 d2 i2 t2 -> c1 = c2 -> i1 = i2 ->
        l1 = l2 /\ a1 = a2 /\ d1 = d2 /\ t1 = t2.
    Proof.
      intros.
      pose (Build_ReqSet c1 l1 a1 d1 i1 t1 H) as q1.
      pose (Build_ReqSet c2 l2 a2 d2 i2 t2 H0) as q2.
      assert (c: procQ q1 = procQ q2) by (unfold procQ; simpl in *; auto).
      assert (i: index q1 = index q2) by (unfold index; simpl in *; auto).
      pose proof uniqReqIndicesPerProc c i as eq.
      assert (labelQ q1 = labelQ q2) by (f_equal; assumption); unfold labelQ in *.
      assert (loc q1 = loc q2) by (f_equal; assumption); unfold loc in *.
      assert (desc q1 = desc q2) by (f_equal; assumption); unfold desc in *.
      assert (index q1 = index q2) by (f_equal; assumption); unfold index in *.
      assert (timeQ q1 = timeQ q2) by (f_equal; assumption); unfold timeQ in *.
      simpl in *.
      firstorder.
    Qed.
  End mkRealL1InputAxioms.
End mkL1InputAxioms.
