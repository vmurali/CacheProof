Require Import DataTypes L1 StoreAtomicity LatestValue Cache Channel Compatible.

Module mkTop (dt: DataTypes) (l1: L1Axioms dt) (ch: ChannelPerAddr dt)
       (ba: BehaviorAxioms dt ch) (comp: CompatBehavior dt ch)
       (lv: LatestValueAxioms dt ch l1).
  Module test := mkL1InputAxioms dt l1.
  Module li := test.li.
  Import dt l1 ch ba comp lv test li.
  Module mkStoreAtomicity (lb: L1BaseInputAxioms dt li)
  : StoreAtomicity dt li.
    Module liA := mkRealL1InputAxioms lb.
    Module l1T := LatestValueTheorems dt ch ba l1 comp lv.
    Module l1S := mkL1StoreAtomicity dt l1 liA l1T.
    Import l1T l1S liA.

    Theorem respProc:
      forall {r q}, labelR r = labelQ q -> procR r = procQ q.
    Proof.
      intros.
      destruct r. destruct q.
      simpl in *.
      pose proof (enqProc defR0 defQ0 H).
      assumption.
    Qed.

    Theorem uniqRespLabels:
      forall {r1 r2}, labelR r1 = labelR r2 ->
                      procR r1 = procR r2 /\ timeR r1 = timeR r2 /\
                      forall {q}, labelQ q = labelR r1 -> desc q = Ld ->
                                  stl r1 = stl r2.
    Proof.
      intros.
      destruct r1; destruct r2; simpl in *.
      pose proof (uniqEnqLabels defR0 defR1 H).
      destruct H0 as [p1 [p2 p3]].
      constructor. firstorder.
      constructor. firstorder.
      intros.
      destruct q.
      simpl in *.
      pose proof (p3 procQ0 labelQ0 loc0 desc0 index0 timeQ0 defQ0 H0 H1).
      assumption.
    Qed.

    Theorem localOrdering:
      forall {r1 r2 q1 q2}, labelR r1 = labelQ q1 -> labelR r2 = labelQ q2 ->
                            procQ q1 = procQ q2 ->
                            loc q1 = loc q2 -> index q1 < index q2 -> ~ timeR r1 > timeR r2.
    Proof.
      intros.
      destruct r1; destruct r2; destruct q1; destruct q2.
      simpl in *.
      pose proof (localOrdering' defR0 defR1 defQ0 defQ1 H H0 H1 H2 H3).
      assumption.
    Qed.

    Theorem storeAtomicity:
      forall {r q},
        labelR r = labelQ q -> desc q = Ld ->
        match stl r with
          | Initial => forall {r' q'},
                         labelR r' = labelQ q' -> 0 <= timeR r' < timeR r
                         -> ~ (loc q = loc q' /\ desc q' = St)
          | Store m => exists rm qm, labelR rm = m /\ labelQ qm = m /\
                                     timeR rm < timeR r /\ loc qm = loc q /\ desc qm = St /\
                                     forall {r' q'},
                                       labelR r' = labelQ q' -> timeR rm < timeR r' < timeR r ->
                                       ~ (loc q = loc q' /\ desc q' = St)
        end.
    Proof.
      intros.
      destruct r; destruct q.
      simpl in *.
      pose proof (storeAtomicity' defR0 H H0 defQ0).
      destruct stl0.
      intros.
      destruct r'; destruct q'.
      simpl in *.
      specialize (H1 procR1 labelR1 stl0 timeR1 procQ1 labelQ1 loc1 desc1 index1 timeQ1
                     defR1 defQ1 H2 H3).
      assumption.
      destruct H1 as [rmc [rml [rms [rmt [qmc [qml [qma [qmd [qmi [qmt [enqM [deqM rest]]]]]]]
                     ]]]]].
      exists (Build_RespSet rmc rml rms rmt enqM).
      exists (Build_ReqSet qmc qml qma qmd qmi qmt deqM).
      simpl in *.
      destruct rest as [a1 [a2 [a3 [a4 [a5 last]]]]].
      constructor. assumption.
      constructor. assumption.
      constructor. assumption.
      constructor. assumption.
      constructor. assumption.
      intros.
      destruct r'; destruct q'.
      simpl in *.
      pose proof (last procR1 labelR1 stl0 timeR1 procQ1 labelQ1 loc1 desc1 index1 timeQ1 defR1 defQ1 H1 H2).
      assumption.
    Qed.

    Theorem respHasReq:
      forall {r}, exists q, labelR r = labelQ q.
    Proof.
      intros.
      destruct r.
      pose proof enqHasDeq defR0 as [p [l [a [d [i [t [deq leq]]]]]]].
      exists (Build_ReqSet p l a d i t deq).
      simpl.
      assumption.
    Qed.

    Theorem uniqRespTimes:
      forall {r1 r2}, timeR r1 = timeR r2 ->
                      forall {q1 q2}, labelR r1 = labelQ q1 -> labelR r2 = labelQ q2 ->
                                      loc q1 = loc q2 -> desc q1 = St -> labelR r1 = labelR r2.
    Proof.
      intros.
      destruct r1; destruct r2; simpl in *; intros.
      destruct q1; destruct q2; simpl in *.
      pose proof (uniqEnqTimes defR0 defR1 H defQ0 defQ1 H0 H1 H2 H3).
      assumption.
    Qed.
  End mkStoreAtomicity.
End mkTop.
