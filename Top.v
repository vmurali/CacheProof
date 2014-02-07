Require Import DataTypes L1 StoreAtomicity LatestValue Cache Channel Compatible
Rules ChannelAxiom L1Axioms CompatBehavior LatestValueAxioms BehaviorAxioms MsiState.

Module mkTop.
  Module dt := mkDataTypes.
  Module l1 := mkL1Axioms.
  Module ch' := mkChannel.
  Module ch := mkChannelPerAddr dt ch'.
  Module comp := mkCompatBehavior ch.
  Module lv := mkLatestValueAxioms ch.
  Module ba := mkBehaviorAxioms.
  Module l1T := LatestValueTheorems dt ch ba l1 comp lv.
  Module l1In := mkL1InputTypes dt l1.
  Module mkStoreAtomicity: StoreAtomicity dt l1In.
    Import dt l1 l1In l1T.
    Theorem uniqRespLabels:
      forall {r1 r2}, labelR r1 = labelR r2 ->
                      timeR r1 = timeR r2 /\
                      desc (reqFn (fst (labelR r1)) (snd (labelR r1))) = Ld ->
                      dataR r1 = dataR r2.
    Proof.
      intros r1 r2 lEq.
      destruct r1; destruct r2; simpl in *.
      destruct labelR0; destruct labelR1.
      injection lEq as c_eq i_eq.
      rewrite <- c_eq in *; rewrite <- i_eq in *; clear lEq c_eq i_eq.
      destruct defR0; destruct defR1; simpl in *.
      pose proof (enqLdImpDeq e) as [q1 [f1 v1]]; pose proof (enqLdImpDeq e0) as [q2 [f2 v2]].
      pose proof (uniqDeqProc2 q1 q2) as H; rewrite H in *.
      rewrite v1 in v2; firstorder.
      pose proof (enqLdImpDeq e) as [q1 [f1 v1]]; pose proof (enqStImpDeq e0) as [q2 f2].
      rewrite f1 in f2; discriminate.
      pose proof (enqLdImpDeq e0) as [q1 [f1 v1]]; pose proof (enqStImpDeq e) as [q2 f2].
      rewrite f1 in f2; discriminate.
      pose proof (enqStImpDeq e0) as [q1 f1]; pose proof (enqStImpDeq e) as [q2 f2].
      pose proof (uniqDeqProc2 q1 q2) as H; rewrite H in *.
      intuition.
      rewrite f2 in H2; discriminate.
    Qed.

  Theorem uniqRespTimes:
    forall {r1 r2}, timeR r1 = timeR r2 ->
                    loc (reqFn (fst (labelR r1)) (snd (labelR r1))) =
                         loc (reqFn (fst (labelR r2)) (snd (labelR r2))) ->
                    desc (reqFn (fst (labelR r1)) (snd (labelR r1))) = St ->
                    labelR r1 = labelR r2.
    Proof.
      intros r1 r2 tEq addrEq dSt.
      destruct r1; destruct r2; simpl in *.
      destruct labelR0; destruct labelR1.
      rewrite tEq in *; clear tEq.
      destruct defR0.
      pose proof (enqLdImpDeq e) as [q1 [f1 v1]].
      simpl in dSt.
      rewrite f1 in dSt; discriminate.
      pose proof (enqStImpDeq e) as [q1 _].
      pose proof (processDeq q1) as sth.
      simpl in sth.
      simpl in dSt.
      rewrite dSt in sth.
      destruct (decTree c c0).
      rewrite <- e0 in *; clear e0.
      destruct defR1.
      pose proof (enqLdImpDeq e0) as [q2 _].
      pose proof (uniqDeqProc q1 q2) as H.
      rewrite <- H in *.
      reflexivity.
      pose proof (enqStImpDeq e0) as [q2 _].
      pose proof (uniqDeqProc q1 q2) as H.
      rewrite <- H in *.
      reflexivity.
      pose proof (deqLeaf q1) as l1.
      pose proof (deqDef q1) as d1.

      destruct defR1.

      pose proof (enqLdImpDeq e0) as [q2 _].
      pose proof (deqLeaf q2) as l2.
      pose proof (deqDef q2) as d2.
      pose proof (uniqM d1 l1 sth d2 l2 n) as stIn.
      pose proof (processDeq q2) as sth2.
      simpl in sth2.
      simpl in addrEq.
      rewrite <- addrEq in sth2.
      rewrite stIn in sth2.
      destruct (desc (reqFn c0 i0)).
      intuition.
      discriminate.

      pose proof (enqStImpDeq e0) as [q2 _].
      pose proof (deqLeaf q2) as l2.
      pose proof (deqDef q2) as d2.
      pose proof (uniqM d1 l1 sth d2 l2 n) as stIn.
      pose proof (processDeq q2) as sth2.
      simpl in sth2.
      simpl in addrEq.
      rewrite <- addrEq in sth2.
      rewrite stIn in sth2.
      destruct (desc (reqFn c0 i0)).
      intuition.
      discriminate.
    Qed.

    Theorem localOrdering:
      forall {r1 r2}, fst (labelR r1) = fst (labelR r2) ->
                      snd (labelR r1) < snd (labelR r2) -> ~ timeR r1 > timeR r2.
    Proof.
      unfold not; intros r1 r2 pEq lblLt tLt.
      destruct r1; destruct r2; simpl in *.
      destruct labelR0; destruct labelR1; simpl in *.
      rewrite pEq in *; clear pEq.

      destruct defR0; destruct defR1.

      pose proof (enqLdImpDeq e) as [d1 _].
      pose proof (enqLdImpDeq e0) as [d2 _].
      apply (deqOrder d1 d2 lblLt tLt).
      
      pose proof (enqLdImpDeq e) as [d1 _].
      pose proof (enqStImpDeq e0) as [d2 _].
      apply (deqOrder d1 d2 lblLt tLt).

      pose proof (enqStImpDeq e) as [d1 _].
      pose proof (enqLdImpDeq e0) as [d2 _].
      apply (deqOrder d1 d2 lblLt tLt).

      pose proof (enqStImpDeq e) as [d1 _].
      pose proof (enqStImpDeq e0) as [d2 _].
      apply (deqOrder d1 d2 lblLt tLt).
    Qed.

    Theorem allPrevious:
      forall {r1 i}, i < snd (labelR r1) -> exists r2, fst (labelR r2) = fst (labelR r1) /\
                                                       snd (labelR r2) = i.
    Proof.
      intros r1 i i_lt_r1t.
      destruct r1.
      destruct labelR0.
      simpl in *.
      destruct defR0.

      pose proof (enqLdImpDeq e) as [deq _].
      pose proof (deqImpDeqBefore deq i_lt_r1t) as [t' deq2].
      pose proof (deqImpEnq deq2) as stf.
      destruct (desc (reqFn c i)).
      exists (Build_RespSet (c,i) (mkDataTypes.data c (loc (reqFn c i)) t') t'
                            (inl stf)).
      simpl; intuition.
      exists (Build_RespSet (c,i) (initData zero) t' (inr stf)).
      simpl; intuition.

      pose proof (enqStImpDeq e) as [deq _].
      pose proof (deqImpDeqBefore deq i_lt_r1t) as [t' deq2].
      pose proof (deqImpEnq deq2) as stf.
      destruct (desc (reqFn c i)).
      exists (Build_RespSet (c,i) (mkDataTypes.data c (loc (reqFn c i)) t') t'
                            (inl stf)).
      simpl; intuition.
      exists (Build_RespSet (c,i) (initData zero) t' (inr stf)).
      simpl; intuition.
    Qed.

    Theorem storeAtomicity:
      forall {r},
        let q := reqFn (fst (labelR r)) (snd (labelR r)) in
        desc q = Ld ->
        (dataR r = initData (loc q) /\
         forall {r'}, let q' := reqFn (fst (labelR r')) (snd (labelR r')) in
                      0 <= timeR r' < timeR r -> ~ (loc q' = loc q /\ desc q' = St)) \/
        (exists rm,
           let qm := reqFn (fst (labelR rm)) (snd (labelR rm)) in
           dataR r = dataQ qm /\
           timeR rm < timeR r /\ loc qm = loc q /\ desc qm = St /\
           forall {r'}, let q' := reqFn (fst (labelR r')) (snd (labelR r')) in
                        timeR rm < timeR r' < timeR r -> ~ (loc q' = loc q /\ desc q' = St)).
    Proof.
      intros r q isLd.
      unfold q in *; clear q.
      destruct r; destruct labelR0; simpl in *.
      destruct defR0.

      pose proof (enqLdImpDeq e) as [d1 [f1 v1]].

      assert (cond: sle Sh (state c (loc (reqFn c i)) timeR0)).
      pose proof (processDeq d1) as sth.
      simpl in sth.
      rewrite f1 in sth.
      destruct (state c (loc (reqFn c i)) timeR0); unfold sle; auto.

      pose proof (deqLeaf d1) as l1.
      pose proof (deqDef d1) as def1.
      pose proof (latestValue def1 l1 cond) as sth.
      rewrite v1 in *.

      destruct sth.

      left.
      constructor.
      intuition.
      unfold not; intros r' cond1 [addrEq isSt].
      destruct r'; destruct labelR0; simpl in *.

      destruct defR0.
      pose proof (enqLdImpDeq e0) as [deq1 _].
      pose proof (deqDef deq1) as df1.
      generalize H cond1 df1 deq1 addrEq isSt; clear; firstorder.

      pose proof (enqStImpDeq e0) as [deq1 _].
      pose proof (deqDef deq1) as df1.
      generalize H cond1 df1 deq1 addrEq isSt; clear; firstorder.


      right.
      destruct H as [cb [ib [tb [defcb [tb_lt [deqcb [isSt [dtEq rest]]]]]]]].
      pose proof (deqImpEnq deqcb) as sth.
      rewrite isSt in sth.
      exists (Build_RespSet (cb, ib) dataR0 tb (inr sth)); simpl in *.
      constructor. intuition.
      constructor. intuition.
      constructor. intuition.
      constructor. intuition.

      unfold not; intros r' cond1 [addrEq isSt'].
      destruct r'; destruct labelR0; simpl in *.

      destruct defR0.
      pose proof (enqLdImpDeq e0) as [deq1 _].
      pose proof (deqDef deq1) as df1.
      generalize rest cond1 df1 deq1 addrEq isSt'; clear; firstorder.

      pose proof (enqStImpDeq e0) as [deq1 _].
      pose proof (deqDef deq1) as df1.
      generalize rest cond1 df1 deq1 addrEq isSt'; clear; firstorder.



      pose proof (enqStImpDeq e) as [d1 f1].
      rewrite isLd in f1; discriminate.
    Qed.

    Print Assumptions uniqRespLabels.
    Print Assumptions uniqRespTimes.
    Print Assumptions localOrdering.
    Print Assumptions storeAtomicity.
  End mkStoreAtomicity.
End mkTop.
