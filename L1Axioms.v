Require Import Coq.Logic.Classical Rules DataTypes MsiState L1 Omega Coq.Relations.Relation_Operators Coq.Lists.Streams DataTypes.

Module mkL1Axioms : L1Axioms mkDataTypes.
  Import mkDataTypes.

  Theorem deqLeaf: forall {c l a d i t}, deqR c l a d i t -> leaf c.
  Proof.
    intros c l a d i t deqr.
    unfold deqR in deqr.
    destruct (trans oneBeh t);
    (simpl in *; destruct (decTree c c0) as [eq|notEq]; [rewrite eq in *; firstorder| firstorder]);
    assert (c = c0) by auto; firstorder.
  Qed.

  Theorem deqDef: forall {c l a d i t}, deqR c l a d i t -> defined c.
  Proof.
    intros c l a d i t deqr.
    unfold deqR in deqr.
    destruct (trans oneBeh t);
    (simpl in *; destruct (decTree c c0) as [eq|notEq]; [rewrite eq in *; firstorder| firstorder]); assert (c = c0) by auto; firstorder.
  Qed.

  Theorem uniqDeqProc: forall {c l1 a1 d1 i1 t l2 a2 d2 i2},
                         deqR c l1 a1 d1 i1 t -> deqR c l2 a2 d2 i2 t ->
                         l1 = l2.
  Proof.
    intros c l1 a1 d1 i1 t l2 a2 d2 i2 deq1 deq2.
    unfold deqR in *.
    destruct (trans oneBeh t).
    simpl in *; destruct deq1 as [_ [use1 _]]; destruct deq2 as [_ [use2 _]];
                                           rewrite use1 in use2; firstorder.
    simpl in *; destruct deq1 as [_ [use1 _]]; destruct deq2 as [_ [use2 _]];
                                           rewrite use1 in use2; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
  Qed.

  Theorem processDeq: forall {c l a d i t}, deqR c l a d i t ->
                                            match d with
                                              | Ld => sle Sh (state c a t)
                                              | St => state c a t = Mo
                                            end.
  Proof.
    intros c l a d i t deqr.
    unfold state.
    unfold deqR in *.
    destruct (trans oneBeh t).

    destruct deqr as [eq [_ [use1 [use2 _]]]];
      rewrite <- eq in *; rewrite use1 in *; rewrite use2 in *; rewrite e; assumption.
    destruct deqr as [eq [_ [use1 [use2 _]]]];
      rewrite <- eq in *; rewrite use1 in *; rewrite use2 in *; rewrite e; assumption.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
  Qed.

  Theorem deqImpEnq: forall {c l a d i t}, deqR c l a d i t ->
                                           match d with
                                             | Ld => enqLd c l (data c a t) t
                                             | St => enqSt c l t
                                           end.
  Proof.
    intros c l a d i t deqr.
    unfold state.
    unfold deqR in *; unfold enqLd; unfold enqSt; unfold data.
    destruct (trans oneBeh t).
    destruct deqr as [eq [use0 [use1 [use2 _]]]]; rewrite <- eq in *; rewrite use1 in *;
                 rewrite use2 in *; rewrite use0 in *; rewrite e;
                 constructor; firstorder.
    destruct deqr as [eq [use0 [use1 [use2 _]]]]; rewrite <- eq in *; rewrite use1 in *;
                 rewrite use2 in *; rewrite use0 in *; rewrite e;
                 constructor; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
  Qed.

  Theorem enqLdImpDeq: forall {c l st t}, enqLd c l st t -> exists a i, deqR c l a Ld i t
                                                                        /\ data c a t = st.
  Proof.
    intros c l st t enql.
    unfold enqLd in *; unfold deqR; unfold data.
    destruct (trans oneBeh t).
    simpl in *; destruct enql as [eq [use0 [use1 use2]]];
      exists (lct (req (sys oneBeh t) c));
      exists (idx (req (sys oneBeh t) c));
      rewrite <- eq in *;
      rewrite use1 in *; rewrite use2 in *;
      rewrite use0 in *; constructor; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
  Qed.
    
  Theorem enqStImpDeq: forall {c l t}, enqSt c l t -> exists a i, deqR c l a St i t.
  Proof.
    intros c l t enql.
    unfold enqSt in *; unfold deqR; unfold data.
    destruct (trans oneBeh t).
    simpl in *; firstorder.
    destruct enql as [ef [use1 use2]];
      exists (lct (req (sys oneBeh t) c0));
      exists (idx (req (sys oneBeh t) c0));
      rewrite ef in *; rewrite use1; rewrite use2; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
  Qed.

  Theorem nextHigh: forall {c l a d i t},
                      deqR c l a d i t ->
                      idx (req (sys oneBeh t) c) < idx (req (sys oneBeh (S t)) c).
  Proof.
    intros c l a d i t deqr.
    unfold deqR in *.
    destruct (trans oneBeh t).

    simpl.
    destruct deqr as [u _].
    rewrite u.
    destruct (nextReq (req (sys oneBeh t) c)).
    destruct (decTree c c).
    assumption.
    intuition.

    simpl.
    destruct deqr as [u _].
    rewrite u.
    destruct (nextReq (req (sys oneBeh t) c)).
    destruct (decTree c c).
    assumption.
    intuition.

    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
  Qed.

  Theorem futureHigh: forall {c l a d i t1 t2}, t1 < t2 ->
                        deqR c l a d i t1 ->
                        idx (req (sys oneBeh t1) c) < idx (req (sys oneBeh t2) c).
  Proof.
    intros c l a d i t1 t2 cond deqr1.
    remember (t2 - t1 - 1) as td.
    assert (t2 = t1 + S td) by omega.
    rewrite H in *; clear Heqtd H t2 cond.
    induction td.
    assert (t1 + 1 = S t1) by omega.
    rewrite H.
    apply (nextHigh deqr1).
    assert (t1 + S (S td) = S (t1 + S td)) by omega.
    rewrite H; clear H.

    assert (idx (req (sys oneBeh (t1 + S td)) c) <= idx (req (sys oneBeh (S (t1 + S td))) c)).

    destruct (trans oneBeh (t1 + S td)).

    simpl.
    destruct nextReq.
    destruct (decTree c c0).
    rewrite <- e0 in *.
    destruct (decTree c c); intuition.
    omega.


    simpl.
    destruct nextReq.
    destruct (decTree c c0).
    rewrite <- e1 in *.
    destruct (decTree c c); intuition.
    omega.

    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.

    omega.
  Qed.

  Theorem deqIdx: forall {c l a d i t}, deqR c l a d i t -> idx (req (sys oneBeh t) c) = i.
  Proof.
    intros c l a d i t deqr.
    unfold deqR in *.
    destruct (trans oneBeh t); intuition.
    rewrite H in *; intuition.
    rewrite H in *; intuition.
  Qed.

  Theorem deqOrder: forall {c l1 a1 d1 i1 t1 l2 a2 d2 i2 t2},
                      deqR c l1 a1 d1 i1 t1 -> deqR c l2 a2 d2 i2 t2 ->
                      i1 < i2 -> ~ t1 > t2.
  Proof.
    unfold not; intros c l1 a1 d1 i1 t1 l2 a2 d2 i2 t2 deq1 deq2 i1_lt_i2 t1_gt_t2.
    pose proof (futureHigh t1_gt_t2 deq2) as idxLt.
    pose proof (deqIdx deq1) as u1.
    pose proof (deqIdx deq2) as u2.
    rewrite u1 in *; rewrite u2 in *.
    omega.
  Qed.
End mkL1Axioms.