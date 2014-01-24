Require Import Coq.Logic.Classical Rules DataTypes MsiState L1 Omega Coq.Relations.Relation_Operators Coq.Lists.Streams DataTypes.

Module mkL1Axioms : L1Axioms mkDataTypes.
  Import mkDataTypes.

  Theorem deqLeaf: forall {c i t}, deqR c i t -> leaf c.
  Proof.
    intros c i t deqr.
    unfold deqR in deqr.
    destruct (trans oneBeh t);
    (simpl in *; destruct (decTree c c0) as [eq|notEq]; [rewrite eq in *; firstorder| firstorder]);
    assert (c = c0) by auto; firstorder.
  Qed.

  Theorem deqDef: forall {c i t}, deqR c i t -> defined c.
  Proof.
    intros c i t deqr.
    unfold deqR in deqr.
    destruct (trans oneBeh t);
    (simpl in *; destruct (decTree c c0) as [eq|notEq]; [rewrite eq in *; firstorder| firstorder]);
    assert (c = c0) by auto; firstorder.
  Qed.

  Theorem uniqDeqProc: forall {c i1 t i2},
                       deqR c i1 t -> deqR c i2 t ->
                       i1 = i2.
  Proof.
    intros c i1 t i2 deq1 deq2.
    unfold deqR in *.
    destruct (trans oneBeh t).
    simpl in *; destruct deq1 as [_ use1]; destruct deq2 as [_ use2];
                                           rewrite use1 in use2; firstorder.
    simpl in *; destruct deq1 as [_ use1]; destruct deq2 as [_ use2];
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

  Theorem processDeq: forall {c i t}, deqR c i t ->
                                      let q := reqFn c i in
                                      match desc q with
                                        | Ld => sle Sh (state c (loc q) t)
                                        | St => state c (loc q) t = Mo
                                      end.
  Proof.
    intros c i t deqr.
    unfold state.
    unfold deqR in *.
    destruct (trans oneBeh t).

    destruct deqr as [eq u1].
    rewrite eq in *.
    rewrite u1 in *.
    rewrite e in *.
    assumption.

    destruct deqr as [eq u1].
    rewrite eq in *.
    rewrite u1 in *.
    rewrite e in *.
    assumption.

    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
  Qed.


  Theorem deqImpEnq: forall {c i t}, deqR c i t ->
                                     match desc (reqFn c i) with
                                       | Ld => enqLd c i (data c (loc (reqFn c i)) t) t
                                       | St => enqSt c i t
                                     end.
  Proof.
    intros c i t deqr.
    unfold state.
    unfold deqR in *; unfold enqLd; unfold enqSt; unfold data.
    destruct (trans oneBeh t).
    destruct deqr as [eq u].
    rewrite eq in *; rewrite u in *; rewrite e in *.
    intuition.
    destruct deqr as [eq u].
    rewrite eq in *; rewrite u in *; rewrite e in *.
    intuition.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
  Qed.

  Theorem enqLdImpDeq: forall {c i st t}, enqLd c i st t -> deqR c i t /\ desc (reqFn c i) = Ld /\
                                                          data c (loc (reqFn c i)) t = st.
  Proof.
    intros c i st t enql.
    unfold enqLd in *; unfold deqR; unfold data.
    destruct (trans oneBeh t).
    destruct enql as [eq [u1 u2]].
    rewrite eq in *; rewrite u1 in *; rewrite u2 in *.
    intuition.
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
    
  Theorem enqStImpDeq: forall {c i t}, enqSt c i t -> deqR c i t /\ desc (reqFn c i) = St.
  Proof.
    intros c i t enql.
    unfold enqSt in *; unfold deqR; unfold data.
    destruct (trans oneBeh t).
    intuition.
    destruct enql as [eq u1].
    rewrite eq in *; rewrite u1 in *.
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

  Theorem reqGe: forall {c t1 t2}, t1 <= t2 -> req (sys oneBeh t2) c >= req (sys oneBeh t1) c.
  Proof.
    intros c t1 t2 le.
    remember (t2 - t1) as td.
    assert (t2 = t1 + td) by omega.
    rewrite H in *; clear le Heqtd H.
    induction td.
    assert (t1 + 0 = t1) by omega.
    rewrite H.
    omega.
    assert (t1 + S td = S (t1 + td)) by omega.
    rewrite H; clear H.
    assert (req (sys oneBeh (S (t1 + td))) c >= req (sys oneBeh (t1 + td)) c).
    destruct (trans oneBeh (t1 + td)).

    simpl.
    destruct (decTree c c0); omega.
    simpl.
    destruct (decTree c c0); omega.
    simpl.
    omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
  Qed.

  Theorem reqGt: forall {c i t1 t2}, t1 < t2 -> deqR c i t1 ->
                                     req (sys oneBeh t2) c > i.
  Proof.
    intros c i t1 t2 cond deqr.
    assert (S t1 <= t2) by omega.
    assert (req (sys oneBeh (S t1)) c > i).
    unfold deqR in *.
    destruct (trans oneBeh t1).
    simpl.
    destruct deqr as [eq sth].
    rewrite eq in *.
    destruct (decTree c c).
    rewrite sth; omega.
    firstorder.
    simpl.
    destruct deqr as [eq sth].
    rewrite eq in *.
    destruct (decTree c c).
    rewrite sth; omega.
    firstorder.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    pose proof (@reqGe c _ _ H).
    omega.
  Qed.

  Theorem uniqDeqProc2: forall {c i t1 t2},
                        deqR c i t1 -> deqR c i t2 -> t1 = t2.
  Proof.
    intros c i t1 t2 deq1 deq2.
    unfold Time in *.
    assert (t1 = t2 \/ t1 < t2 \/ t2 < t1) by omega.
    destruct H as [e1 | [e2 | e3]].
    assumption.
    pose proof (reqGt e2 deq1).
    unfold deqR in deq2.
    destruct (trans oneBeh t2).
    destruct deq2 as [_ u2].
    omega.
    destruct deq2 as [_ u2].
    omega.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    pose proof (reqGt e3 deq2).
    unfold deqR in deq1.
    destruct (trans oneBeh t1).
    destruct deq1 as [_ u2].
    omega.
    destruct deq1 as [_ u2].
    omega.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
  Qed.

  Theorem deqOrder: forall {c i1 t1 i2 t2},
                      deqR c i1 t1 -> deqR c i2 t2 ->
                      i1 < i2 -> ~ t1 > t2.
  Proof.
    unfold not; intros c i1 t1 i2 t2 deq1 deq2 iLess t2Less.
    pose proof (reqGt t2Less deq2).
    unfold deqR in deq1.
    destruct (trans oneBeh t1).
    destruct deq1 as [_ u]; omega.
    destruct deq1 as [_ u]; omega.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
  Qed.

End mkL1Axioms.