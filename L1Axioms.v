Require Import DataTypes Coq.Logic.Classical Rules.

Module L1Axioms (dt: DataTypes) (rl: Rules dt).
  Import dt rl.

  Theorem deqLeaf: forall {c l a d i t}, deqR c l a d i t -> leaf c.
  Proof.
    intros c l a d i t deqr.
    unfold deqR in deqr.
    destruct oneBeh as [fn [initState trans]].
    destruct t.
    rewrite initState in deqr; unfold initGlobalState in deqr; simpl in deqr.
    firstorder.
    specialize (trans t).
    destruct trans; 
    (simpl in *; destruct (decTree c c0) as [eq|notEq]; [rewrite eq in *; firstorder| firstorder]).
  Qed.

  Theorem deqDef: forall {c l a d i t}, deqR c l a d i t -> defined c.
  Proof.
    intros c l a d i t deqr.
    unfold deqR in deqr.
    destruct oneBeh as [fn [initState trans]].
    destruct t.
    rewrite initState in deqr; unfold initGlobalState in deqr; simpl in deqr.
    firstorder.
    specialize (trans t).
    destruct trans; 
    (simpl in *; destruct (decTree c c0) as [eq|notEq]; [rewrite eq in *; firstorder| firstorder]).
  Qed.

  Theorem uniqDeqProc: forall {c l1 a1 d1 i1 t l2 a2 d2 i2},
                         deqR c l1 a1 d1 i1 t -> deqR c l2 a2 d2 i2 t ->
                         l1 = l2.
  Proof.
    intros c l1 a1 d1 i1 t l2 a2 d2 i2 deq1 deq2.
    unfold deqR in *.
    destruct oneBeh as [fn [initState trans]].
    destruct t.
    rewrite initState in *; unfold initGlobalState in *; simpl in *.
    firstorder.
    specialize (trans t).
    destruct trans.
    simpl in *; destruct (decTree c c0); [
                                           destruct deq1 as [use1 _]; destruct deq2 as [use2 _];
                                           rewrite use1 in use2; firstorder| firstorder].
    simpl in *; destruct (decTree c c0); [
                                           destruct deq1 as [use1 _]; destruct deq2 as [use2 _];
                                           rewrite use1 in use2; firstorder| firstorder].
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
  Qed.

  Theorem deqOrder: forall {c l1 a1 d1 i1 t1 l2 a2 d2 i2 t2},
                      deqR c l1 a1 d1 i1 t1 -> deqR c l2 a2 d2 i2 t2 ->
                      i1 < i2 -> ~ t1 > t2.
  Proof.
    unfold not; intros c l1 a1 d1 i1 t1 l2 a2 d2 i2 t2 deq1 deq2 i1_lt_i2 t1_gt_t2.
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
