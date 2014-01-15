Require Import Coq.Logic.Classical Rules DataTypes MsiState L1 Omega Coq.Relations.Relation_Operators Coq.Lists.Streams.

Module mkL1Axioms : L1Axioms mkDataTypes.
  Import mkDataTypes.

  Theorem deqLeaf: forall {c l a d i t}, deqR c l a d i t -> leaf c.
  Proof.
    intros c l a d i t deqr.
    unfold deqR in deqr.
    destruct oneBeh as [fn [initState trans]].
    destruct (trans t) as [transx _].
    destruct transx; 
    (simpl in *; destruct (decTree c c0) as [eq|notEq]; [rewrite eq in *; firstorder| firstorder]).
  Qed.

  Theorem deqDef: forall {c l a d i t}, deqR c l a d i t -> defined c.
  Proof.
    intros c l a d i t deqr.
    unfold deqR in deqr.
    destruct oneBeh as [fn [initState trans]].
    destruct (trans t) as [transx _].
    destruct transx; 
    (simpl in *; destruct (decTree c c0) as [eq|notEq]; [rewrite eq in *; firstorder| firstorder]).
  Qed.

  Theorem uniqDeqProc: forall {c l1 a1 d1 i1 t l2 a2 d2 i2},
                         deqR c l1 a1 d1 i1 t -> deqR c l2 a2 d2 i2 t ->
                         l1 = l2.
  Proof.
    intros c l1 a1 d1 i1 t l2 a2 d2 i2 deq1 deq2.
    unfold deqR in *.
    destruct oneBeh as [fn [initState trans]].
    destruct (trans t) as [transx _].
    destruct transx.
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

  Theorem processDeq: forall {c l a d i t}, deqR c l a d i t ->
                                            match d with
                                              | Ld => sle Sh (state c a t)
                                              | St => state c a t = Mo
                                            end.
  Proof.
    intros c l a d i t deqr.
    unfold state.
    unfold deqR in *.
    destruct oneBeh as [fn [initState trans]].
    destruct (trans t) as [transx _].
    destruct transx.
    simpl in *. destruct (decTree c c0) as [eq|notEq];
                [rewrite <- eq in *; destruct deqr as [_ [use1 [use2 _]]]; rewrite use1 in *;
                 rewrite use2 in *; rewrite e; assumption | firstorder].
    simpl in *; destruct (decTree c c0) as [eq|notEq];
                [rewrite <- eq in *; destruct deqr as [_ [use1 [use2 _]]]; rewrite use1 in *;
                 rewrite use2 in *; rewrite e; assumption | firstorder].
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
    destruct oneBeh as [fn [initState trans]].
    destruct (trans t) as [transx _].
    destruct transx.
    simpl in *; destruct (decTree c c0) as [eq|notEq]; [
                rewrite <- eq in *; destruct deqr as [use0 [use1 [use2 _]]]; rewrite use1 in *;
                 rewrite use2 in *; rewrite use0 in *; rewrite e; firstorder | firstorder].
    simpl in *; destruct (decTree c c0) as [eq|notEq]; [
                rewrite <- eq in *; destruct deqr as [use0 [use1 [use2 _]]]; rewrite use1 in *;
                 rewrite use2 in *; rewrite use0 in *; rewrite e; firstorder | firstorder].
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
    destruct oneBeh as [fn [initState trans]].
    destruct (trans t) as [transx _].
    destruct transx.
    simpl in *; destruct (decTree c c0) as [eq|notEq]; [
      rewrite <- eq in *;
      exists (lct (Streams.hd (req (fn t) c))); exists (idx (Streams.hd (req (fn t) c)));
      destruct enql as [use0 [use1 use2]]; rewrite use1 in *; rewrite use2 in *;
      rewrite use0 in *; auto | firstorder].
    simpl in *; destruct (decTree c c0); [
      rewrite e in *; destruct enql as [_ [_ use]]; discriminate | firstorder].
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
    destruct oneBeh as [fn [initState trans]].
    destruct (trans t) as [transx _].
    destruct transx.
    simpl in *; destruct (decTree c c0); [
      rewrite e in *; destruct enql as [_ use]; discriminate | firstorder].
    simpl in *; destruct (decTree c c0) as [eq|notEq]; [
      rewrite <- eq in *;
      exists (lct (Streams.hd (req (fn t) c))); exists (idx (Streams.hd (req (fn t) c)));
      destruct enql as [use1 use2]; rewrite use1 in *; rewrite use2 in *;
      auto | firstorder].
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
  Qed.

  Theorem futureSub: forall {t1 t2} c, t1 <= t2 -> match oneBeh with
                                                     | exist sys _ => subStr (req (sys t1) c)
                                                                             (req (sys t2) c)
                                                   end.
  Proof.
    intros t1 t2 c t1_le_t2.
    remember (t2 - t1) as td.
    assert (eq: t2 = t1 + td) by omega.
    rewrite eq in *; clear eq Heqtd t1_le_t2.
    destruct oneBeh as [fn [initState trans]].
    induction td.
    assert (H: t1 + 0 = t1) by omega.
    rewrite H.
    apply (rt_refl (Stream BaseReq) tlStr (req (fn t1) c)).
    assert (H: t1 + S td = S (t1 + td)) by omega.
    rewrite H; clear H.
    assert (step: subStr (req (fn (t1 + td)) c) (req (fn (S (t1 + td))) c)).
    destruct (trans (t1 + td)) as [transx _].
    destruct transx.
    simpl in *; destruct (decTree c c0); [
    apply (rt_step (Stream BaseReq) tlStr (req (fn (t1 + td)) c) (tl (req (fn (t1 + td)) c)));
      unfold tlStr; reflexivity|
    apply (rt_refl (Stream BaseReq) tlStr (req (fn (t1 + td)) c))].
    simpl in *; destruct (decTree c c0); [
    apply (rt_step (Stream BaseReq) tlStr (req (fn (t1 + td)) c) (tl (req (fn (t1 + td)) c)));
      unfold tlStr; reflexivity|
    apply (rt_refl (Stream BaseReq) tlStr (req (fn (t1 + td)) c))].
    simpl in *; apply (rt_refl (Stream BaseReq) tlStr (req (fn (t1 + td)) c)).
    simpl in *; apply (rt_refl (Stream BaseReq) tlStr (req (fn (t1 + td)) c)).
    simpl in *; apply (rt_refl (Stream BaseReq) tlStr (req (fn (t1 + td)) c)).
    simpl in *; apply (rt_refl (Stream BaseReq) tlStr (req (fn (t1 + td)) c)).
    simpl in *; apply (rt_refl (Stream BaseReq) tlStr (req (fn (t1 + td)) c)).
    simpl in *; apply (rt_refl (Stream BaseReq) tlStr (req (fn (t1 + td)) c)).
    simpl in *; apply (rt_refl (Stream BaseReq) tlStr (req (fn (t1 + td)) c)).
    simpl in *; apply (rt_refl (Stream BaseReq) tlStr (req (fn (t1 + td)) c)).
    apply (rt_trans (Stream BaseReq) tlStr (req (fn t1) c) (req (fn (t1 + td)) c)
                    (req (fn (S (t1 + td))) c)); assumption.
  Qed.

  Theorem deqHd: forall {c l a d i t},
                   deqR c l a d i t ->
                   idx (Streams.hd (req (match oneBeh with
                                           | exist sys _ => sys
                                         end t) c)) = i.
  Proof.
    intros c l a d i t deqr.
    unfold deqR in *.
    destruct oneBeh as [fn [initState trans]].
    destruct (trans t) as [transx _].
    destruct transx.
    simpl in *;
      destruct (decTree c c0); [
        rewrite <- e0 in *;
        firstorder|
        firstorder].
    simpl in *;
      destruct (decTree c c0); [
        rewrite <- e1 in *;
        firstorder|
        firstorder].
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
    assert (H: t2 <= t1) by omega.
    pose proof (futureSub c H) as sth.
    pose proof (deqHd deq1) as deqr1.
    pose proof (deqHd deq2) as deqr2.
    unfold deqR in *; clear deq1 deq2.
    destruct oneBeh as [fn [initState trans]].
    assert (notEq: req (fn t2) c <> req (fn t1) c).
    unfold not; intros contra.
    assert (Hd: Streams.hd (req (fn t2) c) = Streams.hd (req (fn t1) c)) by (f_equal; assumption).
    assert (H2: i2 <> i1) by omega.
    assert (H3: idx (hd (req (fn t2) c)) = idx (hd (req (fn t1) c))) by (f_equal; assumption).
    rewrite deqr1 in H3; rewrite deqr2 in H3.
    firstorder.
    pose proof (reqsGood sth notEq) as contra.
    rewrite deqr1 in contra; rewrite deqr2 in contra.
    omega.
  Qed.
End mkL1Axioms.