Require Import Rules Channel DataTypes MsiState.

Module mkLatestValueAxioms (ch: ChannelPerAddr mkDataTypes).
  Import mkDataTypes ch.

  Theorem toChild: forall {n a t p m},
                     defined n -> defined p ->
                     parent n p -> 
                     mark mch p n a t m -> from m = MsiState.In -> dataM m = data p a t.
  Proof.
    intros n a t p m defn defp n_p markm fromm.
    unfold mark in *; unfold data in *. unfold mkDataTypes.mark in *.
    destruct (trans oneBeh t).
    firstorder.
    firstorder.
    destruct markm as [[_ [_ [use _]]] _]; discriminate.
    destruct markm as [[use0 [_ [_ [_ [_ [use1 [use2 _]]]]]]] use3];
    rewrite <- use1 in *; rewrite use3 in *; rewrite use0 in *; assumption.
    firstorder.
    destruct markm as [[_ [_ [use _]]] _]; discriminate.
    destruct markm as [[use3 [use0 _]] _];
    rewrite use3 in *; rewrite use0 in *; pose proof (noCycle n_p p1); firstorder.
    firstorder.
    destruct markm as [[use3 [use0 _]] _];
    rewrite use3 in *; rewrite use0 in *; pose proof (noCycle n_p p1); firstorder.
    firstorder.
  Qed.

  Theorem fromParent: forall {n a t p m}, defined n -> defined p ->
                      parent n p -> 
                      recv mch p n a t m -> from m = MsiState.In -> data n a (S t) = dataM m.
  Proof.
    intros n a t p m defn defp n_p recvm fromm.
    unfold recv in *; unfold data; unfold mkDataTypes.recv in *.
    destruct (trans oneBeh t).
    firstorder.
    firstorder.
    firstorder.
    destruct recvm as [[use1 [use2 _]] _];
    rewrite use1 in *; rewrite use2 in *; pose proof (noCycle n_p p1); firstorder.
    simpl;
    assert (eq: m0 = List.last (ch (sys oneBeh t) mch p0 c) dmy) by auto;
      assert (eq2: a0 = addrB m0) by auto;
    destruct recvm as [[use1 [use2 [_ [use3 [_ [use4 [use5 _]]]]]]] use0]; rewrite <- eq in *;
    rewrite use1 in *; rewrite use2 in *;
    rewrite use3 in *; rewrite use4 in *; rewrite use0 in *; rewrite eq2 in *; rewrite fromm in *; rewrite use5 in *;
    destruct (decTree n n); destruct (decAddr a a); firstorder.
    firstorder.
    destruct recvm as [[_ [_ [use _]]] _]; discriminate. 
    destruct recvm as [[use1 [use2 _]] _];
    rewrite use1 in *; rewrite use2 in *; pose proof (noCycle n_p p1); firstorder.
    firstorder.
    destruct recvm as [[_ [_ [use _]]] _]; discriminate. 
  Qed.

  Theorem toParent: forall {n a t c m},
                      defined n -> defined c ->
                      parent c n ->
                      mark mch c n a t m -> slt Sh (from m) -> dataM m = data c a t.
  Proof.
    intros n a t c m defn defc c_n markm isM.
    assert (fromm: from m = Mo) by (unfold slt; destruct (from m); firstorder); clear isM.
    unfold mark in *; unfold data in *. unfold mkDataTypes.mark in *.
    destruct (trans oneBeh t).
    firstorder.
    firstorder.
    destruct markm as [[_ [_ [use _]]] _]; discriminate.
    destruct markm as [[use0 [_ [_ [_ [_ [use1 [use2 _]]]]]]] use3];
    rewrite <- use1 in *; rewrite use3 in *; rewrite use0 in *; assumption.
    firstorder.
    destruct markm as [[_ [_ [use _]]] _]; discriminate.
    destruct markm as [[use0 [_ [_ [_ [_ [use1 [use2 _]]]]]]] use3];
    rewrite <- use1 in *; rewrite use3 in *; rewrite use0 in *; assumption.
    firstorder.
    destruct markm as [[use0 [_ [_ [_ [_ [use1 [use2 _]]]]]]] use3];
    rewrite <- use1 in *; rewrite use3 in *; rewrite use0 in *; assumption.
    firstorder.
  Qed.

  Theorem fromChild: forall {n a t c m},
                       defined n -> defined c ->
                       parent c n ->
                       recv mch c n a t m -> slt Sh (from m) -> data n a (S t) = dataM m.
  Proof.
    intros n a t c m defn defc c_n recvm isM.
    assert (fromm: from m = Mo) by (unfold slt; destruct (from m); firstorder); clear isM.
    unfold recv in *; unfold data in *. unfold mkDataTypes.recv in *.
    destruct (trans oneBeh t).
    firstorder.
    firstorder.
    firstorder.
    destruct recvm as [[_ [_ [use _]]] _]; discriminate.
    destruct recvm as [[use1 [use2 _]] _];
    rewrite use1 in *; rewrite use2 in *; pose proof (noCycle c_n p0); firstorder.
    firstorder.
    destruct recvm as [[_ [_ [use _]]] _]; discriminate.
    simpl;
    assert (eq: m0 = List.last (ch (sys oneBeh t) mch c0 p) dmy) by auto;
      assert (eq2: a0 = addrB m0) by auto;
    destruct recvm as [[use1 [use2 [_ [use3 [_ [use4 [use5 _]]]]]]] use0]; rewrite <- eq in *;
    rewrite use1 in *; rewrite use2 in *;
    rewrite use3 in *; rewrite use4 in *; rewrite use0 in *; rewrite eq2 in *; rewrite fromm in *; rewrite use5 in *;
    destruct (decTree n n); destruct (decAddr a a); firstorder.
    firstorder.
    destruct recvm as [[_ [_ [use _]]] _]; discriminate.
  Qed.

  Theorem initLatest: forall a, data hier a 0 = Initial /\ state hier a 0 = Mo.
  Proof.
    intros a.
    unfold data; unfold state.
    pose proof (init oneBeh) as initi.
    rewrite initi.
    unfold initGlobalState.
    simpl.
    destruct (decTree hier hier) as [eq |neq].
    constructor; firstorder.
    firstorder.
  Qed.

  Theorem deqImpData: forall {n a t l i}, defined n -> deqR n l a St i t ->
                                          data n a (S t) = Store l.
  Proof.
    intros n a t l i defn deqr.
    unfold deqR in *; unfold data.
    destruct (trans oneBeh t).
    destruct deqr as [_ [_ [_ [eq _]]]].
    rewrite e in eq.
    discriminate.
    simpl.
    destruct deqr as [c_eq_n [lab [loc [des ind]]]].
    destruct (decTree n c) as [eq | neq].
    rewrite eq.
    destruct (decAddr a (lct (Streams.hd (req (sys oneBeh t) c)))) as [seq | sneq].
    rewrite lab; reflexivity.
    rewrite loc in *.
    firstorder.
    rewrite c_eq_n in neq; firstorder.
    firstorder.
    firstorder.
    firstorder.
    firstorder.
    firstorder.
    firstorder.
    firstorder.
    firstorder.
  Qed.

  Theorem changeData:
    forall {n a t}, defined n ->
                    data n a (S t) <> data n a t ->
                    (exists m, (exists p, defined p /\ parent n p /\ recv mch p n a t m /\ from m = MsiState.In) \/
                               (exists c, defined c /\ parent c n /\ recv mch c n a t m /\
                                          slt Sh (from m))) \/
                    exists l i, deqR n l a St i t.
  Proof.
    intros n a t defn dtNeq.
    unfold data in *; unfold recv in *; unfold deqR in *; unfold mkDataTypes.recv in *.
    destruct (trans oneBeh t).
    simpl in *. firstorder.
    simpl in *.
    right.
    destruct (decTree n c).
    rewrite e1 in *.
    destruct (decAddr a (lct (Streams.hd (req (sys oneBeh t) c)))).
    exists (lbl (Streams.hd (req (sys oneBeh t) c))).
    exists (idx (Streams.hd (req (sys oneBeh t) c))).
    constructor; firstorder.
    firstorder.
    firstorder.
    simpl in *.
    firstorder.
    simpl in *.
    firstorder.
    simpl in *.
    left.
    exists (Build_Mesg (fromB m) (toB m) (addrB m) (dataBM m) (List.last (labelCh t mch p c) 0)).
    simpl.
    left.
    exists p.
    assert (sth: m = List.last (ch (sys oneBeh t) mch p c) dmy) by auto.
    rewrite <- sth in *.
    destruct (decTree n c) as [nEq | nNeq].
    rewrite <- nEq in *.
    destruct (decAddr a a0) as [aEq | aNeq].
    destruct (fromB m); firstorder.
    firstorder.
    firstorder.

    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *.
    left.
    exists (Build_Mesg (fromB m) (toB m) (addrB m) (dataBM m) (List.last (labelCh t mch c p) 0)).
    simpl.
    right.
    exists c.
    assert (sth: m = List.last (ch (sys oneBeh t) mch c p) dmy) by auto.
    rewrite <- sth in *.
    destruct (decTree n p) as [nEq | nNeq].
    rewrite <- nEq in *.
    destruct (decAddr a a0) as [aEq | aNeq].
    destruct (fromB m); firstorder.
    firstorder.
    firstorder.

    simpl in *; firstorder.
    simpl in *; firstorder.
  Qed.

  Theorem deqImpNoSend: forall {c l a d i t},
                          defined c -> deqR c l a d i t ->
                          forall {m p}, defined p -> ~ mark mch c p a t m.
  Proof.
    unfold not; intros c l a d i t defc deqr m p defp markm.
    unfold deqR in *; unfold mark in *; unfold mkDataTypes.mark in *.

    destruct (trans oneBeh t); firstorder.
  Qed.
End mkLatestValueAxioms.
