Require Import Omega Useful Rules ChannelAxiom ChannelAxiomHelp Channel Coq.Logic.Classical MsiState DataTypes Tree HierProperties Cache.

Module ch' := mkChannel.
Module ch := mkChannelPerAddr mkDataTypes ch'.
Module mkBehaviorAxioms: BehaviorAxioms mkDataTypes ch.
  Import mkDataTypes ch.

  Section CommonBeh.
    Context {st: Addr -> Time -> State}.
    Context {toRSComp: State -> State -> Prop}.
    Context {src dst: Cache}.
    Context {wt: Addr -> Time -> bool}.
    Context {wtS: Addr -> Time -> State}.
Record CommonBehavior :=
  {
    change: forall {t a}, st a (S t) <> st a t -> (exists m, mark mch src dst a t m) \/
                                                  (exists m, recv mch dst src a t m);
    sendmChange: forall {t a m}, mark mch src dst a t m -> st a (S t) = to m;
    recvmChange: forall {t a m}, recv mch dst src a t m -> st a (S t) = to m;
    sendrImpSt: forall {t a r}, mark rch src dst a t r -> toRSComp (to r) (st a t);

    sendrImpSetWait: forall {t a r}, mark rch src dst a t r -> wt a (S t) = true;
    sendrImpSetWaitState: forall {t a r}, mark rch src dst a t r -> wtS a (S t) = to r;
    sendrImpNoPrevWait: forall {t a r}, mark rch src dst a t r -> wt a t = false;
    waitReset: forall {t a}, wt a t = true -> wt a (S t) = false ->
                             exists m, recv mch dst src a t m /\
                                       ~ toRSComp (wtS a t) (to m);
    waitSSet: forall {t a}, wtS a (S t) <> wtS a t -> exists r, mark rch src dst a t r;
    sendmFrom: forall {t a m}, mark mch src dst a t m -> from m = st a t;
    sendrFrom: forall {t a r}, mark rch src dst a t r -> from r = st a t;
    noSendmRecvm: forall {t a m}, mark mch src dst a t m ->
                                  forall {m'}, recv mch dst src a t m' -> False;
    noSendmSendr: forall {t a m}, mark mch src dst a t m ->
                                  forall {r}, mark rch src dst a t r -> False
  }.

  End CommonBeh.

  Section Pair.
    Theorem noParentSame: forall {n a t}, defined n ->
                                          (forall {p}, defined p -> ~ parent n p) ->
                                          state n a (S t) = state n a t.
    Proof.
      intros n a t defn noP.
      unfold state in *.
      destruct (trans oneBeh t).
      reflexivity.
      reflexivity.
      reflexivity.
      reflexivity.
      simpl.
      destruct (decTree n c).
      rewrite <- e0 in p0.
      firstorder.
      reflexivity.
      intuition.
      simpl.
      destruct (decTree n c).
      rewrite <- e0 in p0.
      firstorder.
      reflexivity.
      intuition.
      simpl.
      destruct (decTree n c).
      rewrite <- e0 in p0.
      firstorder.
      reflexivity.
      intuition.
    Qed.

    Context {p c: Cache}.

    Section Local.
    Context {defp: defined p}.
    Context {defc: defined c}.
    Context {c_p: parent c p}.
    Theorem st_change:
      forall {t a}, state c a (S t) <> state c a t -> (exists m, mark mch c p a t m) \/
                                                      (exists m, recv mch p c a t m).
    Proof.
      intros t a stNeq.
      unfold state in *; unfold mark; unfold recv; unfold mkDataTypes.mark;
      unfold mkDataTypes.recv.
      destruct (trans oneBeh t).
      intuition.
      intuition.
      intuition.
      intuition.

      simpl in *.
      destruct (decTree c c0).
      rewrite e0 in *.
      destruct (decAddr a a0).
      rewrite e1 in *.
      pose proof (uniqParent defc defp d c_p p1) as p_p0.
      rewrite p_p0 in *.
      assert (H: mch = type m) by auto.
      unfold a0 in *.
      fold m.
      right.
      exists (Build_Mesg (fromB m) (toB m) (addrB m) (dataBM m)
                         (List.last (labelCh t mch p0 c0) 0)).
      simpl.
      intuition.
      intuition.
      intuition.

      intuition.

      simpl in *.
      left.
      destruct (decTree c c0).
      rewrite e0 in *.
      destruct (decAddr a a0).
      rewrite e1 in *.
      pose proof (uniqParent defc defp d c_p p1) as p_p0.
      rewrite p_p0 in *.
      unfold a0 in *.
      fold r.
      exists (Build_Mesg (st (sys oneBeh t) c0 (addrB r)) (toB r) (addrB r)
                         (dt (sys oneBeh t) c0 (addrB r))
                         t).
      simpl.
      intuition.
      intuition.
      intuition.

      intuition.

      simpl in *.
      destruct (decTree c c0).
      rewrite e0 in *.
      destruct (decAddr a a0).
      rewrite e1 in *.
      pose proof (uniqParent defc defp d c_p p1) as p_p0.
      rewrite p_p0 in *.
      left.
      exists (Build_Mesg (st (sys oneBeh t) c0 a0) x a0
                         (dt (sys oneBeh t) c0 a0) t).
      simpl.
      intuition.
      intuition.
      intuition.

      intuition.
    Qed.

    Theorem st_sendmChange: forall {t a m}, mark mch c p a t m -> state c a (S t) = to m.
    Proof.
      intros t a m markm.
      unfold mark in *; unfold mkDataTypes.mark in *; unfold state in *.
      destruct (trans oneBeh t).

      intuition.
      intuition.

      destruct markm as [[_ [_ [u _]]] _]; discriminate.

      destruct markm as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); firstorder.

      intuition.

      destruct markm as [[_ [_ [u _]]] _]; discriminate.

      simpl in *.
      destruct (decTree c c0).
      destruct (decAddr a a0).
      destruct markm as [[_ [_ [_ [_ [u _]]]]] _].
      unfold toR.
      unfold r.
      auto.
      destruct markm as [[_ [_ [_ [_ [_ [u1 _]]]]]] u2].
      unfold a0 in n0; unfold r in n0.
      rewrite u2 in u1.
      intuition.
      destruct markm as [[c_eq _] _].
      assert (c = c0) by auto.
      intuition.

      intuition.

      simpl.
      destruct (decTree c c0).
      destruct (decAddr a a0).
      destruct markm as [[_ [_ [_ [_ [u _]]]]] _].
      auto.
      destruct markm as [[_ [_ [_ [_ [_ [u1 _]]]]]] u2].
      rewrite u2 in u1.
      intuition.
      destruct markm as [[c_eq _] _].
      assert (c = c0) by auto.
      intuition.

      intuition.
    Qed.

    Theorem st_recvmChange: forall {t a m}, recv mch p c a t m -> state c a (S t) = to m.
    Proof.
      intros t a m recvm.
      unfold state; unfold recv in *; unfold mkDataTypes.recv in *.
      destruct (trans oneBeh t).

      intuition.
      intuition.
      intuition.

      destruct recvm as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); firstorder.

      simpl.
      destruct (decTree c c0).
      destruct (decAddr a a0).
      destruct recvm as [[_ [_ [_ [_ [u _]]]]] _].
      unfold toM; unfold m0.
      auto.
      destruct recvm as [[_ [_ [_ [_ [_ [u1 _]]]]]] u2].
      rewrite u2 in u1.
      unfold a0 in n0; unfold m0 in n0.
      intuition.
      destruct recvm as [[_ [c_eq _]] _].
      assert (c = c0) by auto.
      intuition.

      intuition.

      unfold r in e; rewrite e in recvm.
      destruct recvm as [[_ [_ [u _]]] _]; discriminate.

      destruct recvm as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); firstorder.

      intuition.

      unfold r in e; rewrite e in recvm.
      destruct recvm as [[_ [_ [u _]]] _]; discriminate.
    Qed.

    Theorem st_sendrImpSt: forall {t a r}, mark rch c p a t r -> slt (state c a t) (to r).
    Proof.
      intros t a r markr.
      unfold mark in markr; unfold mkDataTypes.mark in markr.
      destruct (trans oneBeh t).

      intuition.
      intuition.

      destruct markr as [[u1 [_ [_ [_ [u2 [u3 _]]]]]] u4].
      rewrite <- u1; rewrite u4 in u3; rewrite u3; rewrite u2 in *.
      unfold state. assumption.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.

      destruct markr as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle c_p p1); firstorder.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.
    Qed.

    Theorem st_sendrImpSetWait: forall {t a r}, mark rch c p a t r -> wait c a (S t) = true.
    Proof.
      intros t a r markr.
      unfold mark in *; unfold mkDataTypes.mark in *; unfold wait in *.
      destruct (trans oneBeh t).

      intuition.
      intuition.

      simpl.
      destruct (decTree c c0).
      destruct (decAddr a a0).
      reflexivity.
      destruct markr as [[_ [_ [_ [_ [_ [u2 _]]]]]] u1].
      rewrite u1 in u2.
      intuition.
      destruct markr as [[u1 _] _].
      assert (c = c0) by auto; intuition.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.

      destruct markr as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); intuition.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.
    Qed.

    Theorem st_sendrImpSetWaitState: forall {t a r},
                                       mark rch c p a t r -> waitS c a (S t) = to r.
    Proof.
      intros t a r markr.
      unfold mark in *; unfold mkDataTypes.mark in *; unfold waitS.
      destruct (trans oneBeh t).

      intuition.
      intuition.

      simpl.
      destruct (decTree c c0).
      destruct (decAddr a a0).
      destruct markr as [[_ [_ [_ [_ [u _]]]]] _].
      auto.
      destruct markr as [[_ [_ [_ [_ [_ [u1 _]]]]]] u2].
      rewrite u2 in u1; intuition.
      destruct markr as [[u _] _].
      assert (c = c0) by auto; intuition.

      destruct markr as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); intuition.

      intuition.

      destruct markr as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); intuition.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.
    Qed.

    Theorem st_sendrImpNoPrevWait: forall {t a r}, mark rch c p a t r -> wait c a t = false.
    Proof.
      intros t a r markr.
      unfold mark in *; unfold mkDataTypes.mark in *; unfold waitS.
      destruct (trans oneBeh t).

      intuition.
      intuition.

      simpl.
      destruct (decTree c c0).
      destruct (decAddr a a0).
      rewrite e0 in *; rewrite e1 in *.
      assumption.
      destruct markr as [[_ [_ [_ [_ [_ [u1 _]]]]]] u2].
      rewrite u2 in u1; intuition.
      destruct markr as [[u _] _].
      assert (c = c0) by auto; intuition.

      destruct markr as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); intuition.

      intuition.

      destruct markr as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); intuition.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.
    Qed.

    Theorem st_waitReset: forall {t a}, wait c a t = true -> wait c a (S t) = false ->
                                        exists m, recv mch p c a t m /\
                                                  ~ sgt (waitS c a t) (to m).
    Proof.
      intros t a waitT waitF.
      unfold wait in *.
      unfold recv in *; unfold mkDataTypes.recv in *.
      destruct (trans oneBeh t).

      simpl in *.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      destruct (decTree c c0).
      destruct (decAddr a a0).
      discriminate.
      rewrite waitF in waitT; discriminate.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      destruct (decTree c c0).
      destruct (decAddr a a0).
      fold m.
      exists (Build_Mesg (fromB m) (toB m) (addrB m) (dataBM m)
                         (List.last (labelCh t mch p0 c0) 0)).
      simpl.
      rewrite e0 in *.
      pose proof (uniqParent defc defp d c_p p1) as peq.
      rewrite peq in *.
      assert (mch = type m) by auto.
      rewrite e1 in *.
      unfold a0 in *.
      unfold toM in *.
      unfold waitS.
      intuition.
      unfold sgt in *.
      destruct (toB m); destruct (wtS (sys oneBeh t) c0 (addrB m)); simpl in *; auto.
      rewrite waitF in waitT; discriminate.
      rewrite waitF in waitT; discriminate.
      rewrite waitF in waitT; discriminate.
      rewrite waitF in waitT; discriminate.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      rewrite waitF in waitT; discriminate.
    Qed.

    Theorem st_waitSSet: forall {t a}, waitS c a (S t) <> waitS c a t ->
                                       exists r, mark rch c p a t r.
    Proof.
      intros t a waitNeq.
      unfold waitS in *; unfold mark; unfold mkDataTypes.mark.
      destruct (trans oneBeh t).
      simpl in *; intuition.
      simpl in *; intuition.

      simpl in *.
      destruct (decTree c c0).
      destruct (decAddr a a0).
      exists (Build_Mesg (st (sys oneBeh t) c0 a0) x a0 Initial t).
      simpl.
      rewrite e0 in *.
      pose proof (uniqParent defc defp d c_p p1) as peq.
      rewrite peq in *.
      rewrite e1.
      intuition.
      intuition.
      intuition.

      simpl in *.
      intuition.

      simpl in *.
      intuition.

      simpl in *.
      intuition.

      simpl in *.
      intuition.

      simpl in *.
      intuition.

      simpl in *.
      intuition.

      simpl in *.
      intuition.
    Qed.
      
    Theorem st_sendmFrom: forall {t a m}, mark mch c p a t m -> from m = state c a t.
    Proof.
      intros t a m markm.
      unfold mark in *; unfold mkDataTypes.mark in *.
      destruct (trans oneBeh t).
      intuition.
      intuition.

      destruct markm as [[_ [_ [u _]]] _].
      discriminate.

      destruct markm as [[u1 [u2 _]] _].
      rewrite <- u1 in *; rewrite <- u2 in *.
      pose proof (noCycle c_p p1); intuition.

      intuition.
      
      destruct markm as [[u1 [u2 _]] _].
      rewrite <- u1 in *; rewrite <- u2 in *.
      pose proof (noCycle c_p p1); intuition.

      destruct markm as [[u1 [_ [_ [u2 [_ [u3 _]]]]]] u4].
      unfold r in a0.
      rewrite u4 in u3.
      rewrite u3.
      rewrite <- u1.
      assumption.

      intuition.

      destruct markm as [[u1 [_ [_ [u2 [_ [u3 _]]]]]] u4].
      rewrite u4 in u3.
      rewrite u3; rewrite <- u1.
      assumption.

      intuition.
    Qed.

    Theorem st_sendrFrom: forall {t a r}, mark rch c p a t r -> from r = state c a t.
    Proof.
      intros t a r markr.
      unfold mark in *; unfold mkDataTypes.mark in *.
      destruct (trans oneBeh t).

      intuition.
      intuition.

      destruct markr as [[u1 [_ [_ [u2 [_ [u3 _]]]]]] u4].
      rewrite u4 in u3.
      rewrite u3.
      rewrite <- u1.
      assumption.

      destruct markr as [[_ [_ [u _]]] _].
      discriminate.

      intuition.

      destruct markr as [[u1 [u2 _]] _].
      rewrite <- u1 in *; rewrite <- u2 in *.
      pose proof (noCycle c_p p1); intuition.

      destruct markr as [[_ [_  [u _]]] _].
      discriminate.

      intuition.

      destruct markr as [[_ [_  [u _]]] _].
      discriminate.

      intuition.
    Qed.

    Theorem st_noSendmRecvm: forall {t a m}, mark mch c p a t m ->
                                             forall {m'}, recv mch p c a t m' -> False.
    Proof.
      intros t a m markm m' recvm'.
      unfold mark in *; unfold recv in *; unfold mkDataTypes.mark in *;
      unfold mkDataTypes.recv in *.
      destruct (trans oneBeh t).

      intuition.
      intuition.
      intuition.

      destruct markm as [[u1 [u2 _]] _].
      rewrite <- u1 in *. rewrite <- u2 in *.

      pose proof (noCycle c_p p1); firstorder.

      intuition.
      intuition.

      unfold r in e.
      rewrite e in recvm'.
      destruct recvm' as [[_ [_ [u _]]] _].
      discriminate.

      intuition.
      intuition.
      intuition.
    Qed.

    Theorem st_noSendmSendr: forall {t a m}, mark mch c p a t m ->
                                             forall {r}, mark rch c p a t r -> False.
    Proof.
      intros t a m markm r markr.
      unfold mark in *; unfold mkDataTypes.mark in *.
      destruct (trans oneBeh t).

      intuition.
      intuition.

      destruct markm as [[_ [_ [u _]]] _]; discriminate.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.

      destruct markm as [[_ [_ [u _]]] _]; discriminate.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.
    Qed.
    End Local.

    Theorem st: defined p -> defined c -> parent c p ->
                @CommonBehavior (state c) sgt c p (wait c) (waitS c).
    Proof.
      intros defp defc c_p.

      apply (Build_CommonBehavior
               (@st_change defp defc c_p)
               (@st_sendmChange c_p)
               (@st_recvmChange c_p)
               (@st_sendrImpSt c_p)
               (@st_sendrImpSetWait c_p)
               (@st_sendrImpSetWaitState c_p)
               (@st_sendrImpNoPrevWait defc c_p)
               (@st_waitReset defp defc c_p)
               (@st_waitSSet defp defc c_p)
               (@st_sendmFrom defp defc c_p)
               (@st_sendrFrom defp defc c_p)
               (@st_noSendmRecvm defp defc c_p)
               (@st_noSendmSendr)).
    Qed.

    Theorem sendmImpSt: defined p -> defined c -> parent c p ->
                      forall {a t m}, mark mch c p a t m -> slt (to m) (state c a t).
    Proof.
      intros defp defc c_p a t m markm.
      unfold mark in *; unfold state in *.
      unfold mkDataTypes.mark in *.
      destruct (trans oneBeh t).
      intuition.
      intuition.
      destruct markm as [[_ [_ [ttt _]]] _]; discriminate.
      destruct markm as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); firstorder.
      intuition.
      destruct markm as [[_ [_ [ttt _]]] _]; discriminate.

      destruct markm as [[u1 [u2 [_ [_ [u3 [u4 _]]]]]] u5].
      unfold toR in *.
      unfold a0 in *.
      unfold r in *.
      rewrite u3.
      rewrite u1 in *; rewrite u2 in *.
      rewrite u5 in *; rewrite u4 in *.
      assumption.

      intuition.

      destruct markm as [[u1 [u2 [_ [_ [u3 [u4 _]]]]]] u5].
      rewrite u3.
      rewrite u1 in *; rewrite u2 in *.
      rewrite u5 in *; rewrite u4 in *.
      assumption.

      intuition.
    Qed.

    Theorem volAxiom: defined p -> defined c -> parent c p ->
                      forall {t' a m}, mark mch c p a t' m ->
                                       wait c a t' = true ->
                                       exists r1, recv rch p c a t' r1 /\
                                                  slt (to r1) (state c a t').
    Proof.
      intros defp defc c_p t' a  m markm waitt.
      unfold mark in *; unfold mkDataTypes.mark in *; unfold wait in *; unfold recv in *;
      unfold mkDataTypes.recv in *.
      destruct (trans oneBeh t').

      intuition.
      intuition.
      destruct markm as [[_ [_ [ttt _]]] _]; discriminate.

      destruct markm as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); firstorder.

      intuition.

      destruct markm as [[_ [_ [ttt _]]] _]; discriminate.

      exists (Build_Mesg (fromB r) (toB r) (addrB r) (dataBM r) (List.last (labelCh t' mch p0 c0) 0)).
      simpl in *.
      unfold r in *.
      unfold fromR in *.
      unfold toR in *.
      unfold a0 in *.
      unfold d1 in *.
      destruct markm as [[u1 [u2 [u3 [u4 [u5 [u6 u7]]]]]] u0].
      rewrite <- u1 in *; rewrite <- u2 in *.
      rewrite u0 in u6; rewrite u6 in *.
      unfold state.
      firstorder.

      intuition.
      destruct markm as [[u1 [u2 [u3 [u4 [u5 [u6 u7]]]]]] u0].
      rewrite <- u1 in *; rewrite <- u2 in *.
      rewrite u0 in u6; rewrite u6 in *.
      rewrite e in waitt.
      discriminate.

      intuition.
    Qed.
      
    Section Local2.
    Context {defp: defined p}.
    Context {defc: defined c}.
    Context {c_p: parent c p}.
    Theorem dt_change:
      forall {t a}, dir p c a (S t) <> dir p c a t -> (exists m, mark mch p c a t m) \/
                                                      (exists m, recv mch c p a t m).
    Proof.
      intros t a stNeq.
      unfold dir in *; unfold mark; unfold recv; unfold mkDataTypes.mark;
      unfold mkDataTypes.recv.
      destruct (trans oneBeh t).
      intuition.
      intuition.
      intuition.

      simpl in *.
      left.
      destruct (decTree p p0).
      destruct (decTree c c0).
      destruct (decAddr a a0).
      fold r; fold a0.
      exists (Build_Mesg (dirSt (sys oneBeh t) p0 c0 a0) (toB r) a0 (dt (sys oneBeh t) p0 a0)
             t).
      simpl.
      rewrite e0; rewrite e1; rewrite e2.
      intuition.
      intuition.
      intuition.
      intuition.

      intuition.

      intuition.

      intuition.

      simpl in *.
      right.
      destruct (decTree p p0).
      destruct (decTree c c0).
      destruct (decAddr a a0).
      pose proof (enqC2P p1 n) as H.
      fold m; fold m in H; fold a0.
      exists (Build_Mesg (fromB m) (toB m) a0 (dataBM m) (List.last (labelCh t mch c0 p0) 0)).
      simpl.
      rewrite H; rewrite e2; rewrite e0; rewrite e1.
      intuition.
      intuition.
      intuition.
      intuition.

      intuition.

      intuition.
    Qed.

    Theorem dt_sendmChange: forall {t a m}, mark mch p c a t m -> dir p c a (S t) = to m.
    Proof.
      intros t a m markm.
      unfold mark in *; unfold mkDataTypes.mark in *; unfold dir in *.
      destruct (trans oneBeh t).

      intuition.
      intuition.

      destruct markm as [[_ [_ [u _]]] _]; discriminate.

      simpl in *.
      destruct (decTree p p0).
      destruct (decTree c c0).
      destruct (decAddr a a0).
      fold r in markm; fold toR in markm.
      destruct markm as [[_ [_ [_ [_ [u _]]]]] _].
      auto.
      destruct markm as [[_ [_ [_ [_ [_ [u1 _]]]]]] u2].
      fold r in u1; fold a0 in u1.
      rewrite u2 in u1; intuition.
      destruct markm as [[_ [u _]] _].
      assert (c = c0) by auto.
      intuition.
      destruct markm as [[u _] _].
      assert (p = p0) by auto.
      intuition.

      intuition.

      destruct markm as [[_ [_ [u _]]] _].
      discriminate.

      destruct markm as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle c_p p1); intuition.

      intuition.


      destruct markm as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle c_p p1); intuition.

      intuition.
    Qed.

    Theorem dt_recvmChange: forall {t a m}, recv mch c p a t m -> dir p c a (S t) = to m.
    Proof.
      intros t a m recvm.
      unfold dir; unfold recv in *; unfold mkDataTypes.recv in *.
      destruct (trans oneBeh t).

      intuition.
      intuition.
      intuition.

      simpl.
      destruct (decTree p p0).
      destruct (decTree c c0).
      destruct (decAddr a a0).
      destruct recvm as [[_ [_ [_ [_ [u _]]]]] _].
      unfold toR; unfold r.
      auto.
      destruct recvm as [[_ [_ [_ [_ [_ [u1 _]]]]]] u2].
      rewrite u2 in u1.
      unfold a0 in n0; unfold r in n0.
      intuition.
      destruct recvm as [[c_eq _] _].
      assert (c = c0) by auto.
      intuition.
      destruct recvm as [[_ [u _]] _].
      assert (p = p0) by auto.
      intuition.

      destruct recvm as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); firstorder.

      intuition.

      destruct recvm as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); firstorder.

      simpl.
      destruct (decTree p p0).
      destruct (decTree c c0).
      destruct (decAddr a a0).
      destruct recvm as [[_ [_ [_ [_ [u _]]]]] _].
      unfold toM; unfold m0.
      auto.
      destruct recvm as [[_ [_ [_ [_ [_ [u1 _]]]]]] u2].
      rewrite u2 in u1.
      unfold a0 in n0; unfold m0 in n0.
      intuition.
      destruct recvm as [[c_eq _] _].
      assert (c = c0) by auto.
      intuition.
      destruct recvm as [[_ [u _]] _].
      assert (p = p0) by auto.
      intuition.

      intuition.

      destruct recvm as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); firstorder.

    Qed.

    Theorem dt_sendrImpSt: forall {t a r}, mark rch p c a t r -> slt (to r) (dir p c a t).
    Proof.
      intros t a r markr.
      unfold mark in markr; unfold mkDataTypes.mark in markr.
      destruct (trans oneBeh t).

      intuition.
      intuition.

      destruct markr as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle c_p p1); firstorder.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.

      destruct markr as [[u1 [u5 [_ [_ [u2 [u3 _]]]]]] u4].
      rewrite <- u1; rewrite u4 in u3; rewrite u3; rewrite u2 in *; rewrite <- u5 in *.
      unfold dir; assumption.

      destruct markr as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle c_p p1); firstorder.

      intuition.

      intuition.

      discriminate.

      intuition.
    Qed.

    Theorem dt_sendrImpSetWait: forall {t a r}, mark rch p c a t r -> dwait p c a (S t) = true.
    Proof.
      intros t a r markr.
      unfold mark in *; unfold mkDataTypes.mark in *; unfold dwait in *.
      destruct (trans oneBeh t).

      intuition.
      intuition.

      destruct markr as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); intuition.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.

      simpl.
      destruct (decTree p p0).
      destruct (decTree c c0).
      destruct (decAddr a a0).
      reflexivity.
      destruct markr as [[_ [_ [_ [_ [_ [u2 _]]]]]] u1].
      rewrite u1 in u2.
      intuition.
      destruct markr as [[_ [u1 _]] _].
      assert (c = c0) by auto; intuition.
      destruct markr as [[u1 _] _].
      assert (p = p0) by auto; intuition.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.
    Qed.

    Theorem dt_sendrImpSetWaitState: forall {t a r},
                                       mark rch p c a t r -> dwaitS p c a (S t) = to r.
    Proof.
      intros t a r markr.
      unfold mark in *; unfold mkDataTypes.mark in *; unfold dwaitS.
      destruct (trans oneBeh t).

      intuition.
      intuition.

      destruct markr as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); intuition.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.

      simpl.
      destruct (decTree p p0).
      destruct (decTree c c0).
      destruct (decAddr a a0).
      destruct markr as [[_ [_ [_ [_ [u _]]]]] _].
      auto.
      destruct markr as [[_ [_ [_ [_ [_ [u1 _]]]]]] u2].
      rewrite u2 in u1; intuition.
      destruct markr as [[_ [u _]] _].
      assert (c = c0) by auto; intuition.
      destruct markr as [[u _] _].
      assert (p = p0) by auto; firstorder.

      destruct markr as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); intuition.

      intuition.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.
    Qed.

    Theorem dt_sendrImpNoPrevWait: forall {t a r}, mark rch p c a t r -> dwait p c a t = false.
    Proof.
      intros t a r markr.
      unfold mark in *; unfold mkDataTypes.mark in *; unfold dwaitS.
      destruct (trans oneBeh t).

      intuition.
      intuition.

      destruct markr as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); intuition.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.

      simpl.
      destruct (decTree p p0).
      destruct (decTree c c0).
      destruct (decAddr a a0).
      rewrite e0 in *; rewrite e1 in *; rewrite e2 in *.
      assumption.
      destruct markr as [[_ [_ [_ [_ [_ [u1 _]]]]]] u2].
      rewrite u2 in u1; intuition.
      destruct markr as [[_ [u _]] _].
      assert (c = c0) by auto; intuition.
      destruct markr as [[u _] _].
      assert (p = p0) by auto; intuition.

      destruct markr as [[u1 [u2 _]] _].
      rewrite u1 in *; rewrite u2 in *.
      pose proof (noCycle p1 c_p); intuition.

      intuition.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.
    Qed.

    Theorem dt_waitReset: forall {t a}, dwait p c a t = true -> dwait p c a (S t) = false ->
                                        exists m, recv mch c p a t m /\
                                                  ~ slt (dwaitS p c a t) (to m).
    Proof.
      intros t a waitT waitF.
      unfold dwait in *.
      unfold recv in *; unfold mkDataTypes.recv in *.
      destruct (trans oneBeh t).

      simpl in *.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      destruct (decTree p p0).
      destruct (decTree c c0).
      destruct (decAddr a a0).
      discriminate.
      rewrite waitF in waitT; discriminate.
      rewrite waitF in waitT; discriminate.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      destruct (decTree p p0).
      destruct (decTree c c0).
      destruct (decAddr a a0).
      fold m.
      exists (Build_Mesg (fromB m) (toB m) (addrB m) (dataBM m)
                         (List.last (labelCh t mch c0 p0) 0)).
      simpl.
      rewrite e0 in *.
      rewrite e1 in *.
      pose proof (enqC2P c_p n) as whichmch.
      rewrite <- whichmch in *.
      unfold a0 in *.
      unfold toM in *.
      unfold dwaitS.
      intuition.
      unfold sgt in *.
      rewrite e2 in *.
      destruct (toB m); destruct (dirWtS (sys oneBeh t) p0 c0 (addrB m)); simpl in *; auto.
      rewrite waitF in waitT; discriminate.
      rewrite waitF in waitT; discriminate.
      rewrite waitF in waitT; discriminate.
      rewrite waitF in waitT; discriminate.
      rewrite waitF in waitT; discriminate.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      rewrite waitF in waitT; discriminate.

      simpl in *.
      rewrite waitF in waitT; discriminate.
    Qed.

    Theorem dt_waitSSet: forall {t a}, dwaitS p c a (S t) <> dwaitS p c a t ->
                                       exists r, mark rch p c a t r.
    Proof.
      intros t a waitNeq.
      unfold dwaitS in *; unfold mark; unfold mkDataTypes.mark.
      destruct (trans oneBeh t).
      simpl in *; intuition.
      simpl in *; intuition.

      simpl in *.
      intuition.

      simpl in *.
      intuition.

      simpl in *.
      intuition.

      simpl in *.
      destruct (decTree p p0).
      destruct (decTree c c0).
      destruct (decAddr a a0).
      exists (Build_Mesg (dirSt (sys oneBeh t) p0 c0 a0) x a0 Initial t).
      simpl.
      rewrite e0 in *.
      rewrite e1 in *.
      rewrite e2.
      intuition.
      intuition.
      intuition.
      intuition.

      simpl in *.
      intuition.

      simpl in *.
      intuition.

      simpl in *.
      intuition.

      simpl in *.
      intuition.
    Qed.

    Theorem dt_sendmFrom: forall {t a m}, mark mch p c a t m -> from m = dir p c a t.
    Proof.
      intros t a m markm.
      unfold mark in *; unfold mkDataTypes.mark in *.
      destruct (trans oneBeh t).
      intuition.
      intuition.

      destruct markm as [[u1 [u2 _]] _].
      rewrite <- u1 in *; rewrite <- u2 in *.
      pose proof (noCycle c_p p1); intuition.

      destruct markm as [[u1 [u5 [_ [u2 [_ [u3 _]]]]]] u4].
      unfold r in a0.
      rewrite u4 in u3.
      rewrite u3.
      rewrite <- u1.
      rewrite <- u5.
      assumption.
      intuition.

      destruct markm as [[_ [_ [u _]]] _].
      discriminate.

      destruct markm as [[u1 [u2 _]] _].
      rewrite <- u1 in *; rewrite <- u2 in *.
      pose proof (noCycle c_p p1); intuition.

      intuition.

      destruct markm as [[u1 [u2 _]] _].
      rewrite <- u1 in *; rewrite <- u2 in *.
      pose proof (noCycle c_p p1); intuition.

      intuition.
    Qed.

    Theorem dt_sendrFrom: forall {t a r}, mark rch p c a t r -> from r = dir p c a t.
    Proof.
      intros t a r markr.
      unfold mark in *; unfold mkDataTypes.mark in *.
      destruct (trans oneBeh t).

      intuition.
      intuition.

      destruct markr as [[u1 [u2 _]] _].
      rewrite <- u1 in *; rewrite <- u2 in *.
      pose proof (noCycle c_p p1); intuition.

      destruct markr as [[_ [_  [u _]]] _].
      discriminate.

      intuition.

      destruct markr as [[u1 [u5 [_ [u2 [_ [u3 _]]]]]] u4].
      rewrite u4 in u3.
      rewrite u3.
      rewrite <- u1; rewrite <- u5.
      assumption.

      destruct markr as [[_ [_ [u _]]] _].
      discriminate.

      intuition.

      destruct markr as [[_ [_  [u _]]] _].
      discriminate.

      intuition.
    Qed.

    Theorem dt_noSendmRecvm: forall {t a m}, mark mch p c a t m ->
                                             forall {m'}, recv mch c p a t m' -> False.
    Proof.
      intros t a m markm m' recvm'.
      unfold mark in *; unfold recv in *; unfold mkDataTypes.mark in *;
      unfold mkDataTypes.recv in *.
      destruct (trans oneBeh t).

      intuition.
      intuition.

      intuition.

      pose proof (enqC2P p1 n) as H.
      rewrite H in recvm'.
      destruct recvm' as [[_ [_ [u _]]] _].
      discriminate.

      intuition.

      intuition.

      destruct markm as [[u1 [u2 _]] _].
      rewrite <- u1 in *. rewrite <- u2 in *.
      pose proof (noCycle c_p p1); firstorder.

      intuition.

      intuition.

      intuition.
    Qed.

    Theorem dt_noSendmSendr: forall {t a m}, mark mch p c a t m ->
                                             forall {r}, mark rch p c a t r -> False.
    Proof.
      intros t a m markm r markr.
      unfold mark in *; unfold mkDataTypes.mark in *.
      destruct (trans oneBeh t).

      intuition.
      intuition.

      destruct markm as [[_ [_ [u _]]] _]; discriminate.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.

      destruct markm as [[_ [_ [u _]]] _]; discriminate.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.

      destruct markr as [[_ [_ [u _]]] _]; discriminate.

      intuition.
    Qed.
    End Local2.


    Theorem dt: defined p -> defined c -> parent c p -> @CommonBehavior (dir p c) slt p c
    (dwait p c) (dwaitS p c).
    Proof.
      intros defp defc c_p.

      pose proof @dt_change.

      apply (Build_CommonBehavior
               (@dt_change)
               (@dt_sendmChange c_p)
               (@dt_recvmChange c_p)
               (@dt_sendrImpSt defc c_p)
               (@dt_sendrImpSetWait c_p)
               (@dt_sendrImpSetWaitState c_p)
               (@dt_sendrImpNoPrevWait defp defc c_p)
               (@dt_waitReset defp defc c_p)
               (@dt_waitSSet defp defc c_p)
               (@dt_sendmFrom defp defc c_p)
               (@dt_sendrFrom defp defc c_p)
               (@dt_noSendmRecvm defp defc c_p)
               (@dt_noSendmSendr)).
    Qed.

    Section ForT.
      Context {a: Addr} {t: Time}.

      Theorem sendmImpRecvr: defined p -> defined c -> parent c p -> 
                             forall {m}, mark mch p c a t m -> exists r, recv rch c p a t r.
      Proof.
        intros defp defc c_p m markm.
        unfold mark in *; unfold mkDataTypes.mark in *; unfold wait in *; unfold recv in *;
        unfold mkDataTypes.recv in *.
        destruct (trans oneBeh t).

        intuition.
        intuition.
        destruct markm as [[_ [_ [ttt _]]] _]; discriminate.


        exists (Build_Mesg (fromB r) (toB r) (addrB r) (dataBM r) (List.last (labelCh t rch c0 p0) 0)).
        simpl in *.
        unfold r in *.
        unfold fromR in *.
        unfold toR in *.
        unfold a0 in *.
        destruct markm as [[u1 [u2 [u3 [u4 [u5 [u6 u7]]]]]] u0].
        rewrite <- u1 in *; rewrite <- u2 in *.
        rewrite u0 in u6; rewrite u6 in *.
        pose proof (enqC2P c_p n) as useful.
        rewrite useful.
        intuition.

        intuition.


        destruct markm as [[_ [_ [ttt _]]] _]; discriminate.

        destruct markm as [[u1 [u2 _]] _].
        rewrite u1 in *; rewrite u2 in *.
        pose proof (noCycle p1 c_p); firstorder.


        intuition.

        destruct markm as [[u1 [u2 _]] _].
        rewrite u1 in *; rewrite u2 in *.
        pose proof (noCycle p1 c_p); firstorder.

        intuition.
      Qed.

      Theorem sendmImpRecvrGe: defined p -> defined c -> parent c p ->
                               forall {m}, mark mch p c a t m ->
                                           forall {r}, recv rch c p a t r ->
                                                       sle (to r) (to m).
      Proof.
        intros defp defc c_p m markm r recvr.
        unfold mark in markm. unfold mkDataTypes.mark in markm. unfold recv in recvr.
        unfold mkDataTypes.recv in recvr.
        destruct (trans oneBeh t).

        intuition.
        intuition.
        intuition.

        destruct markm as [[_ [_ [_ [_ [tom _]]]]] _].
        destruct recvr as [[_ [_ [_ [_ [tor _]]]]] _].
        rewrite <- tom in tor.
        destruct (to r); destruct (to m); unfold sle in *; auto; discriminate.

        intuition.
        intuition.

        destruct markm as [[u1 [u2 _]] _].
        rewrite u1 in *; rewrite u2 in *.
        pose proof (noCycle p1 c_p); firstorder.

        intuition.
        intuition.
        intuition.
      Qed.

      Theorem recvrCond: defined p -> defined c -> parent c p ->
                         forall {r}, recv rch c p a t r -> sle (dir p c a t) (from r).
      Proof.
        intros defp defc c_p r recvr.
        unfold recv in recvr. unfold mkDataTypes.recv in recvr.
        destruct (trans oneBeh t).

        intuition.
        intuition.
        intuition.

        destruct recvr as [[u2 [u3 [_ [u4 [_ [u6 _]]]]]] u1].
        unfold fromR in s1.
        unfold a0 in s1.
        unfold r0 in s1.
        rewrite <- u4 in s1.
        rewrite <- u6 in s1.
        rewrite u2 in s1.
        rewrite u3 in s1.
        rewrite u1 in s1.
        unfold dir.
        assumption.

        
        destruct recvr as [[u1 [u2 _]] _].
        rewrite u1 in *; rewrite u2 in *.
        pose proof (noCycle p1 c_p); firstorder.

        intuition.

        destruct recvr as [[u1 [u2 _]] _].
        rewrite u1 in *; rewrite u2 in *.
        pose proof (noCycle p1 c_p); firstorder.

        pose proof (enqC2P p1 n) as H.
        rewrite H in recvr.

        destruct recvr as [[_ [_ [stt _]]] _].
        discriminate.

        intuition.

        destruct recvr as [[u1 [u2 _]] _].
        rewrite u1 in *; rewrite u2 in *.
        pose proof (noCycle p1 c_p); firstorder.
      Qed.

      Theorem recvmCond: defined p -> defined c -> parent c p ->
                         forall {m}, recv mch c p a t m -> from m = dir p c a t.
      Proof.
        intros defp defc c_p m recvm.
        unfold recv in *; unfold mkDataTypes.recv in *.
        destruct (trans oneBeh t).

        intuition.
        intuition.
        intuition.

        pose proof (enqC2P p1 n) as disc.
        rewrite disc in recvm.
        destruct recvm as [[_ [_ [stt _]]] _].
        discriminate.

        destruct recvm as [[u1 [u2 _]] _].
        rewrite u1 in *; rewrite u2 in *.
        pose proof (noCycle p1 c_p); firstorder.

        intuition.

        destruct recvm as [[u1 [u2 _]] _].
        rewrite u1 in *; rewrite u2 in *.
        pose proof (noCycle p1 c_p); firstorder.

        destruct recvm as [[u2 [u3 [_ [u4 [_ [u6 _]]]]]] u1].
        rewrite u6 in u1.
        rewrite <- u1.
        rewrite <- u2; rewrite <- u3.
        unfold dir.
        unfold a0 in e.
        unfold fromM in e.
        unfold m0 in e.
        rewrite <- u4 in e.
        assumption.

        intuition.

        destruct recvm as [[u1 [u2 _]] _].
        rewrite u1 in *; rewrite u2 in *.
        pose proof (noCycle p1 c_p); firstorder.
      Qed.

      Theorem sendmNoWait: defined p -> defined c -> parent c p ->
                           forall {t2 m2}, mark mch p c a t2 m2 -> dwait p c a t2 = false.
      Proof.
        intros defp defc c_p t2 m2 markm.
        unfold mark in *.
        unfold mkDataTypes.mark in *.
        destruct (trans oneBeh t2).

        intuition.
        intuition.

        destruct markm as [[u1 [u2 _]] _].
        rewrite u1 in *; rewrite u2 in *.
        pose proof (noCycle p1 c_p); firstorder.

        destruct markm as [[u2 [u3 [_ [u4 [_ [u6 _]]]]]] u1].
        rewrite u6 in u1.
        rewrite <- u1.
        rewrite <- u2; rewrite <- u3.
        unfold dir.
        unfold a0 in e.
        assumption.

        intuition.

        destruct markm as [[_ [_ [stt _]]] _].
        discriminate.

        destruct markm as [[u1 [u2 _]] _].
        rewrite u1 in *; rewrite u2 in *.
        pose proof (noCycle p1 c_p); firstorder.


        intuition.


        destruct markm as [[u1 [u2 _]] _].
        rewrite u1 in *; rewrite u2 in *.
        pose proof (noCycle p1 c_p); firstorder.


        intuition.
      Qed.
    End ForT.

    Theorem init: defined p -> defined c -> parent c p -> forall {a}, dir p c a 0 = state c a 0.
    Proof.
      intros defp defc c_p a.
      pose proof (init oneBeh) as initi.
      unfold initGlobalState in *.
      unfold dir; unfold state.
      rewrite initi.
      simpl.
      destruct (decTree c hier).
      rewrite e in *.
      unfold defined in *.
      clear initi e a defc defc c.
      pose proof (parentHt c_p).
      pose proof (descHt defp).
      omega.
      reflexivity.
    Qed.

    Definition twoEqPRespFalse (pDef: defined p) (cDef: defined c) (isParent: parent c p) :=
      forall a t t1 m1, t1 <= t -> mark mch p c a t1 m1 ->
                        forall t2 m2, t2 <= t -> mark mch p c a t2 m2 ->
                                      (forall t3, t3 <= t -> ~ recv mch p c a t3 m1) ->
                                      (forall {t4}, t4 <= t -> ~ recv mch p c a t4 m2) ->
                                      t1 = t2.

    Definition twoPReqEqNeedsPResp (pDef: defined p) (cDef: defined c) (isParent: parent c p):=
      forall a t t1 r1,
        t1 <= t -> mark rch p c a t1 r1 ->
        forall t2 r2,
          t2 <= t -> mark rch p c a t2 r2 ->
          (forall t3, t3 <= t -> ~ recv rch p c a t3 r1) ->
          (forall t4, t4 <= t -> ~ recv rch p c a t4 r2) -> t1 < t2 ->
          sle (to r1) (to r2) -> exists tm, t1 < tm < t2 /\ exists m, mark mch p c a tm m.

    Section ForA.
      Context {a: Addr}.
      Theorem pRespReq: forall (pDef: defined p) (cDef: defined c) (isParent: parent c p),
                      twoEqPRespFalse pDef cDef isParent ->
                      twoPReqEqNeedsPResp pDef cDef isParent ->
                      forall {t1 t2 t3},
                      forall {m},
                        mark mch p c a t1 m ->
                        forall {r}, mark rch p c a t2 r -> recv rch p c a t3 r -> t1 <= t2 ->
                                    exists t4, t4 < t3 /\ recv mch p c a t4 m.
      Proof.
        intros defp defc c_p _ _ t1 t2 t3 m markm r markr recvr t1_le_t2.
        admit.
      Qed.

      Theorem pReqResp: forall (pDef: defined p) (cDef: defined c) (isParent: parent c p),
                          twoEqPRespFalse pDef cDef isParent ->
                          twoPReqEqNeedsPResp pDef cDef isParent ->
                          forall {t1 t2 t3},
                          forall {r},
                            mark rch p c a t1 r ->
                            forall {m}, mark mch p c a t2 m ->
                                        recv mch p c a t3 m -> t1 <= t2 ->
                                        exists t4, t4 < t3 /\ recv rch p c a t4 r.
      Proof.
        intros defp defc c_p _ _ t1 t2 t3 r markr m markm recvm t1_le_t2.
        admit.
      Qed.
    End ForA.

  End Pair.
End mkBehaviorAxioms.