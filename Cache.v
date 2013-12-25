Require Import Arith Omega.

Require Import Useful.
Require Import DataTypes.
Require Import Channel.

Module Type BehaviorAxioms (dt: DataTypes) (ch: ChannelPerAddr dt).
  Import dt ch.

  Section CommonBeh.
    Context {st: Addr -> Time -> State}.
    Context {toRSComp: State -> State -> Prop}.
    Context {src dst: Cache}.
    Record CommonBehavior :=
      {
        change: forall {t a}, st a (S t) <> st a t -> (exists m, mark mch src dst a t m) \/
                                                      (exists m, recv mch dst src a t m);
        sendmChange: forall {t a m}, mark mch src dst a t m -> st a (S t) = to m;
        recvmChange: forall {t a m}, recv mch dst src a t m -> st a (S t) = to m;
        sendrImpSt: forall {t a r}, mark rch src dst a t r -> toRSComp (to r) (st a t);
        sendrImpNoSendr: forall {a t1 t2 r1 r2},
                           t1 < t2 -> mark rch src dst a t1 r1 ->
                           mark rch src dst a t2 r2 ->
                           exists t', t1 < t' <= t2 /\ ~ toRSComp (to r1) (st a t');
        sendmFrom: forall {t a m}, mark mch src dst a t m -> from m = st a t;
        sendrFrom: forall {t a r}, mark rch src dst a t r -> from r = st a t;
        noSendmRecvm: forall {t a m}, mark mch src dst a t m ->
                                      forall {m'}, recv mch dst src a t m' -> False;
        noSendmSendr: forall {t a m}, mark mch src dst a t m ->
                                      forall {r}, mark rch src dst a t r -> False
      }.
    Variable cb: CommonBehavior.
    Lemma nochange': forall {a t t'},
                       (forall tn, t <= tn < t + t' ->
                                   (forall m, ~ mark mch src dst a tn m) /\
                                   (forall m, ~ recv mch dst src a tn m)) ->
                       st a t = st a (t + t').
    Proof.
      intros a t t'.
      induction t'.
      intro false.
      firstorder.
      intros noChange.
      assert (help: forall tn, t <= tn < t + t' -> (forall m, ~ mark mch src dst a tn m) /\
        (forall m, ~ recv mch dst src a tn m)) by (
          intros tn comp;
            assert (comp2: t <= tn < t + S t') by omega;
              firstorder).
      assert (stTEqstT': st a t = st a (t + t')) by firstorder.
      assert (nothing: (forall m, ~ mark mch src dst a (t + t') m) /\
        forall m, ~ recv mch dst src a (t + t') m) by
      (assert (t <= t + t' < t + S t'); firstorder).
      rewrite stTEqstT'.
      assert (two: st a (t + S t') = st a (t + t') \/ st a (t + S t') <> st a (t + t')) by decide equality.
      destruct two as [easy | hard].
      intuition.
      assert (sth: t + S t' = S (t + t')) by omega.
      rewrite sth in *.
      pose proof (change cb hard) as contra.
      firstorder.
    Qed.

    Lemma noChange: forall {a t t'}, t < t' -> (forall tn, t <= tn < t' ->
      (forall m, ~ mark mch src dst a tn m) /\ (forall m, ~ recv mch dst src a tn m)) -> st a t = st a t'.
    Proof.
      intros a t t' tLtT'.
      remember (t' - t) as td.
      assert (rew: t' = t + td) by omega.
      rewrite rew in *.
      apply (@nochange' a t).
    Qed.

    Lemma noChange2: forall {a t t'}, t <= t' -> (forall tn, t <= tn < t' ->
      (forall m, ~ mark mch src dst a tn m) /\ (forall m, ~ recv mch dst src a tn m)) -> st a t = st a t'.
    Proof.
      intros a t t' tLeT'.
      assert (opts: t = t' \/ t < t') by omega.
      destruct opts as [tEqT' | tLtT'].
      rewrite tEqT'.
      reflexivity.
      apply noChange; intuition.
    Qed.
  End CommonBeh.

  Section Pair.
    Context {p c: Cache}.
    Variable isParent: parent c p.
    Axiom st: parent c p -> @CommonBehavior (state c) sgt c p.
    Axiom sendmImpSt: parent c p ->
                      forall {a t m}, mark mch c p a t m -> slt (to m) (state c a t).
    Axiom voluntary: parent c p ->
      forall {a t r}, mark rch c p a t r -> forall {t' m}, t' > t -> mark mch c p a t' m ->
        (forall {tm}, t < tm <= t' -> slt (state c a tm) (to r)) ->
        exists r1, recv rch p c a t' r1 /\ slt (to r1) (state c a t').

(*    Axiom recvrSendm: forall {r}, recv rch p c a t r -> state c a t > to r -> exists {m}, mark mch c p a t m.*)

    Axiom dt: parent c p -> @CommonBehavior (dir p c) slt p c.
    Section ForT.
      Context {a: Addr} {t: Time}.

      Axiom sendmImpRecvr: parent c p -> 
                           forall {m}, mark mch p c a t m -> exists r, recv rch c p a t r.

      Axiom sendmImpRecvrGe: parent c p ->
                             forall {m}, mark mch p c a t m ->
                                         forall {r}, recv rch c p a t r -> sle (to r) (to m).

      Axiom recvrCond: parent c p ->
                       forall {r}, recv rch c p a t r -> sle (dir p c a t) (from r).

      Axiom recvmCond: parent c p ->
                       forall {m}, recv mch c p a t m -> from m = dir p c a t.

      Axiom sendrImpNoSendm: parent c p ->
        forall {t1 t2 r1 m2},
          t1 < t2 -> mark rch p c a t1 r1 ->
          mark mch p c a t2 m2 ->
          exists t', t1 < t' < t2 /\ exists m, recv mch c p a t' m /\ sle (to m) (to r1).

      (*    Axiom recvrImpSendm: forall {r}, recv rch c p a t r -> exists m, mark mch p c a t m /\ to m >= to r.*)
    End ForT.

    Axiom init: parent c p -> forall {a}, dir p c a 0 = state c a 0.

    Definition twoEqPRespFalse (isParent: parent c p) :=
      forall a t t1 m1, t1 <= t -> mark mch p c a t1 m1 ->
                        forall t2 m2, t2 <= t -> mark mch p c a t2 m2 ->
                                      (forall t3, t3 <= t -> ~ recv mch p c a t3 m1) ->
                                      (forall {t4}, t4 <= t -> ~ recv mch p c a t4 m2) ->
                                      t1 = t2.

    Definition twoPReqEqNeedsPResp (isParent: parent c p) :=
      forall a t t1 r1,
        t1 <= t -> mark rch p c a t1 r1 ->
        forall t2 r2,
          t2 <= t -> mark rch p c a t2 r2 ->
          (forall t3, t3 <= t -> ~ recv rch p c a t3 r1) ->
          (forall t4, t4 <= t -> ~ recv rch p c a t4 r2) -> t1 < t2 ->
          sle (to r1) (to r2) -> exists tm, t1 < tm < t2 /\ exists m, mark mch p c a tm m.

    Section ForA.
      Context {a: Addr}.
      Axiom pRespReq: forall isParent: parent c p,
                      twoEqPRespFalse isParent ->
                      twoPReqEqNeedsPResp isParent ->
                      forall {t1 t2 t3},
                      forall {m},
                        mark mch p c a t1 m ->
                        forall {r}, mark rch p c a t2 r -> recv rch p c a t3 r -> t1 <= t2 ->
                                    exists t4, t4 < t3 /\ recv mch p c a t4 m.

      Axiom pReqResp: forall isParent: parent c p,
        twoEqPRespFalse isParent ->
                      twoPReqEqNeedsPResp isParent ->
                      forall {t1 t2 t3},
                      forall {r},
                        mark rch p c a t1 r ->
                        forall {m}, mark mch p c a t2 m -> recv mch p c a t3 m -> t1 <= t2 ->
                                    exists t4, t4 < t3 /\ recv rch p c a t4 r.
    End ForA.

  End Pair.
End BehaviorAxioms.

Module mkBehaviorTheorems (dt: DataTypes) (ch: ChannelPerAddr dt) (st: BehaviorAxioms dt ch).
  Import dt ch st.
  Section Pair.
    Context {p c: Cache}.
    Variable isParent: parent c p.
    Definition st := @st.st p c isParent.
    Definition dt := @st.dt p c isParent.


      Lemma whenChildHighRecvm: forall {a t},
                                  slt (state c a t) (state c a (S t)) ->
                                  exists m, recv mch p c a t m /\ to m = state c a (S t).
      Proof.
        intros a t sStgst.
        assert (sStnst: state c a (S t) <> state c a t) by 
            (
              unfold slt in *;
              destruct (state c a t); destruct (state c a (S t)); auto; discriminate).
        pose proof (change st sStnst) as [[m sendmm] | [m recvmm] ].
        pose proof (sendmImpSt isParent sendmm) as stgm.
        pose proof (sendmChange st sendmm) as sStem.
        rewrite <- sStem in stgm.
        unfold slt in *; destruct (state c a t); destruct (state c a (S t)); auto; firstorder.
        exists m.
        intuition.
        pose proof (recvmChange st recvmm) as sStem.
        intuition.
      Qed.

      Lemma whenChildHigh': forall {a t t'}, slt (state c a t) (state c a (S (t' + t))) ->
                                           exists t'', t'' <= t' /\ exists m, recv mch p c a (t'' + t) m /\ sle (state c a (S (t' + t))) (to m).
      Proof.
        intros a t t' sSt'tgst.
        induction t'.
        pose proof (whenChildHighRecvm sSt'tgst) as [m [recvmm mesSt]].
        exists 0.
        assert (temp: 0 + t = t) by omega.
        rewrite temp in *; clear temp.
        rewrite <- mesSt.
        intuition.
        exists m.
        intuition.
        unfold sle.
        destruct (to m); auto.
        pose proof (@slt_eq_slt_dec (state c a (S (S t' + t))) (state c a (S (t' + t)))) as [lt | [eq | gt']].
        assert (gt: slt (state c a t) (state c a (S (t' + t)))) by 
            (
              unfold slt in *; destruct (state c a t); destruct (state c a (S (S t' + t)));
              destruct (state c a (S (t' + t))); auto).
        specialize (IHt' gt).
        destruct IHt' as [t'' [le [m [recvmm mgesSt't]]]].
        assert (t''leSt': t'' <= S t') by omega.
        assert (mgesSSt't: sle (state c a (S (S t' + t))) (to m)) by
            (
              unfold sle in *; unfold slt in *; destruct (state c a (S (t' + t)));
              destruct (to m);
              destruct (state c a (S (S t' + t))); auto).
        exists t''.
        intuition.
        exists m.
        intuition.
        rewrite <- eq in IHt'.
        specialize (IHt' sSt'tgst).
        destruct IHt' as [t'' [le rest]].
        exists t''.
        intuition.
        assert (gt: slt (state c a (S (t' + t))) (state c a (S (S t' + t)))) by
            ( unfold slt; destruct (state c a (S (t' + t)));
                          destruct (state c a (S (S t' + t)));
                          auto).
        clear gt'.
        pose proof (whenChildHighRecvm gt) as [m [recvmm mesSt]].
        exists (S t').
        intuition.
        exists m.
        assert (jjj: S t' + t = S (t' + t)) by omega.
        rewrite jjj.
        constructor.
        intuition.
        assert (me': state c a (S (S (t' + t))) = to m) by auto.
        apply (sle_eq me').
      Qed.

      Lemma whenChildHigh: forall {a t t'}, t' > t -> slt (state c a t) (state c a t') ->
                                            exists t'',
                                              t <= t'' < t' /\
                                              exists m,
                                                recv mch p c a t'' m /\
                                                sle (state c a t') (to m).
      Proof.
        intros a t tPlust'.
        intros diff.
        remember (tPlust' - S t) as t'.
        assert (eq: tPlust' = S (t' + t)) by omega.
        rewrite eq.
        intro cond.
        pose proof (whenChildHigh' cond) as [t'' [cond2 exm]].
        exists (t'' + t).
        constructor.
        omega.
        assumption.
      Qed.

      Lemma whenChildHighConv: forall {a t t'}, t' >= t ->
                                              (~ exists t'', t <= t'' < t' /\ exists m, recv mch p c a t'' m /\ sle (state c a t') (to m)) ->
                                              sle (state c a t') (state c a t).
      Proof.
        intros a t t' t'GeT notE.
        assert (opts: t' = t \/ t' > t) by omega.
        destruct opts as [t'EqT | t'GtT].
        assert (eq': state c a t' = state c a t) by auto.
        apply (sle_eq eq').
        assert (notX: ~ slt (state c a t) (state c a t')) by (intros one;
                                                        pose proof (whenChildHigh t'GtT one); firstorder).
        apply (not_slt_sle notX).
      Qed.

    Lemma dirRecvImpLow: forall {a t m}, recv mch c p a t m -> slt (dir p c a (S t)) (dir p c a t).
    Proof.
      intros a t m recvm.
      pose proof (recvImpMark recvm) as [t' [t'LeT sendm]].
      pose proof (recvmChange dt recvm) as sth.
      pose proof (sendmImpSt isParent sendm) as sth2.
      pose proof (recvmCond isParent recvm) as sth3.
      pose proof (sendmFrom st sendm) as sth4.
      rewrite sth4 in sth3.
      rewrite sth3 in sth2.
      rewrite <- sth in sth2.
      assumption.
    Qed.

    Lemma whenDirLow': forall {a t t'},
                         slt (dir p c a t) (dir p c a (t' + t)) ->
                         exists t'', t'' < t' /\ exists m, mark mch p c a (t'' + t) m.
    Proof.
      intros a t t'.
      induction t'.
      intros dirGt.
      unfold plus in *; simpl. unfold slt in dirGt; destruct (dir p c a t) in *; firstorder.
      intros dirGt.
      assert (opts: slt (dir p c a t) (dir p c a (t' + t)) \/ sle (dir p c a (t' + t)) (dir p c a t)) by
          (unfold slt; unfold sle; destruct (dir p c a t); destruct (dir p c a (t' + t));auto).
      destruct opts as [gt | le].
      firstorder.
      assert (gt: slt (dir p c a (t' + t)) (dir p c a (S (t' + t)))) by
          (assert (eq: S t' + t = S (t' + t)) by omega;
           rewrite eq in *;
             unfold slt in *; unfold sle in *; destruct (dir p c a (t'+t));
           destruct (dir p c a (S (t' + t))); destruct (dir p c a t); auto).
      assert (nestuff: dir p c a (S (t' + t)) <> dir p c a (t' + t)) by
       ( unfold not; intro x; assert (y: dir p c a (t'+t) = dir p c a (S (t'+t))) by auto;
         pose proof ((slt_neq y) gt); firstorder).
      pose proof (change dt nestuff) as [sendm | recvm].
      firstorder.
      destruct recvm as [x recvstuff].
      pose proof (dirRecvImpLow recvstuff) as contra.
      pose proof (slt_slti_false contra gt).
      firstorder.
    Qed.

    Lemma whenDirLow: forall {a t t1},
                        t <= t1 -> slt (dir p c a t) (dir p c a t1) ->
                        exists t'', t <= t'' < t1 /\ exists m, mark mch p c a t'' m.
    Proof.
      intros a t t1 t1LeT1 dirGt.
      assert (opt: t = t1 \/ t < t1) by omega.
      destruct opt as [tEqT1 | tLeT1].
      assert (dEq: dir p c a t = dir p c a t1) by auto.
      pose proof (slt_neq dEq); firstorder.
      remember (t1 - t - 1) as t'.
      assert (eq: t1 = (t' + 1) + t) by omega.
      rewrite eq in *.
      pose proof (whenDirLow' dirGt) as [t'' [t''Cond ext]]. 
      exists (t'' + t).
      firstorder.
    Qed.

    Lemma childSth: forall {a t x},
                      slt x (dir p c a t) ->
                      forall {td},
                        ~ (exists tn, t <= tn < t + td /\
                                      ((exists m, mark mch p c a tn m) \/
                                       (exists m, recv mch c p a tn m /\ sle (to m) x))) ->
                        slt x (dir p c a (t + td)).
    Proof.
      intros a t x cond.
      induction td.
      intros _.
      assert (t+0=t) by omega.
      rewrite H in *.
      intuition.
      intros nothing.
      assert (contra: ~ exists tn, t <= tn < t + td /\ ((exists m, mark mch p c a tn m) \/
                                                        (exists m, recv mch c p a tn m /\ sle (to m) x))) by (unfold not; intros [tn [cond3 rest]];
                                                                                                           assert (cond2: t <= tn < t + S td) by omega;
                                                                                                           generalize nothing cond2 rest; clear; firstorder).
      specialize (IHtd contra).
      pose proof (@change (dir p c) slt p c dt (t + td) a) as stUnEq.
      assert (opts: dir p c a (t + S td) = dir p c a (t + td) \/
                    dir p c a (t + S td) <> dir p c a (t + td))
        by decide equality.
      destruct opts as [easy | hard].
      rewrite easy.
      assumption.
      assert (eq: t + S td = S (t + td)) by omega.
      rewrite eq in *.
      specialize (stUnEq hard).
      assert (pre: t <= t + td < S (t + td)) by omega.
      destruct stUnEq as [[m sendm]|[m recvm]].
      firstorder.
      assert (opts: sle (to m) x \/ slt x (to m)).
      unfold sle; unfold slt; destruct (to m); destruct x; auto.
      destruct opts as [toMLeX | toMGtX].
      firstorder.
      pose proof (recvmChange dt recvm) as H.
      rewrite H.
      assumption.
    Qed.

    Lemma dirCantGoLower: forall {a t x},
                            slt x (dir p c a t) ->
                            forall {t1},
                              t <= t1 ->
                              ~ (exists tn, t <= tn < t1 /\
                                            ((exists m, mark mch p c a tn m) \/
                                             (exists m, recv mch c p a tn m /\ sle (to m) x))) ->
                              slt x (dir p c a (t1)).
    Proof.
      intros a t x dirx t1 tLeT1 contra.
      remember (t1 - t) as td.
      assert (t1 = t + td) by omega.
      rewrite H in *.
      apply (childSth dirx contra).
    Qed.



    Lemma cReqPRespCrossInd:
      forall {a t tc tp},
        tc <= t -> tp <= t -> 
        forall {r m}, mark rch c p a tc r ->
                      mark mch p c a tp m ->
                      (forall tc', tc' < tc -> ~ recv mch p c a tc' m) ->
                      (forall tp', tp' <= tp -> ~ recv rch c p a tp' r) -> False.
    Proof.
      intros a t.
      induction t.
      intros tc tp tcLeT tpLeT r m rsendr msendm mrecvNo rrecvNo.
      assert (tc0: tc = 0) by omega; clear tcLeT.
      assert (tp0: tp = 0) by omega; clear tpLeT.
      rewrite tc0 in *; rewrite tp0 in *; clear tc0 tp0.
      pose proof (sendmImpRecvr isParent msendm) as [r' rrecvr'].
      pose proof (recvImpMark rrecvr') as [t' [t'Le0 rsendr']].
      assert (t'0: t' = 0) by omega; clear t'Le0.
      rewrite t'0 in rsendr'; clear t'0.
      pose proof (uniqMark1 rsendr rsendr') as rEqr'.
      rewrite <- rEqr' in *; clear rEqr'.
      assert (zero: 0 <= 0) by omega.
      firstorder.
      intros tc tp tcLeST tpLeST r m rsendr msendm mrecvNo rrecvNo.

      pose proof (sendmImpRecvr isParent msendm) as [r' rrecvr'].
      pose proof (recvImpMark rrecvr') as [t' [t'LeSt rsendr']].

      assert (diff: t' = tc \/ t' > tc \/ t' < tc) by omega.
      destruct diff as [eq | [t'GtTc | tcGtT']].
      rewrite eq in rsendr'.
      pose proof (uniqMark1 rsendr rsendr') as rEqr'.
      rewrite <- rEqr' in *.
      assert (tpEq: tp <= tp) by omega.
      firstorder.

      pose proof (sendrImpNoSendr st t'GtTc rsendr rsendr') as [t'' [cond neg]].
      unfold sgt in neg.
      pose proof (not_slt_sle neg) as toRLes.
      pose proof (sendrImpSt st rsendr) as toGtt.
      unfold sgt in toGtt.
      assert (tcLtT'': slt (state c a tc) (state c a t'')) by
          (unfold sle in *; unfold slt in *; destruct (to r); destruct (state c a tc);
           destruct (state c a t''); auto).
      assert (t''GtTc: t'' > tc) by omega.
      pose proof (whenChildHigh t''GtTc tcLtT'') as [t''' [[tcLeT''' t'''LtT''] [m' [mrecvm' _]]]].
      pose proof (recvImpMark mrecvm') as [td [tdLeT''' msendm']].
      assert (tdLet: td <= t) by omega.
      assert (noRecv: forall tc', tc' < tc -> ~ recv mch p c a tc' m') by (
                                                                           unfold not; intros tc' tc'LtTc mrecvm'Tc';
                                                                           pose proof (uniqRecv2 mrecvm' mrecvm'Tc') as tc'EqT''; omega).
      assert (noRecv': forall tp', tp' <= td -> ~ recv rch c p a tp' r) by (
                                                                            unfold not; intros tp' tp'LeTd;
                                                                            assert (tp'LeTp: tp' <= tp) by omega;
                                                                            firstorder).
      assert (tcLeT: tc <= t) by omega.
      apply (IHt tc td tcLeT tdLet r m' rsendr msendm' noRecv noRecv').

      pose proof (sendrImpNoSendr st tcGtT' rsendr' rsendr) as [tmur [cond neg]].
      pose proof (not_slt_sle neg) as toRLeS.
      pose proof (sendrImpSt st rsendr') as toGtt.
      assert (stt'LtstTc: slt (state c a t') (state c a tmur)) by
          (unfold sle in *; unfold slt in *; destruct (to r'); destruct (state c a tmur);
           destruct (state c a t'); auto).
      assert (tmurGtT': tmur > t') by omega.
      pose proof (whenChildHigh tmurGtT' stt'LtstTc) as [t'' [[tcLeT'' t''LtT'] [m' [mrecvm' _]]]].
      pose proof (recvImpMark mrecvm') as [td [tdLeT'' msendm']].
      assert (tdLet: td <= t) by omega.
      assert (noRecv: forall tc', tc' < t' -> ~ recv mch p c a tc' m') by (
                                                                           unfold not; intros tc' tc'LtTc mrecvm'Tc';
                                                                           pose proof (uniqRecv2 mrecvm' mrecvm'Tc') as tc'EqT''; omega).
      assert (opts: td = tp \/ td < tp \/ td > tp) by omega.
      destruct opts as [trecvTp | [tdLTp | tdGtTp]].
      rewrite trecvTp in *.
      pose proof (uniqMark1 msendm msendm') as mEqm'.
      rewrite <- mEqm' in *.
      assert (t''LtTc: t'' < tc) by omega.
      firstorder.
      assert (noRecv': forall tp', tp' <= td -> ~ recv rch c p a tp' r') by (
                                                                             unfold not; intros tp' tp'LeTd rrecvr'Tp';
                                                                             pose proof (uniqRecv2 rrecvr' rrecvr'Tp') as tp'EqTp;
                                                                             omega).
      assert (t'LeT: t' <= t) by omega.
      apply (IHt t' td t'LeT tdLet r' m' rsendr' msendm' noRecv noRecv').
      pose proof (sendmImpRecvr isParent msendm') as [r'' rrecvr''].
      pose proof (recvImpMark rrecvr'') as [ts [tsLeTd rsendr'']].
      assert (tpLeT: tp <= t) by omega.
      assert (tsLeT: ts <= t) by omega.
      assert (hyp1: forall tc', tc' < ts -> ~ recv mch p c a tc' m) by (
                                                                        intros tc' tc'LtTs;
                                                                        assert (tc'LtTc: tc' < tc) by omega;
                                                                        firstorder).
      assert (hyp2: forall tp', tp' <= tp -> ~ recv rch c p a tp' r'') by (
                                                                           unfold not; intros tp' tpLeTp rrecvr''Tp';
                                                                           pose proof (uniqRecv2 rrecvr'' rrecvr''Tp') as trecvTp';
                                                                           rewrite <- trecvTp' in *;
                                                                             firstorder).
      apply (IHt ts tp tsLeT tpLeT r'' m rsendr'' msendm hyp1 hyp2).
    Qed.

    Lemma cReqPRespCross:
      forall {a tc tp r m},
        mark rch c p a tc r ->
        mark mch p c a tp m -> (forall tc', tc' < tc -> ~ recv mch p c a tc' m) ->
        (forall tp', tp' <= tp -> ~ recv rch c p a tp' r) -> False.
    Proof.
      intros a tc tp.
      assert (tcLeT: tc <= tc + tp) by omega.
      assert (tpLeT: tp <= tc + tp) by omega.
      apply (@cReqPRespCrossInd a (tc + tp) tc tp tcLeT tpLeT).
    Qed.

    Lemma pRespFifo: forall {a ts1 ts2 tr2 m1 m2},
                       ts1 < ts2 ->
                       mark mch p c a ts1 m1 ->
                       mark mch p c a ts2 m2 ->
                       recv mch p c a tr2 m2 ->
                       exists tr1, tr1 < tr2 /\ recv mch p c a tr1 m1.
      intros a ts1 ts2 tr2 m1 m2 ts1_lt_ts2 markm1 markm2 recvm2.
      pose proof (sendmImpRecvr isParent markm2) as [r2 recvr2].
      assert (noRecvr: forall tp', tp' <= ts1 -> ~ recv rch c p a tp' r2)
        by (
            unfold not; intros tp' tp'_le_ts1 recv'r2;
            pose proof (uniqRecv2 recvr2 recv'r2);
            omega).
      pose proof (recvImpMark recvr2) as [tsr2 [tsr2_le_ts2 markr2]].
      destruct (classical (exists tr1, tr1 < tr2 /\ recv mch p c a tr1 m1)) as [easy|hard].
      assumption.
      assert (noRecvm1: forall tr1, tr1 < tr2 -> ~ recv mch p c a tr1 m1) by firstorder.
      clear hard.
      pose proof (recvImpMarkBefore recvm2 markm2) as ts2_le_tr2.
      assert (tsr2_le_tr2: tsr2 <= tr2) by omega.
      assert (noRecv'm1: forall tc', tc' < tsr2 -> ~ recv mch p c a tc' m1) by
          (
            intros tc' tc'_lt_tsr2; assert (tc'_lt_tr2: tc' < tr2) by omega; generalize noRecvm1 tc'_lt_tr2; clear; firstorder).
      pose proof (cReqPRespCross markr2 markm1 noRecv'm1 noRecvr) as [].
    Qed.

    Lemma noTwoPResp: @twoEqPRespFalse p c isParent.
    Proof.
      intros a tx t1 m1 t1LeTx sendm1 t2 m2 t2LeTx sendm2 norecvm1 norecvm2.
      pose proof (sendmImpRecvr isParent sendm1) as [r1 recvr1].
      pose proof (sendmImpRecvr isParent sendm2) as [r2 recvr2].
      pose proof (recvImpMark recvr1) as [t3 [t3LeT1 sendr1]].
      pose proof (recvImpMark recvr2) as [t4 [t4LeT2 sendr2]].
      assert (opts: t3 = t4 \/ t3 < t4 \/ t4 < t3) by omega.
      destruct opts as [t3EqT4|[t3LtT4|t4LtT3]].
      rewrite t3EqT4 in *; pose proof (uniqMark1 sendr1 sendr2) as r1EqR2.
      rewrite r1EqR2 in *; apply (uniqRecv2 recvr1 recvr2).

      assert (noRecv: ~ exists t, t3 <= t < t4 /\ exists m, recv mch p c a t m) by (
                                                                                    unfold not; intros [t [cond [m recvm]]];
                                                                                    pose proof (recvImpMark recvm) as [t5 [t5LeT sendm]];
                                                                                    assert (opts: t5 = t1 \/ t5 < t1 \/ t5 > t1) by omega;
                                                                                    destruct opts as [t5EqT1 | [t5LtT1 | t5GtT1]]; [
                                                                                      rewrite t5EqT1 in *; pose proof (uniqMark1 sendm1 sendm) as m1EqM;
                                                                                      rewrite m1EqM in *; assert (tLeTx: t <= tx) by omega;
                                                                                      generalize tLeTx norecvm1 recvm; clear; firstorder |
                                                                                      assert (one: forall tc', tc' < t3 -> ~ recv mch p c a tc' m) by (
                                                                                                                                                       unfold not; intros tc' tc'LtT3 recv'm; pose proof (uniqRecv2 recvm recv'm) as tEqTc';
                                                                                                                                                       rewrite tEqTc' in *; firstorder);
                                                                                        assert (two: forall tp', tp' <= t5 -> ~ recv rch c p a tp' r1) by (
                                                                                                                                                           unfold not; intros tp' tp'LeT1 recv'r1; pose proof (uniqRecv2 recvr1 recv'r1) as t5EqTp';
                                                                                                                                                           rewrite <- t5EqTp' in *; firstorder);
                                                                                        apply (cReqPRespCross sendr1 sendm one two) |
                                                                                      pose proof (sendmImpRecvr isParent sendm) as [r recvr];
                                                                                        pose proof (recvImpMark recvr) as [t6 [t6LeT5 sendr]];
                                                                                        assert (one: forall tc', tc' < t6 -> ~ recv mch p c a tc' m1) by (
                                                                                                                                                          unfold not; intros tc' tc'LtT6 recv'm1; assert (tc'LeT6: tc' <= tx) by omega;
                                                                                                                                                          generalize norecvm1 recv'm1 tc'LeT6; clear; firstorder);
                                                                                        assert (two: forall tp', tp' <= t1 -> ~ recv rch c p a tp' r) by (
                                                                                                                                                          unfold not; intros tp' tp'LeT1 recv'r; pose proof (uniqRecv2 recvr recv'r) as t1EqTp';
                                                                                                                                                          rewrite <- t1EqTp' in *; firstorder);
                                                                                        apply (cReqPRespCross sendr sendm1 one two)]).
      assert (t3LeT4: t3 <= t4) by omega.
      pose proof (sendrImpSt st sendr1) as stG.
      pose proof (sendrImpNoSendr st t3LtT4 sendr1 sendr2) as [t5 [t3LtT5LeT4 neg]].
      assert (pos: slt (state c a t3) (state c a t5)) by
          (unfold sgt in *; unfold slt in *; destruct (to r1); destruct (state c a t3);
           destruct (state c a t5); auto).
      assert (noRecv': ~ exists t, t3 <= t < t5 /\ exists m, recv mch p c a t m /\ sle (state c a t5) (to m)) by (
                                                                                                             unfold not; intros [t [cond1 [mg [recvmg _]]]];
                                                                                                             assert (cond: t3 <= t < t4) by omega;
                                                                                                             generalize recvmg cond noRecv; clear; firstorder).
      assert (t3LeT5: t3 <= t5) by omega.
      pose proof (whenChildHighConv t3LeT5 noRecv') as stContra.
      assert False by (unfold slt in *; unfold sle in *; destruct (state c a t5); destruct (state c a t3); auto).
      firstorder.

      assert (noRecv: ~ exists t, t4 <= t < t3 /\ exists m, recv mch p c a t m) by (
                                                                                    unfold not; intros [t [cond [m recvm]]];
                                                                                    pose proof (recvImpMark recvm) as [t5 [t5LeT sendm]];
                                                                                    assert (opts: t5 = t2 \/ t5 < t2 \/ t5 > t2) by omega;
                                                                                    destruct opts as [t5EqT1 | [t5LtT1 | t5GtT1]]; [
                                                                                      rewrite t5EqT1 in *; pose proof (uniqMark1 sendm2 sendm) as m1EqM;
                                                                                      rewrite m1EqM in *; assert (tLeTx: t <= tx) by omega;
                                                                                      generalize tLeTx norecvm2 recvm; clear; firstorder |
                                                                                      assert (one: forall tc', tc' < t4 -> ~ recv mch p c a tc' m) by (
                                                                                                                                                       unfold not; intros tc' tc'LtT3 recv'm; pose proof (uniqRecv2 recvm recv'm) as tEqTc';
                                                                                                                                                       rewrite tEqTc' in *; firstorder);
                                                                                        assert (two: forall tp', tp' <= t5 -> ~ recv rch c p a tp' r2) by (
                                                                                                                                                           unfold not; intros tp' tp'LeT1 recv'r1; pose proof (uniqRecv2 recvr2 recv'r1) as t5EqTp';
                                                                                                                                                           rewrite <- t5EqTp' in *; firstorder);
                                                                                        apply (cReqPRespCross sendr2 sendm one two)|
                                                                                      pose proof (sendmImpRecvr isParent sendm) as [r recvr];
                                                                                        pose proof (recvImpMark recvr) as [t6 [t6LeT5 sendr]];
                                                                                        assert (one: forall tc', tc' < t6 -> ~ recv mch p c a tc' m2) by (
                                                                                                                                                          unfold not; intros tc' tc'LtT6 recv'm1; assert (tc'LeT6: tc' <= tx) by omega;
                                                                                                                                                          generalize norecvm2 recv'm1 tc'LeT6; clear; firstorder);
                                                                                        assert (two: forall tp', tp' <= t2 -> ~ recv rch c p a tp' r) by (
                                                                                                                                                          unfold not; intros tp' tp'LeT1 recv'r; pose proof (uniqRecv2 recvr recv'r) as t1EqTp';
                                                                                                                                                          rewrite <- t1EqTp' in *; firstorder);
                                                                                        apply (cReqPRespCross sendr sendm2 one two)]).
      assert (t3LeT4: t4 <= t3) by omega.
      pose proof (sendrImpSt st sendr2) as stG.
      pose proof (sendrImpNoSendr st t4LtT3 sendr2 sendr1) as [t5 [t3LtT5LeT4 neg]].
      assert (pos: slt (state c a t4) (state c a t5)) by
          (unfold sgt in *; unfold slt in *; destruct (to r2); destruct (state c a t4);
           destruct (state c a t5); auto).
      assert (noRecv': ~ exists t, t4 <= t < t5 /\ exists m, recv mch p c a t m /\ sle (state c a t5) (to m)) by (
                                                                                                             unfold not; intros [t [cond1 [mg [recvmg _]]]];
                                                                                                             assert (cond: t4 <= t < t3) by omega;
                                                                                                             generalize recvmg cond noRecv; clear; firstorder).
      assert (t3LeT5: t4 <= t5) by omega.
      pose proof (whenChildHighConv t3LeT5 noRecv') as stContra.
      assert False by (unfold slt in *; unfold sle in *; destruct (state c a t5); destruct (state c a t4); destruct (to r2); auto).
      firstorder.
    Qed.

    Lemma noTwoPReqNon: @twoPReqEqNeedsPResp p c isParent.
    Proof.
      intros a t t1 r1 t1LeT sendr1 t2 r2 t2LeT sendr2 norecvr1 norecvr2 t1LtT2 toR1GeToR2.
      pose proof (sendrImpSt dt sendr1) as gt1.
      pose proof (sendrImpSt dt sendr2) as gt2.
      pose proof (sendrImpNoSendr dt t1LtT2 sendr1 sendr2) as [t5 [cond dr]].
      pose proof (not_slt_sle dr) as toR1GeDirT5.
      clear dr.
      assert (dT5LtDt2: slt (dir p c a t5) (dir p c a t2)) by
          (unfold sle in *; unfold slt in *; destruct (to r1); destruct (dir p c a t1);
           destruct (to r2); destruct (dir p c a t2); destruct (dir p c a t5); auto).
      assert (t5LeT2: t5 <= t2) by omega.
      pose proof (whenDirLow t5LeT2 dT5LtDt2) as [tm [m [cond2 sendm]]].
      assert (cond3: t1 < tm < t2) by omega.
      firstorder.
    Qed.

    Lemma mainInd: forall {a t},
                     (forall {to}, to <= t -> sle (state c a to) (dir p c a to)) /\
                     (forall {tc tp}, tc <= t -> tp <= t -> forall {mc}, mark mch c p a tc mc ->
                                                                         forall {mp}, mark mch p c a tp mp -> (forall tc', tc' < tc -> ~ recv mch p c a tc' mp) ->
                                                                                      (forall tp', tp' < tp -> ~ recv mch c p a tp' mc) -> False) /\
                     (forall {t1 t2 t3}, t3 <= t -> forall {m}, mark mch c p a t1 m ->
                                                                forall {r}, mark rch c p a t2 r -> recv rch c p a t3 r -> t1 <= t2 ->
                                                                            (forall t4, t4 < t3 -> ~ recv mch c p a t4 m) -> False) /\
                     (forall {t1 t2 t3}, t3 <= t -> forall {m}, mark mch c p a t1 m ->
                                                                forall {m'}, mark mch c p a t2 m' -> recv mch c p a t3 m' -> t1 < t2 ->
                                                                             (forall t4, t4 < t3 -> ~ recv mch c p a t4 m) -> False).
    Proof.
      intros a t.
      induction t.
      constructor.
      intros to0 to0Le0.
      assert (to0Eq0: to0 = 0) by omega.
      pose proof (@init p c isParent a) as start.
      rewrite to0Eq0.
      assert (H: state c a 0 = dir p c a 0) by auto.
      apply (sle_eq H).
      constructor.
      intros tc tp tcLe0 tpLe0 mc msendmc mp msendmp _ _.
      assert (tcEq0: tc = 0) by omega; assert (tpEq0: tp = 0) by omega.
      rewrite tcEq0 in *; rewrite tpEq0 in *.
      pose proof (sendmImpRecvr isParent msendmp) as [r rrecvr].
      pose proof (recvImpMark rrecvr) as [t' [t'Le0 rsendr]].
      assert (t'Eq0: t' = 0) by omega.
      rewrite t'Eq0 in *.
      apply (noSendmSendr st msendmc rsendr).
      constructor.
      intros t1 t2 t3 t3Le0 m msendm r rsendr rrecvr t1LeT2 neg.
      pose proof (recvImpMark rrecvr) as [t5 [t5LeT3 rsendrT5]].
      pose proof (uniqMark2 rsendr rsendrT5) as t2EqT5.
      assert (t30: t3 = 0) by omega.
      rewrite t2EqT5, t30 in *.
      assert (t1Le0: t1 <= 0) by omega.
      assert (t10: t1 = 0) by intuition.
      assert (t50: t5 = 0) by omega.
      rewrite t10, t50 in *.
      apply (noSendmSendr st msendm rsendr).
      intros t1 t2 t3 t3Le0 m msendm m' msendm' mrecvm' t1LeT2 neg.
      pose proof (recvImpMark mrecvm') as [t5 [t5LeT3 msendm'T5]].
      pose proof (uniqMark2 msendm' msendm'T5) as t2EqT5.
      assert (t30: t3 = 0) by omega.
      rewrite t2EqT5, t30 in *.
      assert (t1Le0: t1 <= 0) by omega.
      assert (t10: t1 = 0) by intuition.
      assert (t50: t5 = 0) by omega.
      rewrite t10, t50 in *.
      omega.
      
      destruct IHt as [cons [cross [cReqResp cRespResp]]].

      assert (cross': forall to0, to0 <= S t -> sle (state c a to0) (dir p c a to0)).
      intros tm toLtT.
      destruct (classical (exists ts, ts < tm /\ ((exists m, recv mch c p a ts m) \/
                                                  (exists m, mark mch p c a ts m)))) as [chnge|noChnge].
      pose proof (maxExists' classical chnge) as lastChnge; clear chnge.
      destruct lastChnge as [ts [tsLtTo [recvOrSend noPrevChnge]]].
      assert (eq: dir p c a (S ts) = dir p c a tm) by (
                                                       assert (two: S ts = tm \/ S ts < tm) by omega;
                                                       destruct two as [eq|less]; [
                                                         intuition|
                                                         apply (@noChange (dir p c) slt p c dt); [ intuition | generalize noPrevChnge; clear; firstorder]]).
      destruct recvOrSend as [[m mrecvm] | [m msendm]].
      pose proof (recvImpMark mrecvm) as [t' [t'LeTs msendm]].
      destruct (classical (exists tc, t' < tc < tm /\ exists m, recv mch p c a tc m)) as [recv|noRecv].
      destruct recv as [tc [comp [m' mrecvm']]].
      pose proof (recvImpMark mrecvm') as [t'' [t''LeTc msendm']].
      assert (gOrl: t'' > ts \/ t'' <= ts) by omega.
      destruct gOrl as [t''GtTs | t''LeTs].
      assert (t''LtTc: t'' < tm) by omega.
      generalize noPrevChnge msendm' t''LtTc t''GtTs; clear; firstorder.
      assert (t'LeT: t' <= t) by omega.
      assert (t''LeT: t'' <= t) by omega.
      assert (hyp1: forall tc', tc' < t' -> ~ recv mch p c a tc' m') by (
                                                                         unfold not; intros tc' tc'LtT' mrecvm'Tc';
                                                                         pose proof (uniqRecv2 mrecvm' mrecvm'Tc'); intuition).
      assert (hyp2: forall tp', tp' < t'' -> ~ recv mch c p a tp' m) by (
                                                                         unfold not; intros tp' tp'LtT'' mrecvmTp';
                                                                         pose proof (uniqRecv2 mrecvm mrecvmTp'); intuition).
      pose proof (cross t' t'' t'LeT t''LeT m msendm m' msendm' hyp1 hyp2).
      firstorder.
      assert (noRecv': ~ (exists tc, S t' <= tc < tm /\ exists m, recv mch p c a tc m /\ slt (state c a tm) (to m))) by
          (
            unfold not; intros [tc [cond [m0 [mrecvm0 _]]]];
            assert (cond': t' < tc < tm) by omega; generalize noRecv cond' mrecvm0; clear; firstorder).
      assert (nGt: ~ slt (state c a (S t')) (state c a tm)) by
          (
            assert (eqOrGt: tm = S t' \/ tm > S t') by omega;
            destruct eqOrGt as [toEqSt' | toGtSt']; [
            assert (H: state c a (S t') = state c a tm) by auto;
              apply (slt_neq H)|
              
              pose proof (@whenChildHigh a (S t') tm toGtSt') as contra;
                generalize contra noRecv; clear; firstorder]).
      assert (dirEqSt: dir p c a (S ts) = state c a (S t')) by (
                                                                pose proof (sendmChange st msendm) as one;
                                                                pose proof (recvmChange dt mrecvm) as two;
                                                                  congruence).
      pose proof (not_slt_sle nGt) as stoLesSt'.
      congruence.
      pose proof (sendmImpRecvr isParent msendm) as [r rrecvr].
      pose proof (recvImpMark rrecvr) as [t' [t'LeTs rsendr]].
      destruct (classical (exists tc, tc < tm /\ recv mch p c a tc m)) as [[tc [tcLtTo mrecvm]] | notEx].
      assert (eqOrNot: tm = S tc \/ tm > S tc) by omega.
      destruct eqOrNot as [toEqStc | toGtStc].
      assert (dirEqSt: state c a tm = dir p c a tm) by (
                                                        pose proof (sendmChange dt msendm) as one; pose proof (recvmChange st mrecvm) as two;
                                                         congruence).
      apply (sle_eq dirEqSt).
      assert (noLower: ~ exists t'', S tc <= t'' < tm /\ exists m', recv mch p c a t'' m' /\ sle (state c a tm) (to m'))
        by (
            unfold not; intros [t'' [cond [m' [mrecvm' _]]]];
            pose proof (recvImpMark mrecvm') as [tf [tfLeT'' msendm']];
            assert (diff: ts = tf \/ tf < ts \/ tf > ts) by omega;
            destruct diff as [tsEqTf | [tfLtTs | tfGtTs]]; [
              rewrite <- tsEqTf in *;
              pose proof (uniqMark1 msendm msendm') as mEqM';
              rewrite <- mEqM' in *;
              pose proof (uniqRecv2 mrecvm mrecvm') as tcEqT'';
              omega |
              assert (t'LeTc: t' <= tc) by (
                                            pose proof (recvImpMark mrecvm) as [tsome [tsomeLe'' msendmTsome]];
                                            pose proof (uniqMark2 msendm msendmTsome) as tcEqTsome;
                                            rewrite <- tcEqTsome in *; omega);
                pose proof @cReqPRespCross;
                assert (cross1: forall tc', tc' < t' -> ~ recv mch p c a tc' m') by (
                                                                                     unfold not; intros tc' tc'LtT' mrecvm'Tc';
                                                                                     pose proof (uniqRecv2 mrecvm' mrecvm'Tc') as t'EqTc'; omega);
                assert (cross2: forall tp', tp' <= tf -> ~ recv rch c p a tp' r) by (
                                                                                     unfold not; intros tp' tp'LeTf rrecvrTp';
                                                                                     pose proof (uniqRecv2 rrecvr rrecvrTp') as tfEqTp'; omega);
                assert (t''LeT: t'' <= t) by omega;
                assert (tfLeT: tf <= t) by omega;
                apply (cReqPRespCross rsendr msendm' cross1 cross2)|
              assert (cond2: ts < tf < tm) by omega;
                generalize cond2 noPrevChnge msendm'; clear; firstorder]).
      pose proof (@whenChildHigh a (S tc) tm toGtStc) as contra.
      assert (not: ~ sgt (state c a tm) (state c a (S tc))) by (generalize noLower contra; clear; firstorder).
      pose proof (not_slt_sle not) as not2.
      clear not.
      assert (dirEqSt: dir p c a (S ts) = state c a (S tc)) by (
                                                                pose proof (sendmChange dt msendm) as one; pose proof (recvmChange st mrecvm) as two;
                                                                congruence).
      rewrite eq in dirEqSt.
      rewrite <- dirEqSt in not2.
      assumption.
      assert (tsLeT: ts <= t) by omega.
      assert (less: sle (state c a ts) (dir p c a ts)) by firstorder.
      assert (tmGtTs: tm > t') by omega.
      assert (noRecv: ~ exists t'', t' <= t'' < tm /\ exists m, recv mch p c a t'' m /\ sle (state c a tm) (to m)) by
          (
            unfold not; intros [t'' [cond [m' [mrecvm' _]]]];
            pose proof (recvImpMark mrecvm') as [t1 [t1LeT'' msendm']];
            assert (t1NeTs: t1 = ts -> False) by
               (
                  intros t1EqTs;
                  rewrite t1EqTs in *;
                    pose proof (uniqMark1 msendm msendm') as mEqm';
                  rewrite <- mEqm' in *;
                    generalize notEx cond mrecvm'; clear; firstorder);
            assert (eqOrNot: t1 = ts \/ t1 > ts \/ t1 < ts) by omega;
            destruct eqOrNot as [t1EqTs | [t1GtTs | t1LtTs]];
            [firstorder |
             assert (cond2: ts < t1 < tm) by omega;
               generalize noPrevChnge cond2 msendm'; clear; firstorder |
             assert (one: forall tc', tc' < t' -> ~ recv mch p c a tc' m') by
                 (
                   unfold not; intros tc' tc'LtT' mrecvm'Tc';
                   pose proof (uniqRecv2 mrecvm' mrecvm'Tc') as t''EqTc'; omega);
               assert (two: forall tp', tp' <= t1 -> ~ recv rch c p a tp' r) by
                 (
                   unfold not; intros tp' tp'LeT1 rrecvrTp';
                   pose proof (uniqRecv2 rrecvr rrecvrTp') as tsEqTp'; omega);
               apply (cReqPRespCross rsendr msendm' one two)]).
      assert (contra1: ~ sgt (state c a tm) (state c a t')) by
          (
                                                          unfold not; intros contra;
                                                          generalize (whenChildHigh tmGtTs contra) noRecv; clear; firstorder).
      pose proof (not_slt_sle contra1) as cont.
      pose proof (sendrImpSt st rsendr) as toRGtDir.
      pose proof (sendmImpRecvrGe isParent msendm rrecvr) as toMGeToR.
      pose proof (sendmChange dt msendm) as toMEq.
      rewrite eq in toMEq.
      rewrite <- toMEq in toMGeToR.
      unfold sle in *; unfold sgt in *; unfold slt in *; destruct (state c a tm);
      destruct (state c a t'); destruct (to r); destruct (dir p c a tm); auto.
      assert (eqOrNot: 0 = tm \/ 0 < tm) by omega.
      destruct eqOrNot as [tmEq0 | tmGt0].
      rewrite <- tmEq0 in *; pose proof (@init p c isParent a) as init.
      assert (H: state c a 0 = dir p c a 0) by auto.
      apply (sle_eq H).
      assert (premise: forall tn, 0 <= tn < tm -> (forall m, ~ mark mch p c a tn m) /\
                                                  (forall m, ~ recv mch c p a tn m)) by (
                                                                                         intros tn [_ tnLtTm];
                                                                                         constructor;
                                                                                         unfold not; intros m msendm;
                                                                                         generalize noChnge tnLtTm msendm; clear; firstorder).
      pose proof (noChange dt tmGt0 premise) as dir0DirTm.
      assert (not: ~ exists t'', 0 <= t'' < tm /\ exists m, recv mch p c a t'' m /\ sle (state c a tm) (to m)) by (
                                                                                                              unfold not; intros [t'' [[_ t''LtTm] [m [mrecvm _]]]];
                                                                                                              pose proof (recvImpMark mrecvm) as [t' [t'LeT'' msendm]];
                                                                                                              assert (t'LtTm: t' < tm) by omega;
                                                                                                              generalize noChnge t'LtTm msendm; clear; firstorder).
      assert (done: ~ sgt (state c a tm) (state c a 0)) by (generalize (@whenChildHigh a 0 tm tmGt0) not;
                                                      clear; firstorder).
      pose proof (@init p c isParent a) as start.
      rewrite <- start in done.
      rewrite dir0DirTm in done.
      unfold sgt in *; unfold sle; unfold slt in *; destruct (state c a tm); destruct (dir p c a tm); auto.

      constructor.
      apply cross'.

      assert (cReqResp': forall {t1 t2 t3}, t3 <= S t -> forall {m}, mark mch c p a t1 m -> forall {r},
                                                                                              mark rch c p a t2 r -> recv rch c p a t3 r -> t1 <= t2 -> (forall t4, t4 < t3 -> ~ recv mch c p a t4 m) ->
                                                                                              False).
      intros t1 t2 t3 t3LeSt m msendm r rsendr rrecvr t1LeT2 neg.
      unfold Time in *.
      assert (eqOrNot: t1 = t2 \/ t1 < t2) by omega.
      destruct eqOrNot as [t1EqT2 | t1LtT2].
      rewrite t1EqT2 in *.
      pose proof (noSendmSendr st msendm rsendr); intuition.
      clear t1LeT2.
      pose proof (recvImpMark rrecvr) as [t' [t'LeT3 rsend'r]].
      pose proof (uniqMark2 rsendr rsend'r) as t2EqT'.
      rewrite <- t2EqT' in *.
      clear rsend'r t2EqT'.
      assert (t1LeT: t1 <= t) by omega.
      pose proof (cons t1 t1LeT) as st1Ledt1.

      assert (notty1: ~ exists t'', t1 <= t'' < t2 /\ exists m, recv mch p c a t'' m /\ sle (state c a t2) (to m)) by (
                                                                                                                  unfold not; intros [t'' [cond [m0 [mrecvm0 _]]]];
                                                                                                                  pose proof (recvImpMark mrecvm0) as [t5 [t5LeT'' msendm0]];
                                                                                                                  assert (one: forall tc', tc' < t1 -> ~ recv mch p c a tc' m0) by (
                                                                                                                                                                                    unfold not; intros tc' tc'LtT1 mrecvM0Tc';
                                                                                                                                                                                    pose proof (uniqRecv2 mrecvm0 mrecvM0Tc') as t''EqTc';
                                                                                                                                                                                    rewrite <- t''EqTc' in *; omega);
                                                                                                                  assert (two: forall tp', tp' < t5 -> ~ recv mch c p a tp' m) by (
                                                                                                                                                                                   unfold not; intros tp' tp'LtT5; assert (t5LtT3: tp' < t3) by omega; firstorder);
                                                                                                                  assert (t5Let: t5 <= t) by omega;
                                                                                                                  apply (cross t1 t5 t1LeT t5Let m msendm m0 msendm0 one two)).
      assert (notty: ~ exists t'', S t1 <= t'' < t2 /\ exists m, recv mch p c a t'' m /\ sle (state c a t2) (to m)) by (
                                                                                                                   clear cRespResp;
                                                                                                                   unfold not; intros [t'' [cond ex]];
                                                                                                                   assert (cond2: t1 <= t'' < t2) by omega;
                                                                                                                   generalize notty1 cond2 ex; clear; firstorder).
      
      assert (notst2Gtst1: ~ sgt (state c a t2) (state c a (S t1))) by (
                                                                  clear cRespResp;
                                                                  clear notty1; assert (eqOrNot: S t1 = t2 \/ S t1 < t2) by omega;
                                                                  destruct eqOrNot as [eq| St1LtT2]; [
                                                                  
                                                                  assert (eq': state c a (S t1) = state c a t2) by auto;
                                                                  apply (slt_neq eq') |
                                                                    
                                                                    unfold not; intros st; pose proof (whenChildHigh St1LtT2 st) as some; firstorder]).
      pose proof (not_slt_sle notst2Gtst1) as stt2LestT1.
      pose proof (recvrCond isParent rrecvr) as fromRLe.
      pose proof (sendrFrom st rsendr) as fromREq.
      pose proof (sendmImpSt isParent msendm) as stGt.
      pose proof (sendmChange st msendm) as stEq.
      rewrite fromREq, <- stEq in *.
      assert (drGt: sgt (dir p c a t1) (dir p c a t3)) by
          (unfold sgt in *; unfold slt in *; unfold sle in *; destruct (state c a t2);
           destruct (state c a (S t1)); destruct (state c a t1); destruct (dir p c a t1);
           destruct (dir p c a t3); auto).
      assert (drNe: dir p c a t1 <> dir p c a t3) by
          (unfold not; intros x; assert (y: dir p c a t3 = dir p c a t1) by auto;
           apply ((slt_neq y) drGt)).
      assert (sendRecv: ~ forall tn, t1 <= tn < t3 -> (forall m, ~ mark mch p c a tn m) /\
                                                      (forall m, ~ recv mch c p a tn m)) by (
                                                                                             unfold not; intros exp; assert (t1LtT3: t1 < t3) by omega; pose proof (noChange dt t1LtT3 exp); firstorder).
      assert (noSend: forall tn, t1 <= tn < t3 -> forall m, ~ mark mch p c a tn m) by (
                                                                                       clear cRespResp;
                                                                                       unfold not; intros tn cond m0 msendm0;
                                                                                       assert (tnLeT: tn <= t) by omega;
                                                                                       assert (one: forall tc', tc' < t1 -> ~ recv mch p c a tc' m0) by (
                                                                                                                                                         unfold not; intros tc' tc'LtT1 mrecvm0;
                                                                                                                                                         pose proof (recvImpMark mrecvm0) as [tm [tmLeTc' msend'm0]];
                                                                                                                                                         pose proof (uniqMark2 msendm0 msend'm0) as tmEqTc';
                                                                                                                                                         rewrite <- tmEqTc' in *; omega);
                                                                                       assert (two: forall tp', tp' < tn -> ~ recv mch c p a tp' m) by (
                                                                                                                                                        unfold not; intros tp' tp'LtTn; assert (tp'LtT3: tp' < t3) by omega; firstorder);
                                                                                       apply (cross t1 tn t1LeT tnLeT m msendm m0 msendm0 one two)).

      destruct (classical (exists tn, tn < t3 /\ t1 <= tn /\ exists m0, recv mch c p a tn m0)) as [ext|noEx].
      pose proof (maxExists' classical ext) as [tn [cond [[tnLtT3 [m0 mrecvm0]] notAfter]]].
      
      pose proof (recvImpMark mrecvm0) as [tr [trLeTn msendm0]].
      assert (opts: tr = t1 \/ tr > t1 \/ tr < t1) by omega.
      destruct opts as [trEqT1 | [trGtT1 | trLtT1]].
      rewrite trEqT1 in *.
      pose proof (uniqMark1 msendm msendm0) as mEqm0.
      rewrite <- mEqm0 in *.
      generalize neg cond mrecvm0; clear; firstorder.
      assert (tnLeT: tn <= t) by omega.
      assert (cond2: forall t4, t4 < tn -> ~ recv mch c p a t4 m) by (
                                                                      intros t4 t4LtTn; assert (t4LtT3: t4 < t3) by omega;
                                                                      generalize neg t4LtT3; clear; firstorder).
      apply (cRespResp t1 tr tn tnLeT m msendm m0 msendm0 mrecvm0 trGtT1 cond2).
      assert (notty2': ~ exists t'', tr <= t'' < t1 /\ exists m, recv mch p c a t'' m) by (
                                                                                                                   unfold not; intros [t'' [cond2 [m1 mrecvm1]]];
                                                                                                                   pose proof (recvImpMark mrecvm1) as [t5 [t5LeT'' msendm1]];
                                                                                                                   assert (trLeT: tr <= t) by omega;
                                                                                                                   assert (t5LeT: t5 <= t) by omega;
                                                                                                                   assert (one: forall tc', tc' < tr -> ~ recv mch p c a tc' m1) by (
                                                                                                                                                                                     unfold not; intros tc' tc'LtTr mrecv'm1;
                                                                                                                                                                                     pose proof (uniqRecv2 mrecvm1 mrecv'm1) as t''EqTc';
                                                                                                                                                                                     rewrite <- t''EqTc' in *;
                                                                                                                                                                                       omega);
                                                                                                                   assert (two: forall tp', tp' < t5 -> ~ recv mch c p a tp' m0) by (
                                                                                                                                                                                     unfold not; intros tp' tp'LtT5 mrecv'm0;
                                                                                                                                                                                     pose proof (uniqRecv2 mrecvm0 mrecv'm0) as tnEqTp';
                                                                                                                                                                                     rewrite <- tnEqTp' in *; omega);
                                                                                                                   apply (cross tr t5 trLeT t5LeT m0 msendm0 m1 msendm1 one two)).
      assert (notty2: ~ exists t'', S tr <= t'' < t1 /\ exists m, recv mch p c a t'' m /\ sle (state c a t1) (to m)) by(
                                                                                                                    unfold not; intros [t'' [cond1 rest]]; assert (cond2: tr <= t'' < t1) by omega;
                     generalize notty2' cond2 rest; clear; firstorder).
      assert (strLeT1: S tr <= t1) by omega.
      pose proof (whenChildHighConv strLeT1 notty2) as st1LeTr.
      pose proof (whenChildHighConv t1LtT2 notty) as sST1LeT2.
      assert (trLtT3: tr < t3) by omega.
      assert (noC: forall tn0, S tn <= tn0 < t3 -> (forall m, ~ mark mch p c a tn0 m) /\
                                                   (forall m, ~ recv mch c p a tn0 m)) by (
                                                                                           intros tn0 cond2;
                                                                                           constructor; [assert (cond3: t1 <= tn0 < t3) by omega; generalize noSend cond3; clear; firstorder|
                                                                                                         assert (cond4: tn < tn0 < t3) by omega; 
                                                                                                           assert (t1LeTn0: t1 <= tn0) by omega; generalize cond4 t1LeTn0 notAfter; clear; firstorder]).
      assert (sTnLtT3: S tn <= t3) by omega.
      pose proof (noChange2 dt sTnLtT3 noC) as dirEq.
      generalize isParent st1LeTr sST1LeT2 sTnLtT3 dirEq rsendr rrecvr msendm msendm0 mrecvm0; clear; intros.
      pose proof (sendmChange st msendm) as sEqTom.
      pose proof (sendmImpSt isParent msendm) as sGtTom.
      pose proof (recvmChange dt mrecvm0) as dSEqTom0.
      pose proof (sendmChange st msendm0) as sSEqTom0.
      pose proof (recvrCond isParent rrecvr) as dLeFromr.
      pose proof (sendrFrom st rsendr) as sEqFromr.
      rewrite <- dSEqTom0 in sSEqTom0.
      rewrite <- sSEqTom0 in dirEq.
      rewrite sEqFromr in dLeFromr.
      rewrite <- dirEq in dLeFromr.
      rewrite <- sEqTom in sGtTom.
      unfold sle in *; unfold slt in *; destruct (state c a t1); destruct (state c a t2);
      destruct (state c a (S tr)); destruct (state c a (S t1)); auto.
      generalize sendRecv noSend noEx; clear; firstorder.

      constructor.

      intros tc tp tcLeSt tpLeSt mc msendmc mp msendmp norecvmp norecvmc.
      pose proof (sendmImpRecvr isParent msendmp) as [r rrecvr].
      pose proof (recvImpMark rrecvr) as [t1 [t1LeTp rsendr]].
      assert (opts: t1 = tc \/ tc < t1 \/ t1 < tc) by omega.
      destruct opts as [t1EqTc | [tcLtT1 | t1LtTc]].
      rewrite t1EqTc in *.
      apply (noSendmSendr st msendmc rsendr).
      assert (tcLeT1: tc <= t1) by omega.
      apply (cReqResp' tc t1 tp tpLeSt mc msendmc r rsendr rrecvr tcLeT1 norecvmc).
      destruct (classical (exists tm, t1 <= tm < tc /\ exists m, recv mch p c a tm m)) as [ext|noExt].
      destruct ext as [tm [[t1LeTm tmLtTc] [m recvm]]].
      pose proof (recvImpMark recvm) as [tn [tnLeTm sendm]].
      assert (opts: tn = tp \/ tn < tp \/ tn > tp) by omega.
      destruct opts as [tnEqTp | [tnLtTp | tnGtTp]].
      rewrite tnEqTp in *.
      pose proof (uniqMark1 sendm msendmp) as mEqMp.
      rewrite mEqMp in *.
      firstorder.
      assert (one: forall tc', tc' < t1 -> ~ recv mch p c a tc' m) by (
                                                                       unfold not; intros tc' tc'LtT1 recv'm;
                                                                       pose proof (uniqRecv2 recvm recv'm) as tmEqTc';
                                                                       omega).
      assert (two: forall tp', tp' <= tn -> ~ recv rch c p a tp' r) by (
                                                                        unfold not; intros tp' tp'LeTn recv'r;
                                                                        pose proof (uniqRecv2 rrecvr recv'r) as tpEqTp';
                                                                        omega).
      apply (cReqPRespCross rsendr sendm one two).
      pose proof (sendmImpRecvr isParent sendm) as [r1 recvr1].
      pose proof (recvImpMark recvr1) as [tq [tqLeTn sendr1]].
      assert (one: forall tc', tc' < tq -> ~ recv mch p c a tc' mp) by (
                                                                        unfold not; intros tc' tc'LtTq; assert (tc'LtTc: tc' < tc) by omega;
                                                                        apply (norecvmp tc' tc'LtTc)).
      assert (two: forall tp', tp' <= tp -> ~ recv rch c p a tp' r1) by (
                                                                         unfold not; intros tp' tp'LeTp recv'r1;
                                                                         pose proof (uniqRecv2 recvr1 recv'r1) as tpEqTp';
                                                                         omega).
      apply (cReqPRespCross sendr1 msendmp one two).
      assert (opt: ~ exists tm, t1 <= tm < tc /\ exists m, recv mch p c a tm m) by (
                                                                                    generalize noExt; clear; firstorder).
      assert (opt': forall t', t1 < t' <= tc -> ~ exists tm, t1 <= tm < t' /\ exists m,
                                                                                recv mch p c a tm m /\ sle (state c a t') (to m)) by (
                                                                                                                                 unfold not; intros t' t'LtTc [tm [cond rest]]; assert (cond2: t1 <= tm < tc) by omega;
                                                                                                                                 generalize opt t'LtTc cond2 rest; clear; firstorder).
      assert (notSth: forall t', t1 < t' <= tc -> ~ sgt (state c a t') (state c a t1)) by (
                                                                                     unfold not; intros t' [t1LtT' t'LeTc] sgt;
                                                                                     pose proof (whenChildHigh t1LtT' sgt) as contra;
                                                                                     generalize opt' contra t1LtT' t'LeTc; clear; firstorder).
      assert (stcLet1: forall t', t1 < t' <= tc -> sle (state c a t') (state c a t1)) by
          (intros t' cond;
           specialize (notSth t' cond);
          apply (not_slt_sle notSth)).
      clear notSth opt opt'.
      pose proof (sendrImpSt st rsendr) as gtRel.
      assert (stcLet2: forall t', t1 < t' <= tc -> slt (state c a t') (to r)) by
          (
            intros t' cond; specialize (stcLet1 t' cond);
            unfold sle in *; unfold sgt in*; unfold slt in *; destruct (state c a t');
            destruct (state c a t1); destruct (to r); auto).
      clear stcLet1 gtRel.
      pose proof (voluntary isParent rsendr t1LtTc msendmc stcLet2) as [r1 [recvr1 sTcGtToR1]].
      pose proof (recvImpMark recvr1) as [t2 [t2LeT1 sendr1]].
      assert (t2LeTp: t2 = tp \/ t2 > tp \/ t2 < tp) by omega.
      destruct t2LeTp as [t2EqTp | [t2GtTp | t2LtTp]].
      rewrite t2EqTp in *.
      apply (noSendmSendr dt msendmp sendr1).
      assert (tpLeT2: tp <= t2) by omega.
      pose proof (pRespReq isParent noTwoPResp noTwoPReqNon msendmp sendr1 recvr1 tpLeT2) as [t4 [t4LtTp recvmp]].
      generalize norecvmp recvmp t4LtTp; clear; firstorder.
      pose proof (sendrImpNoSendm isParent t2LtTp sendr1 msendmp) as [t' [[t2LtT' t'LtTp] [m [recvm toMGeToR1]]]].
      pose proof (recvImpMark recvm) as [t'' [t''LeT' sendm]].
      pose proof (sendmChange st sendm) as stEqToM.
      assert (stTcGtStST'': slt (state c a (S t'')) (state c a tc)) by
          (rewrite <- stEqToM in toMGeToR1;
           unfold slt in *; unfold sle in *; destruct (to r1); destruct (state c a tc);
           destruct (state c a (S t'')); auto).
      assert (opts: t'' = tc \/ t'' > tc \/ t'' < tc) by omega.
      destruct opts as [t''EqTc | [t''GtTc | t''LtTc]].
      rewrite t''EqTc in *.
      pose proof (uniqMark1 msendmc sendm) as mEqMc.
      rewrite mEqMc in *.
      generalize t'LtTp recvm norecvmc; clear; firstorder.
      assert (t'Let: t' <= t) by omega.
      assert (norecv: forall t4, t4 < t' -> ~ recv mch c p a t4 mc) by (
                                                                        unfold not; intros t4 t4LtT'; assert (t4LtTp: t4 < tp) by omega;
                                                                        generalize norecvmc t4LtTp; clear; firstorder).
      apply (cRespResp tc t'' t' t'Let mc msendmc m sendm recvm t''GtTc); intuition.
      assert (opts: S t'' = tc \/ S t'' < tc) by omega.
      destruct opts as [St''EqTc | St''LtTc].
      assert (H: state c a (S t'') = state c a tc) by auto.
      apply (slt_neq H stTcGtStST'').
      pose proof (whenChildHigh St''LtTc stTcGtStST'') as [ts [cond [s [recvs _]]]].
      pose proof (recvImpMark recvs) as [tsr [tsrLeTs sends]].
      assert (opts: tsr = t' \/ tsr > t' \/ tsr < t') by omega.
      destruct opts as [tsrEqT' | [tsrGtT' | tsrLtT']].
      rewrite tsrEqT' in *.
      apply (noSendmRecvm dt sends recvm).
      assert (t2LeTsr: t2 <= tsr) by omega.
      pose proof (pReqResp isParent noTwoPResp noTwoPReqNon sendr1 sends recvs t2LeTsr) as [tf [tfLtTs recv'r1]].
      assert (tfLtTc: tf < tc) by omega.
      pose proof (uniqRecv2 recvr1 recv'r1) as tcEqTf.
      omega.
      assert (t''LeT: t'' <= t) by omega.
      assert (tsrLeT: tsr <= t) by omega.
      assert (one: forall tc', tc' < t'' -> ~ recv mch p c a tc' s) by (
                                                                        unfold not; intros tc' tc'LtT'' recv's; pose proof (uniqRecv2 recvs recv's) as tc'EqT';
                                                                        rewrite tc'EqT' in *; omega).
      assert (two: forall tp', tp' < tsr -> ~ recv mch c p a tp' m) by (
                                                                        unfold not; intros tp' tp'LtTsr recv'm; pose proof (uniqRecv2 recvm recv'm) as tp'EqTsr;
                                                                        omega).
      apply (cross t'' tsr t''LeT tsrLeT  m sendm s sends one two).

      constructor.
      intuition.

      intros t1 t2 t3 t3LeSt m msendm r rsendr rrecvr t1LeT2 neg.
      unfold Time in *.
      assert (eqOrNot: t1 = t2 \/ t1 < t2) by omega.
      destruct eqOrNot as [t1EqT2 | t1LtT2].
      rewrite t1EqT2 in *.
      pose proof (uniqMark1 msendm rsendr) as mEqR; omega.
      clear t1LeT2.
      pose proof (recvImpMark rrecvr) as [t' [t'LeT3 rsend'r]].
      pose proof (uniqMark2 rsendr rsend'r) as t2EqT'.
      rewrite <- t2EqT' in *.
      clear rsend'r t2EqT'.
      assert (t1LeT: t1 <= t) by omega.
      pose proof (cons t1 t1LeT) as st1Ledt1.

      assert (notty1: ~ exists t'', t1 <= t'' < t2 /\ exists m, recv mch p c a t'' m /\ sle (state c a t2) (to m)) by (
                                                                                                                  unfold not; intros [t'' [cond [m0 [mrecvm0 _]]]];
                                                                                                                  pose proof (recvImpMark mrecvm0) as [t5 [t5LeT'' msendm0]];
                                                                                                                  assert (one: forall tc', tc' < t1 -> ~ recv mch p c a tc' m0) by (
                                                                                                                                                                                    unfold not; intros tc' tc'LtT1 mrecvM0Tc';
                                                                                                                                                                                    pose proof (uniqRecv2 mrecvm0 mrecvM0Tc') as t''EqTc';
                                                                                                                                                                                    rewrite <- t''EqTc' in *; omega);
                                                                                                                  assert (two: forall tp', tp' < t5 -> ~ recv mch c p a tp' m) by (
                                                                                                                                                                                   unfold not; intros tp' tp'LtT5; assert (t5LtT3: tp' < t3) by omega; firstorder);
                                                                                                                  assert (t5Let: t5 <= t) by omega;
                                                                                                                  apply (cross t1 t5 t1LeT t5Let m msendm m0 msendm0 one two)).
      assert (notty: ~ exists t'', S t1 <= t'' < t2 /\ exists m, recv mch p c a t'' m /\ sle (state c a t2) (to m)) by (
                                                                                                                   clear cRespResp;
                                                                                                                   unfold not; intros [t'' [cond ex]];
                                                                                                                   assert (cond2: t1 <= t'' < t2) by omega;
                                                                                                                   generalize notty1 cond2 ex; clear; firstorder).
      
      assert (notst2Gtst1: ~ sgt (state c a t2) (state c a (S t1))) by (
      
        clear cRespResp;
        clear notty1; assert (eqOrNot: S t1 = t2 \/ S t1 < t2) by omega;
        destruct eqOrNot as [eq| St1LtT2]; [
        assert (H: state c a (S t1) = state c a t2) by auto;
        apply (slt_neq H) |
          unfold not; intros st; pose proof (whenChildHigh St1LtT2 st) as some; firstorder]).
      assert (stt2LestT1: sle (state c a t2) (state c a (S t1))) by (apply (not_slt_sle notst2Gtst1)).
      pose proof (recvmCond isParent rrecvr) as fromRLe.
      pose proof (sendmFrom st rsendr) as fromREq.
      pose proof (sendmImpSt isParent msendm) as stGt.
      pose proof (sendmChange st msendm) as stEq.
      rewrite fromREq, <- stEq in *.
      assert (drGt: slt (dir p c a t3) (dir p c a t1)) by
          (rewrite fromRLe in stt2LestT1;
           unfold slt in *; unfold sle in *; destruct (dir p c a t3);
           destruct (state c a (S t1));
           destruct (dir p c a t1); destruct (state c a t1);
           auto).
      assert (drNe: dir p c a t1 <> dir p c a t3) by
          (unfold not; intros X; assert (Y: dir p c a t3 = dir p c a t1) by auto;
           pose proof (slt_neq Y); auto).
      assert (sendRecv: ~ forall tn, t1 <= tn < t3 -> (forall m, ~ mark mch p c a tn m) /\
                                                      (forall m, ~ recv mch c p a tn m)) by (
                                                                                             unfold not; intros exp; assert (t1LtT3: t1 < t3) by omega; pose proof (noChange dt t1LtT3 exp); firstorder).
      assert (noSend: forall tn, t1 <= tn < t3 -> forall m, ~ mark mch p c a tn m) by (
                                                                                       clear cRespResp;
                                                                                       unfold not; intros tn cond m0 msendm0;
                                                                                       assert (tnLeT: tn <= t) by omega;
                                                                                       assert (one: forall tc', tc' < t1 -> ~ recv mch p c a tc' m0) by (
                                                                                                                                                         unfold not; intros tc' tc'LtT1 mrecvm0;
                                                                                                                                                         pose proof (recvImpMark mrecvm0) as [tm [tmLeTc' msend'm0]];
                                                                                                                                                         pose proof (uniqMark2 msendm0 msend'm0) as tmEqTc';
                                                                                                                                                         rewrite <- tmEqTc' in *; omega);
                                                                                       assert (two: forall tp', tp' < tn -> ~ recv mch c p a tp' m) by (
                                                                                                                                                        unfold not; intros tp' tp'LtTn; assert (tp'LtT3: tp' < t3) by omega; firstorder);
                                                                                       apply (cross t1 tn t1LeT tnLeT m msendm m0 msendm0 one two)).

      destruct (classical (exists tn, tn < t3 /\ t1 <= tn /\ exists m0, recv mch c p a tn m0)) as [ext|noEx].
      pose proof (maxExists' classical ext) as [tn [cond [[tnLtT3 [m0 mrecvm0]] notAfter]]].
      
      pose proof (recvImpMark mrecvm0) as [tr [trLeTn msendm0]].
      assert (opts: tr = t1 \/ tr > t1 \/ tr < t1) by omega.
      destruct opts as [trEqT1 | [trGtT1 | trLtT1]].
      rewrite trEqT1 in *.
      pose proof (uniqMark1 msendm msendm0) as mEqm0.
      rewrite <- mEqm0 in *.
      generalize neg cond mrecvm0; clear; firstorder.
      assert (tnLeT: tn <= t) by omega.
      assert (cond2: forall t4, t4 < tn -> ~ recv mch c p a t4 m) by (
                                                                      intros t4 t4LtTn; assert (t4LtT3: t4 < t3) by omega;
                                                                      generalize neg t4LtT3; clear; firstorder).
      apply (cRespResp t1 tr tn tnLeT m msendm m0 msendm0 mrecvm0 trGtT1 cond2).
      assert (notty2': ~ exists t'', tr <= t'' < t1 /\ exists m, recv mch p c a t'' m /\ sle (state c a t1) (to m)) by (
                                                                                                                   unfold not; intros [t'' [cond2 [m1 [mrecvm1 _]]]];
                                                                                                                   pose proof (recvImpMark mrecvm1) as [t5 [t5LeT'' msendm1]];
                                                                                                                   assert (trLeT: tr <= t) by omega;
                                                                                                                   assert (t5LeT: t5 <= t) by omega;
                                                                                                                   assert (one: forall tc', tc' < tr -> ~ recv mch p c a tc' m1) by (
                                                                                                                                                                                     unfold not; intros tc' tc'LtTr mrecv'm1;
                                                                                                                                                                                     pose proof (uniqRecv2 mrecvm1 mrecv'm1) as t''EqTc';
                                                                                                                                                                                     rewrite <- t''EqTc' in *;
                                                                                                                                                                                       omega);
                                                                                                                   assert (two: forall tp', tp' < t5 -> ~ recv mch c p a tp' m0) by (
                                                                                                                                                                                     unfold not; intros tp' tp'LtT5 mrecv'm0;
                                                                                                                                                                                     pose proof (uniqRecv2 mrecvm0 mrecv'm0) as tnEqTp';
                                                                                                                                                                                     rewrite <- tnEqTp' in *; omega);
                                                                                                                   apply (cross tr t5 trLeT t5LeT m0 msendm0 m1 msendm1 one two)).
      assert (notty2: ~ exists t'', S tr <= t'' < t1 /\ exists m, recv mch p c a t'' m /\ sle (state c a t1) (to m)) by (
                                                                                                                    unfold not; intros [t'' [cond1 rest]]; assert (cond2: tr <= t'' < t1) by omega;
                                                                                                                    generalize notty2' cond2 rest; clear; firstorder).
      assert (strLeT1: S tr <= t1) by omega.
      pose proof (whenChildHighConv strLeT1 notty2) as st1LeTr.
      pose proof (whenChildHighConv t1LtT2 notty) as sST1LeT2.
      assert (trLtT3: tr < t3) by omega.
      assert (noC: forall tn0, S tn <= tn0 < t3 -> (forall m, ~ mark mch p c a tn0 m) /\
                                                   (forall m, ~ recv mch c p a tn0 m)) by (
                                                                                           intros tn0 cond2;
                                                                                           constructor; [assert (cond3: t1 <= tn0 < t3) by omega; generalize noSend cond3; clear; firstorder|
                                                                                                         assert (cond4: tn < tn0 < t3) by omega; 
                                                                                                           assert (t1LeTn0: t1 <= tn0) by omega; generalize cond4 t1LeTn0 notAfter; clear; firstorder]).
      assert (sTnLtT3: S tn <= t3) by omega.
      pose proof (noChange2 dt sTnLtT3 noC) as dirEq.
      generalize st1LeTr isParent sST1LeT2 sTnLtT3 dirEq rsendr rrecvr msendm msendm0 mrecvm0; clear; intros.
      pose proof (sendmChange st msendm) as sEqTom.
      pose proof (sendmImpSt isParent msendm) as sGtTom.
      pose proof (recvmChange dt mrecvm0) as dSEqTom0.
      pose proof (sendmChange st msendm0) as sSEqTom0.
      pose proof (recvmCond isParent rrecvr) as dLeFromr.
      pose proof (sendmFrom st rsendr) as sEqFromr.
      rewrite sEqFromr in dLeFromr.
      rewrite <- dirEq in dLeFromr.
      rewrite <- sSEqTom0 in  dSEqTom0.
      rewrite dSEqTom0 in dLeFromr.
      rewrite <- sEqTom in sGtTom.
      rewrite dLeFromr in sST1LeT2.
      unfold sle in *; unfold slt in *; destruct (state c a t1); destruct (state c a (S tr));
      destruct (state c a (S t1)); auto.
      generalize sendRecv noSend noEx; clear; firstorder.
    Qed.

    Theorem conservative: forall a t, sle (state c a t) (dir p c a t).
    Proof.
      intros a t.
      pose proof (@mainInd a t) as [first _].
      assert (tLeT: t <= t) by omega; firstorder.
    Qed.

    Lemma cRespFifo: forall {a t1 t2 t3 m1 m2}, mark mch c p a t1 m1 -> mark mch c p a t2 m2 ->
                                                recv mch c p a t3 m2 -> t1 < t2 -> (forall t4, t4 < t3 -> ~ recv mch c p a t4 m1) -> False.
    Proof.
      intros a t1 t2 t3 m1 m2 sendm1 sendm2 recvm2 t1LtT2.
      pose proof (@mainInd a t3) as [_ [_ [_ last]]].
      specialize (last t1 t2 t3).
      assert (t3LeT3: t3 <= t3) by omega.
      firstorder.
    Qed.

    Lemma cross: forall {a t1 t2 m1 m2}, mark mch c p a t1 m1 -> mark mch p c a t2 m2 ->
                                         (forall t3, t3 < t1 -> ~ recv mch p c a t3 m2) -> (forall t4, t4 < t2 -> ~ recv mch c p a t4 m1) -> False.
      intros a t1 t2 m1 m2 sendm1 sendm2 one two.
      assert (opts: t1 <= t2 \/ t1 > t2) by omega.
      destruct opts as [t1LeT2 | t2LtT1].
      assert (t2LeT2: t2 <= t2) by omega.
      pose proof (@mainInd a t2) as [_ [sec _]].
      apply (sec t1 t2 t1LeT2 t2LeT2 m1 sendm1 m2 sendm2 one two).
      assert (t2LeT1: t2 <= t1) by omega.
      assert (t1LeT1: t1 <= t1) by omega.
      pose proof (@mainInd a t1) as [_ [sec _]].
      apply (sec t1 t2 t1LeT1 t2LeT1 m1 sendm1 m2 sendm2 one two).
    Qed.

    Theorem cReqRespSent: forall {a t1 t2 r}, mark rch p c a t1 r -> recv rch p c a t2 r ->
                                              sle (state c a t2) (to r) -> exists t3, t3 < t2 /\ exists m, mark mch c p a t3 m /\ sle (to m) (to r) /\
                                                                                                      (forall t4, t4 < t1 -> ~ recv mch c p a t4 m).
    Proof.
      intros a t1 t2 r sendr recvr toRGestT2.
      destruct (classical (exists t3, t3 < t2 /\ exists m, mark mch c p a t3 m /\ sle (to m) (to r) /\ forall t4,
                                                                                                    t4 < t1 -> ~ recv mch c p a t4 m)) as [easy|hard].
      intuition.
      pose proof (recvImpMark recvr) as [t1' [t1LeT2 send'r]].
      pose proof (uniqMark2 sendr send'r) as t1'EqT1.
      rewrite <- t1'EqT1 in *.
      clear t1'EqT1 send'r t1'.

      destruct (classical (exists t, t < t1 /\ ((exists m, recv mch c p a t m) \/
                                                (exists m, mark mch p c a t m)))) as [ex | notEx].
      pose proof (maxExists' classical ex) as [t [tLtT1 [sendOrRecv notAfter]]].
      assert (nothing: forall y, S t <= y < t1 -> (forall m, ~ mark mch p c a y m) /\
                                                  (forall m, ~ recv mch c p a y m)) by
          (intros y cond; assert (cond2: t < y < t1)by omega; generalize cond2 notAfter; clear; firstorder).
      pose proof (noChange2 dt tLtT1 nothing) as dirEq.
      clear nothing.
      destruct sendOrRecv as [[m recvm] | [m sendm]].
      pose proof (recvImpMark recvm) as [t' [t'LeT sendm]].
      assert (noCRecv: forall tm, t' <= tm < t2 -> forall m', ~ recv mch p c a tm m') by (
                                                                                          unfold not; intros tm cond m' recvm';
                                                                                          pose proof (recvImpMark recvm') as [ts [tsLeTm sendm']];
                                                                                          assert (opts: ts < t \/ ts = t \/ t < ts < t1 \/ t1 <= ts) by omega;
                                                                                          destruct opts as [tsLtT | [tsEqT | [tLtTsLtT1  | t1LeTs ]]]; [
                                                                                            assert (one: forall x, x < t' -> ~ recv mch p c a x m') by ( unfold not; intros x xLtT' recv'm';
                                                                                                                                                         pose proof (uniqRecv2 recvm' recv'm') as xEqTm; omega);
                                                                                            assert (two: forall x, x < ts -> ~ recv mch c p a x m) by (unfold not; intros x xLtTs recv'm;
                                                                                                                                                       pose proof (uniqRecv2 recvm recv'm) as xEqTs; omega);
                                                                                            apply (cross sendm sendm' one two) |
                                                                                            rewrite tsEqT in *;
                                                                                              apply (noSendmRecvm dt sendm' recvm) |
                                                                                            generalize notAfter tLtTsLtT1 sendm'; clear; firstorder |
                                                                                            pose proof (pReqResp isParent noTwoPResp noTwoPReqNon sendr sendm' recvm' t1LeTs) as [t4 [t4LtTm recv'r]];
                                                                                              pose proof (uniqRecv2 recvr recv'r) as t4EqT2; omega]).
      destruct (classical (exists ts, ts < t2 /\ t' < ts /\ exists m', mark mch c p a ts m'))
        as [ ex2 | notEx2].
      pose proof (maxExists' classical ex2) as [ts [tsLtT2 [[t'LtTs [m' sendm']] notAfter2]]].
      assert (nothing: forall y, S ts <= y < t2 ->
                                 (forall m, ~ mark mch c p a y m) /\ (forall m, ~ recv mch p c a y m)) by
          (intros y cond; assert (cond1: t' < y < t2) by omega; assert (cond2: t' <= y < t2) by omega;
           generalize notAfter2 noCRecv cond cond1 cond2; clear; firstorder).
      pose proof (noChange2 st tsLtT2 nothing) as stEq.
      destruct (classical (exists tr, tr < t1 /\ recv mch c p a tr m')) as [ [tr [trLtT1 recvm']] | noRecv].
      assert (opts: tr < t \/ tr = t \/ t < tr < t1) by omega.
      destruct opts as [trLtT | [trEqT | cond]].
      assert (forall t4, t4 < tr -> ~ recv mch c p a t4 m) by (
                                                               unfold not; intros t4 t4LtTr recv'm; pose proof (uniqRecv2 recvm recv'm) as t4EqT; omega).
      pose proof (cRespFifo sendm sendm' recvm' t'LtTs). intuition.
      rewrite trEqT in *.
      pose proof (uniqRecv1 recvm recvm') as mEqM'.
      rewrite mEqM' in *.
      pose proof (uniqMark2 sendm sendm') as t'EqTs.
      omega.
      generalize notAfter cond recvm'; clear; firstorder.
      assert (opts: sle (to m') (to r) \/ slt (to r) (to m')).
      unfold sle in *; unfold slt in *; destruct (to m'); destruct (to r); auto.
      destruct opts as [toM'LeToR | toM'GtToR].
      generalize tsLtT2 sendm' toM'LeToR noRecv; clear; firstorder.
      pose proof (sendmChange  st sendm') as stEqToM'.
      rewrite stEqToM' in stEq.
      rewrite <- stEq in toRGestT2.
      pose proof (slt_slei_false toM'GtToR toRGestT2) as f.
      firstorder.
      assert (nothing: forall y, S t' <= y < t2 ->
                                 (forall m, ~ mark mch c p a y m) /\ (forall m, ~ recv mch p c a y m)) by
          (intros y cond; assert (cond2: t' <= y < t2) by omega;
           generalize notEx2 noCRecv cond cond2; clear; firstorder).
      assert (t'LeT2: S t' <= t2) by omega.
      pose proof (noChange2 st t'LeT2 nothing) as stEq.
      pose proof (sendrImpSt dt sendr) as toRLtD.
      pose proof (sendmChange  st sendm) as st1.
      pose proof (recvmChange dt recvm) as st2.
      rewrite dirEq in st2.
      rewrite <- st2 in st1.
      rewrite st1 in stEq.
      rewrite stEq in toRLtD.
      pose proof (slt_slei_false toRLtD toRGestT2) as f.
      firstorder.

      assert (tLeT1: t <= t1) by omega.
      pose proof (pRespReq isParent noTwoPResp noTwoPReqNon sendm sendr recvr tLeT1) as [t' [t'LtT2 recvm]].
      pose proof (recvImpMark recvm) as [t'' [tLeT' send'm]].
      pose proof (uniqMark2 sendm send'm) as t''EqT.
      rewrite <- t''EqT in *. clear t''EqT t'' send'm.
      assert (noCRecv: forall tm, t' < tm < t2 -> forall m', ~ recv mch p c a tm m').
      unfold not; intros tm cond m' recvm';
      pose proof (recvImpMark recvm') as [ts [tsLeTm sendm']];
      assert (opts: ts < t \/ ts = t \/ t < ts < t1 \/ t1 <= ts) by omega;
      destruct opts as [tsLtT | [tsEqT | [tLtTsLtT1  | t1LeTs ]]]; [
        pose proof (sendmImpRecvr isParent sendm) as [r' recvr'];
        pose proof (recvImpMark recvr') as [tx [txLeT sendr']];
        assert (one: forall t3, t3 < tx -> ~ recv mch p c a t3 m') by (
                                                                       unfold not; intros t3 t3LtTx recv'm'; pose proof (uniqRecv2 recvm' recv'm') as t3EqTr;
                                                                       omega);
        assert (two: forall t4, t4 <= ts -> ~ recv rch c p a t4 r') by (
                                                                        unfold not; intros t4 t4LeTs recv'r'; pose proof (uniqRecv2 recvr' recv'r') as t4EqTs;
                                                                        omega);
        apply (cReqPRespCross sendr' sendm' one two)|
        rewrite tsEqT in *; pose proof (uniqMark1 sendm sendm') as mEqM'; rewrite mEqM' in *;
        pose proof (uniqRecv2 recvm recvm') as trEqT'; omega |
        generalize notAfter tLtTsLtT1 sendm'; clear; firstorder |
        pose proof (pReqResp isParent noTwoPResp noTwoPReqNon sendr sendm' recvm' t1LeTs) as [t4 [t4LtTm recv'r]];
          pose proof (uniqRecv2 recvr recv'r) as t4EqT2; omega].
      
      destruct (classical (exists ts, ts < t2 /\ t' < ts /\ exists m', mark mch c p a ts m'))
        as [ ex2 | notEx2].
      pose proof (maxExists' classical ex2) as [ts [tsLtT2 [[t'LtTs [m' sendm']] notAfter2]]].
      assert (nothing: forall y, S ts <= y < t2 ->
                                 (forall m, ~ mark mch c p a y m) /\ (forall m, ~ recv mch p c a y m)) by
          (intros y cond; assert (cond1: t' < y < t2) by omega;
           generalize notAfter2 noCRecv cond cond1; clear; firstorder).
      pose proof (noChange2 st tsLtT2 nothing) as stEq.
      destruct (classical (exists tr, tr < t1 /\ recv mch c p a tr m')) as [ [tr [trLtT1 recvm']] | noRecv].
      pose proof (recvImpMark recvm') as [ts' [ts'LeTr send'm']].
      pose proof (uniqMark2 send'm' sendm') as ts'EqTs.
      assert (trGtT: tr > t) by omega.
      clear ts' ts'LeTr send'm' ts'EqTs.
      assert (opts: t < tr < t1 \/ t1 <= tr) by omega.
      destruct opts as [cond1 | t1LeTr].
      generalize cond1 notAfter recvm'; clear; firstorder.
      assert (opts: sle (to m') (to r) \/ slt (to r) (to m')) by
          (unfold sle; unfold slt; destruct (to m'); destruct (to r); auto).
      destruct opts as [toM'LeToR | toM'GtToR].
      assert (noRecv: forall t4, t4 < t1 -> ~ recv mch c p a t4 m') by
          (
            unfold not; intros t4 t4LtT1 recv'm';
            pose proof (uniqRecv2 recvm' recv'm') as t4EqTr; omega).
      generalize tsLtT2 sendm' toM'LeToR noRecv; clear; firstorder.
      pose proof (sendmChange st sendm') as stEqToM'.
      omega.
      assert (last: forall t4, t4 < t1 -> ~ recv mch c p a t4 m') by (generalize noRecv; clear; firstorder).
      assert (opts: sle (to m') (to r) \/ slt (to r) (to m')) by
      (unfold sle; unfold slt; destruct (to m'); destruct (to r); auto).
      destruct opts as [toM'LeToR | toM'GtToR].
      generalize last tsLtT2 toM'LeToR sendm'; clear; firstorder.
      pose proof (sendmChange st sendm') as stEqToM'.
      rewrite stEqToM' in stEq.
      rewrite stEq in toM'GtToR.
      pose proof (slt_slei_false toM'GtToR  toRGestT2) as f.
      firstorder.
      assert (nothing: forall y, S t' <= y < t2 ->
                                 (forall m, ~ mark mch c p a y m) /\ (forall m, ~ recv mch p c a y m)) by
          (generalize noCRecv notEx2; clear; firstorder).
      pose proof (noChange2 st t'LtT2 nothing) as stEq.
      pose proof (recvmChange st recvm) as st1.
      pose proof (sendmChange dt sendm) as d1.
      pose proof (sendrImpSt dt sendr) as d2.
      rewrite stEq in st1; rewrite <- st1 in d1; rewrite d1 in dirEq; rewrite <- dirEq in d2.
      pose proof (slt_slei_false d2 toRGestT2) as f.
      firstorder.
      assert (cNoRecv: forall t4, t4 < t2 -> forall m, ~ recv mch p c a t4 m) by (
                                                                                  unfold not; intros t4 t4LtT2 m recvm; pose proof (recvImpMark recvm) as [t3 [t3LeT4 sendm]];
                                                                                  assert (opts: t3 < t1 \/ t3 >= t1) by omega;
                                                                                  destruct opts as [t3LtT1 | t4GeT1]; [
                                                                                    generalize notEx t3LtT1 sendm; clear; firstorder;
                                                                                    intuition |
                                                                                    pose proof (pReqResp isParent noTwoPResp noTwoPReqNon sendr sendm recvm t4GeT1) as [t5 [t4LtT4 recv'r]];
                                                                                      pose proof (uniqRecv2 recvr recv'r) as t5EqT2; omega]).
      destruct (classical (exists t3, t3 < t2 /\ exists m, mark mch c p a t3 m)) as [ex2 | notEx2].
      pose proof (maxExists' classical ex2) as [ts [tsLtT2 [[m' sendm'] notAfter2]]].
      assert (nothing: forall y, S ts <= y < t2 ->
                                 (forall m, ~ mark mch c p a y m) /\ (forall m, ~ recv mch p c a y m)) by
          (intros y cond;
           generalize notAfter2 cNoRecv cond; clear; firstorder).
      pose proof (noChange2 st tsLtT2 nothing) as stEq.
      destruct (classical (exists tr, tr < t1 /\ recv mch c p a tr m')) as [ [tr [trLtT1 recvm']] | noRecv].
      generalize notEx trLtT1 recvm'; clear; firstorder.
      assert (opts: sle (to m') (to r) \/ slt (to r) (to m')) by
          (unfold sle; unfold slt; destruct (to r); destruct (to m'); auto).
      destruct opts as [toM'LeToR | toM'GtToR].
      generalize toM'LeToR noRecv tsLtT2 sendm'; clear; firstorder.
      pose proof (sendmChange st sendm') as stEqToM'.
      rewrite stEq in stEqToM'; rewrite <- stEqToM' in toM'GtToR.
      pose proof (slt_slei_false toM'GtToR toRGestT2) as f.
      firstorder.
      assert (nothing1: forall y, 0 <= y < t2 ->
                                  (forall m, ~ mark mch c p a y m) /\ (forall m, ~ recv mch p c a y m)) by
          (generalize cNoRecv notEx2; clear; firstorder).
      assert (x1: 0 <= t2) by omega.
      pose proof (noChange2 st x1 nothing1) as st1.
      assert (nothing2: forall y, 0 <= y < t1 ->
                                  (forall m, ~ mark mch p c a y m) /\ (forall m, ~ recv mch c p a y m)) by
          (generalize notEx; clear; firstorder).
      assert (x2: 0 <= t1) by omega.
      pose proof (noChange2 dt x2 nothing2) as d1.
      pose proof (@init p c isParent a) as start.
      pose proof (sendrImpSt dt sendr) as d2.
      rewrite d1 in start; rewrite <- start in st1; rewrite st1 in d2.
      pose proof (slt_slei_false d2 toRGestT2) as f.
      firstorder.
    Qed.

    Lemma vol: forall {a t}, forall {t1 r1}, mark rch p c a t1 r1 ->
                                             forall {t2 m2}, mark mch c p a t2 m2 ->
                                                             forall {t3}, t3 <= t -> t1 <= t3 -> recv mch c p a t3 m2 ->
                                                                          (forall {t4}, t4 <= t2 -> ~ recv rch p c a t4 r1) ->
                                                                          (forall {t5}, t1 < t5 <= t3 -> forall r, ~ mark rch p c a t5 r) ->
                                                                          forall r3, recv rch p c a t2 r3 -> slt (to r3) (state c a t2) -> False.
    Proof.
      intros a.
      induction t.
      intros t1 r1 sendr1 t2 m2 sendm2 t3 t3LeT t1LeT3 recvm2 notRecvr1 notSendr r3
             recvr3 toR3LtStT2.
      unfold Time in *.
      pose proof (ch.recvImpMark recvm2) as [t' [t'LeT3 send'm2]].
      pose proof (ch.uniqMark2 sendm2 send'm2) as t'EqT2.
      assert (t3Eq0: t3 = 0) by omega.
      assert (t2Eq0: t2 = 0) by omega.
      assert (t1Eq0: t1 = 0) by omega.
      rewrite t3Eq0, t2Eq0, t1Eq0 in *; clear t' t'LeT3 send'm2 t'EqT2 t1Eq0
                                              t2Eq0 t3Eq0 t3LeT t1LeT3.
      pose proof (ch.recvImpMark recvr3) as [t' [t'Le0 send'r3]].
      assert (t'Eq0: t' = 0) by omega; rewrite t'Eq0 in *.
      pose proof (ch.uniqMark1 sendr1 send'r3) as r1EqR3.
      rewrite r1EqR3 in *.
      firstorder.

      intros t1 r1 sendr1 t2 m2 sendm2 t3 t3LeT t1LeT3 recvm2 notRecvr1 notSendr r3
             recvr3 toR3LtStT2.
      unfold Time in *.
      pose proof (ch.recvImpMark recvm2) as [t' [t2LeT3 send'm2]].
      pose proof (ch.uniqMark2 sendm2 send'm2) as t'EqT2.
      rewrite <- t'EqT2 in *; clear send'm2 t' t'EqT2.
      pose proof (ch.recvImpMark recvr3) as [ts [tsLeT2 sendr3]].
      assert (opts: ts > t3 \/ t1 < ts <= t3 \/ ts = t1 \/ ts < t1) by omega.
      destruct opts as [tsGtT3 | [cond | [tsEqT1 | tsLtT1]]].
      omega.
      generalize notSendr cond sendr3; clear; firstorder.
      assert (t2LeT2: t2 <= t2) by omega.
      rewrite tsEqT1 in *. pose proof (ch.uniqMark1 sendr3 sendr1) as r1EqR3.
      rewrite r1EqR3 in *.
      generalize notRecvr1 t2LeT2 recvr3; clear; firstorder.
      pose proof (sendrImpNoSendr dt tsLtT1 sendr3 sendr1) as exist. 
      destruct exist as [tx [cond dirLt']].
      (*    pose proof (minExists classical exist) as [tx [[cond dirLt'] notBefore]]. *)
      assert (dirLt: sle (dir p c a tx) (to r3)) by
          ( unfold slt in *; unfold sle in *; destruct (to r3); destruct (dir p c a tx);
            destruct (state c a t2); auto).
      clear dirLt'.
      pose proof (sendrImpSt dt sendr3) as gt.
      assert (dirGt: slt (dir p c a tx) (dir p c a ts)) by
          (unfold sle in *; unfold slt in *; destruct (dir p c a ts); destruct (dir p c a tx);
           destruct (to r3); auto).
      destruct (classical (exists tn, ts <= tn < tx /\ ((exists m, mark mch p c a tn m) \/
                                                        (exists m, recv mch c p a tn m /\ sle (to m) (to r3))))) as [sth|notExist].
      destruct (minExists classical sth) as [tn [[cond2 sendOrRecv] notBefore]].
      (* destruct sth as [tn [cond2 sendOrRecv]]. *)
      destruct sendOrRecv as [[m sendm] | [m [recvm toMLeToR3]]].
      assert (opts: ts = tn \/ ts < tn) by omega.
      destruct opts as [tsEqTn | tsLtTn].
      rewrite tsEqTn in *.
      apply (noSendmSendr dt sendm sendr3).
      pose proof (sendrImpNoSendm isParent tsLtTn sendr3 sendm) as [t' [cond3 [m' [recvm' toM'LeToR3]]]].
      assert (cond4: ts <= t' < tx) by omega.
      assert (cond5: t' < tn) by omega.
      generalize notBefore recvm' toM'LeToR3 cond4 cond5; clear; firstorder.
      pose proof (ch.recvImpMark recvm) as [t'' [t''Letn sendm]].
      assert (opts: t'' > t2 \/ t'' = t2 \/ t'' < t2) by omega.
      destruct opts as [t''GtT2 | [t''EqT2 | t''LtT2]].
      assert (notRecv: forall tq, tq < tn -> ~ recv mch c p a tq m2) by (
                                                                         unfold not; intros tq tqLtTn recvq;
                                                                         pose proof (ch.uniqRecv2 recvq recvm2) as tqEqT'';
                                                                         omega).
      apply (cRespFifo sendm2 sendm recvm t''GtT2 notRecv).
      rewrite t''EqT2 in *.
      pose proof (ch.uniqMark1 sendm sendm2) as mEqM2.
      rewrite mEqM2 in *.
      pose proof (ch.uniqRecv2 recvm recvm2) as t3EqTn.
      omega.
      assert (nothing: forall ty, t'' <= ty < t2 -> forall q, ~ recv mch p c a ty q).
      unfold not; intros ty cond3 q recvq.
      assert (opts: t'' = ty \/ t'' < ty) by omega.
      destruct opts as [t''EqTy | t''LtTy].
      rewrite t''EqTy in *.
      apply (noSendmRecvm st sendm recvq).
      pose proof (ch.recvImpMark recvq) as [tz [tzLeTy sendq]].
      assert (opts: tz < ts \/ tz = ts \/ tz > ts) by omega.
      destruct opts as [tzLtTs | [tzEqTs | tzGtTs]].
      assert (tzLtT1: tz < t1) by omega.
      assert (one: forall t0, t0 < t'' -> ~ recv mch p c a t0 q) by (
                                                                     unfold not; intros t0 t0LtT'' recv'q;
                                                                     pose proof (ch.uniqRecv2 recvq recv'q) as t0EqTz;
                                                                     omega).
      assert (two: forall t0, t0 < tz -> ~ recv mch c p a t0 m) by (
                                                                    unfold not; intros t0 t0LtTz recv'm;
                                                                    pose proof (ch.uniqRecv2 recvm recv'm); omega).
      apply (cross sendm sendq one two).
      rewrite tzEqTs in *.
      apply (noSendmSendr dt sendq sendr3).
      pose proof @pReqResp.
      assert (tsLeTz: ts <= tz) by omega.
      pose proof (pReqResp isParent noTwoPResp noTwoPReqNon sendr3 sendq recvq tsLeTz) as sth2.
      destruct sth2 as [t4 [t4LtTy recv'r3]].
      pose proof (ch.uniqRecv2 recvr3 recv'r3); omega.
      assert (nothing2: forall ty, S t'' <= ty < t2 -> forall q, ~ recv mch p c a ty q) by (
                                                                                            intros ty cond4; assert (h: t'' <= ty < t2) by omega; generalize h nothing; clear;
                                                                                            firstorder).
      assert (nothing3: ~ exists ty, S t'' <= ty < t2 /\ exists q, recv mch p c a ty q /\
                                                                   sle (state c a t2) (to q)) by (generalize nothing2; clear; firstorder).
      pose proof (whenChildHighConv t''LtT2 nothing3) as stLe.
      assert (contra: ~ exists tk, tk < tn /\ ts <= tk /\ exists m, mark mch p c a tk m) by (
                                                                                             unfold not; intros [tk [tkLtTn [tsLeTk rest]]]; assert (h: ts <= tk < tx) by omega;
                                                                                             generalize notBefore h tkLtTn tsLeTk rest; clear; firstorder).
      assert (tsLeTn: ts <= tn) by omega.
      assert (contra2: ~ sgt (dir p c a tn) (dir p c a ts)) by (unfold not; intros sttt;
                                                          pose proof (whenDirLow tsLeTn sttt) as sth3; generalize contra sth3; clear; firstorder).
      pose proof (not_slt_sle contra2) as good.
      pose proof (sendmChange st sendm) as eq1.
      pose proof (recvmChange dt recvm) as eq2.
      pose proof (sendmImpSt isParent sendm) as eq3.
      pose proof (sendmFrom st sendm) as eq4.
      pose proof (recvmCond isParent recvm) as eq5.
      generalize good eq1 eq2 eq3 eq4 eq5 toR3LtStT2 toMLeToR3 stLe.
      clear; intros.
      rewrite <- eq1 in *; clear eq1.
      rewrite <- eq2 in *; clear eq2.
      rewrite eq4 in *; clear eq4.
      rewrite eq5 in *; clear eq5.
      assert (trans: sle (state c a t2) (to r3)) by
          (
            unfold sle in *; destruct (state c a t2); destruct (to r3); destruct (dir p c a (S tn)); auto).
      pose proof (slt_slei_false toR3LtStT2 trans) as f.
      firstorder.
      assert (tsLeTx: ts <= tx) by omega.
      pose proof (sendrFrom dt sendr3).
      pose proof (sendrImpSt dt sendr3).
      pose proof (dirCantGoLower H0 tsLeTx notExist).
      pose proof (slt_slei_false H1 dirLt) as f.
      intuition.
    Qed.

    Lemma pReqsCVolRespReqLt: forall {t a t1 t2 r1 r2}, t1 <= t -> t2 <= t ->
                                                        mark rch p c a t1 r1 ->
                                                        mark rch p c a t2 r2 -> t1 < t2 ->
                                                        (forall ts, t1 < ts < t2 -> forall r, ~ mark rch p c a ts r) ->
                                                        (forall ts, t1 < ts < t2 -> forall m, ~ mark mch p c a ts m) ->
                                                        (forall t3, t3 <= t -> ~ recv rch p c a t3 r1) ->
                                                        (forall t4, t4 <= t -> ~ recv rch p c a t4 r2) -> exists t5 m, mark mch c p a t5 m /\
                                                                                                                       exists t6, t1 <= t6 < t2 /\ recv mch c p a t6 m /\ 
                                                                                                                                  (forall r, recv rch p c a t5 r -> sle (state c a t5) (to r)) /\ slt (to r2) (to m).
    Proof.
      intros t a t1 t2 r1 r2 t1LeT t2LeT sendr1 sendr2 t1LtT2 noSendR noSendM noRecvR1 noRecvR2.
      pose proof (sendrImpNoSendr dt t1LtT2 sendr1 sendr2) as ex1.
      assert (ex2: exists t', t' <= t2 /\ t1 < t' /\ ~ slt (to r1) (dir p c a t')) by
          firstorder.
      pose proof (maxExists classical ex2) as [t' [t'LeT2 [[t1LtT' dir1] notAfter1]]].
      pose proof (sendrImpSt dt sendr1) as dirSth.
      assert (sthMural: slt (dir p c a t') (dir p c a t1)) by
          (unfold slt in *; destruct (to r1) in *; destruct (dir p c a t1) in *;
           destruct (dir p c a t') in *; auto).
      pose proof (slt_neq' sthMural) as dirNotEq.
      destruct (classical (exists tn, tn < t' /\ t1 <= tn /\ ((exists m, mark mch p c a tn m) \/
                                                              exists m, recv mch c p a tn m))) as [ext|easy].
       pose proof (maxExists' classical ext) as [tn [tnLtT'[[t1LeTn sendOrRecv] notAfter]]].
      destruct sendOrRecv as [[m sendm] | [m recvm]].
      unfold Time in *.
      assert (opts: t1 = tn \/ t1 < tn) by omega.
      destruct opts as [t1EqTn | t1LtTn].
      rewrite t1EqTn in *.
      pose proof (noSendmSendr dt sendm sendr1) as false; firstorder.
      assert (tnLtT2: tn < t2) by omega.
      generalize noSendM t1LtTn tnLtT2 sendm; clear; firstorder.
      assert (tnLeTn: tn <= tn) by omega.
      pose proof (ch.recvImpMark recvm) as [tm [tmLeTn sendm]].
      assert (noRecv'R1: forall t4, t4 <= tm -> ~ recv rch p c a t4 r1) by (
                                                                            unfold not; intros t4 cond4 recvr1; assert (sth: t4 <= t) by omega;
                                                                            generalize noRecvR1 sth recvr1; clear; firstorder).
      assert (noSendAny: forall t5, t1 < t5 <= tn -> forall r, ~ mark rch p c a t5 r) by (
                                                                                          intros t5 cond4; assert (sth: t1 < t5 < t2) by omega; generalize noSendR sth;
                                                                                          clear; firstorder).
      pose proof (vol sendr1 sendm tnLeTn t1LeTn recvm noRecv'R1 noSendAny) as isVol.
      assert (isVolR: forall r3, recv rch p c a tm r3 -> sle (state c a tm) (to r3)) by
          (
            intros r3 recv'r3; specialize (isVol r3 recv'r3);
                               apply (not_slt_sle isVol)).
      assert (cond3: t1 <= tn < t2) by omega.
      assert (StnLeT': S tn <= t') by omega.
      assert (noChange: forall tx, S tn <= tx < t' -> (forall m, ~ mark mch p c a tx m) /\
                                                      forall m, ~ recv mch c p a tx m) by (intros tx cond2;
                                                                                           assert (cond4: tn < tx < t') by omega; assert (cond6: t1 <= tx) by omega;
                                                                                           generalize notAfter cond4 cond6; clear; firstorder).
      pose proof (noChange2 dt StnLeT' noChange) as dirEq1.
      assert (t'LeT1: t' <= t2) by omega.
      assert (contra: ~ sgt (dir p c a t2) (dir p c a t')) by (unfold not; intros d;
                                                         pose proof (whenDirLow t'LeT1 d) as [t'' [cond rest]];
                                                         assert (condn: t1 < t'' < t2) by omega; generalize noSendM condn rest; clear; firstorder).
      pose proof (not_slt_sle contra) as real.
      pose proof (recvmChange dt recvm) as eq1.
      pose proof (sendrImpSt dt sendr2) as eq2.
      assert (H: slt (to r2) (to m)) by
          (rewrite <- eq1; rewrite dirEq1;
           unfold sgt in *; unfold sle in *; unfold slt in *; destruct (dir p c a t2) in *;
           destruct (dir p c a t') in *; destruct (to r2) in *; auto).
      generalize sendm cond3 recvm isVolR H; clear; firstorder.
      assert (Hik: forall tn, t1 <= tn < t' -> (forall m, ~ mark mch p c a tn m) /\
                                               (forall m, ~ recv mch c p a tn m)) by (generalize easy; clear; firstorder).
      pose proof (noChange dt t1LtT' Hik).
      assert (H2: dir p c a t' = dir p c a t1) by auto.
      pose proof (dirNotEq H2) as f.
      firstorder.
    Qed.

    Theorem pRecvRespPrevState:
      forall {m a tr ts}, recv mch c p a tr m -> mark mch c p a ts m ->
                          dir p c a tr = state c a ts.
    Proof.
      intros.
      pose proof (recvmCond isParent H).
      pose proof (sendmFrom st H0).
      rewrite H1 in H2.
      assumption.
    Qed.

    Theorem noPRespImpSameState:
      forall {sm rm m a},
        recv mch p c a rm m -> mark mch p c a sm m ->
        (forall ti mi, ti < sm -> ~ recv mch c p a ti mi /\ ~ mark mch p c a ti mi) ->
        state c a rm = dir p c a sm.
      intros sm rm m a recvm markm noRecvSend.
      assert (noCRecv: forall t mt, 0 <= t < rm -> ~ recv mch p c a t mt).
      unfold not; intros t mt t_lt_rm recvmt.
      pose proof (recvImpMark recvmt) as [t' [t'_le_t markmt]].
      assert (stuff: t' < sm \/ t' = sm \/ sm < t') by omega.
      destruct stuff as [t'_lt_sm | [t'_eq_sm | sm_lt_t']].
      generalize noRecvSend t'_lt_sm markmt; clear; firstorder.
      rewrite t'_eq_sm in *.
      pose proof (uniqMark1 markm markmt) as m_eq_mt.
      rewrite m_eq_mt in *.
      pose proof (uniqRecv2 recvm recvmt) as t_eq_rm.
      omega.
      pose proof (pRespFifo sm_lt_t' markm markmt recvmt) as [t'' [t''_lt_t recv'm]].
      pose proof (uniqRecv2 recvm recv'm) as t''_eq_rm.
      omega.
      assert (noCSend: forall t mt, 0 <= t < rm -> ~ mark mch c p a t mt).
      unfold not; intros t mt t_lt_rm markmt.
      assert (noRecvEarlier: forall ti, ti < sm -> ~ recv mch c p a ti mt) by
          (generalize noRecvSend; clear; firstorder).
      assert (noRecvEarlier': forall ti, ti < t -> ~ recv mch p c a ti m) by
          (unfold not; intros ti ti_lt_t recv'm;
           pose proof (uniqRecv2 recvm recv'm) as ti_eq_rm; omega).
      apply (cross markmt markm noRecvEarlier' noRecvEarlier).
      assert (z_le_sm: 0 <= sm) by omega.
      assert (z_le_rm: 0 <= rm) by omega.
      assert (first: state c a 0 = state c a rm) by (generalize (@noChange2 (state c) sgt c p st a 0 rm z_le_rm) noCRecv noCSend z_le_sm z_le_rm; clear; firstorder).
      assert (second: dir p c a 0 = dir p c a sm) by (generalize (@noChange2 (dir p c) slt p c dt a 0 sm z_le_sm) noRecvSend z_le_sm z_le_rm; clear; firstorder).
      pose proof @init p c isParent a as i0.
      rewrite first in i0.
      rewrite second in i0.
      auto.
    Qed.

    Theorem noCRespImpSameState:
      forall {sm rm m a},
        recv mch p c a rm m -> mark mch p c a sm m ->
        (forall ti mi, ti < rm -> ~ recv mch p c a ti mi /\ ~ mark mch c p a ti mi) ->
        state c a rm = dir p c a sm.
      intros sm rm m a recvm markm noRecvSend.
      assert (noPRecv: forall t mt, 0 <= t < sm -> ~ recv mch c p a t mt).
      unfold not; intros t mt t_lt_sm recvmt.
      pose proof (recvImpMark recvmt) as [t' [t'_le_t markmt]].
      pose proof (recvImpMarkBefore recvm markm) as sm_le_rm.
      assert (t'_lt_rm: t' < rm) by omega.
      generalize noRecvSend t'_lt_rm markmt; clear; firstorder.
      assert (noPSend: forall t mt, t < sm -> ~ mark mch p c a t mt).
      unfold not; intros t mt t_lt_sm markmt.
      pose proof (pRespFifo t_lt_sm markmt markm recvm) as stf.
      generalize noRecvSend stf; clear; firstorder.
      assert (z_le_sm: 0 <= sm) by omega.
      assert (z_le_rm: 0 <= rm) by omega.
      assert (first: dir p c a 0 = dir p c a sm) by (generalize (@noChange2 (dir p c) slt p c dt a 0 sm z_le_sm) noPRecv noPSend z_le_sm z_le_rm; clear; firstorder).
      assert (second: state c a 0 = state c a rm) by (generalize (@noChange2 (state c) sgt c p st a 0 rm z_le_rm) noRecvSend z_le_sm z_le_rm; clear; firstorder).
      pose proof @init p c isParent a as i0.
      rewrite first in i0.
      rewrite second in i0.
      auto.
    Qed.

    Theorem cRecvRespPrevState:
      forall {m a tr ts}, recv mch p c a tr m -> mark mch p c a ts m ->
                          state c a tr = dir p c a ts.
    Proof.
      intros m a tr ts recvm markm.
      pose proof (recvImpMarkBefore recvm markm) as ts_le_tr.
      destruct (classical (exists tm', tm' < tr /\ exists mm', recv mch p c a tm' mm'
                                                               \/ mark mch c p a tm' mm')) as
          [ex | notEx].
      pose proof (maxExists' classical ex) as [tm [tm_lt_tr [[mm recvm_recvm_mm] notAfter]]].
      assert (none: forall y,
                      S tm <= y < tr ->
                      (forall mm', ~ mark mch c p a y mm') /\ forall mm', ~ recv mch p c a y mm') by
          (generalize notAfter; clear; firstorder).
      pose proof noChange2 st tm_lt_tr none as dir_S_tm_eq_dir_ts.
      clear none.
      destruct recvm_recvm_mm as [recvm_mm|markm_mm].
      pose proof recvImpMark recvm_mm as [tn [tn_le_tm markm_mm]].
      destruct (classical (exists tk, tn < tk < ts /\ exists mk, recv mch c p a tk mk))
        as [[tk [tn_le_tk_lt_ts [mk recvm_mk]]]|notRecv].
      pose proof recvImpMark recvm_mk as [t2 [t2_le_tk markm_mk]].
      assert (t2_lt_tr: t2 < tr) by omega.
      assert (noRecv: forall t4, t4 < tn -> ~ recv mch c p a t4 mk) by (
                                                                        unfold not; intros t4 t4_lt_tn recvm_mk'; pose proof (uniqRecv2 recvm_mk recvm_mk');
                                                                        omega).
      assert (t2_le_tm: tm < t2 -> False) by (intros l1; generalize notAfter t2_lt_tr l1 markm_mk; clear; firstorder).
      assert (t2_ne_tm: t2 = tm -> False) by (intro r; rewrite r in *; apply (noSendmRecvm st markm_mk recvm_mm)).
      assert (t2_lt_tm: t2 < tm) by omega.
      assert (noRecv': forall t3, t3 < t2 -> ~ recv mch p c a t3 mm) by (
                                                                         unfold not; intros t3 t3_lt_t2 recvm_mm'; pose proof (uniqRecv2 recvm_mm recvm_mm');
                                                                         omega).
      pose proof (cross markm_mk markm_mm noRecv' noRecv); firstorder.
      destruct (classical (exists tk, tn < tk < ts /\ exists mk, mark mch p c a tk mk)) as
          [[tk [[tn_lt_tk tk_lt_ts] [mk markm_mk]]] | notSend].
      pose proof (pRespFifo tk_lt_ts markm_mk markm recvm) as [tl [tl_lt_tr recvmk]].
      pose proof (pRespFifo tn_lt_tk markm_mm markm_mk recvmk) as [t' [t'_lt_tl recv'mm]].
      pose proof (uniqRecv2 recvm_mm recv'mm) as tm_eq_t'.
      rewrite <- tm_eq_t' in *.
      generalize notAfter tl_lt_tr t'_lt_tl recvmk; clear; firstorder.
      assert (st: tn = ts \/ tn > ts \/ tn < ts) by omega.
      destruct st as [eq|[gt|ltt]].
      rewrite eq in *.
      pose proof (uniqMark1 markm_mm markm) as m_eq_mm.
      rewrite m_eq_mm in *.
      pose proof (uniqRecv2 recvm recvm_mm) as tr_eq_tm.
      omega.
      pose proof (pRespFifo gt markm markm_mm recvm_mm) as [tr1 [tr1_lt_tm recv'm]].
      pose proof (uniqRecv2 recvm recv'm) as tr1_eq_tr.
      omega.
      assert (stEq: state c a (S tm) = state c a tr) by
          ( generalize (@noChange2 (state c) sgt c p st a (S tm) tr tm_lt_tr) notAfter; clear; firstorder).
      assert (dirEq: dir p c a (S tn) = dir p c a ts) by
          ( generalize (@noChange2 (dir p c) slt p c dt a (S tn) ts ltt) notSend notRecv; clear; firstorder).
      pose proof (recvmChange st recvm_mm) as toM.
      pose proof (sendmChange dt markm_mm) as toM'.
      rewrite stEq in toM.
      rewrite dirEq in toM'.
      rewrite <- toM' in toM.
      assumption.
      assert (noRecv: forall ti, ti < tm -> ~ recv mch p c a ti m) by
          ( unfold not; intros ti ti_lt_tm recv'm;
            pose proof (uniqRecv2 recvm recv'm) as ti_eq_tr; omega).
      pose proof (cross markm_mm markm noRecv) as noRecvFalse.
      assert (ex2: exists tn, tn < ts /\ recv mch c p a tn mm) by
          (destruct (classical (exists tn, tn < ts /\ recv mch c p a tn mm)) as [easy|easy'];
           [assumption |
            generalize noRecvFalse easy'; clear; firstorder]).
      destruct ex2 as [tn [tn_lt_ts recvmm]].
      clear noRecvFalse.
      assert (noPRecv: forall tk, tn < tk < ts -> forall mi, ~ recv mch c p a tk mi).
      unfold not; intros tk [tn_lt_tk tk_lt_ts] mi recvmi.
      pose proof (recvImpMark recvmi) as [tl [tl_le_tk markmi]].
      assert (opts: tl = tm \/ tm < tl \/ tl < tm) by omega.
      destruct opts as [eq | [tm_lt_tl | tl_lt_tm]].
      rewrite eq in *.
      pose proof (uniqMark1 markm_mm markmi) as m_eq_mi.
      rewrite m_eq_mi in *.
      pose proof (uniqRecv2 recvmm recvmi) as sth.
      omega.
      assert (tl_lt_tr: tl < tr) by omega.
      generalize notAfter tm_lt_tl tl_lt_tr markmi; clear; firstorder.
      pose proof @cRespFifo.
      assert (notRecv: forall t4, t4 < tn -> ~ recv mch c p a t4 mi) by
          (unfold not; intros t4 t4_lt_tn recv'mi;
           pose proof (uniqRecv2 recvmi recv'mi) as t4_eq_tk; omega).
      apply (cRespFifo markmi markm_mm recvmm tl_lt_tm notRecv).
      assert (noPSend: forall tk, tn < tk < ts -> forall mi, ~ mark mch p c a tk mi).
      unfold not; intros tk [tn_lt_tk tk_lt_ts] mi markmi.
      pose proof (pRespFifo tk_lt_ts markmi markm recvm) as [tl [tl_lt_tr recvmi]].
      pose proof (recvImpMarkBefore recvmi markmi) as tk_le_tl.
      pose proof (recvImpMarkBefore recvmm markm_mm) as tm_le_tn.
      assert (tm_lt_tl: tm < tl) by omega.
      generalize tm_lt_tl tl_lt_tr recvmi notAfter; clear; firstorder.
      assert (stEq: state c a (S tm) = state c a tr) by
          ( generalize (@noChange2 (state c) sgt c p st a (S tm) tr tm_lt_tr) notAfter; clear; firstorder).
      assert (dirEq: dir p c a (S tn) = dir p c a ts) by
          ( generalize (@noChange2 (dir p c) slt p c dt a (S tn) ts tn_lt_ts) noPSend noPRecv; clear; firstorder).
      pose proof (recvmChange dt recvmm) as toM.
      pose proof (sendmChange st markm_mm) as toM'.
      rewrite stEq in toM'.
      rewrite dirEq in toM.
      rewrite <- toM' in toM.
      auto.
      pose proof (noCRespImpSameState recvm markm) as good.
      generalize good notEx; clear; firstorder.
    Qed.

    Theorem pRecvDowngrade: forall {m a t},
                              recv mch c p a t m -> slt (dir p c a (S t)) (dir p c a t).
    Proof.
      intros m a t recvm.
      pose proof (recvImpMark recvm) as [ts [ts_le_t markm]].
      pose proof (sendmFrom st markm) as fromM.
      pose proof (sendmImpSt isParent markm) as toM.
      pose proof (recvmChange dt recvm) as dirSt.
      pose proof (recvmCond isParent recvm) as dirT.
      rewrite fromM in dirT; rewrite dirT in toM.
      rewrite <- dirSt in toM; assumption.
    Qed.

    Theorem cSendDowngrade: forall {m a t}, mark mch c p a t m ->
                                            slt (state c a (S t)) (state c a t).
    Proof.
      intros m a t markm.
      pose proof (sendmChange st markm) as toM.
      pose proof (sendmFrom st markm) as fromM.
      pose proof (sendmImpSt isParent markm).
      rewrite <- toM in H; assumption.
    Qed.

    Theorem pSendUpgrade: forall {m a t}, mark mch p c a t m ->
                                          slt (dir p c a t) (dir p c a (S t)).
    Proof.
      intros m a t markm.
      pose proof (sendmImpRecvr isParent markm) as [r recvr].
      pose proof (sendmImpRecvrGe isParent markm recvr) as cond.
      pose proof (recvrCond isParent recvr) as fromR.
      pose proof (recvImpMark recvr) as [t' [t'_le_t markr]].
      pose proof (sendrImpSt st markr)  as toR.
      pose proof (sendrFrom st markr) as fromR'.
      pose proof (sendmChange dt markm) as toM.
      unfold sgt in *.
      rewrite <- toM in *.
      rewrite <- fromR' in toR.
      generalize cond fromR toR; clear.
      intros.
      unfold sle in *; unfold slt in *; destruct (to r); destruct (dir p c a (S t));
      destruct (dir p c a t); destruct (from r); auto.
    Qed.

    Theorem cRecvUpgrade: forall {m a t}, recv mch p c a t m ->
                                            slt (state c a t) (state c a (S t)).
    Proof.
      intros m a t recvm.
      pose proof (recvImpMark recvm) as [t' [t'LeT markm]].
      pose proof (pSendUpgrade markm) as dirs.
      pose proof (sendmChange dt markm) as toM.
      pose proof (recvmChange st recvm) as toM'.
      pose proof (cRecvRespPrevState recvm markm).
      rewrite <- H in dirs.
      rewrite <- toM' in toM.
      rewrite toM in dirs.
      assumption.
    Qed.
  End Pair.
End mkBehaviorTheorems.
