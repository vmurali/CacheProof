Require Import Arith Omega.

Require Import Useful.
Require Import DataTypes.
Require Import Channel.

Module Type LocalState (dt: DataTypes).
  Import dt.
  Parameter st: Addr -> Time -> State.
  Parameter src dst: Cache.
  Parameter toRSComp: State -> State -> Prop.
End LocalState.

Module Type LocalBehavior (dt: DataTypes) (ch: ChannelPerAddr dt).
  Import dt ch.

  Parameter st: Addr -> Time -> State.
  Parameter src dst: Cache.
  Parameter toRSComp: State -> State -> Prop.

  Section ForT.
    Context {t: Time}.
    Context {a: Addr}.

    Axiom change: st a (S t) <> st a t -> (exists m, marksend mch src dst a t m) \/
      (exists m, deq mch dst src a t m).
    Axiom sendmChange: forall {m}, marksend mch src dst a t m -> st a (S t) = to m.
    Axiom deqmChange: forall {m}, deq mch dst src a t m -> st a (S t) = to m.
    Axiom sendrImpSt: forall {r}, marksend rch src dst a t r -> toRSComp (to r) (st a t).
    Axiom sendrImpNoSendr: forall {t1 t2 r1 r2}, t1 < t2 -> marksend rch src dst a t1 r1 ->
      marksend rch src dst a t2 r2 -> exists t', t1 < t' <= t2 /\ ~ toRSComp (to r1) (st a t').
    Axiom sendmFrom: forall {m}, marksend mch src dst a t m -> from m = st a t.
    Axiom sendrFrom: forall {r}, marksend rch src dst a t r -> from r = st a t.
    Axiom sendmTime: forall {m}, marksend mch src dst a t m -> time m = timeStamp src a t.
    Axiom noSendmDeqm: forall {m}, marksend mch src dst a t m ->
      forall {m'}, deq mch dst src a t m' -> False.
    Axiom noSendmSendr: forall {m}, marksend mch src dst a t m -> forall {r}, marksend rch src dst a t r -> False.
  End ForT.
End LocalBehavior.

Module LocalLemmas (dt: DataTypes) (ch: ChannelPerAddr dt) (lb: LocalBehavior dt ch).
  Import dt lb ch.

  Section ForLs.
    Lemma nochange': forall {a t t'}, (forall tn, t <= tn < t + t' ->
      (forall m, ~ marksend mch src dst a tn m) /\ (forall m, ~ deq mch dst src a tn m)) ->
    st a t = st a (t + t').
    Proof.
      intros a t t'.
      induction t'.
      intro false.
      firstorder.
      intros noChange.
      assert (help: forall tn, t <= tn < t + t' -> (forall m, ~ marksend mch src dst a tn m) /\
        (forall m, ~ deq mch dst src a tn m)) by (
          intros tn comp;
            assert (comp2: t <= tn < t + S t') by omega;
              firstorder).
      assert (stTEqstT': st a t = st a (t + t')) by firstorder.
      assert (nothing: (forall m, ~ marksend mch src dst a (t + t') m) /\
        forall m, ~ deq mch dst src a (t + t') m) by
      (assert (t <= t + t' < t + S t'); firstorder).
      rewrite stTEqstT'.
      assert (two: st a (t + S t') = st a (t + t') \/ st a (t + S t') <> st a (t + t')) by decide equality.
      destruct two as [easy | hard].
      intuition.
      assert (sth: t + S t' = S (t + t')) by omega.
      rewrite sth in *.
      pose proof (change hard) as contra.
      firstorder.
    Qed.

    Lemma noChange: forall {a t t'}, t < t' -> (forall tn, t <= tn < t' ->
      (forall m, ~ marksend mch src dst a tn m) /\ (forall m, ~ deq mch dst src a tn m)) -> st a t = st a t'.
    Proof.
      intros a t t' tLtT'.
      remember (t' - t) as td.
      assert (rew: t' = t + td) by omega.
      rewrite rew in *.
      apply (@nochange' a t).
    Qed.

    Lemma noChange2: forall {a t t'}, t <= t' -> (forall tn, t <= tn < t' ->
      (forall m, ~ marksend mch src dst a tn m) /\ (forall m, ~ deq mch dst src a tn m)) -> st a t = st a t'.
    Proof.
      intros a t t' tLeT'.
      assert (opts: t = t' \/ t < t') by omega.
      destruct opts as [tEqT' | tLtT'].
      rewrite tEqT'.
      reflexivity.
      apply noChange; intuition.
    Qed.
  End ForLs.
End LocalLemmas.

Module Type Pair (dt: DataTypes).
  Variable p c : dt.Cache.
  Variable isParent : dt.parent c = p.
End Pair.

Module Type StSemi (dt: DataTypes) (p: Pair dt) (ch: ChannelPerAddr dt) :=
  LocalBehavior dt ch with
  Definition st := dt.state p.c with
    Definition src := p.c with
      Definition dst := p.p with
        Definition toRSComp := gt.

Module Type DirSemi (dt: DataTypes) (p: Pair dt) (ch: ChannelPerAddr dt) :=
  LocalBehavior dt ch with
  Definition st := dt.dir p.p p.c with
    Definition src := p.p with
      Definition dst := p.c with
        Definition toRSComp := lt.

Module Type StBase (dt: DataTypes) (p: Pair dt) (ch: ChannelPerAddr dt) (st: StSemi dt p ch).
  Module ll := LocalLemmas dt ch st.
  Include ll.
  Include st.
  Import dt p ch.

  Section ForT.
    Context {a: Addr} {t: Time}.

    Axiom sendmImpSt: forall {m}, marksend mch c p a t m -> state c a t > to m.

    Axiom voluntary:
      forall {r}, marksend rch c p a t r -> forall {t' m}, t' > t -> marksend mch c p a t' m ->
        (forall {tm}, t < tm <= t' -> state c a tm < to r) ->
        exists r1, deq rch p c a t' r1 /\ state c a t' > to r1.

(*    Axiom deqrSendm: forall {r}, deq rch p c a t r -> state c a t > to r -> exists {m}, marksend mch c p a t m.*)
  End ForT.
End StBase.

Module St (dt: DataTypes) (p: Pair dt) (ch: ChannelPerAddr dt) (st: StSemi dt p ch) (base: StBase dt p ch st).
  Include base.
  Import dt ch st p base.

  Section ForT.
    Context {a: Addr}.
    Lemma whenChildHighDeqm: forall {t}, state c a (S t) > state c a t -> exists m,
      deq mch p c a t m /\ to m = state c a (S t).
    Proof.
      intros t sStgst.
      assert (sStnst: state c a (S t) <> state c a t) by omega.
      pose proof (change sStnst) as [[m sendmm] | [m deqmm] ].
      pose proof (sendmImpSt sendmm) as stgm.
      pose proof (sendmChange sendmm) as sStem.
      unfold st in *.
      omega.
      exists m.
      intuition.
      pose proof (deqmChange deqmm) as sStem.
      unfold src, dst in *.
      intuition.
    Qed.

    Lemma whenChildHigh': forall {t t'}, state c a (S (t' + t)) > state c a t ->
      exists t'', t'' <= t' /\ exists m, deq mch p c a (t'' + t) m /\ to m >= state c a (S (t' + t)).
    Proof.
      intros t t' sSt'tgst.
      induction t'.
      pose proof (whenChildHighDeqm sSt'tgst) as [m [deqmm mesSt]].
      exists 0.
      assert (temp: 0 + t = t) by omega.
      rewrite temp in *; clear temp.
      intuition.
      exists m.
      intuition.
      pose proof (lt_eq_lt_dec (state c a (S (S t' + t))) (state c a (S (t' + t)))) as [[lt | eq] | gt'].
      assert (gt: state c a (S (t' + t)) > state c a t) by omega.
      specialize (IHt' gt).
      destruct IHt' as [t'' [le [m [deqmm mgesSt't]]]].
      assert (t''leSt': t'' <= S t') by omega.
      assert (mgesSSt't: to m >= state c a (S (S t' + t))) by omega.
      exists t''.
      intuition.
      exists m.
      intuition.
      rewrite <- eq in IHt'.
      specialize (IHt' sSt'tgst).
      destruct IHt' as [t'' [le rest]].
      exists t''.
      intuition.
      assert (gt: state c a (S (S t' + t)) > state c a (S (t' + t))) by omega; clear gt'.
      pose proof (whenChildHighDeqm gt) as [m [deqmm mesSt]].
      exists (S t').
      intuition.
      exists m.
      intuition.
    Qed.

    Lemma whenChildHigh: forall {t t'}, t' > t -> state c a t' > state c a t ->
      exists t'', t <= t'' < t' /\ exists m, deq mch p c a t'' m /\ to m >= state c a t'.
    Proof.
      intros t tPlust'.
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

    Lemma whenChildHighConv: forall {t t'}, t' >= t ->
      (~ exists t'', t <= t'' < t' /\ exists m, deq mch p c a t'' m /\ to m >= state c a t') ->
      state c a t' <= state c a t.
    Proof.
      intros t t' t'GeT notE.
      assert (opts: t' = t \/ t' > t) by omega.
      destruct opts as [t'EqT | t'GtT].
      rewrite t'EqT; reflexivity.
      assert (notX: ~ state c a t' > state c a t) by (intros one;
        pose proof (whenChildHigh t'GtT one); firstorder).
      omega.
    Qed.
  End ForT.
End St.

Module Type DirBase (dt: DataTypes) (p: Pair dt) (ch: ChannelPerAddr dt) (st: DirSemi dt p ch).
  Module ll := LocalLemmas dt ch st.
  Include ll.
  Include st.
  Import dt ch st p.

  Section ForT.
    Context {a: Addr} {t: Time}.

    Axiom sendmImpDeqr: forall {m}, marksend mch p c a t m -> exists r, deq rch c p a t r.

    Axiom sendmImpDeqrGe: forall {m}, marksend mch p c a t m ->
      forall {r}, deq rch c p a t r -> to m >= to r.

    Axiom deqrCond: forall {r}, deq rch c p a t r -> from r >= dir p c a t.

    Axiom deqmCond: forall {m}, deq mch c p a t m -> from m = dir p c a t.

    Axiom sendrImpNoSendm: forall {t1 t2 r1 m2}, t1 < t2 -> marksend rch p c a t1 r1 ->
      marksend mch p c a t2 m2 ->
      exists t', t1 < t' < t2 /\ exists m, deq mch c p a t' m /\ to m <= to r1.

(*    Axiom deqrImpSendm: forall {r}, deq rch c p a t r -> exists m, marksend mch p c a t m /\ to m >= to r.*)
  End ForT.
End DirBase.

Module Dir (dt: DataTypes) (p: Pair dt) (ch: ChannelPerAddr dt) (d: DirSemi dt p ch) (db: DirBase dt p ch d)
  (s: StSemi dt p ch) (sb: StBase dt p ch s).
  Include db.
  Import dt ch p.
  
  Lemma dirDeqImpLow: forall {a t m}, deq mch c p a t m -> dir p c a t > dir p c a (S t).
  Proof.
    intros a t m deqm.
    pose proof (deqImpMarksend deqm) as [t' [t'LeT sendm]].
    pose proof (db.deqmChange deqm) as sth.
    pose proof (sb.sendmImpSt sendm) as sth2.
    pose proof (db.deqmCond deqm) as sth3.
    pose proof (sb.sendmFrom sendm) as sth4.
    unfold d.st, sb.st in *.
    omega.
  Qed.

  Lemma whenDirLow': forall {a t t'}, dir p c a (t' + t) > dir p c a t ->
    exists t'', t'' < t' /\ exists m, marksend mch p c a (t'' + t) m.
  Proof.
    intros a t t'.
    induction t'.
    intros dirGt.
    unfold plus in *; simpl. omega.
    intros dirGt.
    assert (opts: dir p c a (t' + t) > dir p c a t \/ dir p c a (t' + t) <= dir p c a t) by omega.
    destruct opts as [gt | le].
    firstorder.
    assert (gt: dir p c a (S (t' + t)) > dir p c a (t' + t)) by (assert (eq: S t' + t = S (t' + t)) by omega;
      rewrite eq in *; omega).
    assert (nestuff: dir p c a (S (t' + t)) <> dir p c a (t' + t)) by omega.
    pose proof (db.change nestuff) as [sendm | deqm].
    firstorder.
    destruct deqm as [x deqstuff].
    pose proof (dirDeqImpLow deqstuff) as contra.
    omega.
  Qed.

  Lemma whenDirLow: forall {a t t1}, t <= t1 -> dir p c a t1 > dir p c a t ->
    exists t'', t <= t'' < t1 /\ exists m, marksend mch p c a t'' m.
  Proof.
    intros a t t1 t1LeT1 dirGt.
    assert (opt: t = t1 \/ t < t1) by omega.
    destruct opt as [tEqT1 | tLeT1].
    rewrite tEqT1 in *; omega.
    remember (t1 - t - 1) as t'.
    assert (eq: t1 = (t' + 1) + t) by omega.
    rewrite eq in *.
    pose proof (whenDirLow' dirGt) as [t'' [t''Cond ext]]. 
    exists (t'' + t).
    firstorder.
  Qed.

  Lemma childSth: forall {a t x}, dir p c a t > x -> forall {td},
    ~ (exists tn, t <= tn < t + td /\ ((exists m, marksend mch p c a tn m) \/
      (exists m, deq mch c p a tn m /\ to m <= x))) ->
    dir p c a (t + td) > x.
  Proof.
    intros a t x cond.
    induction td.
    intros _.
    assert (t+0=t) by omega.
    rewrite H in *.
    intuition.
    intros nothing.
    assert (contra: ~ exists tn, t <= tn < t + td /\ ((exists m, marksend mch p c a tn m) \/
      (exists m, deq mch c p a tn m /\ to m <= x))) by (unfold not; intros [tn [cond3 rest]];
        assert (cond2: t <= tn < t + S td) by omega;
          generalize nothing cond2 rest; clear; firstorder).
    specialize (IHtd contra).
    pose proof (@change (t + td) a) as stUnEq.
    assert (opts: dir p c a (t + S td) = dir p c a (t + td) \/
      dir p c a (t + S td) <> dir p c a (t + td))
      by decide equality.
    destruct opts as [easy | hard].
    omega.
    assert (eq: t + S td = S (t + td)) by omega.
    rewrite eq in *.
    specialize (stUnEq hard).
    assert (pre: t <= t + td < S (t + td)) by omega.
    destruct stUnEq as [[m sendm]|[m deqm]].
    firstorder.
    assert (opts: to m <= x \/ to m > x) by omega.
    destruct opts as [toMLeX | toMGtX].
    firstorder.
    pose proof (deqmChange deqm).
    unfold st in *.
    omega.
  Qed.

  Lemma dirCantGoLower: forall {a t x}, dir p c a t > x -> forall {t1}, t <= t1 ->
    ~ (exists tn, t <= tn < t1 /\ ((exists m, marksend mch p c a tn m) \/
      (exists m, deq mch c p a tn m /\ to m <= x))) ->
    dir p c a (t1) > x.
  Proof.
    intros a t x dirx t1 tLeT1 contra.
    remember (t1 - t) as td.
    assert (t1 = t + td) by omega.
    rewrite H in *.
    apply (childSth dirx contra).
  Qed.
End Dir.

Module Type PairProperties (dt: DataTypes) (ch: ChannelPerAddr dt) (p: Pair dt).
  Import dt ch p.

  Axiom init: forall {a}, dir p c a 0 = state c a 0.

  Definition twoEqPRespFalse := forall a t t1 m1, t1 <= t -> marksend mch p c a t1 m1 ->
    forall t2 m2, t2 <= t -> marksend mch p c a t2 m2 ->
      (forall t3, t3 <= t -> ~ deq mch p c a t3 m1) ->
      (forall {t4}, t4 <= t -> ~ deq mch p c a t4 m2) ->
      t1 = t2.

  Definition twoPReqEqNeedsPResp := forall a t t1 r1, t1 <= t -> marksend rch p c a t1 r1 ->
    forall t2 r2, t2 <= t -> marksend rch p c a t2 r2 ->
      (forall t3, t3 <= t -> ~ deq rch p c a t3 r1) ->
      (forall t4, t4 <= t -> ~ deq rch p c a t4 r2) -> t1 < t2 ->
      to r1 <= to r2 -> exists tm, t1 < tm < t2 /\ exists m, marksend mch p c a tm m.

  Section ForA.
    Context {a: Addr}.
    Axiom pRespReq: twoEqPRespFalse -> twoPReqEqNeedsPResp -> forall {t1 t2 t3},
      forall {m}, marksend mch p c a t1 m ->
        forall {r}, marksend rch p c a t2 r -> deq rch p c a t3 r -> t1 <= t2 ->
          exists t4, t4 < t3 /\ deq mch p c a t4 m.

    Axiom pReqResp: twoEqPRespFalse -> twoPReqEqNeedsPResp -> forall {t1 t2 t3},
      forall {r}, marksend rch p c a t1 r ->
        forall {m}, marksend mch p c a t2 m -> deq mch p c a t3 m -> t1 <= t2 ->
          exists t4, t4 < t3 /\ deq rch p c a t4 r.
  End ForA.
End PairProperties.

Module Type PairTheoremsType (dt: DataTypes) (ch: ChannelPerAddr dt) (p: Pair dt)
  (pp: PairProperties dt ch p).
  Import dt ch p pp.

  Axiom noTwoPResp: twoEqPRespFalse.
  Axiom noTwoPReqNon: twoPReqEqNeedsPResp.

  Axiom conservative: forall {a t}, dir p c a t >= state c a t.
  Axiom cReqRespSent: forall {a t1 t2 r}, marksend rch p c a t1 r -> deq rch p c a t2 r ->
    to r >= state c a t2 -> exists t3, t3 < t2 /\ exists m, marksend mch c p a t3 m /\ to m <= to r /\
      (forall t4, t4 < t1 -> ~ deq mch c p a t4 m).

  Axiom pReqsCVolRespReqLt: forall {t a t1 t2 r1 r2}, t1 <= t -> t2 <= t ->
    marksend rch p c a t1 r1 ->
    marksend rch p c a t2 r2 -> t1 < t2 ->
    (forall ts, t1 < ts < t2 -> forall r, ~ marksend rch p c a ts r) ->
    (forall ts, t1 < ts < t2 -> forall m, ~ marksend mch p c a ts m) ->
    (forall t3, t3 <= t -> ~ deq rch p c a t3 r1) ->
    (forall t4, t4 <= t -> ~ deq rch p c a t4 r2) -> exists t5 m, marksend mch c p a t5 m /\
      exists t6, t1 <= t6 < t2 /\ deq mch c p a t6 m /\ 
        (forall r, deq rch p c a t5 r -> to r >= state c a t5) /\ to r2 < to m.
End PairTheoremsType.

Module Type Classical.
  Axiom classical: forall P, P \/ ~ P.
End Classical.

Module PairTheorems (classical: Classical) (dt: DataTypes) (ch: ChannelPerAddr dt)
  (p: Pair dt) (pp: PairProperties dt ch p)
  (stSemi: StSemi dt p ch) (dirSemi: DirSemi dt p ch) (stBase: StBase dt p ch stSemi)
  (dirBase: DirBase dt p ch dirSemi): PairTheoremsType dt ch p pp.
  Module st := St dt p ch stSemi stBase.
  Module dir := Dir dt p ch dirSemi dirBase stSemi stBase.
  Import dt ch p pp.

  Lemma cReqPRespCrossInd: forall {a t tc tp}, tc <= t -> tp <= t -> 
    forall {r m}, marksend rch c p a tc r ->
      marksend mch p c a tp m -> (forall tc', tc' < tc -> ~ deq mch p c a tc' m) ->
      (forall tp', tp' <= tp -> ~ deq rch c p a tp' r) -> False.
  Proof.
    intros a t.
    induction t.
    intros tc tp tcLeT tpLeT r m rsendr msendm mdeqNo rdeqNo.
    assert (tc0: tc = 0) by omega; clear tcLeT.
    assert (tp0: tp = 0) by omega; clear tpLeT.
    rewrite tc0 in *; rewrite tp0 in *; clear tc0 tp0.
    pose proof (dir.sendmImpDeqr msendm) as [r' rdeqr'].
    pose proof (deqImpMarksend rdeqr') as [t' [t'Le0 rsendr']].
    assert (t'0: t' = 0) by omega; clear t'Le0.
    rewrite t'0 in rsendr'; clear t'0.
    pose proof (uniqMarksend1 rsendr rsendr') as rEqr'.
    rewrite <- rEqr' in *; clear rEqr'.
    assert (zero: 0 <= 0) by omega.
    firstorder.
    intros tc tp tcLeST tpLeST r m rsendr msendm mdeqNo rdeqNo.

    pose proof (dir.sendmImpDeqr msendm) as [r' rdeqr'].
    pose proof (deqImpMarksend rdeqr') as [t' [t'LeSt rsendr']].

    assert (diff: t' = tc \/ t' > tc \/ t' < tc) by omega.
    destruct diff as [eq | [t'GtTc | tcGtT']].
    rewrite eq in rsendr'.
    pose proof (uniqMarksend1 rsendr rsendr') as rEqr'.
    rewrite <- rEqr' in *.
    assert (tpEq: tp <= tp) by omega.
    firstorder.

    pose proof (st.sendrImpNoSendr t'GtTc rsendr rsendr') as [t'' [cond neg]].
    unfold st.toRSComp in *; unfold st.st in *.
    assert (toRLes: to r <= state c a t'') by firstorder.
    pose proof (st.sendrImpSt rsendr) as toGtt.
    unfold st.toRSComp in *; unfold st.st in *.
    assert (tcLtT'': state c a tc < state c a t'') by omega.
    assert (t''GtTc: t'' > tc) by omega.
    pose proof (st.whenChildHigh t''GtTc tcLtT'') as [t''' [[tcLeT''' t'''LtT''] [m' [mdeqm' _]]]].
    pose proof (deqImpMarksend mdeqm') as [td [tdLeT''' msendm']].
    assert (tdLet: td <= t) by omega.
    assert (noDeq: forall tc', tc' < tc -> ~ deq mch p c a tc' m') by (
      unfold not; intros tc' tc'LtTc mdeqm'Tc';
        pose proof (uniqDeq2 mdeqm' mdeqm'Tc') as tc'EqT''; omega).
    assert (noDeq': forall tp', tp' <= td -> ~ deq rch c p a tp' r) by (
      unfold not; intros tp' tp'LeTd;
        assert (tp'LeTp: tp' <= tp) by omega;
          firstorder).
    assert (tcLeT: tc <= t) by omega.
    apply (IHt tc td tcLeT tdLet r m' rsendr msendm' noDeq noDeq').

    pose proof (st.sendrImpNoSendr tcGtT' rsendr' rsendr) as [tmur [cond neg]].
    unfold st.toRSComp in *; unfold st.st in *.
    assert (toRLeS: to r' <= state c a tmur) by omega.
    pose proof (st.sendrImpSt rsendr') as toGtt.
    unfold st.toRSComp in *; unfold st.st in *.
    assert (stt'LtstTc: state c a t' < state c a tmur) by omega.
    assert (tmurGtT': tmur > t') by omega.
    pose proof (st.whenChildHigh tmurGtT' stt'LtstTc) as [t'' [[tcLeT'' t''LtT'] [m' [mdeqm' _]]]].
    pose proof (deqImpMarksend mdeqm') as [td [tdLeT'' msendm']].
    assert (tdLet: td <= t) by omega.
    assert (noDeq: forall tc', tc' < t' -> ~ deq mch p c a tc' m') by (
      unfold not; intros tc' tc'LtTc mdeqm'Tc';
        pose proof (uniqDeq2 mdeqm' mdeqm'Tc') as tc'EqT''; omega).
    assert (opts: td = tp \/ td < tp \/ td > tp) by omega.
    destruct opts as [tdEqTp | [tdLTp | tdGtTp]].
    rewrite tdEqTp in *.
    pose proof (uniqMarksend1 msendm msendm') as mEqm'.
    rewrite <- mEqm' in *.
    assert (t''LtTc: t'' < tc) by omega.
    firstorder.
    assert (noDeq': forall tp', tp' <= td -> ~ deq rch c p a tp' r') by (
      unfold not; intros tp' tp'LeTd rdeqr'Tp';
        pose proof (uniqDeq2 rdeqr' rdeqr'Tp') as tp'EqTp;
          omega).
    assert (t'LeT: t' <= t) by omega.
    apply (IHt t' td t'LeT tdLet r' m' rsendr' msendm' noDeq noDeq').
    pose proof (dir.sendmImpDeqr msendm') as [r'' rdeqr''].
    pose proof (deqImpMarksend rdeqr'') as [ts [tsLeTd rsendr'']].
    assert (tpLeT: tp <= t) by omega.
    assert (tsLeT: ts <= t) by omega.
    assert (hyp1: forall tc', tc' < ts -> ~ deq mch p c a tc' m) by (
      intros tc' tc'LtTs;
        assert (tc'LtTc: tc' < tc) by omega;
          firstorder).
    assert (hyp2: forall tp', tp' <= tp -> ~ deq rch c p a tp' r'') by (
      unfold not; intros tp' tpLeTp rdeqr''Tp';
        pose proof (uniqDeq2 rdeqr'' rdeqr''Tp') as tdEqTp';
          rewrite <- tdEqTp' in *;
            firstorder).
    apply (IHt ts tp tsLeT tpLeT r'' m rsendr'' msendm hyp1 hyp2).
  Qed.

  Lemma cReqPRespCross: forall {a tc tp r m}, marksend rch c p a tc r ->
    marksend mch p c a tp m -> (forall tc', tc' < tc -> ~ deq mch p c a tc' m) ->
    (forall tp', tp' <= tp -> ~ deq rch c p a tp' r) -> False.
  Proof.
    intros a tc tp.
    assert (tcLeT: tc <= tc + tp) by omega.
    assert (tpLeT: tp <= tc + tp) by omega.
    apply (@cReqPRespCrossInd a (tc + tp) tc tp tcLeT tpLeT).
  Qed.

  Lemma noTwoPResp: twoEqPRespFalse.
  Proof.
    intros a tx t1 m1 t1LeTx sendm1 t2 m2 t2LeTx sendm2 nodeqm1 nodeqm2.
    pose proof (dir.sendmImpDeqr sendm1) as [r1 deqr1].
    pose proof (dir.sendmImpDeqr sendm2) as [r2 deqr2].
    pose proof (deqImpMarksend deqr1) as [t3 [t3LeT1 sendr1]].
    pose proof (deqImpMarksend deqr2) as [t4 [t4LeT2 sendr2]].
    assert (opts: t3 = t4 \/ t3 < t4 \/ t4 < t3) by omega.
    destruct opts as [t3EqT4|[t3LtT4|t4LtT3]].
    rewrite t3EqT4 in *; pose proof (uniqMarksend1 sendr1 sendr2) as r1EqR2.
    rewrite r1EqR2 in *; apply (uniqDeq2 deqr1 deqr2).

    assert (noDeq: ~ exists t, t3 <= t < t4 /\ exists m, deq mch p c a t m) by (
      unfold not; intros [t [cond [m deqm]]];
        pose proof (deqImpMarksend deqm) as [t5 [t5LeT sendm]];
          assert (opts: t5 = t1 \/ t5 < t1 \/ t5 > t1) by omega;
            destruct opts as [t5EqT1 | [t5LtT1 | t5GtT1]]; [
              rewrite t5EqT1 in *; pose proof (uniqMarksend1 sendm1 sendm) as m1EqM;
                rewrite m1EqM in *; assert (tLeTx: t <= tx) by omega;
                  generalize tLeTx nodeqm1 deqm; clear; firstorder |
                    assert (one: forall tc', tc' < t3 -> ~ deq mch p c a tc' m) by (
                      unfold not; intros tc' tc'LtT3 deq'm; pose proof (uniqDeq2 deqm deq'm) as tEqTc';
                        rewrite tEqTc' in *; firstorder);
                    assert (two: forall tp', tp' <= t5 -> ~ deq rch c p a tp' r1) by (
                      unfold not; intros tp' tp'LeT1 deq'r1; pose proof (uniqDeq2 deqr1 deq'r1) as t5EqTp';
                        rewrite <- t5EqTp' in *; firstorder);
                    apply (cReqPRespCross sendr1 sendm one two) |
                      pose proof (dir.sendmImpDeqr sendm) as [r deqr];
                        pose proof (deqImpMarksend deqr) as [t6 [t6LeT5 sendr]];
                          assert (one: forall tc', tc' < t6 -> ~ deq mch p c a tc' m1) by (
                            unfold not; intros tc' tc'LtT6 deq'm1; assert (tc'LeT6: tc' <= tx) by omega;
                              generalize nodeqm1 deq'm1 tc'LeT6; clear; firstorder);
                          assert (two: forall tp', tp' <= t1 -> ~ deq rch c p a tp' r) by (
                            unfold not; intros tp' tp'LeT1 deq'r; pose proof (uniqDeq2 deqr deq'r) as t1EqTp';
                              rewrite <- t1EqTp' in *; firstorder);
                          apply (cReqPRespCross sendr sendm1 one two)]).
    assert (t3LeT4: t3 <= t4) by omega.
    pose proof (st.sendrImpSt sendr1) as stG. unfold st.st, st.toRSComp in *.
    pose proof (st.sendrImpNoSendr t3LtT4 sendr1 sendr2) as [t5 [t3LtT5LeT4 neg]].
    unfold st.toRSComp, st.st in *.
    assert (pos: state c a t5 > state c a t3) by omega.
    assert (noDeq': ~ exists t, t3 <= t < t5 /\ exists m, deq mch p c a t m /\ to m >= state c a t5) by (
      unfold not; intros [t [cond1 [mg [deqmg _]]]];
        assert (cond: t3 <= t < t4) by omega;
          generalize deqmg cond noDeq; clear; firstorder).
    assert (t3LeT5: t3 <= t5) by omega.
    pose proof (st.whenChildHighConv t3LeT5 noDeq') as stContra.
    omega.

    assert (noDeq: ~ exists t, t4 <= t < t3 /\ exists m, deq mch p c a t m) by (
      unfold not; intros [t [cond [m deqm]]];
        pose proof (deqImpMarksend deqm) as [t5 [t5LeT sendm]];
          assert (opts: t5 = t2 \/ t5 < t2 \/ t5 > t2) by omega;
            destruct opts as [t5EqT1 | [t5LtT1 | t5GtT1]]; [
              rewrite t5EqT1 in *; pose proof (uniqMarksend1 sendm2 sendm) as m1EqM;
                rewrite m1EqM in *; assert (tLeTx: t <= tx) by omega;
                  generalize tLeTx nodeqm2 deqm; clear; firstorder |
                    assert (one: forall tc', tc' < t4 -> ~ deq mch p c a tc' m) by (
                      unfold not; intros tc' tc'LtT3 deq'm; pose proof (uniqDeq2 deqm deq'm) as tEqTc';
                        rewrite tEqTc' in *; firstorder);
                    assert (two: forall tp', tp' <= t5 -> ~ deq rch c p a tp' r2) by (
                      unfold not; intros tp' tp'LeT1 deq'r1; pose proof (uniqDeq2 deqr2 deq'r1) as t5EqTp';
                        rewrite <- t5EqTp' in *; firstorder);
                    apply (cReqPRespCross sendr2 sendm one two)|
                      pose proof (dir.sendmImpDeqr sendm) as [r deqr];
                        pose proof (deqImpMarksend deqr) as [t6 [t6LeT5 sendr]];
                          assert (one: forall tc', tc' < t6 -> ~ deq mch p c a tc' m2) by (
                            unfold not; intros tc' tc'LtT6 deq'm1; assert (tc'LeT6: tc' <= tx) by omega;
                              generalize nodeqm2 deq'm1 tc'LeT6; clear; firstorder);
                          assert (two: forall tp', tp' <= t2 -> ~ deq rch c p a tp' r) by (
                            unfold not; intros tp' tp'LeT1 deq'r; pose proof (uniqDeq2 deqr deq'r) as t1EqTp';
                              rewrite <- t1EqTp' in *; firstorder);
                          apply (cReqPRespCross sendr sendm2 one two)]).
    assert (t3LeT4: t4 <= t3) by omega.
    pose proof (st.sendrImpSt sendr2) as stG. unfold st.st, st.toRSComp in *.
    pose proof (st.sendrImpNoSendr t4LtT3 sendr2 sendr1) as [t5 [t3LtT5LeT4 neg]].
    unfold st.toRSComp, st.st in *.
    assert (pos: state c a t5 > state c a t4) by omega.
    assert (noDeq': ~ exists t, t4 <= t < t5 /\ exists m, deq mch p c a t m /\ to m >= state c a t5) by (
      unfold not; intros [t [cond1 [mg [deqmg _]]]];
        assert (cond: t4 <= t < t3) by omega;
          generalize deqmg cond noDeq; clear; firstorder).
    assert (t3LeT5: t4 <= t5) by omega.
    pose proof (st.whenChildHighConv t3LeT5 noDeq') as stContra.
    omega.
  Qed.

  Lemma noTwoPReqNon: twoPReqEqNeedsPResp.
  Proof.
    intros a t t1 r1 t1LeT sendr1 t2 r2 t2LeT sendr2 nodeqr1 nodeqr2 t1LtT2 toR1GeToR2.
    pose proof (dir.sendrImpSt sendr1) as gt1.
    pose proof (dir.sendrImpSt sendr2) as gt2.
    pose proof (dir.sendrImpNoSendr t1LtT2 sendr1 sendr2) as [t5 [cond dr]].
    unfold dir.st, dir.toRSComp in *.
    assert (toR1GeDirT5: to r1 >= dir p c a t5) by omega; clear dr.
    assert (dT5LtDt2: dir p c a t5 < dir p c a t2) by omega.
    assert (t5LeT2: t5 <= t2) by omega.
    pose proof (dir.whenDirLow t5LeT2 dT5LtDt2) as [tm [m [cond2 sendm]]].
    assert (cond3: t1 < tm < t2) by omega.
    firstorder.
  Qed.

  Import classical.
  Lemma mainInd: forall {a t},
    (forall {to}, to <= t -> state c a to <= dir p c a to) /\
    (forall {tc tp}, tc <= t -> tp <= t -> forall {mc}, marksend mch c p a tc mc ->
      forall {mp}, marksend mch p c a tp mp -> (forall tc', tc' < tc -> ~ deq mch p c a tc' mp) ->
        (forall tp', tp' < tp -> ~ deq mch c p a tp' mc) -> False) /\
    (forall {t1 t2 t3}, t3 <= t -> forall {m}, marksend mch c p a t1 m ->
      forall {r}, marksend rch c p a t2 r -> deq rch c p a t3 r -> t1 <= t2 ->
        (forall t4, t4 < t3 -> ~ deq mch c p a t4 m) -> False) /\
    (forall {t1 t2 t3}, t3 <= t -> forall {m}, marksend mch c p a t1 m ->
      forall {m'}, marksend mch c p a t2 m' -> deq mch c p a t3 m' -> t1 < t2 ->
        (forall t4, t4 < t3 -> ~ deq mch c p a t4 m) -> False).
  Proof.
    intros a t.
    induction t.
    constructor.
    intros to0 to0Le0.
    assert (to0Eq0: to0 = 0) by omega.
    pose proof (@init a) as start.
    rewrite to0Eq0.
    omega.
    constructor.
    intros tc tp tcLe0 tpLe0 mc msendmc mp msendmp _ _.
    assert (tcEq0: tc = 0) by omega; assert (tpEq0: tp = 0) by omega.
    rewrite tcEq0 in *; rewrite tpEq0 in *.
    pose proof (dir.sendmImpDeqr msendmp) as [r rdeqr].
    pose proof (deqImpMarksend rdeqr) as [t' [t'Le0 rsendr]].
    assert (t'Eq0: t' = 0) by omega.
    rewrite t'Eq0 in *.
    apply (st.noSendmSendr msendmc rsendr).
    constructor.
    intros t1 t2 t3 t3Le0 m msendm r rsendr rdeqr t1LeT2 neg.
    pose proof (deqImpMarksend rdeqr) as [t5 [t5LeT3 rsendrT5]].
    pose proof (uniqMarksend2 rsendr rsendrT5) as t2EqT5.
    assert (t30: t3 = 0) by omega.
    rewrite t2EqT5, t30 in *.
    assert (t1Le0: t1 <= 0) by omega.
    assert (t10: t1 = 0) by intuition.
    assert (t50: t5 = 0) by omega.
    rewrite t10, t50 in *.
    apply (st.noSendmSendr msendm rsendr).
    intros t1 t2 t3 t3Le0 m msendm m' msendm' mdeqm' t1LeT2 neg.
    pose proof (deqImpMarksend mdeqm') as [t5 [t5LeT3 msendm'T5]].
    pose proof (uniqMarksend2 msendm' msendm'T5) as t2EqT5.
    assert (t30: t3 = 0) by omega.
    rewrite t2EqT5, t30 in *.
    assert (t1Le0: t1 <= 0) by omega.
    assert (t10: t1 = 0) by intuition.
    assert (t50: t5 = 0) by omega.
    rewrite t10, t50 in *.
    omega.
    
    destruct IHt as [cons [cross [cReqResp cRespResp]]].

    assert (cross': forall to0, to0 <= S t -> state c a to0 <= dir p c a to0).
    intros tm toLtT.
    destruct (classical (exists ts, ts < tm /\ ((exists m, deq mch c p a ts m) \/
      (exists m, marksend mch p c a ts m)))) as [chnge|noChnge].
    pose proof (maxExists' classical chnge) as lastChnge; clear chnge.
    destruct lastChnge as [ts [tsLtTo [deqOrSend noPrevChnge]]].
    assert (eq: dir p c a (S ts) = dir p c a tm) by (
      assert (two: S ts = tm \/ S ts < tm) by omega;
        destruct two as [eq|less]; [
          intuition|
            apply dir.noChange; [ intuition | generalize noPrevChnge; clear; firstorder]]).
    destruct deqOrSend as [[m mdeqm] | [m msendm]].
    pose proof (deqImpMarksend mdeqm) as [t' [t'LeTs msendm]].
    destruct (classical (exists tc, t' < tc < tm /\ exists m, deq mch p c a tc m)) as [deq|noDeq].
    destruct deq as [tc [comp [m' mdeqm']]].
    pose proof (deqImpMarksend mdeqm') as [t'' [t''LeTc msendm']].
    assert (gOrl: t'' > ts \/ t'' <= ts) by omega.
    destruct gOrl as [t''GtTs | t''LeTs].
    assert (t''LtTc: t'' < tm) by omega.
    generalize noPrevChnge msendm' t''LtTc t''GtTs; clear; firstorder.
    assert (t'LeT: t' <= t) by omega.
    assert (t''LeT: t'' <= t) by omega.
    assert (hyp1: forall tc', tc' < t' -> ~ deq mch p c a tc' m') by (
      unfold not; intros tc' tc'LtT' mdeqm'Tc';
        pose proof (uniqDeq2 mdeqm' mdeqm'Tc'); intuition).
    assert (hyp2: forall tp', tp' < t'' -> ~ deq mch c p a tp' m) by (
      unfold not; intros tp' tp'LtT'' mdeqmTp';
        pose proof (uniqDeq2 mdeqm mdeqmTp'); intuition).
    pose proof (cross t' t'' t'LeT t''LeT m msendm m' msendm' hyp1 hyp2).
    firstorder.
    assert (noDeq': ~ (exists tc, S t' <= tc < tm /\ exists m, deq mch p c a tc m /\ to m >= state c a tm)) by
      (
        unfold not; intros [tc [cond [m0 [mdeqm0 _]]]];
          assert (cond': t' < tc < tm) by omega; generalize noDeq cond' mdeqm0; clear; firstorder).
    assert (nGt: ~ state c a tm > state c a (S t')) by (
      assert (eqOrGt: tm = S t' \/ tm > S t') by omega;
        destruct eqOrGt as [toEqSt' | toGtSt']; [
          rewrite <- toEqSt';
            omega |
              pose proof (@st.whenChildHigh a (S t') tm toGtSt') as contra;
                generalize contra noDeq'; clear; firstorder]).
    assert (dirEqSt: dir p c a (S ts) = state c a (S t')) by (
      pose proof (st.sendmChange msendm) as one;
        pose proof (dir.deqmChange mdeqm) as two;
          unfold st.st, dir.st in *;
            congruence).
    assert (stoLesSt': state c a tm <= state c a (S t')) by omega.
    congruence.
    pose proof (dir.sendmImpDeqr msendm) as [r rdeqr].
    pose proof (deqImpMarksend rdeqr) as [t' [t'LeTs rsendr]].
    destruct (classical (exists tc, tc < tm /\ deq mch p c a tc m)) as [[tc [tcLtTo mdeqm]] | notEx].
    assert (eqOrNot: tm = S tc \/ tm > S tc) by omega.
    destruct eqOrNot as [toEqStc | toGtStc].
    assert (dirEqSt: state c a tm = dir p c a tm) by (
      pose proof (dir.sendmChange msendm) as one; pose proof (st.deqmChange mdeqm) as two;
        unfold st.st, dir.st in *; congruence).
    omega.
    assert (noLower: ~ exists t'', S tc <= t'' < tm /\ exists m', deq mch p c a t'' m' /\ to m' >= state c a tm)
      by (
        unfold not; intros [t'' [cond [m' [mdeqm' _]]]];
          pose proof (deqImpMarksend mdeqm') as [tf [tfLeT'' msendm']];
            assert (diff: ts = tf \/ tf < ts \/ tf > ts) by omega;
              destruct diff as [tsEqTf | [tfLtTs | tfGtTs]]; [
                rewrite <- tsEqTf in *;
                  pose proof (uniqMarksend1 msendm msendm') as mEqM';
                    rewrite <- mEqM' in *;
                      pose proof (uniqDeq2 mdeqm mdeqm') as tcEqT'';
                        omega |
                          assert (t'LeTc: t' <= tc) by (
                            pose proof (deqImpMarksend mdeqm) as [tsome [tsomeLe'' msendmTsome]];
                              pose proof (uniqMarksend2 msendm msendmTsome) as tcEqTsome;
                                rewrite <- tcEqTsome in *; omega);
                          pose proof @cReqPRespCross;
                            assert (cross1: forall tc', tc' < t' -> ~ deq mch p c a tc' m') by (
                              unfold not; intros tc' tc'LtT' mdeqm'Tc';
                                pose proof (uniqDeq2 mdeqm' mdeqm'Tc') as t'EqTc'; omega);
                            assert (cross2: forall tp', tp' <= tf -> ~ deq rch c p a tp' r) by (
                              unfold not; intros tp' tp'LeTf rdeqrTp';
                                pose proof (uniqDeq2 rdeqr rdeqrTp') as tfEqTp'; omega);
                            assert (t''LeT: t'' <= t) by omega;
                              assert (tfLeT: tf <= t) by omega;
                                apply (cReqPRespCross rsendr msendm' cross1 cross2)|
                                  assert (cond2: ts < tf < tm) by omega;
                                    generalize cond2 noPrevChnge msendm'; clear; firstorder]).
    pose proof (@st.whenChildHigh a (S tc) tm toGtStc) as contra.
    assert (not: ~ state c a tm > state c a (S tc)) by (generalize noLower contra; clear; firstorder).
    assert (not2: state c a tm <= state c a (S tc)) by omega; clear not.
    assert (dirEqSt: dir p c a (S ts) = state c a (S tc)) by (
      pose proof (dir.sendmChange msendm) as one; pose proof (st.deqmChange mdeqm) as two;
        unfold st.st, dir.st in *; congruence).
    omega.
    assert (tsLeT: ts <= t) by omega.
    assert (less: state c a ts <= dir p c a ts) by firstorder.
    assert (tmGtTs: tm > t') by omega.
    assert (noDeq: ~ exists t'', t' <= t'' < tm /\ exists m, deq mch p c a t'' m /\ to m >= state c a tm) by (
      unfold not; intros [t'' [cond [m' [mdeqm' _]]]];
        pose proof (deqImpMarksend mdeqm') as [t1 [t1LeT'' msendm']];
          assert (t1NeTs: t1 = ts -> False) by (
            intros t1EqTs; rewrite t1EqTs in *;
              pose proof (uniqMarksend1 msendm msendm') as mEqm';
                rewrite <- mEqm' in *; 
                  generalize notEx cond mdeqm'; clear; firstorder);
          assert (eqOrNot: t1 = ts \/ t1 > ts \/ t1 < ts) by omega;
            destruct eqOrNot as [t1EqTs | [t1GtTs | t1LtTs]];
              [firstorder |
                assert (cond2: ts < t1 < tm) by omega;
                  generalize noPrevChnge cond2 msendm'; clear; firstorder |
                    assert (one: forall tc', tc' < t' -> ~ deq mch p c a tc' m') by (
                      unfold not; intros tc' tc'LtT' mdeqm'Tc';
                        pose proof (uniqDeq2 mdeqm' mdeqm'Tc') as t''EqTc'; omega);
                    assert (two: forall tp', tp' <= t1 -> ~ deq rch c p a tp' r) by (
                      unfold not; intros tp' tp'LeT1 rdeqrTp';
                        pose proof (uniqDeq2 rdeqr rdeqrTp') as tsEqTp'; omega);
                    apply (cReqPRespCross rsendr msendm' one two)]).
    assert (contra1: ~ state c a tm > state c a t') by (
      unfold not; intros contra;
        generalize (st.whenChildHigh tmGtTs contra) noDeq; clear; firstorder).
    assert (cont: state c a tm <= state c a t') by omega.
    pose proof (st.sendrImpSt rsendr) as toRGtDir; unfold st.toRSComp in toRGtDir; unfold st.st in *.
    pose proof (dir.sendmImpDeqrGe msendm rdeqr) as toMGeToR.
    pose proof (dir.sendmChange msendm) as toMEq; unfold dir.st in *.
    omega.
    assert (eqOrNot: 0 = tm \/ 0 < tm) by omega.
    destruct eqOrNot as [tmEq0 | tmGt0].
    rewrite <- tmEq0 in *; pose proof @init as init; rewrite init in *; omega.
    assert (premise: forall tn, 0 <= tn < tm -> (forall m, ~ marksend mch p c a tn m) /\
      (forall m, ~ deq mch c p a tn m)) by (
        intros tn [_ tnLtTm];
          constructor;
            unfold not; intros m msendm;
              generalize noChnge tnLtTm msendm; clear; firstorder).
    pose proof (dir.noChange tmGt0 premise) as dir0DirTm; unfold dir.st in *.
    pose proof @st.whenChildHigh.
    assert (not: ~ exists t'', 0 <= t'' < tm /\ exists m, deq mch p c a t'' m /\ to m >= state c a tm) by (
      unfold not; intros [t'' [[_ t''LtTm] [m [mdeqm _]]]];
        pose proof (deqImpMarksend mdeqm) as [t' [t'LeT'' msendm]];
          assert (t'LtTm: t' < tm) by omega;
            generalize noChnge t'LtTm msendm; clear; firstorder).
    assert (done: ~ state c a tm > state c a 0) by (generalize (@st.whenChildHigh a 0 tm tmGt0) not;
      clear; firstorder).
    pose proof (@init a) as start; omega.

    constructor.
    apply cross'.

    assert (cReqResp': forall {t1 t2 t3}, t3 <= S t -> forall {m}, marksend mch c p a t1 m -> forall {r},
      marksend rch c p a t2 r -> deq rch c p a t3 r -> t1 <= t2 -> (forall t4, t4 < t3 -> ~ deq mch c p a t4 m) ->
      False).
    intros t1 t2 t3 t3LeSt m msendm r rsendr rdeqr t1LeT2 neg.
    unfold Time in *.
    assert (eqOrNot: t1 = t2 \/ t1 < t2) by omega.
    destruct eqOrNot as [t1EqT2 | t1LtT2].
    rewrite t1EqT2 in *.
    pose proof (st.noSendmSendr msendm rsendr); intuition.
    clear t1LeT2.
    pose proof (deqImpMarksend rdeqr) as [t' [t'LeT3 rsend'r]].
    pose proof (uniqMarksend2 rsendr rsend'r) as t2EqT'.
    rewrite <- t2EqT' in *.
    clear rsend'r t2EqT'.
    assert (t1LeT: t1 <= t) by omega.
    pose proof (cons t1 t1LeT) as st1Ledt1.

    assert (notty1: ~ exists t'', t1 <= t'' < t2 /\ exists m, deq mch p c a t'' m /\ to m >= state c a t2) by (
      unfold not; intros [t'' [cond [m0 [mdeqm0 _]]]];
        pose proof (deqImpMarksend mdeqm0) as [t5 [t5LeT'' msendm0]];
          assert (one: forall tc', tc' < t1 -> ~ deq mch p c a tc' m0) by (
            unfold not; intros tc' tc'LtT1 mdeqM0Tc';
              pose proof (uniqDeq2 mdeqm0 mdeqM0Tc') as t''EqTc';
                rewrite <- t''EqTc' in *; omega);
          assert (two: forall tp', tp' < t5 -> ~ deq mch c p a tp' m) by (
            unfold not; intros tp' tp'LtT5; assert (t5LtT3: tp' < t3) by omega; firstorder);
          assert (t5Let: t5 <= t) by omega;
            apply (cross t1 t5 t1LeT t5Let m msendm m0 msendm0 one two)).
    assert (notty: ~ exists t'', S t1 <= t'' < t2 /\ exists m, deq mch p c a t'' m /\ to m >= state c a t2) by (
      clear cRespResp;
        unfold not; intros [t'' [cond ex]];
          assert (cond2: t1 <= t'' < t2) by omega;
            generalize notty1 cond2 ex; clear; firstorder).
    
    assert (notst2Gtst1: ~ state c a t2 > state c a (S t1)) by (
      clear cRespResp;
        clear notty1; assert (eqOrNot: S t1 = t2 \/ S t1 < t2) by omega;
          destruct eqOrNot as [eq| St1LtT2]; [
            rewrite eq;
              omega|
                unfold not; intros st; pose proof (st.whenChildHigh St1LtT2 st) as some; firstorder]).
    assert (stt2LestT1: state c a t2 <= state c a (S t1)) by omega.
    pose proof (dir.deqrCond rdeqr) as fromRLe.
    pose proof (st.sendrFrom rsendr) as fromREq; unfold st.st in *.
    pose proof (st.sendmImpSt msendm) as stGt.
    pose proof (st.sendmChange msendm) as stEq; unfold st.st in *.
    rewrite fromREq, <- stEq in *.
    assert (drGt: dir p c a t1 > dir p c a t3) by omega.
    assert (drNe: dir p c a t1 <> dir p c a t3) by omega.
    assert (sendDeq: ~ forall tn, t1 <= tn < t3 -> (forall m, ~ marksend mch p c a tn m) /\
      (forall m, ~ deq mch c p a tn m)) by (
        unfold not; intros exp; assert (t1LtT3: t1 < t3) by omega; pose proof (dir.noChange t1LtT3 exp); firstorder).
    assert (noSend: forall tn, t1 <= tn < t3 -> forall m, ~ marksend mch p c a tn m) by (
      clear cRespResp;
        unfold not; intros tn cond m0 msendm0;
          assert (tnLeT: tn <= t) by omega;
            assert (one: forall tc', tc' < t1 -> ~ deq mch p c a tc' m0) by (
              unfold not; intros tc' tc'LtT1 mdeqm0;
                pose proof (deqImpMarksend mdeqm0) as [tm [tmLeTc' msend'm0]];
                  pose proof (uniqMarksend2 msendm0 msend'm0) as tmEqTc';
                    rewrite <- tmEqTc' in *; omega);
            assert (two: forall tp', tp' < tn -> ~ deq mch c p a tp' m) by (
              unfold not; intros tp' tp'LtTn; assert (tp'LtT3: tp' < t3) by omega; firstorder);
            apply (cross t1 tn t1LeT tnLeT m msendm m0 msendm0 one two)).

    destruct (classical (exists tn, tn < t3 /\ t1 <= tn /\ exists m0, deq mch c p a tn m0)) as [ext|noEx].
    pose proof (maxExists' classical ext) as [tn [cond [[tnLtT3 [m0 mdeqm0]] notAfter]]].
    
    pose proof (deqImpMarksend mdeqm0) as [tr [trLeTn msendm0]].
    assert (opts: tr = t1 \/ tr > t1 \/ tr < t1) by omega.
    destruct opts as [trEqT1 | [trGtT1 | trLtT1]].
    rewrite trEqT1 in *.
    pose proof (uniqMarksend1 msendm msendm0) as mEqm0.
    rewrite <- mEqm0 in *.
    generalize neg cond mdeqm0; clear; firstorder.
    assert (tnLeT: tn <= t) by omega.
    assert (cond2: forall t4, t4 < tn -> ~ deq mch c p a t4 m) by (
      intros t4 t4LtTn; assert (t4LtT3: t4 < t3) by omega;
        generalize neg t4LtT3; clear; firstorder).
    apply (cRespResp t1 tr tn tnLeT m msendm m0 msendm0 mdeqm0 trGtT1 cond2).
    assert (notty2': ~ exists t'', tr <= t'' < t1 /\ exists m, deq mch p c a t'' m /\ to m >= state c a t1) by (
      unfold not; intros [t'' [cond2 [m1 [mdeqm1 _]]]];
        pose proof (deqImpMarksend mdeqm1) as [t5 [t5LeT'' msendm1]];
          assert (trLeT: tr <= t) by omega;
            assert (t5LeT: t5 <= t) by omega;
              assert (one: forall tc', tc' < tr -> ~ deq mch p c a tc' m1) by (
                unfold not; intros tc' tc'LtTr mdeq'm1;
                  pose proof (uniqDeq2 mdeqm1 mdeq'm1) as t''EqTc';
                    rewrite <- t''EqTc' in *;
                      omega);
              assert (two: forall tp', tp' < t5 -> ~ deq mch c p a tp' m0) by (
                unfold not; intros tp' tp'LtT5 mdeq'm0;
                  pose proof (uniqDeq2 mdeqm0 mdeq'm0) as tnEqTp';
                    rewrite <- tnEqTp' in *; omega);
              apply (cross tr t5 trLeT t5LeT m0 msendm0 m1 msendm1 one two)).
    assert (notty2: ~ exists t'', S tr <= t'' < t1 /\ exists m, deq mch p c a t'' m /\ to m >= state c a t1) by (
      unfold not; intros [t'' [cond1 rest]]; assert (cond2: tr <= t'' < t1) by omega;
        generalize notty2' cond2 rest; clear; firstorder).
    assert (strLeT1: S tr <= t1) by omega.
    pose proof (st.whenChildHighConv strLeT1 notty2) as st1LeTr.
    pose proof (st.whenChildHighConv t1LtT2 notty) as sST1LeT2.
    assert (trLtT3: tr < t3) by omega.
    assert (noC: forall tn0, S tn <= tn0 < t3 -> (forall m, ~ marksend mch p c a tn0 m) /\
      (forall m, ~ deq mch c p a tn0 m)) by (
        intros tn0 cond2;
          constructor; [assert (cond3: t1 <= tn0 < t3) by omega; generalize noSend cond3; clear; firstorder|
            assert (cond4: tn < tn0 < t3) by omega; 
              assert (t1LeTn0: t1 <= tn0) by omega; generalize cond4 t1LeTn0 notAfter; clear; firstorder]).
    assert (sTnLtT3: S tn <= t3) by omega.
    pose proof (dir.noChange2 sTnLtT3 noC) as dirEq.
    unfold dir.st in *.
    generalize st1LeTr sST1LeT2 sTnLtT3 dirEq rsendr rdeqr msendm msendm0 mdeqm0; clear; intros.
    pose proof (st.sendmChange msendm) as sEqTom.
    pose proof (st.sendmImpSt msendm) as sGtTom.
    pose proof (dir.deqmChange mdeqm0) as dSEqTom0.
    pose proof (st.sendmChange msendm0) as sSEqTom0.
    pose proof (dir.deqrCond rdeqr) as dLeFromr.
    pose proof (st.sendrFrom rsendr) as sEqFromr.
    unfold st.st, dir.st in *. omega.
    generalize sendDeq noSend noEx; clear; firstorder.

    constructor.

    intros tc tp tcLeSt tpLeSt mc msendmc mp msendmp nodeqmp nodeqmc.
    pose proof (dir.sendmImpDeqr msendmp) as [r rdeqr].
    pose proof (deqImpMarksend rdeqr) as [t1 [t1LeTp rsendr]].
    assert (opts: t1 = tc \/ tc < t1 \/ t1 < tc) by omega.
    destruct opts as [t1EqTc | [tcLtT1 | t1LtTc]].
    rewrite t1EqTc in *.
    apply (st.noSendmSendr msendmc rsendr).
    assert (tcLeT1: tc <= t1) by omega.
    apply (cReqResp' tc t1 tp tpLeSt mc msendmc r rsendr rdeqr tcLeT1 nodeqmc).
    destruct (classical (exists tm, t1 <= tm < tc /\ exists m, deq mch p c a tm m)) as [ext|noExt].
    destruct ext as [tm [[t1LeTm tmLtTc] [m deqm]]].
    pose proof (deqImpMarksend deqm) as [tn [tnLeTm sendm]].
    assert (opts: tn = tp \/ tn < tp \/ tn > tp) by omega.
    destruct opts as [tnEqTp | [tnLtTp | tnGtTp]].
    rewrite tnEqTp in *.
    pose proof (uniqMarksend1 sendm msendmp) as mEqMp.
    rewrite mEqMp in *.
    firstorder.
    assert (one: forall tc', tc' < t1 -> ~ deq mch p c a tc' m) by (
      unfold not; intros tc' tc'LtT1 deq'm;
        pose proof (uniqDeq2 deqm deq'm) as tmEqTc';
          omega).
    assert (two: forall tp', tp' <= tn -> ~ deq rch c p a tp' r) by (
      unfold not; intros tp' tp'LeTn deq'r;
        pose proof (uniqDeq2 rdeqr deq'r) as tpEqTp';
          omega).
    apply (cReqPRespCross rsendr sendm one two).
    pose proof (dir.sendmImpDeqr sendm) as [r1 deqr1].
    pose proof (deqImpMarksend deqr1) as [tq [tqLeTn sendr1]].
    assert (one: forall tc', tc' < tq -> ~ deq mch p c a tc' mp) by (
      unfold not; intros tc' tc'LtTq; assert (tc'LtTc: tc' < tc) by omega;
        apply (nodeqmp tc' tc'LtTc)).
    assert (two: forall tp', tp' <= tp -> ~ deq rch c p a tp' r1) by (
      unfold not; intros tp' tp'LeTp deq'r1;
        pose proof (uniqDeq2 deqr1 deq'r1) as tpEqTp';
          omega).
    apply (cReqPRespCross sendr1 msendmp one two).
    assert (opt: ~ exists tm, t1 <= tm < tc /\ exists m, deq mch p c a tm m) by (
      generalize noExt; clear; firstorder).
    assert (opt': forall t', t1 < t' <= tc -> ~ exists tm, t1 <= tm < t' /\ exists m,
      deq mch p c a tm m /\ to m >= state c a t') by (
        unfold not; intros t' t'LtTc [tm [cond rest]]; assert (cond2: t1 <= tm < tc) by omega;
          generalize opt t'LtTc cond2 rest; clear; firstorder).
    assert (notSth: forall t', t1 < t' <= tc -> ~ state c a t' > state c a t1) by (
      unfold not; intros t' [t1LtT' t'LeTc] sgt;
        pose proof (st.whenChildHigh t1LtT' sgt) as contra;
          generalize opt' contra t1LtT' t'LeTc; clear; firstorder).
    assert (stcLet1: forall t', t1 < t' <= tc -> state c a t' <= state c a t1) by (intros t' cond;
      specialize (notSth t' cond); omega).
    clear notSth opt opt'.
    pose proof (st.sendrImpSt rsendr) as gtRel.
    unfold st.toRSComp, st.st in *.
    assert (stcLet2: forall t', t1 < t' <= tc -> state c a t' < to r) by (
      intros t' cond; specialize (stcLet1 t' cond); omega).
    clear stcLet1 gtRel.
    pose proof (st.voluntary rsendr t1LtTc msendmc stcLet2) as [r1 [deqr1 sTcGtToR1]].
    pose proof (deqImpMarksend deqr1) as [t2 [t2LeT1 sendr1]].
    assert (t2LeTp: t2 = tp \/ t2 > tp \/ t2 < tp) by omega.
    destruct t2LeTp as [t2EqTp | [t2GtTp | t2LtTp]].
    rewrite t2EqTp in *.
    apply (dir.noSendmSendr msendmp sendr1).
    assert (tpLeT2: tp <= t2) by omega.
    pose proof (pRespReq noTwoPResp noTwoPReqNon msendmp sendr1 deqr1 tpLeT2) as [t4 [t4LtTp deqmp]].
    generalize nodeqmp deqmp t4LtTp; clear; firstorder.
    pose proof (dir.sendrImpNoSendm t2LtTp sendr1 msendmp) as [t' [[t2LtT' t'LtTp] [m [deqm toMGeToR1]]]].
    pose proof (deqImpMarksend deqm) as [t'' [t''LeT' sendm]].
    pose proof (st.sendmChange sendm) as stEqToM. unfold st.st in *.
    assert (stTcGtStST'': state c a tc > state c a (S t'')) by omega.
    assert (opts: t'' = tc \/ t'' > tc \/ t'' < tc) by omega.
    destruct opts as [t''EqTc | [t''GtTc | t''LtTc]].
    rewrite t''EqTc in *.
    pose proof (uniqMarksend1 msendmc sendm) as mEqMc.
    rewrite mEqMc in *.
    generalize t'LtTp deqm nodeqmc; clear; firstorder.
    assert (t'Let: t' <= t) by omega.
    assert (nodeq: forall t4, t4 < t' -> ~ deq mch c p a t4 mc) by (
      unfold not; intros t4 t4LtT'; assert (t4LtTp: t4 < tp) by omega;
        generalize nodeqmc t4LtTp; clear; firstorder).
    apply (cRespResp tc t'' t' t'Let mc msendmc m sendm deqm t''GtTc); intuition.
    assert (opts: S t'' = tc \/ S t'' < tc) by omega.
    destruct opts as [St''EqTc | St''LtTc].
    rewrite St''EqTc in *.
    omega.
    pose proof (st.whenChildHigh St''LtTc stTcGtStST'') as [ts [cond [s [deqs _]]]].
    pose proof (deqImpMarksend deqs) as [tsr [tsrLeTs sends]].
    assert (opts: tsr = t' \/ tsr > t' \/ tsr < t') by omega.
    destruct opts as [tsrEqT' | [tsrGtT' | tsrLtT']].
    rewrite tsrEqT' in *.
    apply (dir.noSendmDeqm sends deqm).
    assert (t2LeTsr: t2 <= tsr) by omega.
    pose proof (pReqResp noTwoPResp noTwoPReqNon sendr1 sends deqs t2LeTsr) as [tf [tfLtTs deq'r1]].
    assert (tfLtTc: tf < tc) by omega.
    pose proof (uniqDeq2 deqr1 deq'r1) as tcEqTf.
    omega.
    assert (t''LeT: t'' <= t) by omega.
    assert (tsrLeT: tsr <= t) by omega.
    assert (one: forall tc', tc' < t'' -> ~ deq mch p c a tc' s) by (
      unfold not; intros tc' tc'LtT'' deq's; pose proof (uniqDeq2 deqs deq's) as tc'EqT';
        rewrite tc'EqT' in *; omega).
    assert (two: forall tp', tp' < tsr -> ~ deq mch c p a tp' m) by (
      unfold not; intros tp' tp'LtTsr deq'm; pose proof (uniqDeq2 deqm deq'm) as tp'EqTsr;
        omega).
    apply (cross t'' tsr t''LeT tsrLeT  m sendm s sends one two).

    constructor.
    intuition.

    intros t1 t2 t3 t3LeSt m msendm r rsendr rdeqr t1LeT2 neg.
    unfold Time in *.
    assert (eqOrNot: t1 = t2 \/ t1 < t2) by omega.
    destruct eqOrNot as [t1EqT2 | t1LtT2].
    rewrite t1EqT2 in *.
    pose proof (uniqMarksend1 msendm rsendr) as mEqR; omega.
    clear t1LeT2.
    pose proof (deqImpMarksend rdeqr) as [t' [t'LeT3 rsend'r]].
    pose proof (uniqMarksend2 rsendr rsend'r) as t2EqT'.
    rewrite <- t2EqT' in *.
    clear rsend'r t2EqT'.
    assert (t1LeT: t1 <= t) by omega.
    pose proof (cons t1 t1LeT) as st1Ledt1.

    assert (notty1: ~ exists t'', t1 <= t'' < t2 /\ exists m, deq mch p c a t'' m /\ to m >= state c a t2) by (
      unfold not; intros [t'' [cond [m0 [mdeqm0 _]]]];
        pose proof (deqImpMarksend mdeqm0) as [t5 [t5LeT'' msendm0]];
          assert (one: forall tc', tc' < t1 -> ~ deq mch p c a tc' m0) by (
            unfold not; intros tc' tc'LtT1 mdeqM0Tc';
              pose proof (uniqDeq2 mdeqm0 mdeqM0Tc') as t''EqTc';
                rewrite <- t''EqTc' in *; omega);
          assert (two: forall tp', tp' < t5 -> ~ deq mch c p a tp' m) by (
            unfold not; intros tp' tp'LtT5; assert (t5LtT3: tp' < t3) by omega; firstorder);
          assert (t5Let: t5 <= t) by omega;
            apply (cross t1 t5 t1LeT t5Let m msendm m0 msendm0 one two)).
    assert (notty: ~ exists t'', S t1 <= t'' < t2 /\ exists m, deq mch p c a t'' m /\ to m >= state c a t2) by (
      clear cRespResp;
        unfold not; intros [t'' [cond ex]];
          assert (cond2: t1 <= t'' < t2) by omega;
            generalize notty1 cond2 ex; clear; firstorder).
    
    assert (notst2Gtst1: ~ state c a t2 > state c a (S t1)) by (
      clear cRespResp;
        clear notty1; assert (eqOrNot: S t1 = t2 \/ S t1 < t2) by omega;
          destruct eqOrNot as [eq| St1LtT2]; [
            rewrite eq;
              omega|
                unfold not; intros st; pose proof (st.whenChildHigh St1LtT2 st) as some; firstorder]).
    assert (stt2LestT1: state c a t2 <= state c a (S t1)) by omega.
    pose proof (dir.deqmCond rdeqr) as fromRLe.
    pose proof (st.sendmFrom rsendr) as fromREq; unfold st.st in *.
    pose proof (st.sendmImpSt msendm) as stGt.
    pose proof (st.sendmChange msendm) as stEq; unfold st.st in *.
    rewrite fromREq, <- stEq in *.
    assert (drGt: dir p c a t1 > dir p c a t3) by omega.
    assert (drNe: dir p c a t1 <> dir p c a t3) by omega.
    assert (sendDeq: ~ forall tn, t1 <= tn < t3 -> (forall m, ~ marksend mch p c a tn m) /\
      (forall m, ~ deq mch c p a tn m)) by (
        unfold not; intros exp; assert (t1LtT3: t1 < t3) by omega; pose proof (dir.noChange t1LtT3 exp); firstorder).
    assert (noSend: forall tn, t1 <= tn < t3 -> forall m, ~ marksend mch p c a tn m) by (
      clear cRespResp;
        unfold not; intros tn cond m0 msendm0;
          assert (tnLeT: tn <= t) by omega;
            assert (one: forall tc', tc' < t1 -> ~ deq mch p c a tc' m0) by (
              unfold not; intros tc' tc'LtT1 mdeqm0;
                pose proof (deqImpMarksend mdeqm0) as [tm [tmLeTc' msend'm0]];
                  pose proof (uniqMarksend2 msendm0 msend'm0) as tmEqTc';
                    rewrite <- tmEqTc' in *; omega);
            assert (two: forall tp', tp' < tn -> ~ deq mch c p a tp' m) by (
              unfold not; intros tp' tp'LtTn; assert (tp'LtT3: tp' < t3) by omega; firstorder);
            apply (cross t1 tn t1LeT tnLeT m msendm m0 msendm0 one two)).

    destruct (classical (exists tn, tn < t3 /\ t1 <= tn /\ exists m0, deq mch c p a tn m0)) as [ext|noEx].
    pose proof (maxExists' classical ext) as [tn [cond [[tnLtT3 [m0 mdeqm0]] notAfter]]].
    
    pose proof (deqImpMarksend mdeqm0) as [tr [trLeTn msendm0]].
    assert (opts: tr = t1 \/ tr > t1 \/ tr < t1) by omega.
    destruct opts as [trEqT1 | [trGtT1 | trLtT1]].
    rewrite trEqT1 in *.
    pose proof (uniqMarksend1 msendm msendm0) as mEqm0.
    rewrite <- mEqm0 in *.
    generalize neg cond mdeqm0; clear; firstorder.
    assert (tnLeT: tn <= t) by omega.
    assert (cond2: forall t4, t4 < tn -> ~ deq mch c p a t4 m) by (
      intros t4 t4LtTn; assert (t4LtT3: t4 < t3) by omega;
        generalize neg t4LtT3; clear; firstorder).
    apply (cRespResp t1 tr tn tnLeT m msendm m0 msendm0 mdeqm0 trGtT1 cond2).
    assert (notty2': ~ exists t'', tr <= t'' < t1 /\ exists m, deq mch p c a t'' m /\ to m >= state c a t1) by (
      unfold not; intros [t'' [cond2 [m1 [mdeqm1 _]]]];
        pose proof (deqImpMarksend mdeqm1) as [t5 [t5LeT'' msendm1]];
          assert (trLeT: tr <= t) by omega;
            assert (t5LeT: t5 <= t) by omega;
              assert (one: forall tc', tc' < tr -> ~ deq mch p c a tc' m1) by (
                unfold not; intros tc' tc'LtTr mdeq'm1;
                  pose proof (uniqDeq2 mdeqm1 mdeq'm1) as t''EqTc';
                    rewrite <- t''EqTc' in *;
                      omega);
              assert (two: forall tp', tp' < t5 -> ~ deq mch c p a tp' m0) by (
                unfold not; intros tp' tp'LtT5 mdeq'm0;
                  pose proof (uniqDeq2 mdeqm0 mdeq'm0) as tnEqTp';
                    rewrite <- tnEqTp' in *; omega);
              apply (cross tr t5 trLeT t5LeT m0 msendm0 m1 msendm1 one two)).
    assert (notty2: ~ exists t'', S tr <= t'' < t1 /\ exists m, deq mch p c a t'' m /\ to m >= state c a t1) by (
      unfold not; intros [t'' [cond1 rest]]; assert (cond2: tr <= t'' < t1) by omega;
        generalize notty2' cond2 rest; clear; firstorder).
    assert (strLeT1: S tr <= t1) by omega.
    pose proof (st.whenChildHighConv strLeT1 notty2) as st1LeTr.
    pose proof (st.whenChildHighConv t1LtT2 notty) as sST1LeT2.
    assert (trLtT3: tr < t3) by omega.
    assert (noC: forall tn0, S tn <= tn0 < t3 -> (forall m, ~ marksend mch p c a tn0 m) /\
      (forall m, ~ deq mch c p a tn0 m)) by (
        intros tn0 cond2;
          constructor; [assert (cond3: t1 <= tn0 < t3) by omega; generalize noSend cond3; clear; firstorder|
            assert (cond4: tn < tn0 < t3) by omega; 
              assert (t1LeTn0: t1 <= tn0) by omega; generalize cond4 t1LeTn0 notAfter; clear; firstorder]).
    assert (sTnLtT3: S tn <= t3) by omega.
    pose proof (dir.noChange2 sTnLtT3 noC) as dirEq.
    unfold dir.st in *.
    generalize st1LeTr sST1LeT2 sTnLtT3 dirEq rsendr rdeqr msendm msendm0 mdeqm0; clear; intros.
    pose proof (st.sendmChange msendm) as sEqTom.
    pose proof (st.sendmImpSt msendm) as sGtTom.
    pose proof (dir.deqmChange mdeqm0) as dSEqTom0.
    pose proof (st.sendmChange msendm0) as sSEqTom0.
    pose proof (dir.deqmCond rdeqr) as dLeFromr.
    pose proof (st.sendmFrom rsendr) as sEqFromr.
    unfold st.st, dir.st in *. omega.
    generalize sendDeq noSend noEx; clear; firstorder.
  Qed.

  Theorem conservative: forall {a t}, dir p c a t >= state c a t.
  Proof.
    intros a t.
    pose proof (@mainInd a t) as [first _].
    assert (tLeT: t <= t) by omega; firstorder.
  Qed.

  Lemma cRespFifo: forall {a t1 t2 t3 m1 m2}, marksend mch c p a t1 m1 -> marksend mch c p a t2 m2 ->
    deq mch c p a t3 m2 -> t1 < t2 -> (forall t4, t4 < t3 -> ~ deq mch c p a t4 m1) -> False.
  Proof.
    intros a t1 t2 t3 m1 m2 sendm1 sendm2 deqm2 t1LtT2.
    pose proof (@mainInd a t3) as [_ [_ [_ last]]].
    specialize (last t1 t2 t3).
    assert (t3LeT3: t3 <= t3) by omega.
    firstorder.
  Qed.

  Lemma cross: forall {a t1 t2 m1 m2}, marksend mch c p a t1 m1 -> marksend mch p c a t2 m2 ->
    (forall t3, t3 < t1 -> ~ deq mch p c a t3 m2) -> (forall t4, t4 < t2 -> ~ deq mch c p a t4 m1) -> False.
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

  Theorem cReqRespSent: forall {a t1 t2 r}, marksend rch p c a t1 r -> deq rch p c a t2 r ->
    to r >= state c a t2 -> exists t3, t3 < t2 /\ exists m, marksend mch c p a t3 m /\ to m <= to r /\
      (forall t4, t4 < t1 -> ~ deq mch c p a t4 m).
  Proof.
    intros a t1 t2 r sendr deqr toRGestT2.
    destruct (classical (exists t3, t3 < t2 /\ exists m, marksend mch c p a t3 m /\ to m <= to r /\ forall t4,
      t4 < t1 -> ~ deq mch c p a t4 m)) as [easy|hard].
    intuition.
    pose proof (deqImpMarksend deqr) as [t1' [t1LeT2 send'r]].
    pose proof (uniqMarksend2 sendr send'r) as t1'EqT1.
    rewrite <- t1'EqT1 in *.
    clear t1'EqT1 send'r t1'.

    destruct (classical (exists t, t < t1 /\ ((exists m, deq mch c p a t m) \/
      (exists m, marksend mch p c a t m)))) as [ex | notEx].
    pose proof (maxExists' classical ex) as [t [tLtT1 [sendOrDeq notAfter]]].
    assert (nothing: forall y, S t <= y < t1 -> (forall m, ~ marksend mch p c a y m) /\
      (forall m, ~ deq mch c p a y m)) by
    (intros y cond; assert (cond2: t < y < t1)by omega; generalize cond2 notAfter; clear; firstorder).
    pose proof (dir.noChange2 tLtT1 nothing) as dirEq.
    clear nothing; unfold dir.st in *.
    destruct sendOrDeq as [[m deqm] | [m sendm]].
    pose proof (deqImpMarksend deqm) as [t' [t'LeT sendm]].
    assert (noCDeq: forall tm, t' <= tm < t2 -> forall m', ~ deq mch p c a tm m') by (
      unfold not; intros tm cond m' deqm';
        pose proof (deqImpMarksend deqm') as [ts [tsLeTm sendm']];
          assert (opts: ts < t \/ ts = t \/ t < ts < t1 \/ t1 <= ts) by omega;
            destruct opts as [tsLtT | [tsEqT | [tLtTsLtT1  | t1LeTs ]]]; [
              assert (one: forall x, x < t' -> ~ deq mch p c a x m') by ( unfold not; intros x xLtT' deq'm';
                pose proof (uniqDeq2 deqm' deq'm') as xEqTm; omega);
              assert (two: forall x, x < ts -> ~ deq mch c p a x m) by (unfold not; intros x xLtTs deq'm;
                pose proof (uniqDeq2 deqm deq'm) as xEqTs; omega);
              apply (cross sendm sendm' one two) |
                rewrite tsEqT in *;
                  apply (dir.noSendmDeqm sendm' deqm) |
                    generalize notAfter tLtTsLtT1 sendm'; clear; firstorder |
                      pose proof (pReqResp noTwoPResp noTwoPReqNon sendr sendm' deqm' t1LeTs) as [t4 [t4LtTm deq'r]];
                        pose proof (uniqDeq2 deqr deq'r) as t4EqT2; omega]).
    destruct (classical (exists ts, ts < t2 /\ t' < ts /\ exists m', marksend mch c p a ts m'))
      as [ ex2 | notEx2].
    pose proof (maxExists' classical ex2) as [ts [tsLtT2 [[t'LtTs [m' sendm']] notAfter2]]].
    assert (nothing: forall y, S ts <= y < t2 ->
      (forall m, ~ marksend mch c p a y m) /\ (forall m, ~ deq mch p c a y m)) by
    (intros y cond; assert (cond1: t' < y < t2) by omega; assert (cond2: t' <= y < t2) by omega;
      generalize notAfter2 noCDeq cond cond1 cond2; clear; firstorder).
    pose proof (st.noChange2 tsLtT2 nothing) as stEq.
    unfold st.st in *.
    destruct (classical (exists tr, tr < t1 /\ deq mch c p a tr m')) as [ [tr [trLtT1 deqm']] | noDeq].
    assert (opts: tr < t \/ tr = t \/ t < tr < t1) by omega.
    destruct opts as [trLtT | [trEqT | cond]].
    assert (forall t4, t4 < tr -> ~ deq mch c p a t4 m) by (
      unfold not; intros t4 t4LtTr deq'm; pose proof (uniqDeq2 deqm deq'm) as t4EqT; omega).
    pose proof (cRespFifo sendm sendm' deqm' t'LtTs). intuition.
    rewrite trEqT in *.
    pose proof (uniqDeq1 deqm deqm') as mEqM'.
    rewrite mEqM' in *.
    pose proof (uniqMarksend2 sendm sendm') as t'EqTs.
    omega.
    generalize notAfter cond deqm'; clear; firstorder.
    assert (opts: to m' <= to r \/ to m' > to r) by omega.
    destruct opts as [toM'LeToR | toM'GtToR].
    generalize tsLtT2 sendm' toM'LeToR noDeq; clear; firstorder.
    pose proof (st.sendmChange sendm') as stEqToM'.
    unfold st.st in *.
    omega.
    assert (nothing: forall y, S t' <= y < t2 ->
      (forall m, ~ marksend mch c p a y m) /\ (forall m, ~ deq mch p c a y m)) by
    (intros y cond; assert (cond2: t' <= y < t2) by omega;
      generalize notEx2 noCDeq cond cond2; clear; firstorder).
    assert (t'LeT2: S t' <= t2) by omega.
    pose proof (st.noChange2 t'LeT2 nothing) as stEq.
    pose proof (dir.sendrImpSt sendr) as toRLtD.
    pose proof (st.sendmChange sendm) as st1.
    pose proof (dir.deqmChange deqm) as st2.
    unfold st.st, dir.st, dir.toRSComp in *.
    omega.

    assert (tLeT1: t <= t1) by omega.
    pose proof (pRespReq noTwoPResp noTwoPReqNon sendm sendr deqr tLeT1) as [t' [t'LtT2 deqm]].
    pose proof (deqImpMarksend deqm) as [t'' [tLeT' send'm]].
    pose proof (uniqMarksend2 sendm send'm) as t''EqT.
    rewrite <- t''EqT in *. clear t''EqT t'' send'm.
    assert (noCDeq: forall tm, t' < tm < t2 -> forall m', ~ deq mch p c a tm m').
    unfold not; intros tm cond m' deqm';
      pose proof (deqImpMarksend deqm') as [ts [tsLeTm sendm']];
        assert (opts: ts < t \/ ts = t \/ t < ts < t1 \/ t1 <= ts) by omega;
          destruct opts as [tsLtT | [tsEqT | [tLtTsLtT1  | t1LeTs ]]]; [
            pose proof (dir.sendmImpDeqr sendm) as [r' deqr'];
              pose proof (deqImpMarksend deqr') as [tx [txLeT sendr']];
                assert (one: forall t3, t3 < tx -> ~ deq mch p c a t3 m') by (
                  unfold not; intros t3 t3LtTx deq'm'; pose proof (uniqDeq2 deqm' deq'm') as t3EqTr;
                    omega);
                assert (two: forall t4, t4 <= ts -> ~ deq rch c p a t4 r') by (
                  unfold not; intros t4 t4LeTs deq'r'; pose proof (uniqDeq2 deqr' deq'r') as t4EqTs;
                    omega);
                apply (cReqPRespCross sendr' sendm' one two)|
                  rewrite tsEqT in *; pose proof (uniqMarksend1 sendm sendm') as mEqM'; rewrite mEqM' in *;
                    pose proof (uniqDeq2 deqm deqm') as trEqT'; omega |
                      generalize notAfter tLtTsLtT1 sendm'; clear; firstorder |
                        pose proof (pReqResp noTwoPResp noTwoPReqNon sendr sendm' deqm' t1LeTs) as [t4 [t4LtTm deq'r]];
                          pose proof (uniqDeq2 deqr deq'r) as t4EqT2; omega].
    
    destruct (classical (exists ts, ts < t2 /\ t' < ts /\ exists m', marksend mch c p a ts m'))
      as [ ex2 | notEx2].
    pose proof (maxExists' classical ex2) as [ts [tsLtT2 [[t'LtTs [m' sendm']] notAfter2]]].
    assert (nothing: forall y, S ts <= y < t2 ->
      (forall m, ~ marksend mch c p a y m) /\ (forall m, ~ deq mch p c a y m)) by
    (intros y cond; assert (cond1: t' < y < t2) by omega;
      generalize notAfter2 noCDeq cond cond1; clear; firstorder).
    pose proof (st.noChange2 tsLtT2 nothing) as stEq.
    unfold st.st in *.
    destruct (classical (exists tr, tr < t1 /\ deq mch c p a tr m')) as [ [tr [trLtT1 deqm']] | noDeq].
    pose proof (deqImpMarksend deqm') as [ts' [ts'LeTr send'm']].
    pose proof (uniqMarksend2 send'm' sendm') as ts'EqTs.
    assert (trGtT: tr > t) by omega.
    clear ts' ts'LeTr send'm' ts'EqTs.
    assert (opts: t < tr < t1 \/ t1 <= tr) by omega.
    destruct opts as [cond1 | t1LeTr].
    generalize cond1 notAfter deqm'; clear; firstorder.
    assert (opts: to m' <= to r \/ to m' > to r) by omega.
    destruct opts as [toM'LeToR | toM'GtToR].
    assert (noDeq: forall t4, t4 < t1 -> ~ deq mch c p a t4 m') by (
      unfold not; intros t4 t4LtT1 deq'm'; pose proof (uniqDeq2 deqm' deq'm') as t4EqTr; omega).
    generalize tsLtT2 sendm' toM'LeToR noDeq; clear; firstorder.
    pose proof (st.sendmChange sendm') as stEqToM'.
    unfold st.st in *.
    omega.
    assert (last: forall t4, t4 < t1 -> ~ deq mch c p a t4 m') by (generalize noDeq; clear; firstorder).
    assert (opts: to m' <= to r \/ to m' > to r) by omega.
    destruct opts as [toM'LeToR | toM'GtToR].
    generalize last tsLtT2 toM'LeToR sendm'; clear; firstorder.
    pose proof (st.sendmChange sendm') as stEqToM'.
    unfold st.st in *.
    omega.
    assert (nothing: forall y, S t' <= y < t2 ->
      (forall m, ~ marksend mch c p a y m) /\ (forall m, ~ deq mch p c a y m)) by
    (generalize noCDeq notEx2; clear; firstorder).
    pose proof (st.noChange2 t'LtT2 nothing) as stEq.
    unfold st.st in *.
    pose proof (st.deqmChange deqm) as st1.
    pose proof (dir.sendmChange sendm) as d1.
    pose proof (dir.sendrImpSt sendr) as d2.
    unfold dir.toRSComp, dir.st, st.st in *.
    omega.
    assert (cNoDeq: forall t4, t4 < t2 -> forall m, ~ deq mch p c a t4 m) by (
      unfold not; intros t4 t4LtT2 m deqm; pose proof (deqImpMarksend deqm) as [t3 [t3LeT4 sendm]];
        assert (opts: t3 < t1 \/ t3 >= t1) by omega;
          destruct opts as [t3LtT1 | t4GeT1]; [
            generalize notEx t3LtT1 sendm; clear; firstorder;
              intuition |
                pose proof (pReqResp noTwoPResp noTwoPReqNon sendr sendm deqm t4GeT1) as [t5 [t4LtT4 deq'r]];
                  pose proof (uniqDeq2 deqr deq'r) as t5EqT2; omega]).
    destruct (classical (exists t3, t3 < t2 /\ exists m, marksend mch c p a t3 m)) as [ex2 | notEx2].
    pose proof (maxExists' classical ex2) as [ts [tsLtT2 [[m' sendm'] notAfter2]]].
    assert (nothing: forall y, S ts <= y < t2 ->
      (forall m, ~ marksend mch c p a y m) /\ (forall m, ~ deq mch p c a y m)) by
    (intros y cond;
      generalize notAfter2 cNoDeq cond; clear; firstorder).
    pose proof (st.noChange2 tsLtT2 nothing) as stEq.
    unfold st.st in *.
    destruct (classical (exists tr, tr < t1 /\ deq mch c p a tr m')) as [ [tr [trLtT1 deqm']] | noDeq].
    generalize notEx trLtT1 deqm'; clear; firstorder.
    assert (opts: to m' <= to r \/ to m' > to r) by omega.
    destruct opts as [toM'LeToR | toM'GtToR].
    generalize toM'LeToR noDeq tsLtT2 sendm'; clear; firstorder.
    pose proof (st.sendmChange sendm') as stEqToM'.
    unfold st.st in *.
    omega.
    assert (nothing1: forall y, 0 <= y < t2 ->
      (forall m, ~ marksend mch c p a y m) /\ (forall m, ~ deq mch p c a y m)) by
    (generalize cNoDeq notEx2; clear; firstorder).
    assert (x1: 0 <= t2) by omega.
    pose proof (st.noChange2 x1 nothing1) as st1.
    assert (nothing2: forall y, 0 <= y < t1 ->
      (forall m, ~ marksend mch p c a y m) /\ (forall m, ~ deq mch c p a y m)) by
    (generalize notEx; clear; firstorder).
    assert (x2: 0 <= t1) by omega.
    pose proof (dir.noChange2 x2 nothing2) as d1.
    pose proof (@init a) as start.
    pose proof (dir.sendrImpSt sendr) as d2.
    unfold dir.toRSComp, dir.st, dir.st, stSemi.st in *.
    omega.
  Qed.

  Lemma vol: forall {a t}, forall {t1 r1}, marksend rch p c a t1 r1 ->
    forall {t2 m2}, marksend mch c p a t2 m2 ->
    forall {t3}, t3 <= t -> t1 <= t3 -> deq mch c p a t3 m2 ->
      (forall {t4}, t4 <= t2 -> ~ deq rch p c a t4 r1) ->
      (forall {t5}, t1 < t5 <= t3 -> forall r, ~ marksend rch p c a t5 r) ->
        forall r3, deq rch p c a t2 r3 -> to r3 < state c a t2 -> False.
  Proof.
    intros a.
    induction t.

    intros t1 r1 sendr1 t2 m2 sendm2 t3 t3LeT t1LeT3 deqm2 notDeqr1 notSendr r3
      deqr3 toR3LtStT2.
    unfold Time in *.
    pose proof (ch.deqImpMarksend deqm2) as [t' [t'LeT3 send'm2]].
    pose proof (ch.uniqMarksend2 sendm2 send'm2) as t'EqT2.
    assert (t3Eq0: t3 = 0) by omega.
    assert (t2Eq0: t2 = 0) by omega.
    assert (t1Eq0: t1 = 0) by omega.
    rewrite t3Eq0, t2Eq0, t1Eq0 in *; clear t' t'LeT3 send'm2 t'EqT2 t1Eq0
      t2Eq0 t3Eq0 t3LeT t1LeT3.
    pose proof (ch.deqImpMarksend deqr3) as [t' [t'Le0 send'r3]].
    assert (t'Eq0: t' = 0) by omega; rewrite t'Eq0 in *.
    pose proof (ch.uniqMarksend1 sendr1 send'r3) as r1EqR3.
    rewrite r1EqR3 in *.
    firstorder.

    intros t1 r1 sendr1 t2 m2 sendm2 t3 t3LeT t1LeT3 deqm2 notDeqr1 notSendr r3
      deqr3 toR3LtStT2.
    unfold Time in *.
    pose proof (ch.deqImpMarksend deqm2) as [t' [t2LeT3 send'm2]].
    pose proof (ch.uniqMarksend2 sendm2 send'm2) as t'EqT2.
    rewrite <- t'EqT2 in *; clear send'm2 t' t'EqT2.
    pose proof (ch.deqImpMarksend deqr3) as [ts [tsLeT2 sendr3]].
    assert (opts: ts > t3 \/ t1 < ts <= t3 \/ ts = t1 \/ ts < t1) by omega.
    destruct opts as [tsGtT3 | [cond | [tsEqT1 | tsLtT1]]].
    omega.
    generalize notSendr cond sendr3; clear; firstorder.
    assert (t2LeT2: t2 <= t2) by omega.
    rewrite tsEqT1 in *. pose proof (ch.uniqMarksend1 sendr3 sendr1) as r1EqR3.
    rewrite r1EqR3 in *.
    generalize notDeqr1 t2LeT2 deqr3; clear; firstorder.
    pose proof (dir.sendrImpNoSendr tsLtT1 sendr3 sendr1) as exist. 
    unfold dir.st, dir.toRSComp in *.
    destruct exist as [tx [cond dirLt']].
(*    pose proof (minExists classical exist) as [tx [[cond dirLt'] notBefore]]. *)
    assert (dirLt: dir p c a tx <= to r3) by omega; clear dirLt'.
    pose proof (dir.sendrImpSt sendr3) as gt.
    unfold dir.st, dir.toRSComp in *.
    assert (dirGt: dir p c a ts > dir p c a tx) by omega.
    destruct (classical (exists tn, ts <= tn < tx /\ ((exists m, marksend mch p c a tn m) \/
    (exists m, deq mch c p a tn m /\ to m <= to r3)))) as [sth|notExist].
    destruct (minExists classical sth) as [tn [[cond2 sendOrDeq] notBefore]].
    (* destruct sth as [tn [cond2 sendOrDeq]]. *)
    destruct sendOrDeq as [[m sendm] | [m [deqm toMLeToR3]]].
    assert (opts: ts = tn \/ ts < tn) by omega.
    destruct opts as [tsEqTn | tsLtTn].
    rewrite tsEqTn in *.
    apply (dir.noSendmSendr sendm sendr3).
    pose proof (dir.sendrImpNoSendm tsLtTn sendr3 sendm) as [t' [cond3 [m' [deqm' toM'LeToR3]]]].
    assert (cond4: ts <= t' < tx) by omega.
    assert (cond5: t' < tn) by omega.
    generalize notBefore deqm' toM'LeToR3 cond4 cond5; clear; firstorder.
    pose proof (ch.deqImpMarksend deqm) as [t'' [t''Letn sendm]].
    assert (opts: t'' > t2 \/ t'' = t2 \/ t'' < t2) by omega.
    destruct opts as [t''GtT2 | [t''EqT2 | t''LtT2]].
    assert (notDeq: forall tq, tq < tn -> ~ deq mch c p a tq m2) by (
      unfold not; intros tq tqLtTn deqq;
        pose proof (ch.uniqDeq2 deqq deqm2) as tqEqT'';
          omega).
    apply (cRespFifo sendm2 sendm deqm t''GtT2 notDeq).
    rewrite t''EqT2 in *.
    pose proof (ch.uniqMarksend1 sendm sendm2) as mEqM2.
    rewrite mEqM2 in *.
    pose proof (ch.uniqDeq2 deqm deqm2) as t3EqTn.
    omega.
    assert (nothing: forall ty, t'' <= ty < t2 -> forall q, ~ deq mch p c a ty q).
    unfold not; intros ty cond3 q deqq.
    assert (opts: t'' = ty \/ t'' < ty) by omega.
    destruct opts as [t''EqTy | t''LtTy].
    rewrite t''EqTy in *.
    apply (st.noSendmDeqm sendm deqq).
    pose proof (ch.deqImpMarksend deqq) as [tz [tzLeTy sendq]].
    assert (opts: tz < ts \/ tz = ts \/ tz > ts) by omega.
    destruct opts as [tzLtTs | [tzEqTs | tzGtTs]].
    assert (tzLtT1: tz < t1) by omega.
    assert (one: forall t0, t0 < t'' -> ~ deq mch p c a t0 q) by (
      unfold not; intros t0 t0LtT'' deq'q;
        pose proof (ch.uniqDeq2 deqq deq'q) as t0EqTz;
          omega).
    assert (two: forall t0, t0 < tz -> ~ deq mch c p a t0 m) by (
      unfold not; intros t0 t0LtTz deq'm;
        pose proof (ch.uniqDeq2 deqm deq'm); omega).
    apply (cross sendm sendq one two).
    rewrite tzEqTs in *.
    apply (dir.noSendmSendr sendq sendr3).
    pose proof @pReqResp.
    assert (tsLeTz: ts <= tz) by omega.
    pose proof (pReqResp noTwoPResp noTwoPReqNon sendr3 sendq deqq tsLeTz) as sth2.
    destruct sth2 as [t4 [t4LtTy deq'r3]].
    pose proof (ch.uniqDeq2 deqr3 deq'r3); omega.
    assert (nothing2: forall ty, S t'' <= ty < t2 -> forall q, ~ deq mch p c a ty q) by (
      intros ty cond4; assert (h: t'' <= ty < t2) by omega; generalize h nothing; clear;
        firstorder).
    assert (nothing3: ~ exists ty, S t'' <= ty < t2 /\ exists q, deq mch p c a ty q /\
      to q >= state c a t2) by (generalize nothing2; clear; firstorder).
    pose proof (st.whenChildHighConv t''LtT2 nothing3) as stLe.
    assert (contra: ~ exists tk, tk < tn /\ ts <= tk /\ exists m, marksend mch p c a tk m) by (
      unfold not; intros [tk [tkLtTn [tsLeTk rest]]]; assert (h: ts <= tk < tx) by omega;
        generalize notBefore h tkLtTn tsLeTk rest; clear; firstorder).
    assert (tsLeTn: ts <= tn) by omega.
    assert (contra2: ~ dir p c a tn > dir p c a ts) by (unfold not; intros sttt;
      pose proof (dir.whenDirLow tsLeTn sttt) as sth3; generalize contra sth3; clear; firstorder).
    assert (good: dir p c a tn <= dir p c a ts) by omega.
    pose proof (st.sendmChange sendm) as eq1.
    pose proof (dir.deqmChange deqm) as eq2.
    pose proof (st.sendmImpSt sendm) as eq3.
    pose proof (st.sendmFrom sendm) as eq4.
    pose proof (dir.deqmCond deqm) as eq5.
    unfold dir.st, st.st in *.
    omega.
    assert (tsLeTx: ts <= tx) by omega.
    pose proof (dir.sendrFrom sendr3).
    pose proof (dir.sendrImpSt sendr3).
    unfold dir.st, dir.toRSComp in *.
    pose proof (dir.dirCantGoLower H0 tsLeTx notExist).
    omega.
  Qed.

  Lemma pReqsCVolRespReqLt: forall {t a t1 t2 r1 r2}, t1 <= t -> t2 <= t ->
    marksend rch p c a t1 r1 ->
    marksend rch p c a t2 r2 -> t1 < t2 ->
    (forall ts, t1 < ts < t2 -> forall r, ~ marksend rch p c a ts r) ->
    (forall ts, t1 < ts < t2 -> forall m, ~ marksend mch p c a ts m) ->
    (forall t3, t3 <= t -> ~ deq rch p c a t3 r1) ->
    (forall t4, t4 <= t -> ~ deq rch p c a t4 r2) -> exists t5 m, marksend mch c p a t5 m /\
      exists t6, t1 <= t6 < t2 /\ deq mch c p a t6 m /\ 
        (forall r, deq rch p c a t5 r -> to r >= state c a t5) /\ to r2 < to m.
  Proof.
    intros t a t1 t2 r1 r2 t1LeT t2LeT sendr1 sendr2 t1LtT2 noSendR noSendM noDeqR1 noDeqR2.
    pose proof (dir.sendrImpNoSendr t1LtT2 sendr1 sendr2) as ex1.
    assert (ex2: exists t', t' <= t2 /\ t1 < t' /\ ~ dir.toRSComp (to r1) (dir.st a t')) by
      firstorder.
    pose proof (maxExists classical ex2) as [t' [t'LeT2 [[t1LtT' dir1] notAfter1]]].
    pose proof (dir.sendrImpSt sendr1) as dirSth.
    unfold dir.toRSComp, dir.st in *.
    assert (dirNotEq: dir p c a t' <> dir p c a t1) by omega.
    destruct (classical (exists tn, tn < t' /\ t1 <= tn /\ ((exists m, marksend mch p c a tn m) \/
      exists m, deq mch c p a tn m))) as [ext|easy].
    pose proof (maxExists' classical ext) as [tn [tnLtT'[[t1LeTn sendOrDeq] notAfter]]].
    destruct sendOrDeq as [[m sendm] | [m deqm]].
    unfold Time in *.
    assert (opts: t1 = tn \/ t1 < tn) by omega.
    destruct opts as [t1EqTn | t1LtTn].
    rewrite t1EqTn in *.
    pose proof (dir.noSendmSendr sendm sendr1) as false; firstorder.
    assert (tnLtT2: tn < t2) by omega.
    generalize noSendM t1LtTn tnLtT2 sendm; clear; firstorder.
    assert (tnLeTn: tn <= tn) by omega.
    pose proof (ch.deqImpMarksend deqm) as [tm [tmLeTn sendm]].
    assert (noDeq'R1: forall t4, t4 <= tm -> ~ deq rch p c a t4 r1) by (
      unfold not; intros t4 cond4 deqr1; assert (sth: t4 <= t) by omega;
        generalize noDeqR1 sth deqr1; clear; firstorder).
    assert (noSendAny: forall t5, t1 < t5 <= tn -> forall r, ~ marksend rch p c a t5 r) by (
      intros t5 cond4; assert (sth: t1 < t5 < t2) by omega; generalize noSendR sth;
        clear; firstorder).
    pose proof (vol sendr1 sendm tnLeTn t1LeTn deqm noDeq'R1 noSendAny) as isVol.
    assert (isVolR: forall r3, deq rch p c a tm r3 -> to r3 >= state c a tm) by (
      intros r3 deq'r3; specialize (isVol r3 deq'r3); omega).
    assert (cond3: t1 <= tn < t2) by omega.
    assert (StnLeT': S tn <= t') by omega.
    assert (noChange: forall tx, S tn <= tx < t' -> (forall m, ~ marksend mch p c a tx m) /\
      forall m, ~ deq mch c p a tx m) by (intros tx cond2;
        assert (cond4: tn < tx < t') by omega; assert (cond6: t1 <= tx) by omega;
          generalize notAfter cond4 cond6; clear; firstorder).
    pose proof (dir.noChange2 StnLeT' noChange) as dirEq1.
    unfold dirSemi.st in *.
    assert (t'LeT1: t' <= t2) by omega.
    assert (contra: ~ dir p c a t2 > dir p c a t') by (unfold not; intros d;
      pose proof (dir.whenDirLow t'LeT1 d) as [t'' [cond rest]];
        assert (condn: t1 < t'' < t2) by omega; generalize noSendM condn rest; clear; firstorder).
    assert (real: dir p c a t2 <= dir p c a t') by omega.
    pose proof (dir.deqmChange deqm) as eq1.
    pose proof (dir.sendrImpSt sendr2) as eq2.
    unfold dir.st, dir.toRSComp in *.
    assert (H: to r2 < to m) by omega.
    generalize sendm cond3 deqm isVolR H; clear; firstorder.
    assert (Hik: forall tn, t1 <= tn < t' -> (forall m, ~ marksend mch p c a tn m) /\
      (forall m, ~ deq mch c p a tn m)) by (generalize easy; clear; firstorder).
    pose proof (dir.noChange t1LtT' Hik).
    unfold dirSemi.st in *.
    omega.
  Qed.
End PairTheorems.