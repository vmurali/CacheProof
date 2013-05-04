Require Import Arith Omega.

Load Useful.

Module Type DataTypes.
  Parameter Cache: Type.
  Parameter Mesg: Type.
  Parameter Addr: Type.

  Parameter parent: Cache -> Cache.
  Definition State := nat.
  Definition Time := nat.
  Parameter state: Cache -> Addr -> Time -> State.
  Parameter dir: Cache -> Cache -> Addr -> Time -> State.

  Parameter from: Mesg -> State.
  Parameter to: Mesg -> State.
  Parameter time: Mesg -> Time.
  Parameter addr: Mesg -> Addr.

  Parameter timeStamp: Cache -> Addr -> Time -> Time.
  Parameter Channel: Type.

  Parameter mch rch: Channel.
End DataTypes.

Module Type Channel (dt: DataTypes).
  Import dt.

  Variable marksend: Channel -> Cache -> Cache -> Time -> Mesg -> Prop.
  Variable recv: Channel -> Cache -> Cache -> Time -> Mesg -> Prop.

  Section local.
    Context {s: Channel}.
    Context {p c : Cache}.
    Axiom uniqMarksend1: forall {m n t}, marksend s p c t m -> marksend s p c t n -> m = n.
    Axiom uniqMarksend2: forall {m t1 t2}, marksend s p c t1 m -> marksend s p c t2 m -> t1 = t2.
    Axiom uniqRecv1: forall {m n t}, recv s p c t m -> recv s p c t n -> m = n.
    Axiom uniqRecv2: forall {m t1 t2}, recv s p c t1 m -> recv s p c t2 m -> t1 = t2.
    Axiom recvImpMarkSend: forall {m t}, recv s p c t m -> exists t', t' <= t /\ marksend s p c t' m.
  End local.
End Channel.

Module Type ChannelPerAddr (dt: DataTypes).
  Import dt.

  Variable marksend: Channel -> Cache -> Cache -> Addr -> Time -> Mesg -> Prop.
  Variable recv: Channel -> Cache -> Cache -> Addr -> Time -> Mesg -> Prop.

  Section local.
    Context {s: Channel}.
    Context {p c : Cache} {a: Addr}.
    Axiom uniqMarksend1: forall {m n t}, marksend s p c a t m -> marksend s p c a t n -> m = n.
    Axiom uniqMarksend2: forall {m t1 t2}, marksend s p c a t1 m -> marksend s p c a t2 m -> t1 = t2.
    Axiom uniqRecv1: forall {m n t}, recv s p c a t m -> recv s p c a t n -> m = n.
    Axiom uniqRecv2: forall {m t1 t2}, recv s p c a t1 m -> recv s p c a t2 m -> t1 = t2.
    Axiom recvImpMarkSend: forall {m t}, recv s p c a t m -> exists t', t' <= t /\ marksend s p c a t' m.
  End local.
End ChannelPerAddr.

Module mkChannelPerAddr (dt: DataTypes) (ch: Channel dt) : ChannelPerAddr dt.
  Import dt.
  Definition marksend ch p c a t m := ch.marksend ch p c t m /\ addr m = a.
  Definition recv ch p c a t m := ch.recv ch p c t m /\ addr m = a.

  Set Implicit Arguments.
  Section local.
    Variable s: Channel.
    Variable p c : Cache.
    Variable a: Addr.
    Definition uniqMarksend1 {m n t} (sendm : marksend s p c a t m) (sendn : marksend s p c a t n) :=
      ch.uniqMarksend1 (proj1 sendm) (proj1 sendn).
    Definition uniqMarksend2 {m t1 t2} (sendm1: marksend s p c a t1 m) (sendm2: marksend s p c a t2 m) :=
      ch.uniqMarksend2 (proj1 sendm1) (proj1 sendm2).
    Definition uniqRecv1 {m n t} (recvm: recv s p c a t m) (recvn: recv s p c a t n) :=
      ch.uniqRecv1 (proj1 recvm) (proj1 recvn).
    Definition uniqRecv2 {m t1 t2} (recvm1: recv s p c a t1 m) (recvm2: recv s p c a t2 m) :=
      ch.uniqRecv2 (proj1 recvm1) (proj1 recvm2).

    Definition recvImpMarkSend {m t} (recvm: recv s p c a t m) :=
      match ch.recvImpMarkSend (proj1 recvm) with
        | ex_intro x Px => ex_intro (fun t' =>
          t' <= t /\ marksend s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 recvm)))
      end.
  End local.
End mkChannelPerAddr.

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
      (exists m, recv mch dst src a t m).
    Axiom sendmChange: forall {m}, marksend mch src dst a t m -> st a (S t) = to m.
    Axiom recvmChange: forall {m}, recv mch dst src a t m -> st a (S t) = to m.
    Axiom sendrImpSt: forall {r}, marksend rch src dst a t r -> toRSComp (to r) (st a t).
    Axiom sendrImpNoSendr: forall {t1 t2 r1 r2}, t1 < t2 -> marksend rch src dst a t1 r1 ->
      marksend rch src dst a t2 r2 -> exists t', t1 < t' <= t2 /\ ~ toRSComp (to r1) (st a t').
    Axiom sendmFrom: forall {m}, marksend mch src dst a t m -> from m = st a t.
    Axiom sendrFrom: forall {r}, marksend rch src dst a t r -> from r = st a t.
    Axiom sendmTime: forall {m}, marksend mch src dst a t m -> time m = timeStamp src a t.
    Axiom noSendmRecvm: forall {m}, marksend mch src dst a t m ->
      forall {m'}, recv mch dst src a t m' -> False.
    Axiom noSendmSendr: forall {m}, marksend mch src dst a t m -> forall {r}, marksend rch src dst a t r -> False.
  End ForT.
End LocalBehavior.

Module LocalLemmas (dt: DataTypes) (ch: ChannelPerAddr dt) (lb: LocalBehavior dt ch).
  Import dt lb ch.

  Section ForLs.
    Lemma nochange': forall {a t t'}, (forall tn, t <= tn < t + t' ->
      (forall m, ~ marksend mch src dst a tn m) /\ (forall m, ~ recv mch dst src a tn m)) ->
    st a t = st a (t + t').
    Proof.
      intros a t t'.
      induction t'.
      intro false.
      firstorder.
      intros noChange.
      assert (help: forall tn, t <= tn < t + t' -> (forall m, ~ marksend mch src dst a tn m) /\
        (forall m, ~ recv mch dst src a tn m)) by (
          intros tn comp;
            assert (comp2: t <= tn < t + S t') by omega;
              firstorder).
      assert (stTEqstT': st a t = st a (t + t')) by firstorder.
      assert (nothing: (forall m, ~ marksend mch src dst a (t + t') m) /\
        forall m, ~ recv mch dst src a (t + t') m) by
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
      (forall m, ~ marksend mch src dst a tn m) /\ (forall m, ~ recv mch dst src a tn m)) -> st a t = st a t'.
    Proof.
      intros a t t' tLtT'.
      remember (t' - t) as td.
      assert (rew: t' = t + td) by omega.
      rewrite rew in *.
      apply (@nochange' a t).
    Qed.

    Lemma noChange2: forall {a t t'}, t <= t' -> (forall tn, t <= tn < t' ->
      (forall m, ~ marksend mch src dst a tn m) /\ (forall m, ~ recv mch dst src a tn m)) -> st a t = st a t'.
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
        (forall {tm}, t < tm <= t' -> state c a tm < to r) -> exists r1, recv rch p c a t' r1.

    Axiom recvrNoSendm: forall {r}, recv rch p c a t r -> forall {m}, marksend mch c p a t m ->
      state c a t > to r.

    Axiom recvrSendm: forall {r}, recv rch p c a t r -> state c a t > to r -> exists {m}, marksend mch c p a t m.
  End ForT.
End StBase.

Module St (dt: DataTypes) (p: Pair dt) (ch: ChannelPerAddr dt) (st: StSemi dt p ch) (base: StBase dt p ch st).
  Include base.
  Import dt ch st p base.

  Section ForT.
    Context {a: Addr}.
    Lemma whenChildHighRecvm: forall {t}, state c a (S t) > state c a t -> exists m,
      recv mch p c a t m /\ to m = state c a (S t).
    Proof.
      intros t sStgst.
      assert (sStnst: state c a (S t) <> state c a t) by omega.
      pose proof (change sStnst) as [[m sendmm] | [m recvmm] ].
      pose proof (sendmImpSt sendmm) as stgm.
      pose proof (sendmChange sendmm) as sStem.
      unfold st in *.
      omega.
      exists m.
      intuition.
      pose proof (recvmChange recvmm) as sStem.
      unfold src, dst in *.
      intuition.
    Qed.

    Lemma whenChildHigh': forall {t t'}, state c a (S (t' + t)) > state c a t ->
      exists t'', t'' <= t' /\ exists m, recv mch p c a (t'' + t) m /\ to m >= state c a (S (t' + t)).
    Proof.
      intros t t' sSt'tgst.
      induction t'.
      pose proof (whenChildHighRecvm sSt'tgst) as [m [recvmm mesSt]].
      exists 0.
      assert (temp: 0 + t = t) by omega.
      rewrite temp in *; clear temp.
      intuition.
      exists m.
      intuition.
      pose proof (lt_eq_lt_dec (state c a (S (S t' + t))) (state c a (S (t' + t)))) as [[lt | eq] | gt'].
      assert (gt: state c a (S (t' + t)) > state c a t) by omega.
      specialize (IHt' gt).
      destruct IHt' as [t'' [le [m [recvmm mgesSt't]]]].
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
      pose proof (whenChildHighRecvm gt) as [m [recvmm mesSt]].
      exists (S t').
      intuition.
      exists m.
      intuition.
    Qed.

    Lemma whenChildHigh: forall {t t'}, t' > t -> state c a t' > state c a t ->
      exists t'', t <= t'' < t' /\ exists m, recv mch p c a t'' m /\ to m >= state c a t'.
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
      (~ exists t'', t <= t'' < t' /\ exists m, recv mch p c a t'' m /\ to m >= state c a t') ->
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

    Axiom sendmImpRecvr: forall {m}, marksend mch p c a t m -> exists r, recv rch c p a t r.

    Axiom sendmImpRecvrGe: forall {m}, marksend mch p c a t m ->
      forall {r}, recv rch c p a t r -> to m >= to r.

    Axiom recvrCond: forall {r}, recv rch c p a t r -> from r >= dir p c a t.

    Axiom recvmCond: forall {m}, recv mch c p a t m -> from m = dir p c a t.

    Axiom sendrImpNoSendm: forall {t1 t2 r1 m2}, t1 < t2 -> marksend rch p c a t1 r1 ->
      marksend mch p c a t2 m2 ->
      exists t', t1 < t' < t2 /\ exists m, recv mch c p a t' m /\ to m <= to r1.
  End ForT.
End DirBase.

Module Dir (dt: DataTypes) (p: Pair dt) (ch: ChannelPerAddr dt) (d: DirSemi dt p ch) (db: DirBase dt p ch d)
  (s: StSemi dt p ch) (sb: StBase dt p ch s).
  Include db.
  Import dt ch p.
  
  Lemma dirRecvImpLow: forall {a t m}, recv mch c p a t m -> dir p c a t > dir p c a (S t).
  Proof.
    intros a t m recvm.
    pose proof (recvImpMarkSend recvm) as [t' [t'LeT sendm]].
    pose proof (db.recvmChange recvm) as sth.
    pose proof (sb.sendmImpSt sendm) as sth2.
    pose proof (db.recvmCond recvm) as sth3.
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
    pose proof (db.change nestuff) as [sendm | recvm].
    firstorder.
    destruct recvm as [x recvstuff].
    pose proof (dirRecvImpLow recvstuff) as contra.
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
End Dir.

Module Type PairProperties (dt: DataTypes) (ch: ChannelPerAddr dt) (p: Pair dt).
  Import dt ch p.

  Axiom init: forall {a}, dir p c a 0 = state c a 0.

  Definition twoEqPRespFalse := forall a t t1 m1, t1 <= t -> marksend mch p c a t1 m1 ->
    forall t2 m2, t2 <= t -> marksend mch p c a t2 m2 ->
      (forall t3, t3 <= t -> ~ recv mch p c a t3 m1) -> (forall {t4}, t4 <= t -> ~ recv mch p c a t4 m2) ->
      t1 = t2.

  Definition twoPReqNeedsResp := forall a t t1 r1, t1 <= t -> marksend rch p c a t1 r1 -> forall t2 r2,
    t2 <= t -> marksend rch p c a t2 r2 -> (forall t3, t3 <= t -> ~ recv rch p c a t3 r1) ->
    (forall t4, t4 <= t -> ~ recv rch p c a t4 r2) -> to r1 = to r2 -> t1 < t2 ->
    exists tm m, t1 < tm < t2 /\ marksend mch p c a tm m.

  Section ForA.
    Context {a: Addr}.
    Axiom pRespReq: twoEqPRespFalse -> twoPReqNeedsResp -> forall {t1 t2 t3},
      forall {m}, marksend mch p c a t1 m ->
        forall {r}, marksend rch p c a t2 r -> recv rch p c a t3 r -> t1 <= t2 ->
          exists t4, t4 < t3 /\ recv mch p c a t4 m.

    Axiom pReqResp: twoEqPRespFalse -> twoPReqNeedsResp -> forall {t1 t2 t3},
      forall {r}, marksend rch p c a t1 r ->
        forall {m}, marksend mch p c a t2 m -> recv mch p c a t3 m -> t1 <= t2 ->
          exists t4, t4 < t3 /\ recv rch p c a t4 r.
  End ForA.
End PairProperties.

Module Type PairTheoremsType (dt: DataTypes) (ch: ChannelPerAddr dt) (p: Pair dt)
  (pp: PairProperties dt ch p).
  Import dt ch p pp.

  Axiom noTwoPResp: twoEqPRespFalse.
  Axiom noTwoPReqNon: twoPReqNeedsResp.

  Axiom conservative: forall {a t}, dir p c a t >= state c a t.
  Axiom cReqRespSent: forall {a t1 t2 r}, marksend rch p c a t1 r -> recv rch p c a t2 r ->
    to r >= state c a t2 -> exists t3, t3 < t2 /\ exists m, marksend mch c p a t3 m /\ to m <= to r /\
      (forall t4, t4 < t1 -> ~ recv mch c p a t4 m).
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
      marksend mch p c a tp m -> (forall tc', tc' < tc -> ~ recv mch p c a tc' m) ->
      (forall tp', tp' <= tp -> ~ recv rch c p a tp' r) -> False.
  Proof.
    intros a t.
    induction t.
    intros tc tp tcLeT tpLeT r m rsendr msendm mrecvNo rrecvNo.
    assert (tc0: tc = 0) by omega; clear tcLeT.
    assert (tp0: tp = 0) by omega; clear tpLeT.
    rewrite tc0 in *; rewrite tp0 in *; clear tc0 tp0.
    pose proof (dir.sendmImpRecvr msendm) as [r' rrecvr'].
    pose proof (recvImpMarkSend rrecvr') as [t' [t'Le0 rsendr']].
    assert (t'0: t' = 0) by omega; clear t'Le0.
    rewrite t'0 in rsendr'; clear t'0.
    pose proof (uniqMarksend1 rsendr rsendr') as rEqr'.
    rewrite <- rEqr' in *; clear rEqr'.
    assert (zero: 0 <= 0) by omega.
    firstorder.
    intros tc tp tcLeST tpLeST r m rsendr msendm mrecvNo rrecvNo.

    pose proof (dir.sendmImpRecvr msendm) as [r' rrecvr'].
    pose proof (recvImpMarkSend rrecvr') as [t' [t'LeSt rsendr']].

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
    pose proof (st.whenChildHigh t''GtTc tcLtT'') as [t''' [[tcLeT''' t'''LtT''] [m' [mrecvm' _]]]].
    pose proof (recvImpMarkSend mrecvm') as [td [tdLeT''' msendm']].
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

    pose proof (st.sendrImpNoSendr tcGtT' rsendr' rsendr) as [tmur [cond neg]].
    unfold st.toRSComp in *; unfold st.st in *.
    assert (toRLeS: to r' <= state c a tmur) by omega.
    pose proof (st.sendrImpSt rsendr') as toGtt.
    unfold st.toRSComp in *; unfold st.st in *.
    assert (stt'LtstTc: state c a t' < state c a tmur) by omega.
    assert (tmurGtT': tmur > t') by omega.
    pose proof (st.whenChildHigh tmurGtT' stt'LtstTc) as [t'' [[tcLeT'' t''LtT'] [m' [mrecvm' _]]]].
    pose proof (recvImpMarkSend mrecvm') as [td [tdLeT'' msendm']].
    assert (tdLet: td <= t) by omega.
    assert (noRecv: forall tc', tc' < t' -> ~ recv mch p c a tc' m') by (
      unfold not; intros tc' tc'LtTc mrecvm'Tc';
        pose proof (uniqRecv2 mrecvm' mrecvm'Tc') as tc'EqT''; omega).
    assert (opts: td = tp \/ td < tp \/ td > tp) by omega.
    destruct opts as [tdEqTp | [tdLTp | tdGtTp]].
    rewrite tdEqTp in *.
    pose proof (uniqMarksend1 msendm msendm') as mEqm'.
    rewrite <- mEqm' in *.
    assert (t''LtTc: t'' < tc) by omega.
    firstorder.
    assert (noRecv': forall tp', tp' <= td -> ~ recv rch c p a tp' r') by (
      unfold not; intros tp' tp'LeTd rrecvr'Tp';
        pose proof (uniqRecv2 rrecvr' rrecvr'Tp') as tp'EqTp;
          omega).
    assert (t'LeT: t' <= t) by omega.
    apply (IHt t' td t'LeT tdLet r' m' rsendr' msendm' noRecv noRecv').
    pose proof (dir.sendmImpRecvr msendm') as [r'' rrecvr''].
    pose proof (recvImpMarkSend rrecvr'') as [ts [tsLeTd rsendr'']].
    assert (tpLeT: tp <= t) by omega.
    assert (tsLeT: ts <= t) by omega.
    assert (hyp1: forall tc', tc' < ts -> ~ recv mch p c a tc' m) by (
      intros tc' tc'LtTs;
        assert (tc'LtTc: tc' < tc) by omega;
          firstorder).
    assert (hyp2: forall tp', tp' <= tp -> ~ recv rch c p a tp' r'') by (
      unfold not; intros tp' tpLeTp rrecvr''Tp';
        pose proof (uniqRecv2 rrecvr'' rrecvr''Tp') as tdEqTp';
          rewrite <- tdEqTp' in *;
            firstorder).
    apply (IHt ts tp tsLeT tpLeT r'' m rsendr'' msendm hyp1 hyp2).
  Qed.

  Lemma cReqPRespCross: forall {a tc tp r m}, marksend rch c p a tc r ->
    marksend mch p c a tp m -> (forall tc', tc' < tc -> ~ recv mch p c a tc' m) ->
    (forall tp', tp' <= tp -> ~ recv rch c p a tp' r) -> False.
  Proof.
    intros a tc tp.
    assert (tcLeT: tc <= tc + tp) by omega.
    assert (tpLeT: tp <= tc + tp) by omega.
    apply (@cReqPRespCrossInd a (tc + tp) tc tp tcLeT tpLeT).
  Qed.

  Lemma noTwoPResp: twoEqPRespFalse.
  Proof.
    intros a tx t1 m1 t1LeTx sendm1 t2 m2 t2LeTx sendm2 norecvm1 norecvm2.
    pose proof (dir.sendmImpRecvr sendm1) as [r1 recvr1].
    pose proof (dir.sendmImpRecvr sendm2) as [r2 recvr2].
    pose proof (recvImpMarkSend recvr1) as [t3 [t3LeT1 sendr1]].
    pose proof (recvImpMarkSend recvr2) as [t4 [t4LeT2 sendr2]].
    assert (opts: t3 = t4 \/ t3 < t4 \/ t4 < t3) by omega.
    destruct opts as [t3EqT4|[t3LtT4|t4LtT3]].
    rewrite t3EqT4 in *; pose proof (uniqMarksend1 sendr1 sendr2) as r1EqR2.
    rewrite r1EqR2 in *; apply (uniqRecv2 recvr1 recvr2).

    assert (noRecv: ~ exists t, t3 <= t < t4 /\ exists m, recv mch p c a t m) by (
      unfold not; intros [t [cond [m recvm]]];
        pose proof (recvImpMarkSend recvm) as [t5 [t5LeT sendm]];
          assert (opts: t5 = t1 \/ t5 < t1 \/ t5 > t1) by omega;
            destruct opts as [t5EqT1 | [t5LtT1 | t5GtT1]]; [
              rewrite t5EqT1 in *; pose proof (uniqMarksend1 sendm1 sendm) as m1EqM;
                rewrite m1EqM in *; assert (tLeTx: t <= tx) by omega;
                  generalize tLeTx norecvm1 recvm; clear; firstorder |
                    assert (one: forall tc', tc' < t3 -> ~ recv mch p c a tc' m) by (
                      unfold not; intros tc' tc'LtT3 recv'm; pose proof (uniqRecv2 recvm recv'm) as tEqTc';
                        rewrite tEqTc' in *; firstorder);
                    assert (two: forall tp', tp' <= t5 -> ~ recv rch c p a tp' r1) by (
                      unfold not; intros tp' tp'LeT1 recv'r1; pose proof (uniqRecv2 recvr1 recv'r1) as t5EqTp';
                        rewrite <- t5EqTp' in *; firstorder);
                    apply (cReqPRespCross sendr1 sendm one two) |
                      pose proof (dir.sendmImpRecvr sendm) as [r recvr];
                        pose proof (recvImpMarkSend recvr) as [t6 [t6LeT5 sendr]];
                          assert (one: forall tc', tc' < t6 -> ~ recv mch p c a tc' m1) by (
                            unfold not; intros tc' tc'LtT6 recv'm1; assert (tc'LeT6: tc' <= tx) by omega;
                              generalize norecvm1 recv'm1 tc'LeT6; clear; firstorder);
                          assert (two: forall tp', tp' <= t1 -> ~ recv rch c p a tp' r) by (
                            unfold not; intros tp' tp'LeT1 recv'r; pose proof (uniqRecv2 recvr recv'r) as t1EqTp';
                              rewrite <- t1EqTp' in *; firstorder);
                          apply (cReqPRespCross sendr sendm1 one two)]).
    assert (t3LeT4: t3 <= t4) by omega.
    pose proof (st.sendrImpSt sendr1) as stG. unfold st.st, st.toRSComp in *.
    pose proof (st.sendrImpNoSendr t3LtT4 sendr1 sendr2) as [t5 [t3LtT5LeT4 neg]].
    unfold st.toRSComp, st.st in *.
    assert (pos: state c a t5 > state c a t3) by omega.
    assert (noRecv': ~ exists t, t3 <= t < t5 /\ exists m, recv mch p c a t m /\ to m >= state c a t5) by (
      unfold not; intros [t [cond1 [mg [recvmg _]]]];
        assert (cond: t3 <= t < t4) by omega;
          generalize recvmg cond noRecv; clear; firstorder).
    assert (t3LeT5: t3 <= t5) by omega.
    pose proof (st.whenChildHighConv t3LeT5 noRecv') as stContra.
    omega.

    assert (noRecv: ~ exists t, t4 <= t < t3 /\ exists m, recv mch p c a t m) by (
      unfold not; intros [t [cond [m recvm]]];
        pose proof (recvImpMarkSend recvm) as [t5 [t5LeT sendm]];
          assert (opts: t5 = t2 \/ t5 < t2 \/ t5 > t2) by omega;
            destruct opts as [t5EqT1 | [t5LtT1 | t5GtT1]]; [
              rewrite t5EqT1 in *; pose proof (uniqMarksend1 sendm2 sendm) as m1EqM;
                rewrite m1EqM in *; assert (tLeTx: t <= tx) by omega;
                  generalize tLeTx norecvm2 recvm; clear; firstorder |
                    assert (one: forall tc', tc' < t4 -> ~ recv mch p c a tc' m) by (
                      unfold not; intros tc' tc'LtT3 recv'm; pose proof (uniqRecv2 recvm recv'm) as tEqTc';
                        rewrite tEqTc' in *; firstorder);
                    assert (two: forall tp', tp' <= t5 -> ~ recv rch c p a tp' r2) by (
                      unfold not; intros tp' tp'LeT1 recv'r1; pose proof (uniqRecv2 recvr2 recv'r1) as t5EqTp';
                        rewrite <- t5EqTp' in *; firstorder);
                    apply (cReqPRespCross sendr2 sendm one two)|
                      pose proof (dir.sendmImpRecvr sendm) as [r recvr];
                        pose proof (recvImpMarkSend recvr) as [t6 [t6LeT5 sendr]];
                          assert (one: forall tc', tc' < t6 -> ~ recv mch p c a tc' m2) by (
                            unfold not; intros tc' tc'LtT6 recv'm1; assert (tc'LeT6: tc' <= tx) by omega;
                              generalize norecvm2 recv'm1 tc'LeT6; clear; firstorder);
                          assert (two: forall tp', tp' <= t2 -> ~ recv rch c p a tp' r) by (
                            unfold not; intros tp' tp'LeT1 recv'r; pose proof (uniqRecv2 recvr recv'r) as t1EqTp';
                              rewrite <- t1EqTp' in *; firstorder);
                          apply (cReqPRespCross sendr sendm2 one two)]).
    assert (t3LeT4: t4 <= t3) by omega.
    pose proof (st.sendrImpSt sendr2) as stG. unfold st.st, st.toRSComp in *.
    pose proof (st.sendrImpNoSendr t4LtT3 sendr2 sendr1) as [t5 [t3LtT5LeT4 neg]].
    unfold st.toRSComp, st.st in *.
    assert (pos: state c a t5 > state c a t4) by omega.
    assert (noRecv': ~ exists t, t4 <= t < t5 /\ exists m, recv mch p c a t m /\ to m >= state c a t5) by (
      unfold not; intros [t [cond1 [mg [recvmg _]]]];
        assert (cond: t4 <= t < t3) by omega;
          generalize recvmg cond noRecv; clear; firstorder).
    assert (t3LeT5: t4 <= t5) by omega.
    pose proof (st.whenChildHighConv t3LeT5 noRecv') as stContra.
    omega.
  Qed.

  Lemma noTwoPReqNon: twoPReqNeedsResp.
  Proof.
    intros a t t1 r1 t1LeT sendr1 t2 r2 t2LeT sendr2 norecvr1 norecvr2 toR1EqToR2 t1LtT2.
    pose proof (dir.sendrImpSt sendr1) as gt1.
    pose proof (dir.sendrImpSt sendr2) as gt2.
    unfold dir.toRSComp, dir.st.
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
      forall {mp}, marksend mch p c a tp mp -> (forall tc', tc' < tc -> ~ recv mch p c a tc' mp) ->
        (forall tp', tp' < tp -> ~ recv mch c p a tp' mc) -> False) /\
    (forall {t1 t2 t3}, t3 <= t -> forall {m}, marksend mch c p a t1 m ->
      forall {r}, marksend rch c p a t2 r -> recv rch c p a t3 r -> t1 <= t2 ->
        (forall t4, t4 < t3 -> ~ recv mch c p a t4 m) -> False) /\
    (forall {t1 t2 t3}, t3 <= t -> forall {m}, marksend mch c p a t1 m ->
      forall {m'}, marksend mch c p a t2 m' -> recv mch c p a t3 m' -> t1 < t2 ->
        (forall t4, t4 < t3 -> ~ recv mch c p a t4 m) -> False).
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
    pose proof (dir.sendmImpRecvr msendmp) as [r rrecvr].
    pose proof (recvImpMarkSend rrecvr) as [t' [t'Le0 rsendr]].
    assert (t'Eq0: t' = 0) by omega.
    rewrite t'Eq0 in *.
    apply (st.noSendmSendr msendmc rsendr).
    constructor.
    intros t1 t2 t3 t3Le0 m msendm r rsendr rrecvr t1LeT2 neg.
    pose proof (recvImpMarkSend rrecvr) as [t5 [t5LeT3 rsendrT5]].
    pose proof (uniqMarksend2 rsendr rsendrT5) as t2EqT5.
    assert (t30: t3 = 0) by omega.
    rewrite t2EqT5, t30 in *.
    assert (t1Le0: t1 <= 0) by omega.
    assert (t10: t1 = 0) by intuition.
    assert (t50: t5 = 0) by omega.
    rewrite t10, t50 in *.
    apply (st.noSendmSendr msendm rsendr).
    intros t1 t2 t3 t3Le0 m msendm m' msendm' mrecvm' t1LeT2 neg.
    pose proof (recvImpMarkSend mrecvm') as [t5 [t5LeT3 msendm'T5]].
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
    destruct (classical (exists ts, ts < tm /\ ((exists m, recv mch c p a ts m) \/
      (exists m, marksend mch p c a ts m)))) as [chnge|noChnge].
    pose proof (maxExists' classical chnge) as lastChnge; clear chnge.
    destruct lastChnge as [ts [tsLtTo [recvOrSend noPrevChnge]]].
    assert (eq: dir p c a (S ts) = dir p c a tm) by (
      assert (two: S ts = tm \/ S ts < tm) by omega;
        destruct two as [eq|less]; [
          intuition|
            apply dir.noChange; [ intuition | generalize noPrevChnge; clear; firstorder]]).
    destruct recvOrSend as [[m mrecvm] | [m msendm]].
    pose proof (recvImpMarkSend mrecvm) as [t' [t'LeTs msendm]].
    destruct (classical (exists tc, t' < tc < tm /\ exists m, recv mch p c a tc m)) as [recv|noRecv].
    destruct recv as [tc [comp [m' mrecvm']]].
    pose proof (recvImpMarkSend mrecvm') as [t'' [t''LeTc msendm']].
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
    assert (noRecv': ~ (exists tc, S t' <= tc < tm /\ exists m, recv mch p c a tc m /\ to m >= state c a tm)) by
      (
        unfold not; intros [tc [cond [m0 [mrecvm0 _]]]];
          assert (cond': t' < tc < tm) by omega; generalize noRecv cond' mrecvm0; clear; firstorder).
    assert (nGt: ~ state c a tm > state c a (S t')) by (
      assert (eqOrGt: tm = S t' \/ tm > S t') by omega;
        destruct eqOrGt as [toEqSt' | toGtSt']; [
          rewrite <- toEqSt';
            omega |
              pose proof (@st.whenChildHigh a (S t') tm toGtSt') as contra;
                generalize contra noRecv'; clear; firstorder]).
    assert (dirEqSt: dir p c a (S ts) = state c a (S t')) by (
      pose proof (st.sendmChange msendm) as one;
        pose proof (dir.recvmChange mrecvm) as two;
          unfold st.st, dir.st in *;
            congruence).
    assert (stoLesSt': state c a tm <= state c a (S t')) by omega.
    congruence.
    pose proof (dir.sendmImpRecvr msendm) as [r rrecvr].
    pose proof (recvImpMarkSend rrecvr) as [t' [t'LeTs rsendr]].
    destruct (classical (exists tc, tc < tm /\ recv mch p c a tc m)) as [[tc [tcLtTo mrecvm]] | notEx].
    assert (eqOrNot: tm = S tc \/ tm > S tc) by omega.
    destruct eqOrNot as [toEqStc | toGtStc].
    assert (dirEqSt: state c a tm = dir p c a tm) by (
      pose proof (dir.sendmChange msendm) as one; pose proof (st.recvmChange mrecvm) as two;
        unfold st.st, dir.st in *; congruence).
    omega.
    assert (noLower: ~ exists t'', S tc <= t'' < tm /\ exists m', recv mch p c a t'' m' /\ to m' >= state c a tm)
      by (
        unfold not; intros [t'' [cond [m' [mrecvm' _]]]];
          pose proof (recvImpMarkSend mrecvm') as [tf [tfLeT'' msendm']];
            assert (diff: ts = tf \/ tf < ts \/ tf > ts) by omega;
              destruct diff as [tsEqTf | [tfLtTs | tfGtTs]]; [
                rewrite <- tsEqTf in *;
                  pose proof (uniqMarksend1 msendm msendm') as mEqM';
                    rewrite <- mEqM' in *;
                      pose proof (uniqRecv2 mrecvm mrecvm') as tcEqT'';
                        omega |
                          assert (t'LeTc: t' <= tc) by (
                            pose proof (recvImpMarkSend mrecvm) as [tsome [tsomeLe'' msendmTsome]];
                              pose proof (uniqMarksend2 msendm msendmTsome) as tcEqTsome;
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
    pose proof (@st.whenChildHigh a (S tc) tm toGtStc) as contra.
    assert (not: ~ state c a tm > state c a (S tc)) by (generalize noLower contra; clear; firstorder).
    assert (not2: state c a tm <= state c a (S tc)) by omega; clear not.
    assert (dirEqSt: dir p c a (S ts) = state c a (S tc)) by (
      pose proof (dir.sendmChange msendm) as one; pose proof (st.recvmChange mrecvm) as two;
        unfold st.st, dir.st in *; congruence).
    omega.
    assert (tsLeT: ts <= t) by omega.
    assert (less: state c a ts <= dir p c a ts) by firstorder.
    assert (tmGtTs: tm > t') by omega.
    assert (noRecv: ~ exists t'', t' <= t'' < tm /\ exists m, recv mch p c a t'' m /\ to m >= state c a tm) by (
      unfold not; intros [t'' [cond [m' [mrecvm' _]]]];
        pose proof (recvImpMarkSend mrecvm') as [t1 [t1LeT'' msendm']];
          assert (t1NeTs: t1 = ts -> False) by (
            intros t1EqTs; rewrite t1EqTs in *;
              pose proof (uniqMarksend1 msendm msendm') as mEqm';
                rewrite <- mEqm' in *; 
                  generalize notEx cond mrecvm'; clear; firstorder);
          assert (eqOrNot: t1 = ts \/ t1 > ts \/ t1 < ts) by omega;
            destruct eqOrNot as [t1EqTs | [t1GtTs | t1LtTs]];
              [firstorder |
                assert (cond2: ts < t1 < tm) by omega;
                  generalize noPrevChnge cond2 msendm'; clear; firstorder |
                    assert (one: forall tc', tc' < t' -> ~ recv mch p c a tc' m') by (
                      unfold not; intros tc' tc'LtT' mrecvm'Tc';
                        pose proof (uniqRecv2 mrecvm' mrecvm'Tc') as t''EqTc'; omega);
                    assert (two: forall tp', tp' <= t1 -> ~ recv rch c p a tp' r) by (
                      unfold not; intros tp' tp'LeT1 rrecvrTp';
                        pose proof (uniqRecv2 rrecvr rrecvrTp') as tsEqTp'; omega);
                    apply (cReqPRespCross rsendr msendm' one two)]).
    assert (contra1: ~ state c a tm > state c a t') by (
      unfold not; intros contra;
        generalize (st.whenChildHigh tmGtTs contra) noRecv; clear; firstorder).
    assert (cont: state c a tm <= state c a t') by omega.
    pose proof (st.sendrImpSt rsendr) as toRGtDir; unfold st.toRSComp in toRGtDir; unfold st.st in *.
    pose proof (dir.sendmImpRecvrGe msendm rrecvr) as toMGeToR.
    pose proof (dir.sendmChange msendm) as toMEq; unfold dir.st in *.
    omega.
    assert (eqOrNot: 0 = tm \/ 0 < tm) by omega.
    destruct eqOrNot as [tmEq0 | tmGt0].
    rewrite <- tmEq0 in *; pose proof @init as init; rewrite init in *; omega.
    assert (premise: forall tn, 0 <= tn < tm -> (forall m, ~ marksend mch p c a tn m) /\
      (forall m, ~ recv mch c p a tn m)) by (
        intros tn [_ tnLtTm];
          constructor;
            unfold not; intros m msendm;
              generalize noChnge tnLtTm msendm; clear; firstorder).
    pose proof (dir.noChange tmGt0 premise) as dir0DirTm; unfold dir.st in *.
    pose proof @st.whenChildHigh.
    assert (not: ~ exists t'', 0 <= t'' < tm /\ exists m, recv mch p c a t'' m /\ to m >= state c a tm) by (
      unfold not; intros [t'' [[_ t''LtTm] [m [mrecvm _]]]];
        pose proof (recvImpMarkSend mrecvm) as [t' [t'LeT'' msendm]];
          assert (t'LtTm: t' < tm) by omega;
            generalize noChnge t'LtTm msendm; clear; firstorder).
    assert (done: ~ state c a tm > state c a 0) by (generalize (@st.whenChildHigh a 0 tm tmGt0) not;
      clear; firstorder).
    pose proof (@init a) as start; omega.

    constructor.
    apply cross'.

    assert (cReqResp': forall {t1 t2 t3}, t3 <= S t -> forall {m}, marksend mch c p a t1 m -> forall {r},
      marksend rch c p a t2 r -> recv rch c p a t3 r -> t1 <= t2 -> (forall t4, t4 < t3 -> ~ recv mch c p a t4 m) ->
      False).
    intros t1 t2 t3 t3LeSt m msendm r rsendr rrecvr t1LeT2 neg.
    unfold Time in *.
    assert (eqOrNot: t1 = t2 \/ t1 < t2) by omega.
    destruct eqOrNot as [t1EqT2 | t1LtT2].
    rewrite t1EqT2 in *.
    pose proof (st.noSendmSendr msendm rsendr); intuition.
    clear t1LeT2.
    pose proof (recvImpMarkSend rrecvr) as [t' [t'LeT3 rsend'r]].
    pose proof (uniqMarksend2 rsendr rsend'r) as t2EqT'.
    rewrite <- t2EqT' in *.
    clear rsend'r t2EqT'.
    assert (t1LeT: t1 <= t) by omega.
    pose proof (cons t1 t1LeT) as st1Ledt1.

    assert (notty1: ~ exists t'', t1 <= t'' < t2 /\ exists m, recv mch p c a t'' m /\ to m >= state c a t2) by (
      unfold not; intros [t'' [cond [m0 [mrecvm0 _]]]];
        pose proof (recvImpMarkSend mrecvm0) as [t5 [t5LeT'' msendm0]];
          assert (one: forall tc', tc' < t1 -> ~ recv mch p c a tc' m0) by (
            unfold not; intros tc' tc'LtT1 mrecvM0Tc';
              pose proof (uniqRecv2 mrecvm0 mrecvM0Tc') as t''EqTc';
                rewrite <- t''EqTc' in *; omega);
          assert (two: forall tp', tp' < t5 -> ~ recv mch c p a tp' m) by (
            unfold not; intros tp' tp'LtT5; assert (t5LtT3: tp' < t3) by omega; firstorder);
          assert (t5Let: t5 <= t) by omega;
            apply (cross t1 t5 t1LeT t5Let m msendm m0 msendm0 one two)).
    assert (notty: ~ exists t'', S t1 <= t'' < t2 /\ exists m, recv mch p c a t'' m /\ to m >= state c a t2) by (
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
    pose proof (dir.recvrCond rrecvr) as fromRLe.
    pose proof (st.sendrFrom rsendr) as fromREq; unfold st.st in *.
    pose proof (st.sendmImpSt msendm) as stGt.
    pose proof (st.sendmChange msendm) as stEq; unfold st.st in *.
    rewrite fromREq, <- stEq in *.
    assert (drGt: dir p c a t1 > dir p c a t3) by omega.
    assert (drNe: dir p c a t1 <> dir p c a t3) by omega.
    assert (sendRecv: ~ forall tn, t1 <= tn < t3 -> (forall m, ~ marksend mch p c a tn m) /\
      (forall m, ~ recv mch c p a tn m)) by (
        unfold not; intros exp; assert (t1LtT3: t1 < t3) by omega; pose proof (dir.noChange t1LtT3 exp); firstorder).
    assert (noSend: forall tn, t1 <= tn < t3 -> forall m, ~ marksend mch p c a tn m) by (
      clear cRespResp;
        unfold not; intros tn cond m0 msendm0;
          assert (tnLeT: tn <= t) by omega;
            assert (one: forall tc', tc' < t1 -> ~ recv mch p c a tc' m0) by (
              unfold not; intros tc' tc'LtT1 mrecvm0;
                pose proof (recvImpMarkSend mrecvm0) as [tm [tmLeTc' msend'm0]];
                  pose proof (uniqMarksend2 msendm0 msend'm0) as tmEqTc';
                    rewrite <- tmEqTc' in *; omega);
            assert (two: forall tp', tp' < tn -> ~ recv mch c p a tp' m) by (
              unfold not; intros tp' tp'LtTn; assert (tp'LtT3: tp' < t3) by omega; firstorder);
            apply (cross t1 tn t1LeT tnLeT m msendm m0 msendm0 one two)).

    destruct (classical (exists tn, tn < t3 /\ t1 <= tn /\ exists m0, recv mch c p a tn m0)) as [ext|noEx].
    pose proof (maxExists' classical ext) as [tn [cond [[tnLtT3 [m0 mrecvm0]] notAfter]]].
    
    pose proof (recvImpMarkSend mrecvm0) as [tr [trLeTn msendm0]].
    assert (opts: tr = t1 \/ tr > t1 \/ tr < t1) by omega.
    destruct opts as [trEqT1 | [trGtT1 | trLtT1]].
    rewrite trEqT1 in *.
    pose proof (uniqMarksend1 msendm msendm0) as mEqm0.
    rewrite <- mEqm0 in *.
    generalize neg cond mrecvm0; clear; firstorder.
    assert (tnLeT: tn <= t) by omega.
    assert (cond2: forall t4, t4 < tn -> ~ recv mch c p a t4 m) by (
      intros t4 t4LtTn; assert (t4LtT3: t4 < t3) by omega;
        generalize neg t4LtT3; clear; firstorder).
    apply (cRespResp t1 tr tn tnLeT m msendm m0 msendm0 mrecvm0 trGtT1 cond2).
    assert (notty2': ~ exists t'', tr <= t'' < t1 /\ exists m, recv mch p c a t'' m /\ to m >= state c a t1) by (
      unfold not; intros [t'' [cond2 [m1 [mrecvm1 _]]]];
        pose proof (recvImpMarkSend mrecvm1) as [t5 [t5LeT'' msendm1]];
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
    assert (notty2: ~ exists t'', S tr <= t'' < t1 /\ exists m, recv mch p c a t'' m /\ to m >= state c a t1) by (
      unfold not; intros [t'' [cond1 rest]]; assert (cond2: tr <= t'' < t1) by omega;
        generalize notty2' cond2 rest; clear; firstorder).
    assert (strLeT1: S tr <= t1) by omega.
    pose proof (st.whenChildHighConv strLeT1 notty2) as st1LeTr.
    pose proof (st.whenChildHighConv t1LtT2 notty) as sST1LeT2.
    assert (trLtT3: tr < t3) by omega.
    assert (noC: forall tn0, S tn <= tn0 < t3 -> (forall m, ~ marksend mch p c a tn0 m) /\
      (forall m, ~ recv mch c p a tn0 m)) by (
        intros tn0 cond2;
          constructor; [assert (cond3: t1 <= tn0 < t3) by omega; generalize noSend cond3; clear; firstorder|
            assert (cond4: tn < tn0 < t3) by omega; 
              assert (t1LeTn0: t1 <= tn0) by omega; generalize cond4 t1LeTn0 notAfter; clear; firstorder]).
    assert (sTnLtT3: S tn <= t3) by omega.
    pose proof (dir.noChange2 sTnLtT3 noC) as dirEq.
    unfold dir.st in *.
    generalize st1LeTr sST1LeT2 sTnLtT3 dirEq rsendr rrecvr msendm msendm0 mrecvm0; clear; intros.
    pose proof (st.sendmChange msendm) as sEqTom.
    pose proof (st.sendmImpSt msendm) as sGtTom.
    pose proof (dir.recvmChange mrecvm0) as dSEqTom0.
    pose proof (st.sendmChange msendm0) as sSEqTom0.
    pose proof (dir.recvrCond rrecvr) as dLeFromr.
    pose proof (st.sendrFrom rsendr) as sEqFromr.
    unfold st.st, dir.st in *. omega.
    generalize sendRecv noSend noEx; clear; firstorder.

    constructor.

    intros tc tp tcLeSt tpLeSt mc msendmc mp msendmp norecvmp norecvmc.
    pose proof (dir.sendmImpRecvr msendmp) as [r rrecvr].
    pose proof (recvImpMarkSend rrecvr) as [t1 [t1LeTp rsendr]].
    assert (opts: t1 = tc \/ tc < t1 \/ t1 < tc) by omega.
    destruct opts as [t1EqTc | [tcLtT1 | t1LtTc]].
    rewrite t1EqTc in *.
    apply (st.noSendmSendr msendmc rsendr).
    assert (tcLeT1: tc <= t1) by omega.
    apply (cReqResp' tc t1 tp tpLeSt mc msendmc r rsendr rrecvr tcLeT1 norecvmc).
    destruct (classical (exists tm, t1 <= tm < tc /\ exists m, recv mch p c a tm m)) as [ext|noExt].
    destruct ext as [tm [[t1LeTm tmLtTc] [m recvm]]].
    pose proof (recvImpMarkSend recvm) as [tn [tnLeTm sendm]].
    assert (opts: tn = tp \/ tn < tp \/ tn > tp) by omega.
    destruct opts as [tnEqTp | [tnLtTp | tnGtTp]].
    rewrite tnEqTp in *.
    pose proof (uniqMarksend1 sendm msendmp) as mEqMp.
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
    pose proof (dir.sendmImpRecvr sendm) as [r1 recvr1].
    pose proof (recvImpMarkSend recvr1) as [tq [tqLeTn sendr1]].
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
      recv mch p c a tm m /\ to m >= state c a t') by (
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
    pose proof (st.voluntary rsendr t1LtTc msendmc stcLet2) as [r1 recvr1].
    pose proof (recvImpMarkSend recvr1) as [t2 [t2LeT1 sendr1]].
    assert (t2LeTp: t2 = tp \/ t2 > tp \/ t2 < tp) by omega.
    destruct t2LeTp as [t2EqTp | [t2GtTp | t2LtTp]].
    rewrite t2EqTp in *.
    apply (dir.noSendmSendr msendmp sendr1).
    assert (tpLeT2: tp <= t2) by omega.
    pose proof (pRespReq noTwoPResp noTwoPReqNon msendmp sendr1 recvr1 tpLeT2) as [t4 [t4LtTp recvmp]].
    generalize norecvmp recvmp t4LtTp; clear; firstorder.
    pose proof (dir.sendrImpNoSendm t2LtTp sendr1 msendmp) as [t' [[t2LtT' t'LtTp] [m [recvm toMGeToR1]]]].
    pose proof (recvImpMarkSend recvm) as [t'' [t''LeT' sendm]].
    pose proof (st.sendmChange sendm) as stEqToM. unfold st.st in *.
    pose proof (st.recvrNoSendm recvr1 msendmc) as sTcGtToR1.
    assert (stTcGtStST'': state c a tc > state c a (S t'')) by omega.
    assert (opts: t'' = tc \/ t'' > tc \/ t'' < tc) by omega.
    destruct opts as [t''EqTc | [t''GtTc | t''LtTc]].
    rewrite t''EqTc in *.
    pose proof (uniqMarksend1 msendmc sendm) as mEqMc.
    rewrite mEqMc in *.
    generalize t'LtTp recvm norecvmc; clear; firstorder.
    assert (t'Let: t' <= t) by omega.
    assert (norecv: forall t4, t4 < t' -> ~ recv mch c p a t4 mc) by (
      unfold not; intros t4 t4LtT'; assert (t4LtTp: t4 < tp) by omega;
        generalize norecvmc t4LtTp; clear; firstorder).
    apply (cRespResp tc t'' t' t'Let mc msendmc m sendm recvm t''GtTc); intuition.
    assert (opts: S t'' = tc \/ S t'' < tc) by omega.
    destruct opts as [St''EqTc | St''LtTc].
    rewrite St''EqTc in *.
    omega.
    pose proof (st.whenChildHigh St''LtTc stTcGtStST'') as [ts [cond [s [recvs _]]]].
    pose proof (recvImpMarkSend recvs) as [tsr [tsrLeTs sends]].
    assert (opts: tsr = t' \/ tsr > t' \/ tsr < t') by omega.
    destruct opts as [tsrEqT' | [tsrGtT' | tsrLtT']].
    rewrite tsrEqT' in *.
    apply (dir.noSendmRecvm sends recvm).
    assert (t2LeTsr: t2 <= tsr) by omega.
    pose proof (pReqResp noTwoPResp noTwoPReqNon sendr1 sends recvs t2LeTsr) as [tf [tfLtTs recv'r1]].
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
    pose proof (uniqMarksend1 msendm rsendr) as mEqR; omega.
    clear t1LeT2.
    pose proof (recvImpMarkSend rrecvr) as [t' [t'LeT3 rsend'r]].
    pose proof (uniqMarksend2 rsendr rsend'r) as t2EqT'.
    rewrite <- t2EqT' in *.
    clear rsend'r t2EqT'.
    assert (t1LeT: t1 <= t) by omega.
    pose proof (cons t1 t1LeT) as st1Ledt1.

    assert (notty1: ~ exists t'', t1 <= t'' < t2 /\ exists m, recv mch p c a t'' m /\ to m >= state c a t2) by (
      unfold not; intros [t'' [cond [m0 [mrecvm0 _]]]];
        pose proof (recvImpMarkSend mrecvm0) as [t5 [t5LeT'' msendm0]];
          assert (one: forall tc', tc' < t1 -> ~ recv mch p c a tc' m0) by (
            unfold not; intros tc' tc'LtT1 mrecvM0Tc';
              pose proof (uniqRecv2 mrecvm0 mrecvM0Tc') as t''EqTc';
                rewrite <- t''EqTc' in *; omega);
          assert (two: forall tp', tp' < t5 -> ~ recv mch c p a tp' m) by (
            unfold not; intros tp' tp'LtT5; assert (t5LtT3: tp' < t3) by omega; firstorder);
          assert (t5Let: t5 <= t) by omega;
            apply (cross t1 t5 t1LeT t5Let m msendm m0 msendm0 one two)).
    assert (notty: ~ exists t'', S t1 <= t'' < t2 /\ exists m, recv mch p c a t'' m /\ to m >= state c a t2) by (
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
    pose proof (dir.recvmCond rrecvr) as fromRLe.
    pose proof (st.sendmFrom rsendr) as fromREq; unfold st.st in *.
    pose proof (st.sendmImpSt msendm) as stGt.
    pose proof (st.sendmChange msendm) as stEq; unfold st.st in *.
    rewrite fromREq, <- stEq in *.
    assert (drGt: dir p c a t1 > dir p c a t3) by omega.
    assert (drNe: dir p c a t1 <> dir p c a t3) by omega.
    assert (sendRecv: ~ forall tn, t1 <= tn < t3 -> (forall m, ~ marksend mch p c a tn m) /\
      (forall m, ~ recv mch c p a tn m)) by (
        unfold not; intros exp; assert (t1LtT3: t1 < t3) by omega; pose proof (dir.noChange t1LtT3 exp); firstorder).
    assert (noSend: forall tn, t1 <= tn < t3 -> forall m, ~ marksend mch p c a tn m) by (
      clear cRespResp;
        unfold not; intros tn cond m0 msendm0;
          assert (tnLeT: tn <= t) by omega;
            assert (one: forall tc', tc' < t1 -> ~ recv mch p c a tc' m0) by (
              unfold not; intros tc' tc'LtT1 mrecvm0;
                pose proof (recvImpMarkSend mrecvm0) as [tm [tmLeTc' msend'm0]];
                  pose proof (uniqMarksend2 msendm0 msend'm0) as tmEqTc';
                    rewrite <- tmEqTc' in *; omega);
            assert (two: forall tp', tp' < tn -> ~ recv mch c p a tp' m) by (
              unfold not; intros tp' tp'LtTn; assert (tp'LtT3: tp' < t3) by omega; firstorder);
            apply (cross t1 tn t1LeT tnLeT m msendm m0 msendm0 one two)).

    destruct (classical (exists tn, tn < t3 /\ t1 <= tn /\ exists m0, recv mch c p a tn m0)) as [ext|noEx].
    pose proof (maxExists' classical ext) as [tn [cond [[tnLtT3 [m0 mrecvm0]] notAfter]]].
    
    pose proof (recvImpMarkSend mrecvm0) as [tr [trLeTn msendm0]].
    assert (opts: tr = t1 \/ tr > t1 \/ tr < t1) by omega.
    destruct opts as [trEqT1 | [trGtT1 | trLtT1]].
    rewrite trEqT1 in *.
    pose proof (uniqMarksend1 msendm msendm0) as mEqm0.
    rewrite <- mEqm0 in *.
    generalize neg cond mrecvm0; clear; firstorder.
    assert (tnLeT: tn <= t) by omega.
    assert (cond2: forall t4, t4 < tn -> ~ recv mch c p a t4 m) by (
      intros t4 t4LtTn; assert (t4LtT3: t4 < t3) by omega;
        generalize neg t4LtT3; clear; firstorder).
    apply (cRespResp t1 tr tn tnLeT m msendm m0 msendm0 mrecvm0 trGtT1 cond2).
    assert (notty2': ~ exists t'', tr <= t'' < t1 /\ exists m, recv mch p c a t'' m /\ to m >= state c a t1) by (
      unfold not; intros [t'' [cond2 [m1 [mrecvm1 _]]]];
        pose proof (recvImpMarkSend mrecvm1) as [t5 [t5LeT'' msendm1]];
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
    assert (notty2: ~ exists t'', S tr <= t'' < t1 /\ exists m, recv mch p c a t'' m /\ to m >= state c a t1) by (
      unfold not; intros [t'' [cond1 rest]]; assert (cond2: tr <= t'' < t1) by omega;
        generalize notty2' cond2 rest; clear; firstorder).
    assert (strLeT1: S tr <= t1) by omega.
    pose proof (st.whenChildHighConv strLeT1 notty2) as st1LeTr.
    pose proof (st.whenChildHighConv t1LtT2 notty) as sST1LeT2.
    assert (trLtT3: tr < t3) by omega.
    assert (noC: forall tn0, S tn <= tn0 < t3 -> (forall m, ~ marksend mch p c a tn0 m) /\
      (forall m, ~ recv mch c p a tn0 m)) by (
        intros tn0 cond2;
          constructor; [assert (cond3: t1 <= tn0 < t3) by omega; generalize noSend cond3; clear; firstorder|
            assert (cond4: tn < tn0 < t3) by omega; 
              assert (t1LeTn0: t1 <= tn0) by omega; generalize cond4 t1LeTn0 notAfter; clear; firstorder]).
    assert (sTnLtT3: S tn <= t3) by omega.
    pose proof (dir.noChange2 sTnLtT3 noC) as dirEq.
    unfold dir.st in *.
    generalize st1LeTr sST1LeT2 sTnLtT3 dirEq rsendr rrecvr msendm msendm0 mrecvm0; clear; intros.
    pose proof (st.sendmChange msendm) as sEqTom.
    pose proof (st.sendmImpSt msendm) as sGtTom.
    pose proof (dir.recvmChange mrecvm0) as dSEqTom0.
    pose proof (st.sendmChange msendm0) as sSEqTom0.
    pose proof (dir.recvmCond rrecvr) as dLeFromr.
    pose proof (st.sendmFrom rsendr) as sEqFromr.
    unfold st.st, dir.st in *. omega.
    generalize sendRecv noSend noEx; clear; firstorder.
  Qed.

  Theorem conservative: forall {a t}, dir p c a t >= state c a t.
  Proof.
    intros a t.
    pose proof (@mainInd a t) as [first _].
    assert (tLeT: t <= t) by omega; firstorder.
  Qed.

  Lemma cRespFifo: forall {a t1 t2 t3 m1 m2}, marksend mch c p a t1 m1 -> marksend mch c p a t2 m2 ->
    recv mch c p a t3 m2 -> t1 < t2 -> (forall t4, t4 < t3 -> ~ recv mch c p a t4 m1) -> False.
  Proof.
    intros a t1 t2 t3 m1 m2 sendm1 sendm2 recvm2 t1LtT2.
    pose proof (@mainInd a t3) as [_ [_ [_ last]]].
    specialize (last t1 t2 t3).
    assert (t3LeT3: t3 <= t3) by omega.
    firstorder.
  Qed.

  Lemma cross: forall {a t1 t2 m1 m2}, marksend mch c p a t1 m1 -> marksend mch p c a t2 m2 ->
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

  Theorem cReqRespSent: forall {a t1 t2 r}, marksend rch p c a t1 r -> recv rch p c a t2 r ->
    to r >= state c a t2 -> exists t3, t3 < t2 /\ exists m, marksend mch c p a t3 m /\ to m <= to r /\
      (forall t4, t4 < t1 -> ~ recv mch c p a t4 m).
  Proof.
    intros a t1 t2 r sendr recvr toRGestT2.
    destruct (classical (exists t3, t3 < t2 /\ exists m, marksend mch c p a t3 m /\ to m <= to r /\ forall t4,
      t4 < t1 -> ~ recv mch c p a t4 m)) as [easy|hard].
    intuition.
    pose proof (recvImpMarkSend recvr) as [t1' [t1LeT2 send'r]].
    pose proof (uniqMarksend2 sendr send'r) as t1'EqT1.
    rewrite <- t1'EqT1 in *.
    clear t1'EqT1 send'r t1'.

    destruct (classical (exists t, t < t1 /\ ((exists m, recv mch c p a t m) \/
      (exists m, marksend mch p c a t m)))) as [ex | notEx].
    pose proof (maxExists' classical ex) as [t [tLtT1 [sendOrRecv notAfter]]].
    assert (nothing: forall y, S t <= y < t1 -> (forall m, ~ marksend mch p c a y m) /\
      (forall m, ~ recv mch c p a y m)) by
    (intros y cond; assert (cond2: t < y < t1)by omega; generalize cond2 notAfter; clear; firstorder).
    pose proof (dir.noChange2 tLtT1 nothing) as dirEq.
    clear nothing; unfold dir.st in *.
    destruct sendOrRecv as [[m recvm] | [m sendm]].
    pose proof (recvImpMarkSend recvm) as [t' [t'LeT sendm]].
    assert (noCRecv: forall tm, t' <= tm < t2 -> forall m', ~ recv mch p c a tm m') by (
      unfold not; intros tm cond m' recvm';
        pose proof (recvImpMarkSend recvm') as [ts [tsLeTm sendm']];
          assert (opts: ts < t \/ ts = t \/ t < ts < t1 \/ t1 <= ts) by omega;
            destruct opts as [tsLtT | [tsEqT | [tLtTsLtT1  | t1LeTs ]]]; [
              assert (one: forall x, x < t' -> ~ recv mch p c a x m') by ( unfold not; intros x xLtT' recv'm';
                pose proof (uniqRecv2 recvm' recv'm') as xEqTm; omega);
              assert (two: forall x, x < ts -> ~ recv mch c p a x m) by (unfold not; intros x xLtTs recv'm;
                pose proof (uniqRecv2 recvm recv'm) as xEqTs; omega);
              apply (cross sendm sendm' one two) |
                rewrite tsEqT in *;
                  apply (dir.noSendmRecvm sendm' recvm) |
                    generalize notAfter tLtTsLtT1 sendm'; clear; firstorder |
                      pose proof (pReqResp noTwoPResp noTwoPReqNon sendr sendm' recvm' t1LeTs) as [t4 [t4LtTm recv'r]];
                        pose proof (uniqRecv2 recvr recv'r) as t4EqT2; omega]).
    destruct (classical (exists ts, ts < t2 /\ t' < ts /\ exists m', marksend mch c p a ts m'))
      as [ ex2 | notEx2].
    pose proof (maxExists' classical ex2) as [ts [tsLtT2 [[t'LtTs [m' sendm']] notAfter2]]].
    assert (nothing: forall y, S ts <= y < t2 ->
      (forall m, ~ marksend mch c p a y m) /\ (forall m, ~ recv mch p c a y m)) by
    (intros y cond; assert (cond1: t' < y < t2) by omega; assert (cond2: t' <= y < t2) by omega;
      generalize notAfter2 noCRecv cond cond1 cond2; clear; firstorder).
    pose proof (st.noChange2 tsLtT2 nothing) as stEq.
    unfold st.st in *.
    destruct (classical (exists tr, tr < t1 /\ recv mch c p a tr m')) as [ [tr [trLtT1 recvm']] | noRecv].
    assert (opts: tr < t \/ tr = t \/ t < tr < t1) by omega.
    destruct opts as [trLtT | [trEqT | cond]].
    assert (forall t4, t4 < tr -> ~ recv mch c p a t4 m) by (
      unfold not; intros t4 t4LtTr recv'm; pose proof (uniqRecv2 recvm recv'm) as t4EqT; omega).
    pose proof (cRespFifo sendm sendm' recvm' t'LtTs). intuition.
    rewrite trEqT in *.
    pose proof (uniqRecv1 recvm recvm') as mEqM'.
    rewrite mEqM' in *.
    pose proof (uniqMarksend2 sendm sendm') as t'EqTs.
    omega.
    generalize notAfter cond recvm'; clear; firstorder.
    assert (opts: to m' <= to r \/ to m' > to r) by omega.
    destruct opts as [toM'LeToR | toM'GtToR].
    generalize tsLtT2 sendm' toM'LeToR noRecv; clear; firstorder.
    pose proof (st.sendmChange sendm') as stEqToM'.
    unfold st.st in *.
    omega.
    assert (nothing: forall y, S t' <= y < t2 ->
      (forall m, ~ marksend mch c p a y m) /\ (forall m, ~ recv mch p c a y m)) by
    (intros y cond; assert (cond2: t' <= y < t2) by omega;
      generalize notEx2 noCRecv cond cond2; clear; firstorder).
    assert (t'LeT2: S t' <= t2) by omega.
    pose proof (st.noChange2 t'LeT2 nothing) as stEq.
    pose proof (dir.sendrImpSt sendr) as toRLtD.
    pose proof (st.sendmChange sendm) as st1.
    pose proof (dir.recvmChange recvm) as st2.
    unfold st.st, dir.st, dir.toRSComp in *.
    omega.

    assert (tLeT1: t <= t1) by omega.
    pose proof (pRespReq noTwoPResp noTwoPReqNon sendm sendr recvr tLeT1) as [t' [t'LtT2 recvm]].
    pose proof (recvImpMarkSend recvm) as [t'' [tLeT' send'm]].
    pose proof (uniqMarksend2 sendm send'm) as t''EqT.
    rewrite <- t''EqT in *. clear t''EqT t'' send'm.
    assert (noCRecv: forall tm, t' < tm < t2 -> forall m', ~ recv mch p c a tm m').
    unfold not; intros tm cond m' recvm';
      pose proof (recvImpMarkSend recvm') as [ts [tsLeTm sendm']];
        assert (opts: ts < t \/ ts = t \/ t < ts < t1 \/ t1 <= ts) by omega;
          destruct opts as [tsLtT | [tsEqT | [tLtTsLtT1  | t1LeTs ]]]; [
            pose proof (dir.sendmImpRecvr sendm) as [r' recvr'];
              pose proof (recvImpMarkSend recvr') as [tx [txLeT sendr']];
                assert (one: forall t3, t3 < tx -> ~ recv mch p c a t3 m') by (
                  unfold not; intros t3 t3LtTx recv'm'; pose proof (uniqRecv2 recvm' recv'm') as t3EqTr;
                    omega);
                assert (two: forall t4, t4 <= ts -> ~ recv rch c p a t4 r') by (
                  unfold not; intros t4 t4LeTs recv'r'; pose proof (uniqRecv2 recvr' recv'r') as t4EqTs;
                    omega);
                apply (cReqPRespCross sendr' sendm' one two)|
                  rewrite tsEqT in *; pose proof (uniqMarksend1 sendm sendm') as mEqM'; rewrite mEqM' in *;
                    pose proof (uniqRecv2 recvm recvm') as trEqT'; omega |
                      generalize notAfter tLtTsLtT1 sendm'; clear; firstorder |
                        pose proof (pReqResp noTwoPResp noTwoPReqNon sendr sendm' recvm' t1LeTs) as [t4 [t4LtTm recv'r]];
                          pose proof (uniqRecv2 recvr recv'r) as t4EqT2; omega].
    
    destruct (classical (exists ts, ts < t2 /\ t' < ts /\ exists m', marksend mch c p a ts m'))
      as [ ex2 | notEx2].
    pose proof (maxExists' classical ex2) as [ts [tsLtT2 [[t'LtTs [m' sendm']] notAfter2]]].
    assert (nothing: forall y, S ts <= y < t2 ->
      (forall m, ~ marksend mch c p a y m) /\ (forall m, ~ recv mch p c a y m)) by
    (intros y cond; assert (cond1: t' < y < t2) by omega;
      generalize notAfter2 noCRecv cond cond1; clear; firstorder).
    pose proof (st.noChange2 tsLtT2 nothing) as stEq.
    unfold st.st in *.
    destruct (classical (exists tr, tr < t1 /\ recv mch c p a tr m')) as [ [tr [trLtT1 recvm']] | noRecv].
    pose proof (recvImpMarkSend recvm') as [ts' [ts'LeTr send'm']].
    pose proof (uniqMarksend2 send'm' sendm') as ts'EqTs.
    assert (trGtT: tr > t) by omega.
    clear ts' ts'LeTr send'm' ts'EqTs.
    assert (opts: t < tr < t1 \/ t1 <= tr) by omega.
    destruct opts as [cond1 | t1LeTr].
    generalize cond1 notAfter recvm'; clear; firstorder.
    assert (opts: to m' <= to r \/ to m' > to r) by omega.
    destruct opts as [toM'LeToR | toM'GtToR].
    assert (noRecv: forall t4, t4 < t1 -> ~ recv mch c p a t4 m') by (
      unfold not; intros t4 t4LtT1 recv'm'; pose proof (uniqRecv2 recvm' recv'm') as t4EqTr; omega).
    generalize tsLtT2 sendm' toM'LeToR noRecv; clear; firstorder.
    pose proof (st.sendmChange sendm') as stEqToM'.
    unfold st.st in *.
    omega.
    assert (last: forall t4, t4 < t1 -> ~ recv mch c p a t4 m') by (generalize noRecv; clear; firstorder).
    assert (opts: to m' <= to r \/ to m' > to r) by omega.
    destruct opts as [toM'LeToR | toM'GtToR].
    generalize last tsLtT2 toM'LeToR sendm'; clear; firstorder.
    pose proof (st.sendmChange sendm') as stEqToM'.
    unfold st.st in *.
    omega.
    assert (nothing: forall y, S t' <= y < t2 ->
      (forall m, ~ marksend mch c p a y m) /\ (forall m, ~ recv mch p c a y m)) by
    (generalize noCRecv notEx2; clear; firstorder).
    pose proof (st.noChange2 t'LtT2 nothing) as stEq.
    unfold st.st in *.
    pose proof (st.recvmChange recvm) as st1.
    pose proof (dir.sendmChange sendm) as d1.
    pose proof (dir.sendrImpSt sendr) as d2.
    unfold dir.toRSComp, dir.st, st.st in *.
    omega.
    assert (cNoRecv: forall t4, t4 < t2 -> forall m, ~ recv mch p c a t4 m) by (
      unfold not; intros t4 t4LtT2 m recvm; pose proof (recvImpMarkSend recvm) as [t3 [t3LeT4 sendm]];
        assert (opts: t3 < t1 \/ t3 >= t1) by omega;
          destruct opts as [t3LtT1 | t4GeT1]; [
            generalize notEx t3LtT1 sendm; clear; firstorder;
              intuition |
                pose proof (pReqResp noTwoPResp noTwoPReqNon sendr sendm recvm t4GeT1) as [t5 [t4LtT4 recv'r]];
                  pose proof (uniqRecv2 recvr recv'r) as t5EqT2; omega]).
    destruct (classical (exists t3, t3 < t2 /\ exists m, marksend mch c p a t3 m)) as [ex2 | notEx2].
    pose proof (maxExists' classical ex2) as [ts [tsLtT2 [[m' sendm'] notAfter2]]].
    assert (nothing: forall y, S ts <= y < t2 ->
      (forall m, ~ marksend mch c p a y m) /\ (forall m, ~ recv mch p c a y m)) by
    (intros y cond;
      generalize notAfter2 cNoRecv cond; clear; firstorder).
    pose proof (st.noChange2 tsLtT2 nothing) as stEq.
    unfold st.st in *.
    destruct (classical (exists tr, tr < t1 /\ recv mch c p a tr m')) as [ [tr [trLtT1 recvm']] | noRecv].
    generalize notEx trLtT1 recvm'; clear; firstorder.
    assert (opts: to m' <= to r \/ to m' > to r) by omega.
    destruct opts as [toM'LeToR | toM'GtToR].
    generalize toM'LeToR noRecv tsLtT2 sendm'; clear; firstorder.
    pose proof (st.sendmChange sendm') as stEqToM'.
    unfold st.st in *.
    omega.
    assert (nothing1: forall y, 0 <= y < t2 ->
      (forall m, ~ marksend mch c p a y m) /\ (forall m, ~ recv mch p c a y m)) by
    (generalize cNoRecv notEx2; clear; firstorder).
    assert (x1: 0 <= t2) by omega.
    pose proof (st.noChange2 x1 nothing1) as st1.
    assert (nothing2: forall y, 0 <= y < t1 ->
      (forall m, ~ marksend mch p c a y m) /\ (forall m, ~ recv mch c p a y m)) by
    (generalize notEx; clear; firstorder).
    assert (x2: 0 <= t1) by omega.
    pose proof (dir.noChange2 x2 nothing2) as d1.
    pose proof (@init a) as start.
    pose proof (dir.sendrImpSt sendr) as d2.
    unfold dir.toRSComp, dir.st, dir.st, stSemi.st in *.
    omega.
  Qed.
End PairTheorems.
