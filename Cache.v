Require Import Arith Omega.

Load Useful.

Module Type Network.
  Parameter network : Type.
End Network.

Module Type DataTypes.
  Parameter Cache: Type.
  Parameter Mesg: Type.
  Parameter parent: Cache -> Cache.
  Definition State := nat.
  Definition Time := nat.
  Parameter state: Cache -> Time -> State.
  Parameter dir: Cache -> Cache -> Time -> State.

  Parameter from: Mesg -> State.
  Parameter to: Mesg -> State.
  Parameter time: Mesg -> Time.

  Parameter timestamp: Cache -> Time -> Time.
End DataTypes.

Module Channel (n: Network) (dataTypes: DataTypes).
  Import dataTypes.

  Axiom marksend: Cache -> Cache -> Time -> Mesg -> Prop.
  Axiom recv: Cache -> Cache -> Time -> Mesg -> Prop.
  Definition isMarksend x y t := exists m, marksend x y t m.
  Definition isRecv x y t := exists m, recv x y t m.

  Set Implicit Arguments.
  Section local.
    Variable p c : Cache.
    Axiom uniqMarksend1: forall {m n t}, marksend p c t m -> marksend p c t n -> m = n.
    Axiom uniqMarksend2: forall {m t1 t2}, marksend p c t1 m -> marksend p c t2 m -> t1 = t2.
    Axiom uniqRecv1: forall {m n t}, recv p c t m -> recv p c t n -> m = n.
    Axiom uniqRecv2: forall {m t1 t2}, recv p c t1 m -> recv p c t2 m -> t1 = t2.
    Axiom recvImpMarkSend: forall {m t}, recv p c t m -> exists t', t' <= t /\ marksend p c t' m.
  End local.
End Channel.


Module Type System (dataTypes: DataTypes).
  Import dataTypes.

  Axiom classical: forall P, P \/ ~ P.

  Parameter RespNetwork : Type.
  Parameter ReqNetwork : Type.

  Module RespNetwork : Network.
    Definition network := RespNetwork.
  End RespNetwork.

  Module ReqNetwork : Network.
    Definition network := ReqNetwork.
  End ReqNetwork.

  Definition toCompat s := 3 - s.

  Definition compat c p (rel: parent c = p) t := forall c', parent c' = p ->
    dir p c' t <= toCompat (dir p c t).

  Module m := Channel RespNetwork dataTypes.
  Module r := Channel ReqNetwork dataTypes.

  Module Type LocalState.
    Parameter st : Time -> State.
    Parameter mmarksend: Time -> Mesg -> Prop.
    Parameter mrecv: Time -> Mesg -> Prop.
    Parameter rmarksend: Time -> Mesg -> Prop.
    Parameter rrecv: Time -> Mesg -> Prop.
    Parameter toRSComp: State -> State -> Prop.
    Parameter timeStamp: Time -> Time.
  End LocalState.

  Module StateBehave (s : LocalState).
    Import s.
    Definition isMMarksend t := exists m, mmarksend t m.
    Definition isMRecv t := exists m, mrecv t m.
    Definition isRMarksend t := exists m, rmarksend t m.
    Definition isRRecv t := exists m, rrecv t m.

    Set Implicit Arguments.
    Section ForT.
      Variable t: Time.
      Axiom change: st (S t) <> st t -> isMMarksend t \/ isMRecv t.
      Axiom sendmChange: forall {m}, mmarksend t m -> st (S t) = to m.
      Axiom recvmChange: forall {m}, mrecv t m -> st (S t) = to m.
      Axiom sendrImpSt: forall {r}, rmarksend t r -> toRSComp (to r) (st t).
      Axiom sendrImpNoSendr: forall {t1 t2 r1 r2}, t1 < t2 -> rmarksend t1 r1 -> rmarksend t2 r2 ->
        exists t', t1 < t' <= t2 /\ ~ toRSComp (to r1) (st t').
      Axiom sendmFrom: forall {m}, mmarksend t m -> from m = st t.
      Axiom sendrFrom: forall {r}, rmarksend t r -> from r = st t.
      Axiom sendmTime: forall {m}, mmarksend t m -> time m = timeStamp t.
      Axiom noSendmRecvm: forall {m}, mmarksend t m -> forall {m'}, mrecv t m' -> False.
      Axiom noSendmSendr: forall {m}, mmarksend t m -> forall {r}, rmarksend t r -> False.
    End ForT.

    Lemma nochange': forall {t t'}, (forall tn, t <= tn < t + t' -> (forall m, ~ mmarksend tn m) /\ (forall m, ~ mrecv tn m)) -> st t = st (t + t').
    Proof.
      induction t'.
      intro false.
      firstorder.
      intros noChange.
      assert (help: forall tn, t <= tn < t + t' -> (forall m, ~ mmarksend tn m) /\ (forall m, ~ mrecv tn m)) by (
        intros tn comp;
          assert (comp2: t <= tn < t + S t') by omega;
            firstorder).
      assert (stTEqstT': st t = st (t + t')) by firstorder.
      assert (nothing: (forall m, ~ mmarksend (t + t') m) /\ forall m, ~ mrecv (t + t') m) by (assert (t <= t + t' < t + S t'); firstorder).
      rewrite stTEqstT'.
      assert (two: st (t + S t') = st (t + t') \/ st (t + S t') <> st (t + t')) by decide equality.
      destruct two as [easy | hard].
      intuition.
      assert (sth: t + S t' = S (t + t')) by omega.
      rewrite sth in *.
      pose proof (change hard) as contra.
      unfold isMMarksend in contra; unfold isMRecv in contra.
      firstorder.
    Qed.

    Lemma noChange: forall {t t'}, t < t' -> (forall tn, t <= tn < t' -> (forall m, ~ mmarksend tn m) /\ (forall m, ~ mrecv tn m)) -> st t = st t'.
    Proof.
      intros t t' tLtT'.
      remember (t' - t) as td.
      assert (rew: t' = t + td) by omega.
      rewrite rew in *.
      apply (@nochange' t).
    Qed.

    Lemma noChange2: forall {t t'}, t <= t' -> (forall tn, t <= tn < t' -> (forall m, ~ mmarksend tn m) /\ (forall m, ~ mrecv tn m)) -> st t = st t'.
    Proof.
      intros t t' tLeT'.
      assert (opts: t = t' \/ t < t') by omega.
      destruct opts as [tEqT' | tLtT'].
      rewrite tEqT'.
      reflexivity.
      apply noChange; intuition.
    Qed.
  End StateBehave.

  Module Type LocalRules.
    Variables p c: Cache.
    Hypothesis rel: parent c = p.

    Module Dir <: LocalState.
      Section ForT.
        Variable t: Time.

        Definition st := dir p c.
        Definition mmarksend := m.marksend p c.
        Definition mrecv := m.recv c p.
        Definition rmarksend := r.marksend p c.
        Definition rrecv := r.recv c p.
        Definition toRSComp x y := x < y.
        Definition timeStamp := timestamp p.
      End ForT.
    End Dir.

    Module St <: LocalState.
      Section ForT.
        Variable t: Time.

        Definition st := state c.
        Definition mmarksend := m.marksend c p.
        Definition mrecv := m.recv p c.
        Definition rmarksend := r.marksend c p.
        Definition rrecv := r.recv p c.
        Definition toRSComp x y := x > y.
        Definition timeStamp := timestamp c.

      End ForT.
    End St.

    About St.

    Module db := StateBehave Dir.

    Module sb := StateBehave St.

    Set Implicit Arguments.
    Definition twoEqPRespFalse := forall t t1 m1, t1 <= t -> m.marksend p c t1 m1 ->
      forall t2 m2, t2 <= t -> m.marksend p c t2 m2 ->
        (forall t3, t3 <= t -> ~ m.recv p c t3 m1) -> (forall {t4}, t4 <= t -> ~ m.recv p c t4 m2) -> t1 = t2.

    Definition twoPReqNeedsResp := forall t t1 r1, t1 <= t -> r.marksend p c t1 r1 -> forall t2 r2,
      t2 <= t -> r.marksend p c t2 r2 -> (forall t3, t3 <= t -> ~ r.recv p c t3 r1) ->
      (forall t4, t4 <= t -> ~ r.recv p c t4 r2) -> to r1 = to r2 -> t1 < t2 -> exists tm m, t1 < tm < t2 /\ m.marksend p c tm m.


    Section ForT.
      Variable t: Time.

      Axiom init: dir p c 0 = state c 0.

      Axiom stSendmImpSt: forall {m}, m.marksend c p t m -> state c t > to m.

      Axiom dirSendmImpRecvr: forall {m}, m.marksend p c t m -> exists r, r.recv c p t r.

      Axiom dirSendmImpRecvrGe: forall {m}, m.marksend p c t m -> forall {r}, r.recv c p t r -> to m >= to r.

      Axiom dirRecvrCond: forall {r}, r.recv c p t r -> from r >= dir p c t.

      Axiom dirRecvmCond: forall {m}, m.recv c p t m -> from m = dir p c t.

      Axiom pRespReq: twoEqPRespFalse -> twoPReqNeedsResp -> forall {t1 t2 t3}, forall {m}, m.marksend p c t1 m ->
        forall {r}, r.marksend p c t2 r -> r.recv p c t3 r -> t1 <= t2 -> exists t4, t4 < t3 /\ m.recv p c t4 m.

      Axiom pReqResp: twoEqPRespFalse -> twoPReqNeedsResp -> forall {t1 t2 t3}, forall {r}, r.marksend p c t1 r ->
        forall {m}, m.marksend p c t2 m -> m.recv p c t3 m -> t1 <= t2 -> exists t4, t4 < t3 /\ r.recv p c t4 r.

      Axiom stVoluntary:
        forall {r}, r.marksend c p t r -> forall {t' m}, t' > t -> m.marksend c p t' m ->
          (forall {tm}, t < tm <= t' -> state c tm < to r) -> exists r1, r.recv p c t' r1.

      Axiom dirSendrImpNoSendm: forall {t1 t2 r1 m2}, t1 < t2 -> r.marksend p c t1 r1 -> m.marksend p c t2 m2 ->
        exists t', t1 < t' < t2 /\ exists m, m.recv c p t' m /\ to m <= to r1.

      Axiom stRecvrNoSendm: forall {r}, r.recv p c t r -> forall {m}, m.marksend c p t m -> state c t > to r.

      Axiom stRecvrSendm: forall {r}, r.recv p c t r -> state c t > to r -> exists {m}, m.marksend c p t m.

      Lemma whenChildHighRecvm: state c (S t) > state c t -> exists m,
        m.recv p c t m /\ to m = state c (S t).
      Proof.
        intro sStgst.
        assert (sStnst: state c (S t) <> state c t) by omega.
        pose proof (sb.change sStnst) as [[m sendmm] | [m recvmm] ].
        pose proof (stSendmImpSt sendmm) as stgm.
        pose proof (sb.sendmChange sendmm) as sStem.
        unfold St.mmarksend in *.
        unfold St.st in *.
        omega.
        exists m.
        intuition.
        pose proof (sb.recvmChange recvmm) as sStem.
        unfold St.mrecv in *.
        unfold St.st in *.
        intuition.
      Qed.
    End ForT.

    Lemma dirRecvImpLow: forall {t m}, m.recv c p t m -> dir p c t > dir p c (S t).
    Proof.
      intros t m recvm.
      pose proof (m.recvImpMarkSend recvm) as [t' [t'LeT sendm]].
      pose proof (db.recvmChange recvm) as sth.
      pose proof (stSendmImpSt sendm) as sth2.
      pose proof (dirRecvmCond recvm) as sth3.
      pose proof (sb.sendmFrom sendm) as sth4.
      unfold Dir.st, St.st in *.
      omega.
    Qed.

    Lemma whenDirLow': forall {t t'}, dir p c (t' + t) > dir p c t ->
      exists t'', t'' < t' /\ exists m, m.marksend p c (t'' + t) m.
    Proof.
      induction t'.
      intros dirGt.
      unfold plus in *; simpl. omega.
      intros dirGt.
      assert (opts: dir p c (t' + t) > dir p c t \/ dir p c (t' + t) <= dir p c t) by omega.
      destruct opts as [gt | le].
      firstorder.
      assert (gt: dir p c (S (t' + t)) > dir p c (t' + t)) by (assert (eq: S t' + t = S (t' + t)) by omega;
        rewrite eq in *; omega).
      assert (nestuff: dir p c (S (t' + t)) <> dir p c (t' + t)) by omega.
      pose proof (db.change nestuff) as [sendm | recvm].
      firstorder.
      destruct recvm as [x recvstuff].
      pose proof (dirRecvImpLow recvstuff) as contra.
      omega.
    Qed.

    Lemma whenDirLow: forall {t t1}, t <= t1 -> dir p c t1 > dir p c t ->
      exists t'', t <= t'' < t1 /\ exists m, m.marksend p c t'' m.
    Proof.
      intros t t1 t1LeT1 dirGt.
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

    Lemma whenChildHigh': forall {t t'}, state c (S (t' + t)) > state c t ->
      exists t'', t'' <= t' /\ exists m, m.recv p c (t'' + t) m /\ to m >= state c (S (t' + t)).
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
      pose proof (lt_eq_lt_dec (state c (S (S t' + t))) (state c (S (t' + t)))) as [[lt | eq] | gt'].
      assert (gt: state c (S (t' + t)) > state c t) by omega.
      specialize (IHt' gt).
      destruct IHt' as [t'' [le [m [recvmm mgesSt't]]]].
      assert (t''leSt': t'' <= S t') by omega.
      assert (mgesSSt't: to m >= state c (S (S t' + t))) by omega.
      exists t''.
      intuition.
      exists m.
      intuition.
      rewrite <- eq in IHt'.
      specialize (IHt' sSt'tgst).
      destruct IHt' as [t'' [le rest]].
      exists t''.
      intuition.
      assert (gt: state c (S (S t' + t)) > state c (S (t' + t))) by omega; clear gt'.
      pose proof (whenChildHighRecvm gt) as [m [recvmm mesSt]].
      exists (S t').
      intuition.
      exists m.
      intuition.
    Qed.

    Lemma whenChildHigh: forall {t t'}, t' > t -> state c t' > state c t ->
      exists t'', t <= t'' < t' /\ exists m, m.recv p c t'' m /\ to m >= state c t'.
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
      (~ exists t'', t <= t'' < t' /\ exists m, m.recv p c t'' m /\ to m >= state c t') -> state c t' <= state c t.
    Proof.
      intros t t' t'GeT notE.
      assert (opts: t' = t \/ t' > t) by omega.
      destruct opts as [t'EqT | t'GtT].
      rewrite t'EqT; reflexivity.
      assert (notX: ~ state c t' > state c t) by (intros one;
        pose proof (whenChildHigh t'GtT one); firstorder).
      omega.
    Qed.

    Lemma cReqPRespCrossInd: forall {t tc tp}, tc <= t -> tp <= t -> 
      forall {r m}, r.marksend c p tc r ->
        m.marksend p c tp m -> (forall tc', tc' < tc -> ~ m.recv p c tc' m) ->
        (forall tp', tp' <= tp -> ~ r.recv c p tp' r) -> False.
    Proof.
      induction t.
      intros tc tp tcLeT tpLeT r m rsendr msendm mrecvNo rrecvNo.
      assert (tc0: tc = 0) by omega; clear tcLeT.
      assert (tp0: tp = 0) by omega; clear tpLeT.
      rewrite tc0 in *; rewrite tp0 in *; clear tc0 tp0.
      pose proof (dirSendmImpRecvr msendm) as [r' rrecvr'].
      pose proof (r.recvImpMarkSend rrecvr') as [t' [t'Le0 rsendr']].
      assert (t'0: t' = 0) by omega; clear t'Le0.
      rewrite t'0 in rsendr'; clear t'0.
      pose proof (r.uniqMarksend1 rsendr rsendr') as rEqr'.
      rewrite <- rEqr' in *; clear rEqr'.
      assert (zero: 0 <= 0) by omega.
      firstorder.
      intros tc tp tcLeST tpLeST r m rsendr msendm mrecvNo rrecvNo.

      pose proof (dirSendmImpRecvr msendm) as [r' rrecvr'].
      pose proof (r.recvImpMarkSend rrecvr') as [t' [t'LeSt rsendr']].

      assert (diff: t' = tc \/ t' > tc \/ t' < tc) by omega.
      destruct diff as [eq | [t'GtTc | tcGtT']].
      rewrite eq in rsendr'.
      pose proof (r.uniqMarksend1 rsendr rsendr') as rEqr'.
      rewrite <- rEqr' in *.
      assert (tpEq: tp <= tp) by omega.
      firstorder.

      pose proof (sb.sendrImpNoSendr t'GtTc rsendr rsendr') as [t'' [cond neg]].
      unfold sb.isRMarksend in *; unfold St.toRSComp in *; unfold St.st in *; unfold St.rmarksend in *.
      assert (toRLes: to r <= state c t'') by firstorder.
      pose proof (sb.sendrImpSt rsendr) as toGtt.
      unfold St.toRSComp in *; unfold St.st in *.
      assert (tcLtT'': state c tc < state c t'') by omega.
      assert (t''GtTc: t'' > tc) by omega.
      pose proof (whenChildHigh t''GtTc tcLtT'') as [t''' [[tcLeT''' t'''LtT''] [m' [mrecvm' _]]]].
      pose proof (m.recvImpMarkSend mrecvm') as [td [tdLeT''' msendm']].
      assert (tdLet: td <= t) by omega.
      assert (noRecv: forall tc', tc' < tc -> ~ m.recv p c tc' m') by (
        unfold not; intros tc' tc'LtTc mrecvm'Tc';
          pose proof (m.uniqRecv2 mrecvm' mrecvm'Tc') as tc'EqT''; omega).
      assert (noRecv': forall tp', tp' <= td -> ~ r.recv c p tp' r) by (
        unfold not; intros tp' tp'LeTd;
          assert (tp'LeTp: tp' <= tp) by omega;
            firstorder).
      assert (tcLeT: tc <= t) by omega.
      apply (IHt tc td tcLeT tdLet r m' rsendr msendm' noRecv noRecv').

      pose proof (sb.sendrImpNoSendr tcGtT' rsendr' rsendr) as [tmur [cond neg]].
      unfold sb.isRMarksend in *; unfold St.toRSComp in *; unfold St.st in *; unfold St.rmarksend in *.
      assert (toRLeS: to r' <= state c tmur) by omega.
      pose proof (sb.sendrImpSt rsendr') as toGtt.
      unfold St.toRSComp in *; unfold St.st in *.
      assert (stt'LtstTc: state c t' < state c tmur) by omega.
      assert (tmurGtT': tmur > t') by omega.
      pose proof (whenChildHigh tmurGtT' stt'LtstTc) as [t'' [[tcLeT'' t''LtT'] [m' [mrecvm' _]]]].
      pose proof (m.recvImpMarkSend mrecvm') as [td [tdLeT'' msendm']].
      assert (tdLet: td <= t) by omega.
      assert (noRecv: forall tc', tc' < t' -> ~ m.recv p c tc' m') by (
        unfold not; intros tc' tc'LtTc mrecvm'Tc';
          pose proof (m.uniqRecv2 mrecvm' mrecvm'Tc') as tc'EqT''; omega).
      assert (opts: td = tp \/ td < tp \/ td > tp) by omega.
      destruct opts as [tdEqTp | [tdLTp | tdGtTp]].
      rewrite tdEqTp in *.
      pose proof (m.uniqMarksend1 msendm msendm') as mEqm'.
      rewrite <- mEqm' in *.
      assert (t''LtTc: t'' < tc) by omega.
      firstorder.
      assert (noRecv': forall tp', tp' <= td -> ~ r.recv c p tp' r') by (
        unfold not; intros tp' tp'LeTd rrecvr'Tp';
          pose proof (r.uniqRecv2 rrecvr' rrecvr'Tp') as tp'EqTp;
            omega).
      assert (t'LeT: t' <= t) by omega.
      apply (IHt t' td t'LeT tdLet r' m' rsendr' msendm' noRecv noRecv').
      pose proof (dirSendmImpRecvr msendm') as [r'' rrecvr''].
      pose proof (r.recvImpMarkSend rrecvr'') as [ts [tsLeTd rsendr'']].
      assert (tpLeT: tp <= t) by omega.
      assert (tsLeT: ts <= t) by omega.
      assert (hyp1: forall tc', tc' < ts -> ~ m.recv p c tc' m) by (
        intros tc' tc'LtTs;
          assert (tc'LtTc: tc' < tc) by omega;
            firstorder).
      assert (hyp2: forall tp', tp' <= tp -> ~ r.recv c p tp' r'') by (
        unfold not; intros tp' tpLeTp rrecvr''Tp';
          pose proof (r.uniqRecv2 rrecvr'' rrecvr''Tp') as tdEqTp';
            rewrite <- tdEqTp' in *;
              firstorder).
      apply (IHt ts tp tsLeT tpLeT r'' m rsendr'' msendm hyp1 hyp2).
    Qed.

    Lemma cReqPRespCross: forall {tc tp r m}, r.marksend c p tc r ->
      m.marksend p c tp m -> (forall tc', tc' < tc -> ~ m.recv p c tc' m) ->
      (forall tp', tp' <= tp -> ~ r.recv c p tp' r) -> False.
    Proof.
      intros tc tp.
      assert (tcLeT: tc <= tc + tp) by omega.
      assert (tpLeT: tp <= tc + tp) by omega.
      apply (@cReqPRespCrossInd (tc + tp) tc tp tcLeT tpLeT).
    Qed.

    Lemma noTwoPResp: twoEqPRespFalse.
    Proof.
      intros tx t1 m1 t1LeTx sendm1 t2 m2 t2LeTx sendm2 norecvm1 norecvm2.
      pose proof (dirSendmImpRecvr sendm1) as [r1 recvr1].
      pose proof (dirSendmImpRecvr sendm2) as [r2 recvr2].
      pose proof (r.recvImpMarkSend recvr1) as [t3 [t3LeT1 sendr1]].
      pose proof (r.recvImpMarkSend recvr2) as [t4 [t4LeT2 sendr2]].
      assert (opts: t3 = t4 \/ t3 < t4 \/ t4 < t3) by omega.
      destruct opts as [t3EqT4|[t3LtT4|t4LtT3]].
      rewrite t3EqT4 in *; pose proof (r.uniqMarksend1 sendr1 sendr2) as r1EqR2.
      rewrite r1EqR2 in *; apply (r.uniqRecv2 recvr1 recvr2).

      assert (noRecv: ~ exists t, t3 <= t < t4 /\ exists m, m.recv p c t m) by (
        unfold not; intros [t [cond [m recvm]]];
          pose proof (m.recvImpMarkSend recvm) as [t5 [t5LeT sendm]];
            assert (opts: t5 = t1 \/ t5 < t1 \/ t5 > t1) by omega;
              destruct opts as [t5EqT1 | [t5LtT1 | t5GtT1]]; [
                rewrite t5EqT1 in *; pose proof (m.uniqMarksend1 sendm1 sendm) as m1EqM;
                  rewrite m1EqM in *; assert (tLeTx: t <= tx) by omega;
                    generalize tLeTx norecvm1 recvm; clear; firstorder |
                assert (one: forall tc', tc' < t3 -> ~ m.recv p c tc' m) by (
                  unfold not; intros tc' tc'LtT3 recv'm; pose proof (m.uniqRecv2 recvm recv'm) as tEqTc';
                    rewrite tEqTc' in *; firstorder);
                assert (two: forall tp', tp' <= t5 -> ~ r.recv c p tp' r1) by (
                  unfold not; intros tp' tp'LeT1 recv'r1; pose proof (r.uniqRecv2 recvr1 recv'r1) as t5EqTp';
                    rewrite <- t5EqTp' in *; firstorder);
                apply (cReqPRespCross sendr1 sendm one two) |
                  pose proof (dirSendmImpRecvr sendm) as [r recvr];
                    pose proof (r.recvImpMarkSend recvr) as [t6 [t6LeT5 sendr]];
                      assert (one: forall tc', tc' < t6 -> ~ m.recv p c tc' m1) by (
                        unfold not; intros tc' tc'LtT6 recv'm1; assert (tc'LeT6: tc' <= tx) by omega;
                          generalize norecvm1 recv'm1 tc'LeT6; clear; firstorder);
                      assert (two: forall tp', tp' <= t1 -> ~ r.recv c p tp' r) by (
                        unfold not; intros tp' tp'LeT1 recv'r; pose proof (r.uniqRecv2 recvr recv'r) as t1EqTp';
                          rewrite <- t1EqTp' in *; firstorder);
                      apply (cReqPRespCross sendr sendm1 one two)]).
      assert (t3LeT4: t3 <= t4) by omega.
      pose proof (sb.sendrImpSt sendr1) as stG. unfold St.st, St.toRSComp in *.
      pose proof (sb.sendrImpNoSendr t3LtT4 sendr1 sendr2) as [t5 [t3LtT5LeT4 neg]].
      unfold St.toRSComp, St.st in *.
      assert (pos: state c t5 > state c t3) by omega.
      assert (noRecv': ~ exists t, t3 <= t < t5 /\ exists m, m.recv p c t m /\ to m >= state c t5) by (
        unfold not; intros [t [cond1 [mg [recvmg _]]]];
          assert (cond: t3 <= t < t4) by omega;
            generalize recvmg cond noRecv; clear; firstorder).
      assert (t3LeT5: t3 <= t5) by omega.
      pose proof (whenChildHighConv t3LeT5 noRecv') as stContra.
      omega.

      assert (noRecv: ~ exists t, t4 <= t < t3 /\ exists m, m.recv p c t m) by (
        unfold not; intros [t [cond [m recvm]]];
          pose proof (m.recvImpMarkSend recvm) as [t5 [t5LeT sendm]];
            assert (opts: t5 = t2 \/ t5 < t2 \/ t5 > t2) by omega;
              destruct opts as [t5EqT1 | [t5LtT1 | t5GtT1]]; [
                rewrite t5EqT1 in *; pose proof (m.uniqMarksend1 sendm2 sendm) as m1EqM;
                  rewrite m1EqM in *; assert (tLeTx: t <= tx) by omega;
                    generalize tLeTx norecvm2 recvm; clear; firstorder |
                assert (one: forall tc', tc' < t4 -> ~ m.recv p c tc' m) by (
                  unfold not; intros tc' tc'LtT3 recv'm; pose proof (m.uniqRecv2 recvm recv'm) as tEqTc';
                    rewrite tEqTc' in *; firstorder);
                assert (two: forall tp', tp' <= t5 -> ~ r.recv c p tp' r2) by (
                  unfold not; intros tp' tp'LeT1 recv'r1; pose proof (r.uniqRecv2 recvr2 recv'r1) as t5EqTp';
                    rewrite <- t5EqTp' in *; firstorder);
                apply (cReqPRespCross sendr2 sendm one two)|
                  pose proof (dirSendmImpRecvr sendm) as [r recvr];
                    pose proof (r.recvImpMarkSend recvr) as [t6 [t6LeT5 sendr]];
                      assert (one: forall tc', tc' < t6 -> ~ m.recv p c tc' m2) by (
                        unfold not; intros tc' tc'LtT6 recv'm1; assert (tc'LeT6: tc' <= tx) by omega;
                          generalize norecvm2 recv'm1 tc'LeT6; clear; firstorder);
                      assert (two: forall tp', tp' <= t2 -> ~ r.recv c p tp' r) by (
                        unfold not; intros tp' tp'LeT1 recv'r; pose proof (r.uniqRecv2 recvr recv'r) as t1EqTp';
                          rewrite <- t1EqTp' in *; firstorder);
                      apply (cReqPRespCross sendr sendm2 one two)]).
      assert (t3LeT4: t4 <= t3) by omega.
      pose proof (sb.sendrImpSt sendr2) as stG. unfold St.st, St.toRSComp in *.
      pose proof (sb.sendrImpNoSendr t4LtT3 sendr2 sendr1) as [t5 [t3LtT5LeT4 neg]].
      unfold St.toRSComp, St.st in *.
      assert (pos: state c t5 > state c t4) by omega.
      assert (noRecv': ~ exists t, t4 <= t < t5 /\ exists m, m.recv p c t m /\ to m >= state c t5) by (
        unfold not; intros [t [cond1 [mg [recvmg _]]]];
          assert (cond: t4 <= t < t3) by omega;
            generalize recvmg cond noRecv; clear; firstorder).
      assert (t3LeT5: t4 <= t5) by omega.
      pose proof (whenChildHighConv t3LeT5 noRecv') as stContra.
      omega.
    Qed.

    Lemma noTwoPReqNon: twoPReqNeedsResp.
    Proof.
      intros t t1 r1 t1LeT sendr1 t2 r2 t2LeT sendr2 norecvr1 norecvr2 toR1EqToR2 t1LtT2.
      pose proof (db.sendrImpSt sendr1) as gt1.
      pose proof (db.sendrImpSt sendr2) as gt2.
      unfold Dir.toRSComp, Dir.st, db.isRMarksend, Dir.rmarksend in *.
      pose proof (db.sendrImpNoSendr t1LtT2 sendr1 sendr2) as [t5 [cond dr]].
      unfold Dir.st, Dir.toRSComp in *.
      assert (toR1GeDirT5: to r1 >= dir p c t5) by omega; clear dr.
      assert (dT5LtDt2: dir p c t5 < dir p c t2) by omega.
      assert (t5LeT2: t5 <= t2) by omega.
      pose proof (whenDirLow t5LeT2 dT5LtDt2) as [tm [m [cond2 sendm]]].
      assert (cond3: t1 < tm < t2) by omega.
      firstorder.
    Qed.

    Lemma mainInd: forall {t},
      (forall {to}, to <= t -> state c to <= dir p c to) /\
      (forall {tc tp}, tc <= t -> tp <= t -> forall {mc}, m.marksend c p tc mc ->
        forall {mp}, m.marksend p c tp mp -> (forall tc', tc' < tc -> ~ m.recv p c tc' mp) ->
          (forall tp', tp' < tp -> ~ m.recv c p tp' mc) -> False) /\
       (forall {t1 t2 t3}, t3 <= t -> forall {m}, m.marksend c p t1 m ->
         forall {r}, r.marksend c p t2 r -> r.recv c p t3 r -> t1 <= t2 ->
          (forall t4, t4 < t3 -> ~ m.recv c p t4 m) -> False) /\
       (forall {t1 t2 t3}, t3 <= t -> forall {m}, m.marksend c p t1 m ->
         forall {m'}, m.marksend c p t2 m' -> m.recv c p t3 m' -> t1 < t2 ->
          (forall t4, t4 < t3 -> ~ m.recv c p t4 m) -> False).
    Proof.
      induction t.
      constructor.
      intros to0 to0Le0.
      assert (to0Eq0: to0 = 0) by omega.
      pose proof init as init.
      rewrite to0Eq0.
      omega.
      constructor.
      intros tc tp tcLe0 tpLe0 mc msendmc mp msendmp _ _.
      assert (tcEq0: tc = 0) by omega; assert (tpEq0: tp = 0) by omega.
      rewrite tcEq0 in *; rewrite tpEq0 in *.
      pose proof (dirSendmImpRecvr msendmp) as [r rrecvr].
      pose proof (r.recvImpMarkSend rrecvr) as [t' [t'Le0 rsendr]].
      assert (t'Eq0: t' = 0) by omega.
      rewrite t'Eq0 in *.
      apply (sb.noSendmSendr msendmc rsendr).
      constructor.
      intros t1 t2 t3 t3Le0 m msendm r rsendr rrecvr t1LeT2 neg.
      pose proof (r.recvImpMarkSend rrecvr) as [t5 [t5LeT3 rsendrT5]].
      pose proof (r.uniqMarksend2 rsendr rsendrT5) as t2EqT5.
      assert (t30: t3 = 0) by omega.
      rewrite t2EqT5, t30 in *.
      assert (t1Le0: t1 <= 0) by omega.
      assert (t10: t1 = 0) by intuition.
      assert (t50: t5 = 0) by omega.
      rewrite t10, t50 in *.
      apply (sb.noSendmSendr msendm rsendr).
      intros t1 t2 t3 t3Le0 m msendm m' msendm' mrecvm' t1LeT2 neg.
      pose proof (m.recvImpMarkSend mrecvm') as [t5 [t5LeT3 msendm'T5]].
      pose proof (m.uniqMarksend2 msendm' msendm'T5) as t2EqT5.
      assert (t30: t3 = 0) by omega.
      rewrite t2EqT5, t30 in *.
      assert (t1Le0: t1 <= 0) by omega.
      assert (t10: t1 = 0) by intuition.
      assert (t50: t5 = 0) by omega.
      rewrite t10, t50 in *.
      omega.
      
      destruct IHt as [cons [cross [cReqResp cRespResp]]].

      assert (cross': forall to0, to0 <= S t -> state c to0 <= dir p c to0).
      intros tm toLtT.
      destruct (classical (exists ts, ts < tm /\ ((exists m, m.recv c p ts m) \/ (exists m, m.marksend p c ts m)))) as [chnge|noChnge].
      pose proof (maxExists' classical chnge) as lastChnge; clear chnge.
      destruct lastChnge as [ts [tsLtTo [recvOrSend noPrevChnge]]].
      assert (eq: dir p c (S ts) = dir p c tm) by (
        assert (two: S ts = tm \/ S ts < tm) by omega;
          destruct two as [eq|less]; [
            intuition|
              apply db.noChange; [ intuition | generalize noPrevChnge; clear; firstorder]]).
      destruct recvOrSend as [[m mrecvm] | [m msendm]].
      pose proof (m.recvImpMarkSend mrecvm) as [t' [t'LeTs msendm]].
      destruct (classical (exists tc, t' < tc < tm /\ exists m, m.recv p c tc m)) as [recv|noRecv].
      destruct recv as [tc [comp [m' mrecvm']]].
      pose proof (m.recvImpMarkSend mrecvm') as [t'' [t''LeTc msendm']].
      assert (gOrl: t'' > ts \/ t'' <= ts) by omega.
      destruct gOrl as [t''GtTs | t''LeTs].
      assert (t''LtTc: t'' < tm) by omega.
      generalize noPrevChnge msendm' t''LtTc t''GtTs; clear; firstorder.
      assert (t'LeT: t' <= t) by omega.
      assert (t''LeT: t'' <= t) by omega.
      assert (hyp1: forall tc', tc' < t' -> ~ m.recv p c tc' m') by (
        unfold not; intros tc' tc'LtT' mrecvm'Tc';
          pose proof (m.uniqRecv2 mrecvm' mrecvm'Tc'); intuition).
      assert (hyp2: forall tp', tp' < t'' -> ~ m.recv c p tp' m) by (
        unfold not; intros tp' tp'LtT'' mrecvmTp';
          pose proof (m.uniqRecv2 mrecvm mrecvmTp'); intuition).
      pose proof (cross t' t'' t'LeT t''LeT m msendm m' msendm' hyp1 hyp2).
      firstorder.
      assert (noRecv': ~ (exists tc, S t' <= tc < tm /\ exists m, m.recv p c tc m /\ to m >= state c tm)) by (
        unfold not; intros [tc [cond [m0 [mrecvm0 _]]]];
          assert (cond': t' < tc < tm) by omega; generalize noRecv cond' mrecvm0; clear; firstorder).
      assert (nGt: ~ state c tm > state c (S t')) by (
        assert (eqOrGt: tm = S t' \/ tm > S t') by omega;
          destruct eqOrGt as [toEqSt' | toGtSt']; [
            rewrite <- toEqSt';
              omega |
                pose proof (whenChildHigh toGtSt') as contra;
                  generalize contra noRecv'; clear; firstorder]).
      assert (dirEqSt: dir p c (S ts) = state c (S t')) by (
        pose proof (sb.sendmChange msendm) as one;
          pose proof (db.recvmChange mrecvm) as two;
            unfold St.st, Dir.st in *;
              congruence).
      assert (stoLesSt': state c tm <= state c (S t')) by omega.
      congruence.
      pose proof (dirSendmImpRecvr msendm) as [r rrecvr].
      pose proof (r.recvImpMarkSend rrecvr) as [t' [t'LeTs rsendr]].
      destruct (classical (exists tc, tc < tm /\ m.recv p c tc m)) as [[tc [tcLtTo mrecvm]] | notEx].
      assert (eqOrNot: tm = S tc \/ tm > S tc) by omega.
      destruct eqOrNot as [toEqStc | toGtStc].
      assert (dirEqSt: state c tm = dir p c tm) by (
        pose proof (db.sendmChange msendm) as one; pose proof (sb.recvmChange mrecvm) as two;
          unfold St.st, Dir.st in *; congruence).
      omega.
      assert (noLower: ~ exists t'', S tc <= t'' < tm /\ exists m', m.recv p c t'' m' /\ to m' >= state c tm) by (
        unfold not; intros [t'' [cond [m' [mrecvm' _]]]];
          pose proof (m.recvImpMarkSend mrecvm') as [tf [tfLeT'' msendm']];
            assert (diff: ts = tf \/ tf < ts \/ tf > ts) by omega;
              destruct diff as [tsEqTf | [tfLtTs | tfGtTs]]; [
                rewrite <- tsEqTf in *;
                  pose proof (m.uniqMarksend1 msendm msendm') as mEqM';
                    rewrite <- mEqM' in *;
                      pose proof (m.uniqRecv2 mrecvm mrecvm') as tcEqT'';
                        omega |
                          assert (t'LeTc: t' <= tc) by (
                            pose proof (m.recvImpMarkSend mrecvm) as [tsome [tsomeLe'' msendmTsome]];
                              pose proof (m.uniqMarksend2 msendm msendmTsome) as tcEqTsome;
                                rewrite <- tcEqTsome in *; omega);
                          pose proof @cReqPRespCross;
                            assert (cross1: forall tc', tc' < t' -> ~ m.recv p c tc' m') by (
                              unfold not; intros tc' tc'LtT' mrecvm'Tc';
                                pose proof (m.uniqRecv2 mrecvm' mrecvm'Tc') as t'EqTc'; omega);
                            assert (cross2: forall tp', tp' <= tf -> ~ r.recv c p tp' r) by (
                              unfold not; intros tp' tp'LeTf rrecvrTp';
                                pose proof (r.uniqRecv2 rrecvr rrecvrTp') as tfEqTp'; omega);
                            assert (t''LeT: t'' <= t) by omega;
                              assert (tfLeT: tf <= t) by omega;
                                apply (cReqPRespCross rsendr msendm' cross1 cross2)|
                                  assert (cond2: ts < tf < tm) by omega;
                                    generalize cond2 noPrevChnge msendm'; clear; firstorder]).
      pose proof (whenChildHigh toGtStc) as contra.
      assert (not: ~ state c tm > state c (S tc)) by (generalize noLower contra; clear; firstorder).
      assert (not2: state c tm <= state c (S tc)) by omega; clear not.
      assert (dirEqSt: dir p c (S ts) = state c (S tc)) by (
        pose proof (db.sendmChange msendm) as one; pose proof (sb.recvmChange mrecvm) as two;
          unfold St.st, Dir.st in *; congruence).
      omega.
      assert (tsLeT: ts <= t) by omega.
      assert (less: state c ts <= dir p c ts) by firstorder.
      assert (tmGtTs: tm > t') by omega.
      assert (noRecv: ~ exists t'', t' <= t'' < tm /\ exists m, m.recv p c t'' m /\ to m >= state c tm) by (
        unfold not; intros [t'' [cond [m' [mrecvm' _]]]];
          pose proof (m.recvImpMarkSend mrecvm') as [t1 [t1LeT'' msendm']];
            assert (t1NeTs: t1 = ts -> False) by (
              intros t1EqTs; rewrite t1EqTs in *;
                pose proof (m.uniqMarksend1 msendm msendm') as mEqm';
                  rewrite <- mEqm' in *; 
                    generalize notEx cond mrecvm'; clear; firstorder);
            assert (eqOrNot: t1 = ts \/ t1 > ts \/ t1 < ts) by omega;
              destruct eqOrNot as [t1EqTs | [t1GtTs | t1LtTs]];
                [firstorder |
                  assert (cond2: ts < t1 < tm) by omega;
                    generalize noPrevChnge cond2 msendm'; clear; firstorder |
                      assert (one: forall tc', tc' < t' -> ~ m.recv p c tc' m') by (
                        unfold not; intros tc' tc'LtT' mrecvm'Tc';
                          pose proof (m.uniqRecv2 mrecvm' mrecvm'Tc') as t''EqTc'; omega);
                      assert (two: forall tp', tp' <= t1 -> ~ r.recv c p tp' r) by (
                        unfold not; intros tp' tp'LeT1 rrecvrTp';
                          pose proof (r.uniqRecv2 rrecvr rrecvrTp') as tsEqTp'; omega);
                      apply (cReqPRespCross rsendr msendm' one two)]).
      assert (contra1: ~ state c tm > state c t') by (
        unfold not; intros contra;
          generalize (whenChildHigh tmGtTs contra) noRecv; clear; firstorder).
      assert (cont: state c tm <= state c t') by omega.
      pose proof (sb.sendrImpSt rsendr) as toRGtDir; unfold St.toRSComp in toRGtDir; unfold St.st in *.
      pose proof (dirSendmImpRecvrGe msendm rrecvr) as toMGeToR.
      pose proof (db.sendmChange msendm) as toMEq; unfold Dir.st in *.
      omega.
      assert (eqOrNot: 0 = tm \/ 0 < tm) by omega.
      destruct eqOrNot as [tmEq0 | tmGt0].
      rewrite <- tmEq0 in *; pose proof init as init; rewrite init in *; omega.
      assert (premise: forall tn, 0 <= tn < tm -> (forall m, ~ Dir.mmarksend tn m) /\ (forall m, ~ Dir.mrecv tn m)) by (
        intros tn [_ tnLtTm];
          constructor;
            unfold not; intros m msendm;
              generalize noChnge tnLtTm msendm; clear; firstorder).
      pose proof (db.noChange tmGt0 premise) as dir0DirTm; unfold Dir.st in *.
      pose proof @whenChildHigh.
      assert (not: ~ exists t'', 0 <= t'' < tm /\ exists m, m.recv p c t'' m /\ to m >= state c tm) by (
        unfold not; intros [t'' [[_ t''LtTm] [m [mrecvm _]]]];
          pose proof (m.recvImpMarkSend mrecvm) as [t' [t'LeT'' msendm]];
            assert (t'LtTm: t' < tm) by omega;
              generalize noChnge t'LtTm msendm; clear; firstorder).
      assert (done: ~ state c tm > state c 0) by (generalize (whenChildHigh tmGt0) not; clear; firstorder).
      pose proof init as init; omega.

      constructor.
      apply cross'.

      assert (cReqResp': forall {t1 t2 t3}, t3 <= S t -> forall {m}, m.marksend c p t1 m -> forall {r},
        r.marksend c p t2 r -> r.recv c p t3 r -> t1 <= t2 -> (forall t4, t4 < t3 -> ~ m.recv c p t4 m) -> False).
      intros t1 t2 t3 t3LeSt m msendm r rsendr rrecvr t1LeT2 neg.
      unfold Time in *.
      assert (eqOrNot: t1 = t2 \/ t1 < t2) by omega.
      destruct eqOrNot as [t1EqT2 | t1LtT2].
      rewrite t1EqT2 in *.
      pose proof (sb.noSendmSendr msendm rsendr); intuition.
      clear t1LeT2.
      pose proof (r.recvImpMarkSend rrecvr) as [t' [t'LeT3 rsend'r]].
      pose proof (r.uniqMarksend2 rsendr rsend'r) as t2EqT'.
      rewrite <- t2EqT' in *.
      clear rsend'r t2EqT'.
      assert (t1LeT: t1 <= t) by omega.
      pose proof (cons t1 t1LeT) as st1Ledt1.

      assert (notty1: ~ exists t'', t1 <= t'' < t2 /\ exists m, m.recv p c t'' m /\ to m >= state c t2) by (
        unfold not; intros [t'' [cond [m0 [mrecvm0 _]]]];
          pose proof (m.recvImpMarkSend mrecvm0) as [t5 [t5LeT'' msendm0]];
            assert (one: forall tc', tc' < t1 -> ~ m.recv p c tc' m0) by (
              unfold not; intros tc' tc'LtT1 mrecvM0Tc';
                pose proof (m.uniqRecv2 mrecvm0 mrecvM0Tc') as t''EqTc';
                  rewrite <- t''EqTc' in *; omega);
            assert (two: forall tp', tp' < t5 -> ~ m.recv c p tp' m) by (
              unfold not; intros tp' tp'LtT5; assert (t5LtT3: tp' < t3) by omega; firstorder);
            assert (t5Let: t5 <= t) by omega;
              apply (cross t1 t5 t1LeT t5Let m msendm m0 msendm0 one two)).
      assert (notty: ~ exists t'', S t1 <= t'' < t2 /\ exists m, m.recv p c t'' m /\ to m >= state c t2) by (
        clear cRespResp;
          unfold not; intros [t'' [cond ex]];
            assert (cond2: t1 <= t'' < t2) by omega;
              generalize notty1 cond2 ex; clear; firstorder).
              
      assert (notst2Gtst1: ~ state c t2 > state c (S t1)) by (
        clear cRespResp;
        clear notty1; assert (eqOrNot: S t1 = t2 \/ S t1 < t2) by omega;
          destruct eqOrNot as [eq| St1LtT2]; [
            rewrite eq;
              omega|
                unfold not; intros st; pose proof (whenChildHigh St1LtT2 st) as some; firstorder]).
      assert (stt2LestT1: state c t2 <= state c (S t1)) by omega.
      pose proof (dirRecvrCond rrecvr) as fromRLe.
      pose proof (sb.sendrFrom rsendr) as fromREq; unfold St.st in *.
      pose proof (stSendmImpSt msendm) as stGt.
      pose proof (sb.sendmChange msendm) as stEq; unfold St.st in *.
      rewrite fromREq, <- stEq in *.
      assert (drGt: dir p c t1 > dir p c t3) by omega.
      assert (drNe: dir p c t1 <> dir p c t3) by omega.
      assert (sendRecv: ~ forall tn, t1 <= tn < t3 -> (forall m, ~ m.marksend p c tn m) /\ (forall m, ~ m.recv c p tn m)) by (
        unfold not; intros exp; assert (t1LtT3: t1 < t3) by omega; pose proof (db.noChange t1LtT3 exp); firstorder).
      assert (noSend: forall tn, t1 <= tn < t3 -> forall m, ~ m.marksend p c tn m) by (
        clear cRespResp;
        unfold not; intros tn cond m0 msendm0;
          assert (tnLeT: tn <= t) by omega;
            assert (one: forall tc', tc' < t1 -> ~ m.recv p c tc' m0) by (
              unfold not; intros tc' tc'LtT1 mrecvm0;
                pose proof (m.recvImpMarkSend mrecvm0) as [tm [tmLeTc' msend'm0]];
                  pose proof (m.uniqMarksend2 msendm0 msend'm0) as tmEqTc';
                    rewrite <- tmEqTc' in *; omega);
            assert (two: forall tp', tp' < tn -> ~ m.recv c p tp' m) by (
              unfold not; intros tp' tp'LtTn; assert (tp'LtT3: tp' < t3) by omega; firstorder);
            apply (cross t1 tn t1LeT tnLeT m msendm m0 msendm0 one two)).

      destruct (classical (exists tn, tn < t3 /\ t1 <= tn /\ exists m0, m.recv c p tn m0)) as [ext|noEx].
      pose proof (maxExists' classical ext) as [tn [cond [[tnLtT3 [m0 mrecvm0]] notAfter]]].
      
      pose proof (m.recvImpMarkSend mrecvm0) as [tr [trLeTn msendm0]].
      assert (opts: tr = t1 \/ tr > t1 \/ tr < t1) by omega.
      destruct opts as [trEqT1 | [trGtT1 | trLtT1]].
      rewrite trEqT1 in *.
      pose proof (m.uniqMarksend1 msendm msendm0) as mEqm0.
      rewrite <- mEqm0 in *.
      generalize neg cond mrecvm0; clear; firstorder.
      assert (tnLeT: tn <= t) by omega.
      assert (cond2: forall t4, t4 < tn -> ~ m.recv c p t4 m) by (
        intros t4 t4LtTn; assert (t4LtT3: t4 < t3) by omega;
          generalize neg t4LtT3; clear; firstorder).
      apply (cRespResp t1 tr tn tnLeT m msendm m0 msendm0 mrecvm0 trGtT1 cond2).
      assert (notty2': ~ exists t'', tr <= t'' < t1 /\ exists m, m.recv p c t'' m /\ to m >= state c t1) by (
        unfold not; intros [t'' [cond2 [m1 [mrecvm1 _]]]];
          pose proof (m.recvImpMarkSend mrecvm1) as [t5 [t5LeT'' msendm1]];
            assert (trLeT: tr <= t) by omega;
              assert (t5LeT: t5 <= t) by omega;
                assert (one: forall tc', tc' < tr -> ~ m.recv p c tc' m1) by (
                  unfold not; intros tc' tc'LtTr mrecv'm1;
                    pose proof (m.uniqRecv2 mrecvm1 mrecv'm1) as t''EqTc';
                      rewrite <- t''EqTc' in *;
                        omega);
                assert (two: forall tp', tp' < t5 -> ~ m.recv c p tp' m0) by (
                  unfold not; intros tp' tp'LtT5 mrecv'm0;
                    pose proof (m.uniqRecv2 mrecvm0 mrecv'm0) as tnEqTp';
                      rewrite <- tnEqTp' in *; omega);
                apply (cross tr t5 trLeT t5LeT m0 msendm0 m1 msendm1 one two)).
      assert (notty2: ~ exists t'', S tr <= t'' < t1 /\ exists m, m.recv p c t'' m /\ to m >= state c t1) by (
        unfold not; intros [t'' [cond1 rest]]; assert (cond2: tr <= t'' < t1) by omega;
          generalize notty2' cond2 rest; clear; firstorder).
      assert (strLeT1: S tr <= t1) by omega.
      pose proof (whenChildHighConv strLeT1 notty2) as st1LeTr.
      pose proof (whenChildHighConv t1LtT2 notty) as sST1LeT2.
      assert (trLtT3: tr < t3) by omega.
      assert (noC: forall tn0, S tn <= tn0 < t3 -> (forall m, ~ m.marksend p c tn0 m) /\ (forall m, ~ m.recv c p tn0 m)) by (
        intros tn0 cond2;
          constructor; [assert (cond3: t1 <= tn0 < t3) by omega; generalize noSend cond3; clear; firstorder|
            assert (cond4: tn < tn0 < t3) by omega; 
              assert (t1LeTn0: t1 <= tn0) by omega; generalize cond4 t1LeTn0 notAfter; clear; firstorder]).
      assert (sTnLtT3: S tn <= t3) by omega.
      pose proof (db.noChange2 sTnLtT3 noC) as dirEq.
      unfold Dir.st in *.
      generalize st1LeTr sST1LeT2 sTnLtT3 dirEq rsendr rrecvr msendm msendm0 mrecvm0; clear; intros.
      pose proof (sb.sendmChange msendm) as sEqTom.
      pose proof (stSendmImpSt msendm) as sGtTom.
      pose proof (db.recvmChange mrecvm0) as dSEqTom0.
      pose proof (sb.sendmChange msendm0) as sSEqTom0.
      pose proof (dirRecvrCond rrecvr) as dLeFromr.
      pose proof (sb.sendrFrom rsendr) as sEqFromr.
      unfold St.st, Dir.st in *. omega.
      generalize sendRecv noSend noEx; clear; firstorder.

      constructor.

      intros tc tp tcLeSt tpLeSt mc msendmc mp msendmp norecvmp norecvmc.
      pose proof (dirSendmImpRecvr msendmp) as [r rrecvr].
      pose proof (r.recvImpMarkSend rrecvr) as [t1 [t1LeTp rsendr]].
      assert (opts: t1 = tc \/ tc < t1 \/ t1 < tc) by omega.
      destruct opts as [t1EqTc | [tcLtT1 | t1LtTc]].
      rewrite t1EqTc in *.
      apply (sb.noSendmSendr msendmc rsendr).
      assert (tcLeT1: tc <= t1) by omega.
      apply (cReqResp' tc t1 tp tpLeSt mc msendmc r rsendr rrecvr tcLeT1 norecvmc).
      destruct (classical (exists tm, t1 <= tm < tc /\ exists m, m.recv p c tm m)) as [ext|noExt].
      destruct ext as [tm [[t1LeTm tmLtTc] [m recvm]]].
      pose proof (m.recvImpMarkSend recvm) as [tn [tnLeTm sendm]].
      assert (opts: tn = tp \/ tn < tp \/ tn > tp) by omega.
      destruct opts as [tnEqTp | [tnLtTp | tnGtTp]].
      rewrite tnEqTp in *.
      pose proof (m.uniqMarksend1 sendm msendmp) as mEqMp.
      rewrite mEqMp in *.
      firstorder.
      assert (one: forall tc', tc' < t1 -> ~ m.recv p c tc' m) by (
        unfold not; intros tc' tc'LtT1 recv'm;
          pose proof (m.uniqRecv2 recvm recv'm) as tmEqTc';
            omega).
      assert (two: forall tp', tp' <= tn -> ~ r.recv c p tp' r) by (
        unfold not; intros tp' tp'LeTn recv'r;
          pose proof (r.uniqRecv2 rrecvr recv'r) as tpEqTp';
            omega).
      apply (cReqPRespCross rsendr sendm one two).
      pose proof (dirSendmImpRecvr sendm) as [r1 recvr1].
      pose proof (r.recvImpMarkSend recvr1) as [tq [tqLeTn sendr1]].
      assert (one: forall tc', tc' < tq -> ~ m.recv p c tc' mp) by (
        unfold not; intros tc' tc'LtTq; assert (tc'LtTc: tc' < tc) by omega;
          apply (norecvmp tc' tc'LtTc)).
      assert (two: forall tp', tp' <= tp -> ~ r.recv c p tp' r1) by (
        unfold not; intros tp' tp'LeTp recv'r1;
          pose proof (r.uniqRecv2 recvr1 recv'r1) as tpEqTp';
            omega).
      apply (cReqPRespCross sendr1 msendmp one two).
      assert (opt: ~ exists tm, t1 <= tm < tc /\ exists m, m.recv p c tm m) by (
        generalize noExt; clear; firstorder).
      assert (opt': forall t', t1 < t' <= tc -> ~ exists tm, t1 <= tm < t' /\ exists m,
        m.recv p c tm m /\ to m >= state c t') by (
          unfold not; intros t' t'LtTc [tm [cond rest]]; assert (cond2: t1 <= tm < tc) by omega;
            generalize opt t'LtTc cond2 rest; clear; firstorder).
      assert (notSth: forall t', t1 < t' <= tc -> ~ state c t' > state c t1) by (
        unfold not; intros t' [t1LtT' t'LeTc] sgt;
          pose proof (whenChildHigh t1LtT' sgt) as contra;
            generalize opt' contra t1LtT' t'LeTc; clear; firstorder).
      assert (stcLet1: forall t', t1 < t' <= tc -> state c t' <= state c t1) by (intros t' cond;
        specialize (notSth t' cond); omega).
      clear notSth opt opt'.
      pose proof (sb.sendrImpSt rsendr) as gtRel.
      unfold St.toRSComp, St.st in *.
      assert (stcLet2: forall t', t1 < t' <= tc -> state c t' < to r) by (
        intros t' cond; specialize (stcLet1 t' cond); omega).
      clear stcLet1 gtRel.
      pose proof (stVoluntary rsendr t1LtTc msendmc stcLet2) as [r1 recvr1].
      pose proof (r.recvImpMarkSend recvr1) as [t2 [t2LeT1 sendr1]].
      assert (t2LeTp: t2 = tp \/ t2 > tp \/ t2 < tp) by omega.
      destruct t2LeTp as [t2EqTp | [t2GtTp | t2LtTp]].
      rewrite t2EqTp in *.
      apply (db.noSendmSendr msendmp sendr1).
      assert (tpLeT2: tp <= t2) by omega.
      pose proof (pRespReq noTwoPResp noTwoPReqNon msendmp sendr1 recvr1 tpLeT2) as [t4 [t4LtTp recvmp]].
      generalize norecvmp recvmp t4LtTp; clear; firstorder.
      pose proof (dirSendrImpNoSendm t2LtTp sendr1 msendmp) as [t' [[t2LtT' t'LtTp] [m [recvm toMGeToR1]]]].
      pose proof (m.recvImpMarkSend recvm) as [t'' [t''LeT' sendm]].
      pose proof (sb.sendmChange sendm) as stEqToM. unfold St.st in *.
      pose proof (stRecvrNoSendm recvr1 msendmc) as sTcGtToR1.
      assert (stTcGtStST'': state c tc > state c (S t'')) by omega.
      assert (opts: t'' = tc \/ t'' > tc \/ t'' < tc) by omega.
      destruct opts as [t''EqTc | [t''GtTc | t''LtTc]].
      rewrite t''EqTc in *.
      pose proof (m.uniqMarksend1 msendmc sendm) as mEqMc.
      rewrite mEqMc in *.
      generalize t'LtTp recvm norecvmc; clear; firstorder.
      assert (t'Let: t' <= t) by omega.
      assert (norecv: forall t4, t4 < t' -> ~ m.recv c p t4 mc) by (
        unfold not; intros t4 t4LtT'; assert (t4LtTp: t4 < tp) by omega;
          generalize norecvmc t4LtTp; clear; firstorder).
      apply (cRespResp tc t'' t' t'Let mc msendmc m sendm recvm t''GtTc); intuition.
      assert (opts: S t'' = tc \/ S t'' < tc) by omega.
      destruct opts as [St''EqTc | St''LtTc].
      rewrite St''EqTc in *.
      omega.
      pose proof (whenChildHigh St''LtTc stTcGtStST'') as [ts [cond [s [recvs _]]]].
      pose proof (m.recvImpMarkSend recvs) as [tsr [tsrLeTs sends]].
      assert (opts: tsr = t' \/ tsr > t' \/ tsr < t') by omega.
      destruct opts as [tsrEqT' | [tsrGtT' | tsrLtT']].
      rewrite tsrEqT' in *.
      apply (db.noSendmRecvm sends recvm).
      assert (t2LeTsr: t2 <= tsr) by omega.
      pose proof (pReqResp noTwoPResp noTwoPReqNon sendr1 sends recvs t2LeTsr) as [tf [tfLtTs recv'r1]].
      assert (tfLtTc: tf < tc) by omega.
      pose proof (r.uniqRecv2 recvr1 recv'r1) as tcEqTf.
      omega.
      assert (t''LeT: t'' <= t) by omega.
      assert (tsrLeT: tsr <= t) by omega.
      assert (one: forall tc', tc' < t'' -> ~ m.recv p c tc' s) by (
        unfold not; intros tc' tc'LtT'' recv's; pose proof (m.uniqRecv2 recvs recv's) as tc'EqT';
          rewrite tc'EqT' in *; omega).
      assert (two: forall tp', tp' < tsr -> ~ m.recv c p tp' m) by (
        unfold not; intros tp' tp'LtTsr recv'm; pose proof (m.uniqRecv2 recvm recv'm) as tp'EqTsr;
          omega).
      apply (cross t'' tsr t''LeT tsrLeT  m sendm s sends one two).

      constructor.
      intuition.

      intros t1 t2 t3 t3LeSt m msendm r rsendr rrecvr t1LeT2 neg.
      unfold Time in *.
      assert (eqOrNot: t1 = t2 \/ t1 < t2) by omega.
      destruct eqOrNot as [t1EqT2 | t1LtT2].
      rewrite t1EqT2 in *.
      pose proof (m.uniqMarksend1 msendm rsendr) as mEqR; omega.
      clear t1LeT2.
      pose proof (m.recvImpMarkSend rrecvr) as [t' [t'LeT3 rsend'r]].
      pose proof (m.uniqMarksend2 rsendr rsend'r) as t2EqT'.
      rewrite <- t2EqT' in *.
      clear rsend'r t2EqT'.
      assert (t1LeT: t1 <= t) by omega.
      pose proof (cons t1 t1LeT) as st1Ledt1.

      assert (notty1: ~ exists t'', t1 <= t'' < t2 /\ exists m, m.recv p c t'' m /\ to m >= state c t2) by (
        unfold not; intros [t'' [cond [m0 [mrecvm0 _]]]];
          pose proof (m.recvImpMarkSend mrecvm0) as [t5 [t5LeT'' msendm0]];
            assert (one: forall tc', tc' < t1 -> ~ m.recv p c tc' m0) by (
              unfold not; intros tc' tc'LtT1 mrecvM0Tc';
                pose proof (m.uniqRecv2 mrecvm0 mrecvM0Tc') as t''EqTc';
                  rewrite <- t''EqTc' in *; omega);
            assert (two: forall tp', tp' < t5 -> ~ m.recv c p tp' m) by (
              unfold not; intros tp' tp'LtT5; assert (t5LtT3: tp' < t3) by omega; firstorder);
            assert (t5Let: t5 <= t) by omega;
              apply (cross t1 t5 t1LeT t5Let m msendm m0 msendm0 one two)).
      assert (notty: ~ exists t'', S t1 <= t'' < t2 /\ exists m, m.recv p c t'' m /\ to m >= state c t2) by (
        clear cRespResp;
          unfold not; intros [t'' [cond ex]];
            assert (cond2: t1 <= t'' < t2) by omega;
              generalize notty1 cond2 ex; clear; firstorder).
              
      assert (notst2Gtst1: ~ state c t2 > state c (S t1)) by (
        clear cRespResp;
        clear notty1; assert (eqOrNot: S t1 = t2 \/ S t1 < t2) by omega;
          destruct eqOrNot as [eq| St1LtT2]; [
            rewrite eq;
              omega|
                unfold not; intros st; pose proof (whenChildHigh St1LtT2 st) as some; firstorder]).
      assert (stt2LestT1: state c t2 <= state c (S t1)) by omega.
      pose proof (dirRecvmCond rrecvr) as fromRLe.
      pose proof (sb.sendmFrom rsendr) as fromREq; unfold St.st in *.
      pose proof (stSendmImpSt msendm) as stGt.
      pose proof (sb.sendmChange msendm) as stEq; unfold St.st in *.
      rewrite fromREq, <- stEq in *.
      assert (drGt: dir p c t1 > dir p c t3) by omega.
      assert (drNe: dir p c t1 <> dir p c t3) by omega.
      assert (sendRecv: ~ forall tn, t1 <= tn < t3 -> (forall m, ~ m.marksend p c tn m) /\ (forall m, ~ m.recv c p tn m)) by (
        unfold not; intros exp; assert (t1LtT3: t1 < t3) by omega; pose proof (db.noChange t1LtT3 exp); firstorder).
      assert (noSend: forall tn, t1 <= tn < t3 -> forall m, ~ m.marksend p c tn m) by (
        clear cRespResp;
        unfold not; intros tn cond m0 msendm0;
          assert (tnLeT: tn <= t) by omega;
            assert (one: forall tc', tc' < t1 -> ~ m.recv p c tc' m0) by (
              unfold not; intros tc' tc'LtT1 mrecvm0;
                pose proof (m.recvImpMarkSend mrecvm0) as [tm [tmLeTc' msend'm0]];
                  pose proof (m.uniqMarksend2 msendm0 msend'm0) as tmEqTc';
                    rewrite <- tmEqTc' in *; omega);
            assert (two: forall tp', tp' < tn -> ~ m.recv c p tp' m) by (
              unfold not; intros tp' tp'LtTn; assert (tp'LtT3: tp' < t3) by omega; firstorder);
            apply (cross t1 tn t1LeT tnLeT m msendm m0 msendm0 one two)).

      destruct (classical (exists tn, tn < t3 /\ t1 <= tn /\ exists m0, m.recv c p tn m0)) as [ext|noEx].
      pose proof (maxExists' classical ext) as [tn [cond [[tnLtT3 [m0 mrecvm0]] notAfter]]].
      
      pose proof (m.recvImpMarkSend mrecvm0) as [tr [trLeTn msendm0]].
      assert (opts: tr = t1 \/ tr > t1 \/ tr < t1) by omega.
      destruct opts as [trEqT1 | [trGtT1 | trLtT1]].
      rewrite trEqT1 in *.
      pose proof (m.uniqMarksend1 msendm msendm0) as mEqm0.
      rewrite <- mEqm0 in *.
      generalize neg cond mrecvm0; clear; firstorder.
      assert (tnLeT: tn <= t) by omega.
      assert (cond2: forall t4, t4 < tn -> ~ m.recv c p t4 m) by (
        intros t4 t4LtTn; assert (t4LtT3: t4 < t3) by omega;
          generalize neg t4LtT3; clear; firstorder).
      apply (cRespResp t1 tr tn tnLeT m msendm m0 msendm0 mrecvm0 trGtT1 cond2).
      assert (notty2': ~ exists t'', tr <= t'' < t1 /\ exists m, m.recv p c t'' m /\ to m >= state c t1) by (
        unfold not; intros [t'' [cond2 [m1 [mrecvm1 _]]]];
          pose proof (m.recvImpMarkSend mrecvm1) as [t5 [t5LeT'' msendm1]];
            assert (trLeT: tr <= t) by omega;
              assert (t5LeT: t5 <= t) by omega;
                assert (one: forall tc', tc' < tr -> ~ m.recv p c tc' m1) by (
                  unfold not; intros tc' tc'LtTr mrecv'm1;
                    pose proof (m.uniqRecv2 mrecvm1 mrecv'm1) as t''EqTc';
                      rewrite <- t''EqTc' in *;
                        omega);
                assert (two: forall tp', tp' < t5 -> ~ m.recv c p tp' m0) by (
                  unfold not; intros tp' tp'LtT5 mrecv'm0;
                    pose proof (m.uniqRecv2 mrecvm0 mrecv'm0) as tnEqTp';
                      rewrite <- tnEqTp' in *; omega);
                apply (cross tr t5 trLeT t5LeT m0 msendm0 m1 msendm1 one two)).
      assert (notty2: ~ exists t'', S tr <= t'' < t1 /\ exists m, m.recv p c t'' m /\ to m >= state c t1) by (
        unfold not; intros [t'' [cond1 rest]]; assert (cond2: tr <= t'' < t1) by omega;
          generalize notty2' cond2 rest; clear; firstorder).
      assert (strLeT1: S tr <= t1) by omega.
      pose proof (whenChildHighConv strLeT1 notty2) as st1LeTr.
      pose proof (whenChildHighConv t1LtT2 notty) as sST1LeT2.
      assert (trLtT3: tr < t3) by omega.
      assert (noC: forall tn0, S tn <= tn0 < t3 -> (forall m, ~ m.marksend p c tn0 m) /\ (forall m, ~ m.recv c p tn0 m)) by (
        intros tn0 cond2;
          constructor; [assert (cond3: t1 <= tn0 < t3) by omega; generalize noSend cond3; clear; firstorder|
            assert (cond4: tn < tn0 < t3) by omega; 
              assert (t1LeTn0: t1 <= tn0) by omega; generalize cond4 t1LeTn0 notAfter; clear; firstorder]).
      assert (sTnLtT3: S tn <= t3) by omega.
      pose proof (db.noChange2 sTnLtT3 noC) as dirEq.
      unfold Dir.st in *.
      generalize st1LeTr sST1LeT2 sTnLtT3 dirEq rsendr rrecvr msendm msendm0 mrecvm0; clear; intros.
      pose proof (sb.sendmChange msendm) as sEqTom.
      pose proof (stSendmImpSt msendm) as sGtTom.
      pose proof (db.recvmChange mrecvm0) as dSEqTom0.
      pose proof (sb.sendmChange msendm0) as sSEqTom0.
      pose proof (dirRecvmCond rrecvr) as dLeFromr.
      pose proof (sb.sendmFrom rsendr) as sEqFromr.
      unfold St.st, Dir.st in *. omega.
      generalize sendRecv noSend noEx; clear; firstorder.
    Qed.

    Theorem conservative: forall {t}, dir p c t >= state c t.
    Proof.
      intro t.
      pose proof (@mainInd t) as [first _].
      assert (tLeT: t <= t) by omega; firstorder.
    Qed.

    About mainInd.

    Lemma cRespFifo: forall {t1 t2 t3 m1 m2}, m.marksend c p t1 m1 -> m.marksend c p t2 m2 ->
      m.recv c p t3 m2 -> t1 < t2 -> (forall t4, t4 < t3 -> ~ m.recv c p t4 m1) -> False.
    Proof.
      intros t1 t2 t3 m1 m2 sendm1 sendm2 recvm2 t1LtT2.
      pose proof (@mainInd t3) as [_ [_ [_ last]]].
      specialize (last t1 t2 t3).
      assert (t3LeT3: t3 <= t3) by omega.
      firstorder.
    Qed.

    Lemma cross: forall {t1 t2 m1 m2}, m.marksend c p t1 m1 -> m.marksend p c t2 m2 ->
      (forall t3, t3 < t1 -> ~ m.recv p c t3 m2) -> (forall t4, t4 < t2 -> ~ m.recv c p t4 m1) -> False.
      intros t1 t2 m1 m2 sendm1 sendm2 one two.
      assert (opts: t1 <= t2 \/ t1 > t2) by omega.
      destruct opts as [t1LeT2 | t2LtT1].
      assert (t2LeT2: t2 <= t2) by omega.
      pose proof (@mainInd t2) as [_ [sec _]].
      apply (sec t1 t2 t1LeT2 t2LeT2 m1 sendm1 m2 sendm2 one two).
      assert (t2LeT1: t2 <= t1) by omega.
      assert (t1LeT1: t1 <= t1) by omega.
      pose proof (@mainInd t1) as [_ [sec _]].
      apply (sec t1 t2 t1LeT1 t2LeT1 m1 sendm1 m2 sendm2 one two).
    Qed.

    Theorem cReqRespSent: forall {t1 t2 r}, r.marksend p c t1 r -> r.recv p c t2 r -> to r >= state c t2 ->
      exists t3, t3 < t2 /\ exists m, m.marksend c p t3 m /\ to m <= to r /\
        (forall t4, t4 < t1 -> ~ m.recv c p t4 m).
    Proof.
      intros t1 t2 r sendr recvr toRGestT2.
      destruct (classical (exists t3, t3 < t2 /\ exists m, m.marksend c p t3 m /\ to m <= to r /\ forall t4,
        t4 < t1 -> ~ m.recv c p t4 m)) as [easy|hard].
      intuition.
      pose proof (r.recvImpMarkSend recvr) as [t1' [t1LeT2 send'r]].
      pose proof (r.uniqMarksend2 sendr send'r) as t1'EqT1.
      rewrite <- t1'EqT1 in *.
      clear t1'EqT1 send'r t1'.

      destruct (classical (exists t, t < t1 /\ ((exists m, m.recv c p t m) \/ (exists m, m.marksend p c t m)))) as [ex | notEx].
      pose proof (maxExists' classical ex) as [t [tLtT1 [sendOrRecv notAfter]]].
      assert (nothing: forall y, S t <= y < t1 -> (forall m, ~ m.marksend p c y m) /\ (forall m, ~ m.recv c p y m)) by (intros y cond; assert (cond2: t < y < t1)by omega; generalize cond2 notAfter; clear; firstorder).
      pose proof (db.noChange2 tLtT1 nothing) as dirEq.
      clear nothing; unfold Dir.st in *.
      destruct sendOrRecv as [[m recvm] | [m sendm]].
      pose proof (m.recvImpMarkSend recvm) as [t' [t'LeT sendm]].
      assert (noCRecv: forall tm, t' <= tm < t2 -> forall m', ~ m.recv p c tm m') by (
        unfold not; intros tm cond m' recvm';
          pose proof (m.recvImpMarkSend recvm') as [ts [tsLeTm sendm']];
            assert (opts: ts < t \/ ts = t \/ t < ts < t1 \/ t1 <= ts) by omega;
              destruct opts as [tsLtT | [tsEqT | [tLtTsLtT1  | t1LeTs ]]]; [
                assert (one: forall x, x < t' -> ~ m.recv p c x m') by ( unfold not; intros x xLtT' recv'm';
                  pose proof (m.uniqRecv2 recvm' recv'm') as xEqTm; omega);
                assert (two: forall x, x < ts -> ~ m.recv c p x m) by (unfold not; intros x xLtTs recv'm;
                  pose proof (m.uniqRecv2 recvm recv'm) as xEqTs; omega);
                apply (cross sendm sendm' one two) |
                  rewrite tsEqT in *;
                    apply (db.noSendmRecvm sendm' recvm) |
                      generalize notAfter tLtTsLtT1 sendm'; clear; firstorder |
                        pose proof (pReqResp noTwoPResp noTwoPReqNon sendr sendm' recvm' t1LeTs) as [t4 [t4LtTm recv'r]];
      pose proof (r.uniqRecv2 recvr recv'r) as t4EqT2; omega]).
      destruct (classical (exists ts, ts < t2 /\ t' < ts /\ exists m', m.marksend c p ts m')) as [ ex2 | notEx2].
      pose proof (maxExists' classical ex2) as [ts [tsLtT2 [[t'LtTs [m' sendm']] notAfter2]]].
      assert (nothing: forall y, S ts <= y < t2 ->
        (forall m, ~ m.marksend c p y m) /\ (forall m, ~ m.recv p c y m)) by
      (intros y cond; assert (cond1: t' < y < t2) by omega; assert (cond2: t' <= y < t2) by omega;
        generalize notAfter2 noCRecv cond cond1 cond2; clear; firstorder).
      pose proof (sb.noChange2 tsLtT2 nothing) as stEq.
      unfold St.st in *.
      destruct (classical (exists tr, tr < t1 /\ m.recv c p tr m')) as [ [tr [trLtT1 recvm']] | noRecv].
      assert (opts: tr < t \/ tr = t \/ t < tr < t1) by omega.
      destruct opts as [trLtT | [trEqT | cond]].
      assert (forall t4, t4 < tr -> ~ m.recv c p t4 m) by (
        unfold not; intros t4 t4LtTr recv'm; pose proof (m.uniqRecv2 recvm recv'm) as t4EqT; omega).
      pose proof (cRespFifo sendm sendm' recvm' t'LtTs). intuition.
      rewrite trEqT in *.
      pose proof (m.uniqRecv1 recvm recvm') as mEqM'.
      rewrite mEqM' in *.
      pose proof (m.uniqMarksend2 sendm sendm') as t'EqTs.
      omega.
      generalize notAfter cond recvm'; clear; firstorder.
      assert (opts: to m' <= to r \/ to m' > to r) by omega.
      destruct opts as [toM'LeToR | toM'GtToR].
      generalize tsLtT2 sendm' toM'LeToR noRecv; clear; firstorder.
      pose proof (sb.sendmChange sendm') as stEqToM'.
      unfold St.st in *.
      omega.
      assert (nothing: forall y, S t' <= y < t2 ->
        (forall m, ~ m.marksend c p y m) /\ (forall m, ~ m.recv p c y m)) by
      (intros y cond; assert (cond2: t' <= y < t2) by omega;
        generalize notEx2 noCRecv cond cond2; clear; firstorder).
      assert (t'LeT2: S t' <= t2) by omega.
      pose proof (sb.noChange2 t'LeT2 nothing) as stEq.
      pose proof (db.sendrImpSt sendr) as toRLtD.
      pose proof (sb.sendmChange sendm) as st1.
      pose proof (db.recvmChange recvm) as st2.
      unfold St.st, Dir.st, Dir.toRSComp in *.
      omega.

      assert (tLeT1: t <= t1) by omega.
      pose proof (pRespReq noTwoPResp noTwoPReqNon sendm sendr recvr tLeT1) as [t' [t'LtT2 recvm]].
      pose proof (m.recvImpMarkSend recvm) as [t'' [tLeT' send'm]].
      pose proof (m.uniqMarksend2 sendm send'm) as t''EqT.
      rewrite <- t''EqT in *. clear t''EqT t'' send'm.
      assert (noCRecv: forall tm, t' < tm < t2 -> forall m', ~ m.recv p c tm m').
        unfold not; intros tm cond m' recvm';
          pose proof (m.recvImpMarkSend recvm') as [ts [tsLeTm sendm']];
            assert (opts: ts < t \/ ts = t \/ t < ts < t1 \/ t1 <= ts) by omega;
              destruct opts as [tsLtT | [tsEqT | [tLtTsLtT1  | t1LeTs ]]]; [
                pose proof (dirSendmImpRecvr sendm) as [r' recvr'];
                  pose proof (r.recvImpMarkSend recvr') as [tx [txLeT sendr']];
                    assert (one: forall t3, t3 < tx -> ~ m.recv p c t3 m') by (
                      unfold not; intros t3 t3LtTx recv'm'; pose proof (m.uniqRecv2 recvm' recv'm') as t3EqTr;
                        omega);
                    assert (two: forall t4, t4 <= ts -> ~ r.recv c p t4 r') by (
                      unfold not; intros t4 t4LeTs recv'r'; pose proof (r.uniqRecv2 recvr' recv'r') as t4EqTs;
                        omega);
                    apply (cReqPRespCross sendr' sendm' one two)|
                  rewrite tsEqT in *; pose proof (m.uniqMarksend1 sendm sendm') as mEqM'; rewrite mEqM' in *;
                    pose proof (m.uniqRecv2 recvm recvm') as trEqT'; omega |
                      generalize notAfter tLtTsLtT1 sendm'; clear; firstorder |
                        pose proof (pReqResp noTwoPResp noTwoPReqNon sendr sendm' recvm' t1LeTs) as [t4 [t4LtTm recv'r]];
                          pose proof (r.uniqRecv2 recvr recv'r) as t4EqT2; omega].
      
      destruct (classical (exists ts, ts < t2 /\ t' < ts /\ exists m', m.marksend c p ts m')) as [ ex2 | notEx2].
      pose proof (maxExists' classical ex2) as [ts [tsLtT2 [[t'LtTs [m' sendm']] notAfter2]]].
      assert (nothing: forall y, S ts <= y < t2 ->
        (forall m, ~ m.marksend c p y m) /\ (forall m, ~ m.recv p c y m)) by
      (intros y cond; assert (cond1: t' < y < t2) by omega;
        generalize notAfter2 noCRecv cond cond1; clear; firstorder).
      pose proof (sb.noChange2 tsLtT2 nothing) as stEq.
      unfold St.st in *.
      destruct (classical (exists tr, tr < t1 /\ m.recv c p tr m')) as [ [tr [trLtT1 recvm']] | noRecv].
      pose proof (m.recvImpMarkSend recvm') as [ts' [ts'LeTr send'm']].
      pose proof (m.uniqMarksend2 send'm' sendm') as ts'EqTs.
      assert (trGtT: tr > t) by omega.
      clear ts' ts'LeTr send'm' ts'EqTs.
      assert (opts: t < tr < t1 \/ t1 <= tr) by omega.
      destruct opts as [cond1 | t1LeTr].
      generalize cond1 notAfter recvm'; clear; firstorder.
      assert (opts: to m' <= to r \/ to m' > to r) by omega.
      destruct opts as [toM'LeToR | toM'GtToR].
      assert (noRecv: forall t4, t4 < t1 -> ~ m.recv c p t4 m') by (
        unfold not; intros t4 t4LtT1 recv'm'; pose proof (m.uniqRecv2 recvm' recv'm') as t4EqTr; omega).
      generalize tsLtT2 sendm' toM'LeToR noRecv; clear; firstorder.
      pose proof (sb.sendmChange sendm') as stEqToM'.
      unfold St.st in *.
      omega.
      assert (last: forall t4, t4 < t1 -> ~ m.recv c p t4 m') by (generalize noRecv; clear; firstorder).
      assert (opts: to m' <= to r \/ to m' > to r) by omega.
      destruct opts as [toM'LeToR | toM'GtToR].
      generalize last tsLtT2 toM'LeToR sendm'; clear; firstorder.
      pose proof (sb.sendmChange sendm') as stEqToM'.
      unfold St.st in *.
      omega.
      assert (nothing: forall y, S t' <= y < t2 ->
        (forall m, ~ m.marksend c p y m) /\ (forall m, ~ m.recv p c y m)) by
      (generalize noCRecv notEx2; clear; firstorder).
      pose proof (sb.noChange2 t'LtT2 nothing) as stEq.
      unfold St.st in *.
      pose proof (sb.recvmChange recvm) as st1.
      pose proof (db.sendmChange sendm) as d1.
      pose proof (db.sendrImpSt sendr) as d2.
      unfold Dir.toRSComp, Dir.st, St.st in *.
      omega.
      assert (cNoRecv: forall t4, t4 < t2 -> forall m, ~ m.recv p c t4 m) by (
        unfold not; intros t4 t4LtT2 m recvm; pose proof (m.recvImpMarkSend recvm) as [t3 [t3LeT4 sendm]];
          assert (opts: t3 < t1 \/ t3 >= t1) by omega;
            destruct opts as [t3LtT1 | t4GeT1]; [
              generalize notEx t3LtT1 sendm; clear; firstorder;
                intuition |
                  pose proof (pReqResp noTwoPResp noTwoPReqNon sendr sendm recvm t4GeT1) as [t5 [t4LtT4 recv'r]];
                    pose proof (r.uniqRecv2 recvr recv'r) as t5EqT2; omega]).
      destruct (classical (exists t3, t3 < t2 /\ exists m, m.marksend c p t3 m)) as [ex2 | notEx2].
      pose proof (maxExists' classical ex2) as [ts [tsLtT2 [[m' sendm'] notAfter2]]].
      assert (nothing: forall y, S ts <= y < t2 ->
        (forall m, ~ m.marksend c p y m) /\ (forall m, ~ m.recv p c y m)) by
      (intros y cond;
        generalize notAfter2 cNoRecv cond; clear; firstorder).
      pose proof (sb.noChange2 tsLtT2 nothing) as stEq.
      unfold St.st in *.
      destruct (classical (exists tr, tr < t1 /\ m.recv c p tr m')) as [ [tr [trLtT1 recvm']] | noRecv].
      generalize notEx trLtT1 recvm'; clear; firstorder.
      assert (opts: to m' <= to r \/ to m' > to r) by omega.
      destruct opts as [toM'LeToR | toM'GtToR].
      generalize toM'LeToR noRecv tsLtT2 sendm'; clear; firstorder.
      pose proof (sb.sendmChange sendm') as stEqToM'.
      unfold St.st in *.
      omega.
      assert (nothing1: forall y, 0 <= y < t2 ->
        (forall m, ~ m.marksend c p y m) /\ (forall m, ~ m.recv p c y m)) by
      (generalize cNoRecv notEx2; clear; firstorder).
      assert (x1: 0 <= t2) by omega.
      pose proof (sb.noChange2 x1 nothing1) as st1.
      assert (nothing2: forall y, 0 <= y < t1 ->
        (forall m, ~ m.marksend p c y m) /\ (forall m, ~ m.recv c p y m)) by
      (generalize notEx; clear; firstorder).
      assert (x2: 0 <= t1) by omega.
      pose proof (db.noChange2 x2 nothing2) as d1.
      pose proof init as start.
      pose proof (db.sendrImpSt sendr) as d2.
      unfold Dir.toRSComp, Dir.st, St.st in *.
      omega.
    Qed.
  End LocalRules.
End System.

