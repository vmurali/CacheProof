Require Import CpdtTactics.
Load Useful.
Load DataTypes.
Load Fifo.

Module Classical.
  Hypothesis dec: forall P: Prop, P \/ ~ P.
End Classical.

Module RespMesg <: Mesg.
  Definition mesg := (State * State)%type.
End RespMesg.

Module Type RespAxioms (pc cp: FifoHighLevel RespMesg).
  Import RespMesg.

  Definition send pt m t :=
    match pt with
      | p => pc.f.enq m t
      | c => cp.f.enq m t
    end.
  
  Definition recv pt m t :=
    match pt with
      | p => cp.f.deq m t
      | c => pc.f.deq m t
    end.

  Parameter state: Point -> nat -> State.
  Definition nextState pt t := state pt (S t).

  Axiom init: state p 0 = state c 0.
  Axiom stateChange: forall {pt t}, state pt t <> nextState pt t -> exists m, send pt m t \/ recv pt m t.

  Axiom sendCommon: forall {pt m t}, send pt m t -> state pt t = fst m /\ nextState pt t = snd m.

  Axiom recvParent: forall {m t}, recv p m t -> nextState p t = snd m.

  Axiom recvChildChange: forall {m t}, recv c m t -> fst m <= state c t -> nextState c t = snd m.

  Axiom recvChildNoChange: forall {m t}, recv c m t -> fst m > state c t -> nextState c t = state c t.

  Axiom sendParent: forall {m t}, send p m t -> fst m < snd m.

  Axiom sendChild: forall {m t}, send c m t -> fst m > snd m.
End RespAxioms.

Module Type Resp (pc cp: FifoHighLevel RespMesg).
  Import RespMesg.
  Parameter state: Point -> nat -> State.
  Parameter nextState: Point -> nat -> State.
  Parameter send: Point -> mesg -> nat -> Prop.
  Parameter recv: Point -> mesg -> nat -> Prop.
  Axiom conservative: forall t, state c t <= state p t.
End Resp.

Module GetResp (pc cp: FifoHighLevel RespMesg) (axioms: RespAxioms pc cp) : Resp pc cp.
  Import Classical.
  Import axioms.
  Import RespMesg.
  Import Datatypes.

  Section noRecvParent.
    Context {ti : nat}.

    Lemma noRecvParentNow {t} (noRecv : forall m, ~ recv p m t) : nextState p t >= state p t.
    Proof.
      assert (eqOrNot: state p t = nextState p t \/ state p t <> nextState p t) by decide equality.
      destruct eqOrNot as [eq | notEq].
      crush.
      pose proof (stateChange notEq) as exMsg.
      destruct exMsg as [m [sendM | recvM]].
      pose proof (sendCommon sendM) as rel1.
      pose proof (sendParent sendM) as rel2.
      assert (state p t < nextState p t) by crush.
      crush.
      specialize (noRecv m recvM); crush.
    Qed.

    Lemma noRecvParent' {td} (noRecv : forall t, ti <= t <= ti + td -> forall m, ~ recv p m t):
      nextState p (ti + td) >= state p ti.
    Proof.
      induction td.
      assert (noRecvTi: forall m, ~ recv p m ti) by (unfold not; intro m; intro recvM; assert (cond: ti <= ti <= ti + 0) by crush; specialize (noRecv ti cond m); crush).
      assert (nextState p ti >= state p ti) by (apply (noRecvParentNow noRecvTi)).
      assert (ti + 0 = ti) by crush.
      crush.
      assert (indNoRecv: forall t, ti <= t <= ti + td -> forall m, ~ recv p m t) by (
        intro t; intro cond; intro m; assert (cond': ti <= t <= ti + S td) by crush; apply (noRecv t cond' m)).
      specialize (IHtd indNoRecv).
      clear indNoRecv.
      assert (noRecvNow: forall m, ~ recv p m (ti + S td)) by (
        intros; assert (cond: ti <= ti + S td <= ti + S td) by crush; apply (noRecv (ti + S td) cond m)).
      pose proof (noRecvParentNow noRecvNow) as stateRel.
      assert (state p (ti + S td) = nextState p (ti + td)) by (unfold nextState; crush).
      crush.
    Qed.

    Lemma noRecvParent1 {tf} (tiLeTf: ti <= tf) (noRecv: forall t, ti <= t <= tf -> forall m, ~ recv p m t): nextState p tf >= state p ti.
    Proof.
      pose proof (@noRecvParent' (tf - ti)) as noRecvParentInst.      assert (rew: ti + (tf - ti) = tf) by crush.
      rewrite rew in noRecvParentInst.
      firstorder.
    Qed.
  End noRecvParent.

  Lemma noRecvParent2 {ti tf}:
    ti <= tf -> (forall t, S ti <= t <= tf -> forall m, ~ recv p m t) ->
    nextState p tf >= nextState p ti.
  Proof.
    intros.
    assert (dec: S ti <= tf \/ ti = tf) by crush.
    destruct dec.
    apply noRecvParent1; crush.
    crush.
  Qed.

  Lemma zeroRecvParent {m} (sendM: send c m 0) {t} (recvM: recv p m t) {t'} (le: t' <= t):
    state p t' >= state p 0.
  Proof.
    pose proof (cp.enq0First sendM recvM) as enqFirst'.
    destruct t'.
    crush.
    assert (enqFirst: forall t1, 0 <= t1 <= t' -> forall m', ~ recv p m' t1) by (intros; assert (t1 < t) by crush; firstorder).
    apply noRecvParent1; crush.
  Qed.

  Section noRecvChild.
    Context {ti : nat}.

    Lemma noRecvChildNow {t} (noRecv : forall m, ~ (recv c m t /\ fst m <= state c t)):
      nextState c t <= state c t.
    Proof.
      assert (eqOrNot: state c t = nextState c t \/ state c t <> nextState c t) by decide equality.
      destruct eqOrNot as [eq | notEq].
      crush.
      pose proof (stateChange notEq) as exMsg.
      destruct exMsg as [m [sendM | recvM]].
      pose proof (sendCommon sendM) as rel1.
      pose proof (sendChild sendM) as rel2.
      assert (state c t > nextState c t) by crush.
      crush.
      specialize (noRecv m).
      assert (decLe: fst m <= state c t \/ fst m > state c t) by crush.
      destruct decLe as [le | gt].
      crush.
      assert (nextState c t = state c t) by (apply (recvChildNoChange recvM gt)).
      crush.
    Qed.

    Lemma noRecvChild' {td} (noRecv: forall t, ti <= t <= ti + td -> forall m, ~ (recv c m t /\ fst m <= state c t)):
      nextState c (ti + td) <= state c ti.
    Proof.
      induction td.
      assert (noRecvTi: forall m, ~ (recv c m ti /\ fst m <= state c ti)) by (unfold not; intro m; intro recvM; assert (cond: ti <= ti <= ti + 0) by crush; specialize (noRecv ti cond m recvM); crush).
      assert (nextState c ti <= state c ti) by (apply (noRecvChildNow noRecvTi)).
      assert (ti + 0 = ti) by crush.
      crush.
      assert (indNoRecv: forall t, ti <= t <= ti + td -> forall m, ~ (recv c m t /\ fst m <= state c t)) by (
        intro t; intro cond; intro m; assert (cond': ti <= t <= ti + S td) by crush; apply (noRecv t cond' m)).
      specialize (IHtd indNoRecv).
      clear indNoRecv.
      assert (noRecvNow: forall m, ~ (recv c m (ti + S td) /\ fst m <= state c (ti + S td))) by (
        intros; assert (cond: ti <= ti + S td <= ti + S td) by crush; apply (noRecv (ti + S td) cond m)).
      pose proof (noRecvChildNow noRecvNow) as stateRel.
      assert (state c (ti + S td) = nextState c (ti + td)) by (unfold nextState; crush).
      crush.
    Qed.

    Lemma noRecvChild1 {tf} (tiLeTf: ti <= tf) (noRecv: forall t, ti <= t <= tf -> forall m, ~ (recv c m t /\ fst m <= state c t)): nextState c tf <= state c ti.
    Proof.
      pose proof (@noRecvChild' (tf - ti)) as noRecvChildInst.
      assert (rew: ti + (tf - ti) = tf) by crush.
      rewrite rew in noRecvChildInst.
      firstorder.
    Qed.
  End noRecvChild.

  Lemma noRecvChild2 {ti tf}:
    ti <= tf -> (forall t, S ti <= t <= tf -> forall m, ~ (recv c m t /\ fst m <= state c t)) ->
    nextState c tf <= nextState c ti.
  Proof.
    intros.
    assert (dec: S ti <= tf \/ ti = tf) by crush.
    destruct dec.
    apply noRecvChild1; crush.
    crush.
  Qed.

  Lemma childRecv {ti tf} (le: ti <= tf) (nscTiLtTf: nextState c ti < nextState c tf):
    exists t, S ti <= t <= tf /\ exists m, recv c m t /\ fst m <= state c t.
  Proof.
    pose proof (noRecvChild2 le) as noRecv.
    assert (gt: ~ nextState c tf <= nextState c ti) by crush.
    pose proof (dec (exists t, S ti <= t <= tf /\ exists m, recv c m t /\ fst m <= state c t)) as exDec.
    firstorder.
  Qed.

  Lemma zeroRecvChild {m} (sendM: send p m 0) {t} (recvM: recv c m t) {t'} (le: t' <= t):
    state c t' <= state c 0.
  Proof.
    
    pose proof (pc.enq0First sendM recvM) as enqFirst'.
    destruct t'.
    crush.
    assert (enqFirst: forall t1, 0 <= t1 <= t' -> forall m', ~ (recv c m' t1 /\ fst m' <= state c t1)) by (intros; assert (t1 < t) by crush; firstorder).
    apply noRecvChild1; crush.
  Qed.

  Lemma childRecvNoParentRecv {tp tc} (recvpImpSendc: forall m t1 t2, recv p m t1 -> send c m t2 -> t1 <= tp -> t2 <= tc) (recvcImpSendp: forall m t1 t2, recv c m t1 -> send p m t2 -> t1 <= tc -> t2 <= tp) {tr} (trLeTc: tr <= tc) {m} (recvcm: recv c m tr /\ fst m <= state c tr) (noRecvc: forall t, S tr <= t <= tc -> ~ exists m, recv c m t /\ fst m <= state c t) {ts} (sendp: send p m ts) (noRecvp: forall t, S ts <= t <= tp -> forall m, ~ recv p m t) (contra: nextState c tc > nextState p tp): False.
    assert (noRecvc': forall t, S tr <= t <= tc -> forall m, ~ (recv c m t /\ fst m <= state c t)) by (generalize noRecvc; clear; firstorder).
    clear noRecvc.
    assert (nscTcLeTr: nextState c tc <= nextState c tr) by (apply (noRecvChild2 trLeTc noRecvc')).
    assert (tsLeTp: ts <= tp) by (apply (recvcImpSendp m tr); crush).
    assert (nspTpGeTs: nextState p tp >= nextState p ts) by (apply (noRecvParent2 tsLeTp noRecvp)).
    assert (nextState p ts = snd m) by (apply sendCommon; crush).
    assert (nextState c tr = snd m) by (apply recvChildChange; crush).
    crush.
  Qed.

  Theorem strongLess:
    forall tp tc,
      (forall m t1 t2, recv p m t1 -> send c m t2 -> t1 <= tp -> t2 <= tc) ->
      (forall m t1 t2, recv c m t1 -> send p m t2 -> t1 <= tc -> t2 <= tp) ->
      ~ (nextState c tc > nextState p tp).
  Proof.
    apply notExistForallNot.
    unfold not.
    intros exStmt.


    pose proof (minExists dec exStmt) as exMin.
    clear exStmt.
    destruct exMin as [tpmin [[tcmin [pRecvCSend [cRecvPSend wrongState]]] tpminHyp']].
    assert (tpminHyp: ~ exists x y, x < tpmin /\
      (forall m t1 t2, recv p m t1 -> send c m t2 -> t1 <= x -> t2 <= y) /\
      (forall m t1 t2, recv c m t1 -> send p m t2 -> t1 <= y -> t2 <= x) /\
      nextState c y > nextState p x) by firstorder.
    clear tpminHyp'.
    destruct (dec (forall t, 0 <= t <= tpmin -> forall m, ~ recv p m t)) as [pNotRecv | pRecv'].
    destruct (dec (forall t, 0 <= t <= tcmin -> forall m, ~ (recv c m t /\ fst m <= state c t))) as [cNotRecv | cRecv'].
    assert (zeroLeTpmin: 0 <= tpmin) by crush.
    assert (nsPTpminGeStateP0: nextState p tpmin >= state p 0) by (apply (noRecvParent1 zeroLeTpmin pNotRecv)).
    clear pNotRecv zeroLeTpmin.
    assert (zeroLeTcmin: 0 <= tcmin) by crush.
    assert (nsCTcminLeStateC0: nextState c tcmin <= state c 0) by (apply (noRecvChild1 zeroLeTcmin cNotRecv)).
    assert (nsCTcminLeNsPTpmin: nextState c tcmin <= nextState p tpmin) by (pose proof init; crush).
    crush.
    assert (cRecvEx: exists t, 0 <= t <= tcmin /\ exists m, recv c m t /\ fst m <= state c t) by (generalize (dec (exists t, 0 <= t <= tcmin /\ exists m, recv c m t /\ fst m <= state c t)) cRecv'; clear; firstorder).
    clear cRecv'.
    destruct cRecvEx as [tcRecv rest].
    assert (cRecv: exists x, x <= tcmin /\ exists m, recv c m x /\ fst m <= state c x) by (exists tcRecv; crush).
    clear tcRecv rest.
    pose proof (maxExists dec cRecv) as cRecvMax.
    clear cRecv.
    destruct cRecvMax as [tcmax [tcmaxLeTcmin [[m childRecvCond] noCRecv]]].
    assert (exTpmax: exists tpmax, tpmax <= tcmax /\ send p m tpmax) by (apply pc.f.deqImpEnq; crush).
    destruct exTpmax as [tpmax [useless sendPMTpmax]].
    clear useless.
    assert (pNotRecvGtTpmax: forall t, S tpmax <= t <= tpmin -> forall m, ~ recv p m t) by
      (intros; assert (0 <= t <= tpmin) by crush; apply pNotRecv; crush).
    apply (childRecvNoParentRecv pRecvCSend cRecvPSend tcmaxLeTcmin childRecvCond noCRecv sendPMTpmax pNotRecvGtTpmax wrongState).
    assert (pRecv'': exists t, 0 <= t <= tpmin /\ exists m, recv p m t) by (generalize (dec (exists t, 0 <= t <= tpmin /\ exists m, recv p m t)) pRecv'; clear; firstorder).
    clear pRecv'.
    assert (exPRecv: exists t, t <= tpmin /\ exists m, recv p m t) by (destruct pRecv'' as [t rest]; exists t; crush).
    clear pRecv''.
    pose proof (maxExists dec exPRecv) as exPRecvMax.
    clear exPRecv.
    destruct exPRecvMax as [tp1 [tp1LeTpmin [[m recvmPMTp1] noRecvGTTp1']]].
    assert (noRecvGTTp1: forall y, S tp1 <= y <= tpmin -> forall m, ~ recv p m y) by (generalize noRecvGTTp1'; clear; firstorder).
    clear noRecvGTTp1'.
    assert (nsPTpminGeNsPTp1: nextState p tpmin >= nextState p tp1) by (apply noRecvParent2; crush).
    assert (exRest: exists tc1, tc1 <= tp1 /\ send c m tc1) by (apply cp.f.deqImpEnq; crush).
    destruct exRest as [tc1 [tc1LeTp1 sendmCMTc1]].

    assert (rest: state c tc1 = fst m /\ nextState c tc1 = snd m) by (apply sendCommon; crush).
    destruct rest as [sCTc1EqFstM nsCTc1EqSndM].
    assert (nsCTcminGTNsPTp1: nextState c tcmin > nextState p tp1) by crush.
    assert (nsPTp1EqSndM: nextState p tp1 = snd m) by (apply recvParent; crush).
    assert (nsCTc1LtNsCTcmin: nextState c tc1 < nextState c tcmin) by crush.
    assert (tc1LeTcmin: tc1 <= tcmin) by (apply (pRecvCSend m tp1); crush).
    pose proof (childRecv tc1LeTcmin nsCTc1LtNsCTcmin) as exCRecv.

    assert (sCTc1GtNsCTc1: state c tc1 > nextState c tc1) by (assert (fst m > snd m) by (apply (@sendChild m tc1); crush); crush).

    clear nsPTpminGeNsPTp1 sCTc1EqFstM nsCTc1EqSndM nsCTcminGTNsPTp1 nsPTp1EqSndM nsCTc1LtNsCTcmin.

    pose proof (minExists dec exCRecv) as exCRecvMin.

    clear exCRecv.
    destruct exCRecvMin as [tc2 [[tc1LtTc2LeTcmin exCRecv] noCRecvGTTc1']].
    generalize exCRecv; intro rest.
    destruct rest as [n [cRecvN fstN]].
    assert (exPSend: exists tp2, tp2 <= tc2 /\ send p n tp2) by (apply pc.f.deqImpEnq; crush).
    destruct exPSend as [tp2 [tp2LeTc2 pSendN]].
    assert (fstSndPN: state p tp2 = fst n /\ nextState p tp2 = snd n) by (apply sendCommon; crush).
    destruct fstSndPN as [fstPN sndPN].
    assert (sPTp2LeScTc2: state p tp2 <= state c tc2) by crush.

    destruct tc2.
    crush.
    assert (tc1LeTc2: tc1 <= tc2) by crush.
    assert (noCRecv': forall y, S tc1 <= y <= tc2 -> ~ exists m, recv c m y /\ fst m <= state c y) by
      (intro; intro hyp; assert (hyp': y < S tc2) by (generalize hyp; clear; crush); specialize (noCRecvGTTc1' y hyp'); assert (S tc1 <= y <= tcmin) by (generalize hyp tc1LtTc2LeTcmin; clear; crush); crush).
    assert (noCRecv: forall y, S tc1 <= y <= tc2 -> forall m, ~ (recv c m y /\ fst m <= state c y)) by
      (generalize noCRecv'; clear; firstorder).
    clear noCRecv'.
    pose proof (noRecvChild2 tc1LeTc2 noCRecv) as nsCtc2LeNsCTc1.
    assert (sCTc1GtSPTp2: state c tc1 > state p tp2) by (generalize sCTc1GtNsCTc1 sPTp2LeScTc2 nsCtc2LeNsCTc1; clear; unfold nextState in *; crush).
    clear noCRecvGTTc1'.
    clear sCTc1GtNsCTc1 fstPN sndPN sPTp2LeScTc2 nsCtc2LeNsCTc1.

    assert (tp1LeTp2OrNot: tp1 <= tp2 \/ tp2 < tp1) by (clear; crush).
    destruct tp1LeTp2OrNot as [tp1LeTp2 | tp2LtTp1].
    assert (tc2LtTcmin: S tc2 <= tcmin) by crush.
    pose proof (@maxExistsPower dec (fun t => exists m, recv c m t /\ fst m <= state c t) tcmin (S tc2) tc2LtTcmin exCRecv) as exCRecvMax.
    destruct exCRecvMax as [tc3 [tc2LtTc3LeTcmin [exCRecvTc3 noCRecvGtTc3]]].
    destruct exCRecvTc3 as [n' cRecvTc3Fst].
    generalize cRecvTc3Fst; intro hyp.
    destruct hyp as [cRecvTc3 fstTc3].
    assert (tc2LtTc3: S tc2 <= tc3) by crush.
    assert (exPRecvTp3: exists tp3, tp3 <= tc3 /\ send p n' tp3) by (apply pc.f.deqImpEnq; crush).
    destruct exPRecvTp3 as [tp3 [junk pSendX]].
    clear junk.
    pose proof (pc.fifo2' pSendX cRecvTc3 pSendN cRecvN) as impTp2LeTp3.
    specialize (impTp2LeTp3 tc2LtTc3).
    assert (noRecvPLate: forall y, S tp3 <= y <= tpmin -> forall m, ~ recv p m y) by
      (intros; assert (hyp: S tp1 <= y <= tpmin) by crush; generalize y hyp noRecvGTTp1; clear; firstorder).
    assert (tc3LeTcmin: tc3 <= tcmin) by crush.
    pose proof (childRecvNoParentRecv pRecvCSend cRecvPSend tc3LeTcmin cRecvTc3Fst noCRecvGtTc3 pSendX noRecvPLate).
    crush.

    destruct tp2.
    assert (tc1LeSTc2: tc1 <= S tc2) by crush.
    pose proof (zeroRecvChild pSendN cRecvN tc1LeSTc2) as contra1.
    clear tc1LeSTc2.
    pose proof init.
    crush.

    destruct tc1.
    assert (sTp2LeTp1: S tp2 <= tp1) by crush.
    pose proof (zeroRecvParent sendmCMTc1 recvmPMTp1 sTp2LeTp1) as contra2.
    clear sTp2LeTp1.
    pose proof init.
    crush.

    destruct tp1.
    crush.

    assert (hyp1: forall k t1 t2, recv p k t1 -> send c k t2 -> t1 <= tp2 -> t2 <= tc1) by (
      intros; assert (useful: t1 < S tp1 -> t2 < S tc1) by (apply (@cp.f.fifo2 m (S tc1) (S tp1) sendmCMTc1 recvmPMTp1 k); crush);
          assert (lt: t1 < S tp1) by crush; specialize (useful lt); crush).

    assert (hyp2: forall k t1 t2, recv c k t1 -> send p k t2 -> t1 <= tc1 -> t2 <= tp2) by (
      intros; assert (useful: t1 < S tc2 -> t2 < S tp2) by (apply (@pc.f.fifo2 n (S tp2) (S tc2)pSendN cRecvN k); crush);
        assert (lt: t1 < S tc2) by crush; specialize (useful lt); crush).

    assert (basic: tp2 < tpmin) by crush.

    clear tp1LeTpmin m recvmPMTp1 noRecvGTTp1 tc1LeTp1 sendmCMTc1 tc1LeTcmin tc1LtTc2LeTcmin exCRecv n cRecvN fstN tp2LeTc2 pSendN tc1LeTc2 noCRecv tp2LtTp1.

    clear tp1 tc2.

    assert (exists x y, x < tpmin /\ (forall m t1 t2, recv p m t1 -> send c m t2 -> t1 <= x -> t2 <= y) /\ (forall m t1 t2, recv c m t1 -> send p m t2 -> t1 <= y -> t2 <= x) /\ nextState c y > nextState p x) by (exists tp2; exists tc1; crush).

    crush.
  Qed.

  Theorem conservative'' t:
    ~ (nextState c t > nextState p t).
  Proof.
    apply strongLess.
    intros m t1 t2 recv send le.
    pose proof (cp.f.deqImpEnq recv) as exEnq.
    destruct exEnq as [t' [le2 enq]].
    pose proof (cp.f.uniqueEnq1 send enq) as useful.
    crush.
    intros m t1 t2 recv send le.
    pose proof (pc.f.deqImpEnq recv) as exEnq.
    destruct exEnq as [t' [le2 enq]].
    pose proof (pc.f.uniqueEnq1 send enq).
    crush.
  Qed.

  Theorem conservative' t:
    ~ state c t > state p t.
  Proof.
    destruct t.
    unfold not; pose proof init; crush.
    apply (conservative'' t).
  Qed.

  Theorem conservative t:
    state c t <= state p t.
  Proof.
    pose proof (conservative' t).
    crush.
  Qed.

  About noRecvChild2.

  Lemma noRecvChild3 {ti tf} (le: ti <= tf) (noRecv: forall t, S ti <= t < tf -> forall m, ~ (recv c m t /\ fst m <= state c t)): state c tf <= nextState c ti.
  Proof.
    destruct tf.
    assert (ti0: ti = 0) by crush; rewrite ti0 in *.
    assert (state c 0 > state)

  Lemma cSendNoRecv {m} {t} {n} {t1} {t2} (csendm: send c m t) (psendn: send p n t1) (crecvn: recv c n t2)
    (le: t <= t2) (norecvp: forall t', t' <= t1 -> ~ recv p m t') (fstLe: fst n <= state c t2) : False.
  Proof.
    assert (ex: exists t1 t2 n, send p n t1 /\ recv c n t2 /\ t <= t2 /\ (forall t', t' <= t1 -> ~ recv p m t') /\ fst n <= state c t2) by (exists t1; exists t2; exists n; crush).
    pose proof (minExists dec ex) as minEx.
    clear ex n t1 t2 psendn crecvn le norecvp fstLe.
    destruct minEx as [t1 [[t2 [n [psendn [crecvn [le [norecvp fstLe]]]]]] noExists]].
    assert (noRecv: forall t2', S t <= t2' < t2 -> forall n', ~ (recv c n' t2' /\ fst n' <= state c t2')) by (
      unfold not; intros t2' cond n' [crecvn' fstLeN'];
        destruct (pc.f.deqImpEnq crecvn') as [t1' [_ psendn']];
          assert (lt: t1' < t1) by (apply (pc.f.fifo2 psendn crecvn psendn' crecvn'); crush);
            assert (hyp: forall t', t' <= t1' -> ~ recv p m t') by (generalize norecvp lt; clear; intros; crush; firstorder); firstorder ).
    unfold lt in noRecv.
    assert (exists t2' n', send p n' t1' /\ recv c n' t2' /\ t <= t2' /\ (forall t', t' <= t1' -> ~ recv p m t') /\ fst n' <= state c t2').
    exists t2'; exists n'; crush.
    exists t''; exists q; unfold send in *; crush.
    crush.
    

 by (exists t2; exists n; crush).

  Definition state := state.
  Definition nextState := nextState.
  Definition recv := recv.
  Definition send := send.
End GetResp.
