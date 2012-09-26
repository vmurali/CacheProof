Require Import CpdtTactics.
Load Useful.
Load DataTypes.
Load Fifo.

Module CpRespMesg <: Mesg.
  Definition mesg := (State * State)%type.
End CpRespMesg.

Module CpReqMesg <: Mesg.
  Definition mesg := State.
End CpReqMesg.

Module PcMesg <: Mesg.
  Inductive mesg' : Set :=
  | PcResp: (State * State)%type -> mesg'
  | PcReq: State -> mesg'.
  Definition mesg := mesg'.
End PcMesg.

Module Type RespAxioms (pc: FifoHighLevel PcMesg) (cp: FifoHighLevel CpRespMesg) (cpr: FifoHighLevel CpReqMesg).
  Definition send pt m t :=
    match pt with
      | p => pc.f.enq (PcMesg.PcResp m) t
      | c => cp.f.enq m t
    end.
  
  Definition recv pt m t :=
    match pt with
      | p => cp.f.deq m t
      | c => pc.f.deq (PcMesg.PcResp m) t
    end.

  Definition sendr pt r t :=
    match pt with
      | p => pc.f.enq (PcMesg.PcReq r) t
      | c => cpr.f.enq r t
    end.

  Definition recvr pt r t :=
    match pt with
      | p => cpr.f.deq r t
      | c => pc.f.deq (PcMesg.PcReq r) t
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

  Axiom noSendRecv: forall {pt m n t}, send pt m t -> recv pt n t -> False.

  Parameter wait: Point -> nat -> Prop.
  Definition nextWait pt t := wait pt (S t).

  Parameter waitState: Point -> nat -> State.
  Definition nextWaitState pt t := waitState pt (S t).

  Axiom sendrParentReq: forall {r t}, sendr p r t -> r < state p t.

  Axiom sendrChildReq: forall {r t}, sendr c r t -> r > state c t.

  Axiom sendrWait: forall {pt r t}, sendr pt r t -> ~ wait pt t /\ nextWait pt t /\ nextWaitState pt t = r.

  Axiom waitSendr: forall {pt t}, ~ wait pt t -> nextWait pt t -> exists r, sendr pt r t.

  Axiom waitStateSendr: forall {pt t}, waitState pt t <> nextWaitState pt t -> exists r, sendr pt r t.

  Axiom recvPWait: forall {m t}, recv p m t -> snd m <= waitState p t -> ~ nextWait p t.

  Axiom recvCWait: forall {m t}, recv c m t -> snd m >= waitState c t -> ~ nextWait p t.

  Axiom waitNotWait: forall {pt t}, wait pt t -> ~ nextWait pt t -> exists m, recv pt m t.

  Axiom waitPRecv: forall {t m}, wait p t -> ~ nextWait p t -> recv p m t -> snd m <= waitState p t.

  Axiom waitCRecv: forall {t m}, wait c t -> ~ nextWait c t -> recv c m t -> snd m >= waitState c t.

  Axiom pRecvrSend: forall {r t}, recvr p r t -> r > state p t -> exists m, send p m t /\ snd m >= r.

  Axiom pRecvrNoSend: forall {r t}, recvr p r t -> forall {m}, send p m t -> r > state p t.

  Axiom cRecvrSend: forall {r t}, recvr c r t -> r < state c t -> exists m, send c m t /\ snd m <= r.

  Axiom cRecvrNoSend: forall {r t}, recvr c r t -> forall {m}, send c m t -> r < state c t.

  Axiom pSendRecvr: forall {m t}, send p m t -> exists r, recvr p r t.

  Axiom cSendWaitRecvr: forall {m t}, send c m t -> wait c t -> exists r, recvr c r t.

  Axiom noOvertake: forall {r tr1 tr2 m tm1}, sendr c r tr1 -> recvr p r tr2 -> send c m tm1 -> tm1 < tr1 -> exists tm2, tm2 < tr2 /\ recv p m tm2.

  Axiom noSendrRecv: forall {pt r m t}, sendr pt r t -> recv pt m t -> False.

  Axiom noSendrSend: forall {r m t}, sendr c r t -> send c m t -> False.

  Axiom pRecvrNoWait: forall {r t}, recvr p r t -> ~ wait p t.
End RespAxioms.

Module Type Resp (pc: FifoHighLevel PcMesg) (cp: FifoHighLevel CpRespMesg) (cpr: FifoHighLevel CpReqMesg).

  Parameter state: Point -> nat -> State.
  Parameter nextState: Point -> nat -> State.
  Parameter send: Point -> (State * State)%type -> nat -> Prop.
  Parameter recv: Point -> (State * State)%type -> nat -> Prop.
  Parameter sendr: Point -> State -> nat -> Prop.
  Parameter recvr: Point -> State -> nat -> Prop.

  Axiom conservative: forall t, state c t <= state p t.
  Axiom cRecvCStateLt: forall m t, recv c m t -> fst m <= state c t.
  Axiom pRecvrPStateLt: forall r t, recvr p r t -> r > state p t.
  Axiom cRecvrSend: forall {r t}, recvr c r t -> r < state c t -> exists m, send c m t /\ snd m <= r.
  Axiom cRecvrAlreadySent: forall r tc tp, recvr c r tc -> sendr p r tp -> r >= state c tc ->
    exists t, t < tc /\ exists m, send c m t /\ snd m = state c tc /\ forall t', t' < tp -> ~ recv p m t'.
  Axiom pRecvrAlwaysSend: forall r t, recvr p r t -> exists m, send p m t /\ snd m >= r.
End Resp.

Module GetResp (pc: FifoHighLevel PcMesg) (cp: FifoHighLevel CpRespMesg) (cpr: FifoHighLevel CpReqMesg) (axioms: RespAxioms pc cp cpr) : Resp pc cp cpr.
  Import Classical.
  Import axioms.
  Import PcMesg.
  Import CpRespMesg.
  Import CpReqMesg.
  Import Datatypes.

  Section noRecvParent.
    Context {ti : nat}.

    Lemma noSendRecvParentNow {t} (noSend: forall m, ~ recv p m t) (noRecv: forall m, ~ send p m t): nextState p t = state p t.
    Proof.
      assert (eqOrNot: state p t = nextState p t \/ state p t <> nextState p t) by decide equality.
      destruct eqOrNot as [eq|notEq].
      crush.
      pose proof (stateChange notEq) as [m sendRecv].
      destruct sendRecv as [send|recv]; firstorder.
    Qed.

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

    Lemma noRecvParent' {td} (noRecv : forall t, ti <= t < ti + td -> forall m, ~ recv p m t):
      state p (ti + td) >= state p ti.
    Proof.
      induction td.
      assert (ti + 0 = ti) by crush; crush.
      assert (indNoRecv: forall t, ti <= t < ti + td -> forall m, ~ recv p m t) by (
      intros t cond; assert (ti <= t < ti + S td) by crush; firstorder).
      specialize (IHtd indNoRecv); clear indNoRecv.
      assert (hyp: ti <= ti + td < ti + S td) by crush.
      assert (ge: nextState p (ti + td) >= state p (ti + td)) by (apply (@noRecvParentNow (ti + td)); firstorder); unfold nextState in ge.
      assert (eq: state p (S (ti + td)) = state p (ti + S td)) by crush.
      crush.
    Qed.

    Lemma noRecvParent0 {tf} (tiLeTf: ti <= tf) (noRecv: forall t, ti <= t < tf -> forall m, ~ recv p m t): state p tf >= state p ti.
      pose proof (@noRecvParent' (tf - ti)) as noRecvParentInst.
      assert (rew: ti + (tf - ti) = tf) by crush.
      rewrite rew in noRecvParentInst.
      firstorder.
    Qed.

    Lemma noRecvParent1 {tf} (tiLeTf: ti <= tf) (noRecv: forall t, ti <= t <= tf -> forall m, ~ recv p m t): nextState p tf >= state p ti.
    Proof.
      pose proof (@noRecvParent0 (S tf)) as init.
      assert (hyp1: ti < S tf) by crush.
      assert (hyp2: forall t, ti <= t < S tf -> forall m, ~ recv p m t) by
        (intros t cond; assert (h: ti <= t <= tf) by crush; specialize (noRecv t h); crush).
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

    Lemma noSendRecvChildNow {t} (noSend: forall m, ~ send c m t) (noRecv: forall m, ~ (recv c m t /\ fst m <= state c t)): nextState c t = state c t.
    Proof.
      assert (eqOrNot: state c t = nextState c t \/ state c t <> nextState c t) by decide equality.
      destruct eqOrNot as [eq|notEq].
      crush.
      pose proof (stateChange notEq) as [m sendRecv].
      destruct sendRecv as [send|recv].
      firstorder.
      assert (h: ~ (fst m <= state c t)) by firstorder.
      assert (gt: fst m > state c t) by crush; clear h.
      apply (@recvChildNoChange m); crush.
    Qed.

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

    Lemma noRecvChild' {td} (noRecv: forall t, ti <= t < ti + td -> forall m, ~ (recv c m t /\ fst m <= state c t)):
      state c (ti + td) <= state c ti.
    Proof.
      induction td.
      assert (ti + 0 = ti) by crush; crush.
      assert (indNoRecv: forall t, ti <= t < ti + td -> forall m, ~ (recv c m t /\ fst m <= state c t)) by (
      intros t cond; assert (ti <= t < ti + S td) by crush; firstorder).
      specialize (IHtd indNoRecv); clear indNoRecv.
      assert (hyp: ti <= ti + td < ti + S td) by crush.
      assert (ge: nextState c (ti + td) <= state c (ti + td)) by (apply (@noRecvChildNow (ti + td)); firstorder); unfold nextState in ge.
      assert (eq: state c (S (ti + td)) = state c (ti + S td)) by crush.
      crush.
    Qed.

    Lemma noRecvChild0 {tf} (tiLeTf: ti <= tf) (noRecv: forall t, ti <= t < tf -> forall m, ~ (recv c m t /\ fst m <= state c t)): state c tf <= state c ti.
      pose proof (@noRecvChild' (tf - ti)) as noRecvChildInst.
      assert (rew: ti + (tf - ti) = tf) by crush.
      rewrite rew in noRecvChildInst.
      firstorder.
    Qed.

    Lemma noRecvChild1 {tf} (tiLeTf: ti <= tf) (noRecv: forall t, ti <= t <= tf -> forall m, ~ (recv c m t /\ fst m <= state c t)): nextState c tf <= state c ti.
    Proof.
      pose proof (@noRecvChild0 (S tf)) as init.
      assert (hyp1: ti < S tf) by crush.
      assert (hyp2: forall t, ti <= t < S tf -> forall m, ~ (recv c m t /\ fst m <= state c t)) by
        (intros t cond; assert (h: ti <= t <= tf) by crush; specialize (noRecv t h); crush).
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
      intros k t1 t2 recvk sendk le; assert (useful: t1 < S tp1 -> t2 < S tc1) by (apply (cp.fifo2 sendmCMTc1 recvmPMTp1 sendk recvk); crush);
          assert (lt: t1 < S tp1) by crush; specialize (useful lt); crush).

    assert (hyp2: forall k t1 t2, recv c k t1 -> send p k t2 -> t1 <= tc1 -> t2 <= tp2) by (
      intros k t1 t2 recvk sendk le; assert (useful: t1 < S tc2 -> t2 < S tp2) by (apply (pc.fifo2 pSendN cRecvN sendk recvk); crush);
        assert (lt: t1 < S tc2) by crush; specialize (useful lt); crush).

    assert (basic: tp2 < tpmin) by crush.

    clear tp1LeTpmin m recvmPMTp1 noRecvGTTp1 tc1LeTp1 sendmCMTc1 tc1LeTcmin tc1LtTc2LeTcmin exCRecv n cRecvN fstN tp2LeTc2 pSendN tc1LeTc2 noCRecv tp2LtTp1.

    clear tp1 tc2.

    assert (exists x y, x < tpmin /\ (forall m t1 t2, recv p m t1 -> send c m t2 -> t1 <= x -> t2 <= y) /\ (forall m t1 t2, recv c m t1 -> send p m t2 -> t1 <= y -> t2 <= x) /\ nextState c y > nextState p x) by (exists tp2; exists tc1; crush).

    crush.
  Qed.

  Theorem strongLess':
    forall tp tc,
      (forall m t1 t2, recv p m t1 -> send c m t2 -> t1 < tp -> t2 < tc) ->
      (forall m t1 t2, recv c m t1 -> send p m t2 -> t1 < tc -> t2 < tp) ->
      ~ (state c tc > state p tp).
  Proof.
    unfold not.
    intros tp tc hyp1 hyp2 contra.
    destruct tc.
    destruct tp.
    pose proof init; crush.
    destruct (dec (exists m t1, t1 < S tp /\ recv p m t1)) as [ex|notEx].
    destruct ex as [m [t1 [lt recvm]]].
    pose proof (cp.f.deqImpEnq recvm) as sendm.
    destruct sendm as [t2 [le sendm]].
    specialize (hyp1 m t1 t2 recvm sendm lt).
    crush.
    assert (noRecv: forall t1, 0 <= t1 < S tp -> forall m, ~ recv p m t1) by (generalize notEx; clear; intros; assert (t1 < S tp) by crush; firstorder).
    assert (zl: 0 <= S tp) by crush.
    pose proof (noRecvParent0 zl noRecv) as contra2.
    rewrite init in contra2.
    crush.
    destruct tp.
    destruct (dec (exists m t1, t1 < S tc /\ (recv c m t1 /\ fst m <= state c t1))) as [ex|notEx].
    destruct ex as [m [t1 [lt [recvm _]]]].
    pose proof (pc.f.deqImpEnq recvm) as sendm.
    destruct sendm as [t2 [le sendm]].
    specialize (hyp2 m t1 t2 recvm sendm lt).
    crush.
    assert (noRecv: forall t1, 0 <= t1 < S tc -> forall m, ~ (recv c m t1 /\ fst m <= state c t1)) by
      (generalize notEx; clear; intros; assert (t1 < S tc) by crush; firstorder).
    assert (zl: 0 <= S tc) by crush.
    pose proof (noRecvChild0 zl noRecv) as contra2.
    rewrite <- init in contra2.
    crush.
    assert (hyp1': forall m t1 t2, recv p m t1 -> send c m t2 -> t1 <= tp -> t2 <= tc) by (generalize hyp1; clear; intros; assert (t1 < S tp) by crush; assert (t2 < S tc) by firstorder; crush).
    assert (hyp2': forall m t1 t2, recv c m t1 -> send p m t2 -> t1 <= tc -> t2 <= tp) by (generalize hyp2; clear; intros; assert (t1 < S tc) by crush; assert (t2 < S tp) by firstorder; crush).
    pose proof (strongLess tp tc hyp1' hyp2') as final; unfold nextState in final; crush.
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


  Lemma noRecvSendChild' {ti td} (noSendRecv: forall t, t < td -> (forall m, ~ send c m (ti + t)) /\ (forall m, ~ (recv c m (ti + t) /\ fst m <= state c (ti + t)))): state c (ti + td) = state c ti.
  Proof.
    induction td.
    assert (ti + 0 = ti); crush.
    assert (hyp: forall t, t < td -> (forall m, ~ send c m (ti + t)) /\ (forall m, ~ (recv c m (ti + t) /\ fst m <= state c (ti + t)))) by (intros t lt; assert (t < S td) by crush; apply noSendRecv; crush).
    specialize (IHtd hyp); clear hyp.
    assert (now: (forall m, ~ send c m (ti + td)) /\ forall m, ~ (recv c m (ti + td) /\ fst m <= state c (ti + td))) by (assert (td < S td) by crush; firstorder).
    pose proof (@noSendRecvChildNow) as noNow.
    assert (eq: nextState c (ti + td) = state c (ti + td)) by firstorder.
    assert (nextState c (ti + td) = state c (ti + S td)) by (unfold nextState; crush).
    crush.
  Qed.

  Lemma noRecvSendChild {ti tf} (le: ti <= tf) (noSendRecv: forall t, ti <= t < tf -> (forall m, ~ send c m t) /\ (forall m, ~ (recv c m t /\ fst m <= state c t))): state c tf = state c ti.
    assert (hyp: forall t, t < tf - ti -> ((forall m, ~ send c m (ti + t)) /\ forall m, ~ (recv c m (ti + t) /\ fst m <= state c (ti + t)))) by (
      intros t lt;
        remember (t + ti) as t';
          assert (eq: t' - ti = t) by crush;
            rewrite <- eq;
              assert (eq': ti + (t' - ti) = t') by crush;
                rewrite eq' in *;
                  clear eq';
                    assert (hyp:  ti <= t' < tf) by crush;
                      firstorder;
                        crush).
    pose proof (noRecvSendChild' hyp) as final.
    assert (eq: ti + (tf - ti) = tf) by crush.
    crush.
  Qed.

  Lemma noRecvSendParent' {ti td} (noSendRecv: forall t, t < td -> (forall m, ~ send p m (ti + t)) /\ (forall m, ~ recv p m (ti + t))): state p (ti + td) = state p ti.
  Proof.
    induction td.
    assert (ti + 0 = ti); crush.
    assert (hyp: forall t, t < td -> (forall m, ~ send p m (ti + t)) /\ (forall m, ~ recv p m (ti + t))) by (intros t lt; assert (t < S td) by crush; apply noSendRecv; crush).
    specialize (IHtd hyp); clear hyp.
    assert (now: (forall m, ~ send p m (ti + td)) /\ forall m, ~ recv p m (ti + td)) by (assert (td < S td) by crush; firstorder).
    pose proof (@noSendRecvParentNow) as noNow.
    assert (eq: nextState p (ti + td) = state p (ti + td)) by firstorder.
    assert (nextState p (ti + td) = state p (ti + S td)) by (unfold nextState; crush).
    crush.
  Qed.

  Lemma noRecvSendParent {ti tf} (le: ti <= tf) (noSendRecv: forall t, ti <= t < tf -> (forall m, ~ send p m t) /\ (forall m, ~ recv p m t)): state p tf = state p ti.
    assert (hyp: forall t, t < tf - ti -> ((forall m, ~ send p m (ti + t)) /\ forall m, ~ recv p m (ti + t))) by (
      intros t lt;
        remember (t + ti) as t';
          assert (eq: t' - ti = t) by crush;
            rewrite <- eq;
              assert (eq': ti + (t' - ti) = t') by crush;
                rewrite eq' in *;
                  clear eq';
                    assert (hyp:  ti <= t' < tf) by crush;
                      firstorder;
                        crush).
    pose proof (noRecvSendParent' hyp) as final.
    assert (eq: ti + (tf - ti) = tf) by crush.
    crush.
  Qed.


  Lemma cRecvIntersect {m} {t} {n} {t1} {t2} (csendm: send c m t) (psendn: send p n t1) (crecvn: recv c n t2)
    (le: t <= t2) (norecvp: forall t', t' <= t1 -> ~ recv p m t') (fstLe: fst n <= state c t2) : False.
  Proof.
    assert (ex: exists t1 t2 n, send p n t1 /\ recv c n t2 /\ t <= t2 /\ (forall t', t' <= t1 -> ~ recv p m t') /\ fst n <= state c t2) by (exists t1; exists t2; exists n; crush).
    pose proof (minExists dec ex) as minEx.
    clear ex n t1 t2 psendn crecvn le norecvp fstLe.
    destruct minEx as [t1 [[t2 [n [psendn [crecvn [le [norecvp fstLe]]]]]] noExists]].
    assert (noRecv: forall t2', S t <= t2' < t2 -> forall n', ~ (recv c n' t2' /\ fst n' <= state c t2')) by (
      unfold not; intros t2' cond n' [crecvn' fstLeN'];
        destruct (pc.f.deqImpEnq crecvn') as [t1' [_ psendn']];
          assert (lt: t1' < t1) by (apply (pc.fifo2 psendn crecvn psendn' crecvn'); crush);
            assert (hyp: forall t', t' <= t1' -> ~ recv p m t') by (generalize norecvp lt; clear; intros; crush; firstorder); firstorder ).
    assert (eqOrNot: t = t2 \/ t <> t2) by decide equality.
    destruct eqOrNot as [eq|notEq].
    rewrite <- eq in crecvn; pose proof (noSendRecv csendm crecvn); crush.
    assert (StLeT2: S t <= t2) by crush.
    assert (stateLe: state c t2 <= state c (S t)) by (apply noRecvChild0; crush).
    assert (pState: state p t1 = fst n) by (pose proof (sendCommon psendn); crush).
    assert (cState: state c t > state c (S t)) by (
      pose proof (sendChild csendm); pose proof (sendCommon csendm); unfold nextState in *; crush).
    assert (contra: state c t > state p t1) by crush.
    assert (hyp1: forall m tr ts, recv c m tr -> send p m ts -> tr < t -> ts < t1) by (
      intros m' tr ts Recv Send le'; pose proof (pc.fifo2 psendn crecvn Send Recv); assert (tr < t2) by crush; firstorder). 
    assert (hyp2: forall m tr ts, recv p m tr -> send c m ts -> tr < t1 -> ts < t) by (
      intros m' tr ts Recv Send le';
        assert (unique: ts = t -> m' = m) by (apply cp.f.uniqueEnq2; crush);
          assert (m'EqM: m' = m -> recv p m tr) by crush;
            assert (tsEqt: ts = t -> recv p m tr) by crush; clear unique m'EqM;
              assert (trLeT1: tr <= t1) by crush;
                pose proof (norecvp tr trLeT1) as norecvp2; clear trLeT1;
                  assert (rew1: (~ t <= ts) -> ts < t) by crush;
                    apply rew1; unfold not; intro tLeTs; clear rew1;
                      assert (eqOrNot: ts = t \/ ts <> t) by decide equality;
                        destruct eqOrNot as [eq|notEq']; [
                          apply (norecvp2 (tsEqt eq)) |
                            assert (lt: t < ts) by crush;
                              pose proof (cp.f.fifo Send Recv csendm lt) as fifo;
                                destruct fifo as [td' [precvm cond]]; assert (cond2: td' <= t1) by crush;
                                  specialize (norecvp td' cond2 precvm); crush]).
    apply (strongLess' t1 t hyp2 hyp1 contra).
  Qed.

  Lemma cRecvNoIntersect {m} {ts} {tr} (psendm: send p m ts) (crecvm: recv c m tr) (crecvall: forall t, t < tr -> forall n, send c n t -> exists t', t' < ts /\ recv p n t') (contra: fst m > state c tr) : False.
  Proof.
    assert (overall: exists ts tr m, send p m ts /\ recv c m tr /\ fst m > state c tr /\ forall t, t < tr -> forall n, send c n t -> exists t', t' < ts /\ recv p n t') by (exists ts; exists tr; exists m; crush).
    clear m ts tr psendm crecvm crecvall contra.
    pose proof (minExists dec overall) as [ts [[tr [m [psendm [crecvm [contra crecvall]]]]] max]].
    clear overall.
    assert (contra': state p ts > state c tr) by (pose proof sendCommon psendm; crush).
    destruct (dec (~ (exists t, t < ts /\ ((exists m, send p m t) \/ exists m, recv p m t)))) as [nothing|something].
    assert (noSend: forall t, t < ts -> forall m, ~ send p m t) by (clear max; firstorder).
    assert (noRecv: forall t, t < ts -> forall m, ~ recv p m t) by (clear max; firstorder).
    clear nothing.
    assert (forNone: forall t, 0 <= t < ts -> (forall m, ~ send p m t) /\ (forall m, ~ recv p m t)) by (intros t cond; assert (t < ts) by crush; firstorder).
    assert (l1: 0 <= ts) by crush.
    pose proof (noRecvSendParent l1 forNone) as sameState; clear forNone l1.
    assert (cNoRecv: forall t, t < tr -> forall m, ~ (recv c m t /\ fst m <= state c t)) by (
      unfold not;
        intros t cond n [recvn _];
          destruct (pc.f.deqImpEnq recvn) as [t' [_ sendn]];
            pose proof (pc.fifo2 psendm crecvm sendn recvn cond) as lt;
              firstorder;
                pose proof @pc.fifo2).
    assert (cNoSend: forall t, t < tr -> forall m, ~ send c m t) by (
      unfold not; intros t cond n sendn;
        destruct (crecvall t cond n sendn) as [t' [cond2 recvn]];
          generalize cond2 recvn sendn cond noRecv; clear; firstorder).
    assert (forNone: forall t, 0 <= t < tr -> (forall m, ~ send c m t) /\ forall m, ~ (recv c m t /\ fst m <= state c t)) by (intros t cond; assert (hyp: t < tr) by crush; generalize hyp cNoRecv cNoSend; clear; firstorder).
    assert (l1: 0 <= tr) by crush.
    pose proof (noRecvSendChild l1 forNone) as sameState'; clear forNone l1 cNoRecv cNoSend noSend noRecv.
    pose proof init as init.
    crush.
    assert (exi: (exists t, t < ts /\ (exists m, send p m t \/ recv p m t))) by (pose proof (dec ((exists t, t < ts /\ (exists m, send p m t \/ recv p m t)))) as stuff; generalize stuff something; clear; firstorder); clear something.
    pose proof (maxExists' dec exi) as maxExi; clear exi.
    destruct maxExi as [t [cond [[n sendOrRecv] noMore]]].
    assert (noMore': forall y, t < y < ts -> (forall m, ~ send p m y) /\ forall m, ~ recv p m y) by (generalize noMore; clear; firstorder).
    clear noMore.
    destruct sendOrRecv as [sendn | recvn].
    pose proof (pc.f.fifo psendm crecvm sendn cond) as [t' [recvn cond2]].
    assert (noCRecv: forall y, t' < y < tr -> forall m, ~ recv c m y) by (
      unfold not; intros y cond3 m' recvm';
        destruct cond3 as [cond4 cond5];
          destruct (pc.f.deqImpEnq recvm') as [t'' [_ sendm']];
            pose proof (pc.fifo2 sendm' recvm' sendn recvn cond4) as cond6;
              pose proof (pc.fifo2 psendm crecvm sendm' recvm' cond5) as cond7;
                generalize noMore' cond6 cond7 sendm'; clear; firstorder).
    assert (noCSend: forall y, t' < y < tr -> (forall m, ~ send c m y)) by (
      unfold not; intros y [cond3 cond4] m' sendm';
        destruct (crecvall y cond4 m' sendm') as [t'' [cond5 recvm']];
          pose proof (cp.deqEnqLess sendm' recvm') as yLeT'';
            pose proof (pc.deqEnqLess sendn recvn) as tLeT';
              assert (tLtT': t < t'') by crush;
                generalize noMore' tLtT' cond5 recvm'; clear; firstorder).
    assert (noMore: forall y, S t <= y < ts -> (forall m, ~ send p m y) /\ forall m, ~ recv p m y). (intros y cond3; assert (hyp: t < y < ts) by crush; generalize noMore' hyp; clear; firstorder).
    clear noMore'.
    assert (noCMore: forall y, S t' <= y < tr -> (forall m, ~ send c m y) /\ (forall m, ~ (recv c m y /\ fst m <= state c y))) by (intros y cond3; assert (hyp: t' < y < tr) by crush; generalize noCRecv noCSend hyp; clear; firstorder).
    assert (cond1: S t <= ts) by crush; clear cond.
    assert (cond: S t' <= tr) by crush; clear cond2.
    pose proof (noRecvSendChild cond noCMore) as cEq.
    pose proof (noRecvSendParent cond1 noMore) as pEq.
    pose proof (sendCommon sendn) as [fstn sndn]; unfold nextState in *.
    destruct (dec (fst n <= state c t')) as [chang|noChange].
    pose proof (recvChildChange recvn chang) as more; unfold nextState in *.
    assert (contraF: state c tr = state p ts) by crush.
    crush.
    assert (contraF: fst n > state c t') by crush.
    assert (tLtTs: t < ts) by crush.
    assert (final: forall y, y < t' -> forall n', send c n' y -> exists y', y' < t /\ recv p n' y') by (
      intros y cond2 n' sendn';
        assert (cond3: y < tr) by crush;
          pose proof (crecvall y cond3 n' sendn') as [y' [y'LtTs recvn']];
            assert (noRecv: forall k, t < k < ts -> forall m, ~ recv p m k) by (intros k cond4; assert (hyp: S t <= k < ts) by crush; generalize hyp noMore; clear; firstorder);
              assert (y'Range: ~ (t < y' < ts)) by (generalize recvn' noRecv; clear; firstorder);
                assert (y'LeT: y' <= t) by (generalize y'LtTs y'Range; clear; crush);
                  assert (hyp: y' = t \/ y' <> t) by decide equality;
                    destruct hyp as [eq|notEq]; [
                      rewrite eq in *;
                        pose proof (noSendRecv sendn recvn'); crush|
                          assert (lt: y' < t) by crush;
                            exists y'; crush]).
    generalize max tLtTs sendn recvn contraF final; clear; firstorder.
    pose proof (cp.f.deqImpEnq recvn) as [t' [_ sendn]].
    assert (noCSend: forall y, t' < y < tr -> forall m, ~ send c m y) by (
      unfold not; intros y [cond3 cond4] n' sendn';
        pose proof (crecvall y cond4 n' sendn') as [y' [lt recvn']];
          pose proof (cp.fifo1 sendn' recvn' sendn recvn cond3) as tLtY';
            generalize noMore' lt tLtY' recvn'; clear; firstorder;
              pose proof (cp.deqEnqLess sendn recvn) as less;
                assert (cond3: y < tr) by crush).
    assert (noCRecv: forall y, t' < y < tr -> forall m, ~ (recv c m y /\ fst m <= state c y)).
    unfold not; intros y [cond1 cond2] n' [recvn' fstn'].
    pose proof (pc.f.deqImpEnq recvn') as [y' [_ sendn']].
    pose proof (pc.fifo2 psendm crecvm sendn' recvn' cond2) as y'LtTs.
    assert (noBad: ~ (t < y' < ts)) by (generalize noMore' sendn'; clear; firstorder).
    assert (y'LeT: y' <= t) by crush; clear y'LtTs noBad.
    assert (eqOrNot: y' = t \/ y' <> t) by decide equality.
    destruct eqOrNot as [eq|not].
    rewrite eq in sendn'.
    apply (@noSendRecv p n' n t); crush.
    assert (y'LtT: y' < t) by crush.
    clear not y'LeT.
    assert (sth: forall t', t' <= y' -> ~ recv p n t') by (
    unfold not; intros x ctra recvx; assert (nEq: n = n) by crush; assert (xEqT: x = t) by (apply (cp.f.uniqueDeq1 recvx recvn nEq)); rewrite xEqT in *; generalize y'LtT ctra; clear; crush).
    assert (t'LeY: t' <= y) by crush.
    apply (cRecvIntersect sendn sendn' recvn' t'LeY sth fstn').
    assert (noCMore: forall y, S t' <= y < tr -> (forall m, ~ send c m y) /\ forall m, ~ (recv c m y /\ fst m <= state c y)) by (intros y cond'; assert(hyp: t' < y < tr) by crush; generalize hyp noCSend noCRecv; clear; firstorder).
    clear noCSend noCRecv.
    pose proof (cp.deqEnqLess sendn recvn) as t'LeT.
    pose proof (pc.deqEnqLess psendm crecvm) as tsLeTr.
    assert (t'LtTr: S t' <= tr) by crush.
    assert (tLeTs: S t <= ts) by crush.
    assert (final: forall y, S t <= y < ts -> (forall m, ~ send p m y) /\ forall m, ~ recv p m y) by (intros y c'; assert (hyp: t < y < ts) by crush; generalize hyp noMore'; clear; firstorder).
    pose proof (noRecvSendChild t'LtTr noCMore) as cSame.
    pose proof (noRecvSendParent tLeTs final) as pSame.
    pose proof (@sendCommon c n t' sendn) as [fst snd].
    pose proof (recvParent recvn) as snd'.
    assert (hyp: nextState c t' = nextState p t) by crush.
    unfold nextState in hyp.
    assert (state c tr = state p ts) by crush.
    crush.
  Qed.

  Lemma noPendingEqual {tp tc}
    (hyp1: forall m t1 t2, recv p m t1 -> send c m t2 -> t1 < tp -> t2 < tc)
    (hyp2: forall m t1 t2, recv c m t1 -> send p m t2 -> t1 < tc -> t2 < tp)
    (psendRecv: forall m t1, send p m t1 -> t1 < tp -> exists t2, t2 < tc /\ recv c m t2)
    (csendRecv: forall m t1, send c m t1 -> t1 < tc -> exists t2, t2 < tp /\ recv p m t2):
    state c tc = state p tp.
  Proof.
    destruct (dec (exists t, S t <= tp /\ ((exists m, send p m t) \/ (exists m, recv p m t)))) as [something|nothing].
    destruct (maxExists' dec something) as [t [tLtTp_ [sendOrRecv nothingLater]]]; clear something.
    assert (tLtTp: S t <= tp) by crush; clear tLtTp_.
    assert (noSendRecvLater: forall y, S t <= y < tp -> (forall m, ~ send p m y) /\ forall m, ~ recv p m y) by (generalize nothingLater; clear; firstorder); clear nothingLater.
    destruct sendOrRecv as [[m sendm]|[m recvm]].
    destruct (psendRecv m t sendm tLtTp) as [t' [t'LtTc_ recvm]].
    assert (t'LtTc: S t' <= tc) by crush; clear t'LtTc_.
    assert (cnorecv: forall y, S t' <= y < tc -> forall m, ~ recv c m y) by (
      unfold not; intros y [cond1 cond2] n recvn;
        destruct (pc.f.deqImpEnq recvn) as [y' [_ sendn]];
          pose proof (hyp2 n y y' recvn sendn cond2) as y'LtTp;
            pose proof (pc.fifo2 sendn recvn sendm recvm cond1) as tLty';
              generalize y'LtTp tLty' sendn noSendRecvLater; clear; firstorder;
                destruct something as [t [tLtTp sendOrRecv]]).
    assert (cnosend: forall y, S t' <= y < tc -> forall m, ~ send c m y) by (
      unfold not; intros y [cond1 cond2 n sendn];
        pose proof (csendRecv n y sendn cond2) as [y' [y'LtTp recvn]];
          pose proof (pc.deqEnqLess sendm recvm) as tLeT';
            pose proof (cp.deqEnqLess sendn recvn) as yLeY';
              assert (tLtY': t < y') by crush;
                generalize noSendRecvLater tLtY' y'LtTp recvn; clear; firstorder).
    assert (nocross: forall ts, ts < t' -> forall m, send c m ts -> exists tr, tr < t /\ recv p m tr) by (
      intros ts cond n sendn;
        assert (cond1: ts < tc) by crush;
          destruct (csendRecv n ts sendn cond1) as [tr [cond2 recvn]]; clear cond1;
            assert (tGeTr: ~ t < tr) by (generalize noSendRecvLater recvn cond2; clear; firstorder);
              assert (eqOrNot: t = tr \/ t <> tr) by decide equality;
                destruct eqOrNot as [eq|notEq]; [
                  rewrite <- eq in recvn;
                    pose proof (noSendRecv sendm recvn); crush|
                      assert (trLtT: tr < t) by crush;
                        exists tr; crush]).
    pose proof (cRecvNoIntersect sendm recvm nocross) as fstM'; clear nocross.
    assert (fstM: fst m <= state c t') by (apply (Compare_dec.not_gt (fst m) (state c t') fstM')); clear fstM'.
    pose proof (recvChildChange recvm fstM) as nextC.
    pose proof (sendCommon sendm) as [_ nextP].
    assert (noSendRecvC: forall y, S t' <= y < tc -> (forall m, ~ send c m y) /\ (forall m, ~ (recv c m y /\ fst m <= state c y))) by (generalize cnorecv cnosend; clear; firstorder).
    pose proof (noRecvSendParent tLtTp noSendRecvLater) as eqP.
    pose proof (noRecvSendChild t'LtTc noSendRecvC) as eqC.
    unfold axioms.nextState in *.
    crush.
    pose proof (cp.f.deqImpEnq recvm) as [t' [_ sendm]].
    assert (nocsend: forall y, S t' <= y < tc -> forall m, ~ send c m y) by (
      unfold not; intros y [cond1 cond2] n sendn;
        pose proof (csendRecv n y sendn cond2) as [y' [cond3 recvn]];
          pose proof (cp.fifo1 sendn recvn sendm recvm cond1) as cond4;
            generalize noSendRecvLater recvn cond3 cond4; clear; firstorder).
    assert (nocrecv: forall y, S t' <= y < tc -> forall m, ~ (recv c m y /\ fst m <= state c y)) by (
      unfold not; intros y [cond1 cond2] n [recvn fstn];
        pose proof (pc.f.deqImpEnq recvn) as [y' [_ sendn]];
          pose proof (hyp2 n y y' recvn sendn cond2) as cond3;
            assert (cond4': ~ S t <= y') by (generalize noSendRecvLater cond3 sendn; clear; firstorder);
              assert (cond4'': y' <= t) by crush; clear cond4';
                assert (eqOrNot: y' = t \/ y' <> t) by decide equality;
                  destruct eqOrNot as [eq|notEq]; [
                    rewrite eq in sendn;
                      apply (@noSendRecv p n m t sendn recvm) |
                        assert (cond4: y' < t) by crush; clear cond3 cond4'' notEq;
                          pose proof @cRecvIntersect;
                            assert (tempCond: t' <= y) by crush;
                              assert (noRecvBefore: forall k, k <= y' -> ~ recv p m k) by (
                                unfold not; intros k cond5 recvk;
                                  assert (mEq: m = m) by crush;
                                    pose proof (cp.f.uniqueDeq1 recvm recvk mEq) as rew;
                                      rewrite <- rew in cond5; crush);
                              apply (cRecvIntersect sendm sendn recvn tempCond noRecvBefore fstn)]).
    pose proof (hyp1 m t t' recvm sendm tLtTp) as t'LtTc_.
    assert (t'LtTc: S t' <= tc) by crush; clear t'LtTc_.
    assert (noSendRecv: forall y, S t' <= y < tc -> (forall m, ~ send c m y) /\ forall m, ~ (recv c m y /\ fst m <= state c y)) by (generalize nocsend nocrecv; clear; firstorder).
    pose proof (noRecvSendParent tLtTp noSendRecvLater) as ceq.
    pose proof (noRecvSendChild t'LtTc noSendRecv) as peq.
    pose proof (@sendCommon c m t' sendm) as [_ ct'].
    pose proof (recvParent recvm) as pt.
    unfold axioms.nextState in *.
    crush.
    assert (nop: forall t, 0 <= t < tp -> (forall m, ~ send p m t) /\ forall m, ~ recv p m t) by (
      intros t cond; assert (cond2: S t <= tp) by crush; firstorder).
    clear nothing.
    assert (p0: 0 <= tp) by crush.
    assert (nop1: forall t, t < tp -> (forall m, ~ send p m t) /\ forall m, ~ recv p m t) by (intros y cond2; assert (cond3: 0 <= y < tp) by crush; generalize cond3 nop; clear; firstorder).
    assert (cnorecv: forall t, 0 <= t < tc -> forall m, ~ send c m t) by (
      unfold not; intros t [_ cond] m sendm;
        pose proof (csendRecv m t sendm cond) as [t' [cond1 recvm]];
          generalize nop1 recvm cond1; clear; firstorder).
    assert (cnosend: forall t, 0 <= t < tc -> forall m, ~ recv c m t) by (
      unfold not; intros t [_ cond] m recvm;
        pose proof (pc.f.deqImpEnq recvm) as [t' [_ sendm]];
          pose proof (hyp2 m t t' recvm sendm cond) as cond2;
            generalize nop1 cond2 sendm; clear; firstorder).
    assert (noc: forall t, 0 <= t < tc -> (forall m, ~ send c m t) /\ forall m, ~ (recv c m t /\ fst m <= state c t)) by (generalize cnorecv cnosend; clear; firstorder).
    assert (c0: 0 <= tc) by crush.
    pose proof (noRecvSendParent p0 nop) as peq.
    pose proof (noRecvSendChild c0 noc) as ceq.
    pose proof init as init.
    crush.
  Qed.

  Theorem creqLemma' {tp} {tc}
    (hyp2: forall m t1 t2, recv c m t1 -> send p m t2 -> t1 < tc -> t2 < tp)
    (psendRecv: forall m t1, send p m t1 -> t1 < tp -> exists t2, t2 < tc /\ recv c m t2)
    (csendRecv: forall m t1, send c m t1 -> t1 < tc -> exists t2, t2 < tp /\ recv p m t2):
    state p tp <= state c tc.
  Proof.
    assert (maxtc: exists tc', tc' <= tp /\ (forall m t1, send c m t1 -> t1 < tc' -> exists t2, t2 < tp /\ recv p m t2) /\ forall m t1 t2, recv p m t1 -> send c m t2 -> t1 < tp -> t2 < tc') by (
      destruct (dec (exists t, t < tp /\ exists m, recv p m t)) as [recvm' | norecvm]; [
        pose proof (maxExists' dec recvm') as [t [tLtTp [[m recvm] norecvlater]]]; clear recvm';
          pose proof (cp.f.deqImpEnq recvm) as [t' [t'LeT sendm]];
            exists (S t');
              constructor; [
                crush |
                  constructor; [
                    intros n t1 sendn cond;
                      assert (eqOrNot: t1 = t' \/ t1 <> t') by decide equality;
                        destruct eqOrNot as [eq | notEq]; [
                          pose proof (cp.f.uniqueEnq2 sendn sendm eq) as nEqM;
                            rewrite nEqM;
                              exists t; crush |
                                assert (t1LtT': t1 < t') by crush; clear cond notEq;
                                  pose proof (cp.f.fifo sendm recvm sendn t1LtT') as [t2 [recvn cond]];
                                    assert (t2LtTp: t2 < tp) by crush; firstorder] |
                        intros n t1 t2 recvn sendn cond1;
                          assert (t2LeT': t2 > t' -> False) by (
                            intros cond2;
                              pose proof (cp.fifo1 sendn recvn sendm recvm cond2) as tLtT1;
                                generalize norecvlater tLtT1 cond1 recvn; clear; firstorder;
                                  clear recvm'); crush]] |
              exists 0;
                constructor; [
                  crush |
                    constructor;
                      intros m' t1 contra; crush;
                        firstorder]]).
    destruct maxtc as [tc' [tc'LeTp [csendRecv' hyp1']]].
    assert (leOrLt: tc' <= tc \/ tc < tc') by (pose proof (Compare_dec.le_lt_dec tc' tc); crush).
    destruct leOrLt as [le|lt].
    assert (hyp1: forall m t1 t2, recv p m t1 -> send c m t2 -> t1 < tp -> t2 < tc) by (intros m t1 t2 recvm sendm cond; specialize (hyp1' m t1 t2 recvm sendm cond); crush).
    pose proof (noPendingEqual hyp1 hyp2 psendRecv csendRecv); crush.
    assert (psendRecv': forall m t1, send p m t1 -> t1 < tp -> exists t2, t2 < tc' /\ recv c m t2) by (intros m t1 sendm cond; specialize (psendRecv m t1 sendm cond); destruct psendRecv as [t2 [cond2 recvm]]; assert (t2 < tc') by crush; firstorder).
    assert (hyp2': forall m t1 t2, recv c m t1 -> send p m t2 -> t1 < tc' -> t2 < tp) by (
      intros m t1 t2 recvm sendm t1LtTc';
        pose proof (pc.deqEnqLess sendm recvm) as t2LeT1;
          crush).
    assert (cNoRecv: forall t, tc <= t < tc' -> forall m, ~ (recv c m t /\ fst m <= state c t)) by (
      unfold not; intros t [cond1 cond2] m [recvm _];
        pose proof (pc.f.deqImpEnq recvm) as [t' [_ sendm]];
          specialize (hyp2' m t t' recvm sendm cond2);
            specialize (psendRecv m t' sendm hyp2');
              destruct psendRecv as [t2 [cond3 recvm']];
                assert (mEq: PcResp m = PcResp m) by crush;
                  pose proof (pc.f.uniqueDeq1 recvm recvm' mEq) as rew;
                    rewrite <- rew in cond3;
                      crush).
    assert (cond: tc <= tc') by crush.
    pose proof (noRecvChild0 cond cNoRecv) as cLess.
    pose proof (noPendingEqual hyp1' hyp2' psendRecv' csendRecv') as eq.
    crush.
  Qed.

  Theorem creqLemma {tp} {tc}
    (le: tc <= tp)
    (psendRecv: forall m t1, send p m t1 -> t1 < tp -> exists t2, t2 < tc /\ recv c m t2)
    (csendRecv: forall m t1, send c m t1 -> t1 < tc -> exists t2, t2 < tp /\ recv p m t2):
    state p tp <= state c tc.
  Proof.
    assert (hyp2: forall m t1 t2, recv c m t1 -> send p m t2 -> t1 < tc -> t2 < tp) by (
      intros m t1 t2 recvm sendm t1LtTc;
        pose proof (pc.deqEnqLess sendm recvm) as t2LeT1;
          crush).
    apply (creqLemma' hyp2 psendRecv csendRecv).
  Qed.

  Theorem preqLemma' {tp} {tc}
    (hyp1: forall m t1 t2, recv p m t1 -> send c m t2 -> t1 < tp -> t2 < tc)
    (hyp2: forall m t1 t2, recv c m t1 -> send p m t2 -> t1 < tc -> t2 < tp)
    (psendrecv: forall m t1, send p m t1 -> t1 < tp -> exists t2, t2 < tc /\ recv c m t2)
    (stateLt: state c tc < state p tp):
    exists t, t < tc /\ exists m, send c m t /\ snd m = state c tc /\ forall t', t' < tp -> ~ recv p m t'.
  Proof.
    pose proof (noPendingEqual hyp1 hyp2 psendrecv) as csendRecvImpStateEq.
    assert (neq: state c tc <> state p tp) by crush.
    assert (noRecvEarly': ~ forall m t1, send c m t1 -> t1 < tc -> exists t2, t2 < tp /\ recv p m t2) by firstorder.
    assert (imp: (~ exists t, t < tc /\ exists m, send c m t /\ forall t', t' < tp -> ~ recv p m t') -> forall m t1, send c m t1 -> t1 < tc -> exists t2, t2 < tp /\ recv p m t2) by (
      intros contra m;
        destruct (dec (exists t2, t2 < tp /\ recv p m t2)) as [easy|hard]; [
          firstorder |
            assert (fo: forall t', t' < tp -> ~ recv p m t') by (generalize hard; clear; firstorder);
              generalize contra fo; clear; firstorder]).
    assert (opp: ~ ~ exists t, t < tc /\ exists m, send c m t /\ forall t', t' < tp -> ~ recv p m t') by (generalize noRecvEarly' imp; clear; firstorder).
    assert (noRecvEarly: exists t, t < tc /\ exists m, send c m t /\ forall t', t' < tp -> ~ recv p m t') by (
      destruct (dec (exists t, t < tc /\ exists m, send c m t /\ forall t', t' < tp -> ~ recv p m t')); crush).
    clear noRecvEarly' imp opp.
    destruct (maxExists' dec noRecvEarly) as [t [tLtTc [[m [sendm noRecvBefore]] rest]]].
    exists t.
    constructor.
    assumption.
    exists m.
    constructor.
    assumption.
    constructor.
    Focus 2.
    assumption.
    clear neq noRecvEarly.
    clear csendRecvImpStateEq.
    assert (cnorecv: forall y, t < y < tc -> forall m, ~ (recv c m y /\ fst m <= state c y)).
    unfold not; intros y [cond1 cond2] n [recvn fstn].
    pose proof (pc.f.deqImpEnq recvn) as [y' [_ sendn]].
    assert (cond3: t <= y) by crush.
    pose proof @cRecvIntersect.
    pose proof (hyp2 n y y' recvn sendn cond2) as cond4.
    assert (noRecvBefore': forall t', t' <= y' -> ~ recv p m t') by (intros t' cond5; assert (cond6: t' < tp) by crush; apply (noRecvBefore t' cond6)).
    apply (cRecvIntersect sendm sendn recvn cond3 noRecvBefore' fstn).
    assert (cnosend: forall y, t < y < tc -> forall m, ~ send c m y) by (
      unfold not; intros y cond n sendn;
        specialize (rest y cond);
          destruct (dec (forall t', t' < tp -> ~ recv p n t')) as [noRecv | recvsth]; [
            generalize rest sendn noRecv; clear; firstorder |
              assert (imp: (~ exists t', t' < tp /\ recv p n t') -> forall t', t' < tp -> ~ recv p n t') by (clear; firstorder);
                assert (db: ~ ~ exists t', t' < tp /\ recv p n t') by (generalize recvsth imp; clear; firstorder);
                  assert (exSth: exists t', t' < tp /\ recv p n t') by (generalize (dec (exists t', t' < tp /\ recv p n t')) db; clear; firstorder);
                    clear db imp recvsth;
                      destruct exSth as [y' [cond2 recvn]];
                        destruct cond as [cond3 cond4];
                          pose proof (cp.f.fifo sendn recvn sendm cond3) as [t' [recvm cond5]];
                            assert (cond6: t' < tp) by crush;
    apply (noRecvBefore t' cond6 recvm)]).
    assert (tLtTc_: S t <= tc) by crush.
    assert (not: forall y, S t <= y < tc -> (forall m, ~ send c m y) /\ forall m, ~ (recv c m y /\ fst m <= state c y)) by (generalize cnorecv cnosend; clear; firstorder).
    pose proof (noRecvSendChild tLtTc_ not) as ceq.
    pose proof (sendCommon sendm) as [_ sndm].
    unfold axioms.nextState; crush.
  Qed.

  Theorem preqLemma {tp} {tc}
    (le: tp <= tc)
    (hyp2: forall m t1 t2, recv c m t1 -> send p m t2 -> t1 < tc -> t2 < tp)
    (psendrecv: forall m t1, send p m t1 -> t1 < tp -> exists t2, t2 < tc /\ recv c m t2)
    (stateLt: state c tc < state p tp):
    exists t, t < tc /\ exists m, send c m t /\ snd m = state c tc /\ forall t', t' < tp -> ~ recv p m t'.
  Proof.
    apply preqLemma'; crush.
    pose proof (cp.deqEnqLess H0 H).
    crush.
  Qed.

  Definition cRecvrSend {r t} := @cRecvrSend r t.

  Theorem cRecvrAlreadySent {r tc tp}
    (recvr: recvr c r tc)
    (sendr: sendr p r tp)
    (ge: r >= state c tc):
    exists t, t < tc /\ exists m, send c m t /\ snd m = state c tc /\ forall t', t' < tp -> ~ recv p m t'.
  Proof.
    pose proof (pc.deqEnqLess sendr recvr) as tpLeTc.
    assert (hyp2: forall m t1 t2, recv c m t1 -> send p m t2 -> t1 < tc -> t2 < tp) by (intros m t1 t2 recvm sendm; pose proof (pc.fifo2 sendr recvr sendm recvm); crush).
    assert (psendrecv: forall m t1, send p m t1 -> t1 < tp -> exists t2, t2 < tc /\ recv c m t2) by(
      intros m t1 sendm cond; pose proof (pc.f.fifo sendr recvr sendm cond); firstorder).
    pose proof (sendrParentReq sendr) as lt.
    assert (stateLt: state c tc < state p tp) by crush.
    apply (preqLemma tpLeTc hyp2 psendrecv stateLt).
  Qed.

  Theorem waitNoWait' {pt t1 td}
    (waitT1: wait pt t1)
    (notWaitT2: ~ wait pt (t1 + td)):
    exists t, t1 <= t < t1 + td /\ exists m, recv pt m t.
  Proof.
    induction td.
    assert (t1 + 0 = t1) by crush; crush.
    assert (rew: t1 + S td = S (t1 + td)) by crush; rewrite rew in notWaitT2; clear rew.
    destruct (dec (wait pt (t1 + td))) as [waiting|notWait].
    pose proof (waitNotWait waiting notWaitT2) as ex.
    assert (cond: t1 <= t1 + td < t1 + S td) by crush.
    firstorder.
    firstorder.
  Qed.

  Theorem waitNoWait {pt t1 t2}
    (t1LeT2: t1 <= t2)
    (waitT1: wait pt t1)
    (notWaitT2: ~ wait pt t2):
    exists t, t1 <= t < t2 /\ exists m, recv pt m t.
  Proof.
    remember (t2 - t1) as td.
    assert (rew: t2 = t1 + td) by crush.
    rewrite rew in *.
    apply (waitNoWait' waitT1 notWaitT2).
  Qed.

  Theorem pWaitState0 {pt t1 td}
    (nosendr: forall t, t1 <= t < t1 + td -> forall r, ~ sendr pt r t):
    waitState pt t1 = waitState pt (t1 + td).
  Proof.
    induction td.
    assert (t1 + 0 = t1) by crush; crush.
    assert (nosendr1: forall t, t1 <= t < t1 + td -> forall r, ~ sendr pt r t) by (intros t cond; assert (cond2: t1 <= t < t1 + S td) by crush; generalize cond2 nosendr; clear; firstorder).
    specialize (IHtd nosendr1).
    assert (nosendr2: forall r, ~ sendr pt r (t1 + td)) by (assert (t1 <= t1 + td < t1 + S td) by crush; firstorder).
    assert (contra: (~ waitState pt (t1 + td) = nextWaitState pt (t1 + td)) -> False ) by (
      intros wait1;
        pose proof (waitStateSendr wait1) as stuff; generalize stuff nosendr2; clear; firstorder).
    destruct (dec (waitState pt (t1 + td) = nextWaitState pt (t1 + td))) as [tough|easy].
    assert (stuff: t1 + S td = S (t1 + td)) by crush.
    rewrite stuff.
    unfold nextWaitState in tough.
    crush.
    crush.
  Qed.

  Theorem pWaitState1 {pt t1 t2}
    (le: t1 <= t2)
    (nosendr: forall t, t1 <= t < t2 -> forall r, ~ sendr pt r t):
    waitState pt t1 = waitState pt t2.
  Proof.
    remember (t2 - t1) as td.
    assert (rew: t2 = t1 + td) by crush.
    rewrite rew in *.
    apply (pWaitState0 nosendr).
  Qed.

  Theorem pWaitNoWait0 {pt t1 td}
    (waitT1: wait pt t1)
    (notWaitT2: ~ wait pt (t1 + td))
    (noChange: forall t, t1 <= t < t1 + td -> ~ (wait pt t /\ ~ nextWait pt t)):
    False.
  Proof.
    induction td.
    assert (t1 + 0 = t1) by crush; crush.
    destruct (dec (wait pt (t1 + td))) as [waiting | notWaiting].
    assert (le: t1 <= t1 + td < t1 + S td) by crush.
    specialize (noChange (t1 + td) le).
    unfold nextWait in *.
    assert (rew: t1 + S td = S (t1 + td)) by crush.
    rewrite rew in notWaitT2.
    firstorder.
    assert (no: forall t, t1 <= t < t1 + td -> ~ (wait pt t /\ ~ nextWait pt t)) by (
      intros t cond; assert (cond2: t1 <= t < t1 + S td) by crush; apply (noChange t cond2)).
    firstorder.
  Qed.

  Theorem pWaitNoWait1 {pt t1 td}
    (waitT1: wait pt t1)
    (notWaitT2: ~ wait pt (t1 + td)):
    exists t, t1 <= t < t1 + td /\ wait pt t /\ ~ nextWait pt t.
  Proof.
    pose proof (pWaitNoWait0 waitT1 notWaitT2) as waits.
    assert (imp: (~ exists t, t1 <= t < t1 + td /\ wait pt t /\ ~ nextWait pt t) -> forall t, t1 <= t < t1 + td -> ~ (wait pt t /\ ~ nextWait pt t)) by (
      unfold not; intros ex t cond waitDbl;
        firstorder).
    assert (imp': ~ ~ exists t, t1 <= t < t1 + td /\ wait pt t /\ ~ nextWait pt t) by firstorder.
    destruct (dec (exists t, t1 <= t < t1 + td /\ wait pt t /\ ~ nextWait pt t)); firstorder.
  Qed.

  Theorem pWaitNoWait2 {t1 td}
    (waitT1: wait p t1)
    (notWaitT2: ~ wait p (t1 + td)):
    exists t, t1 <= t < t1 + td /\ exists m, recv p m t /\ snd m <= waitState p t.
  Proof.
    pose proof (pWaitNoWait1 waitT1 notWaitT2) as [t [cond [wait1 wait2]]].
    pose proof (waitNotWait wait1 wait2) as [m recvm].
    pose proof (waitPRecv wait1 wait2 recvm) as last.
    firstorder.
  Qed.

  Theorem pWaitNoWait3 {t1 t2}
    (le: t1 <= t2)
    (waitT1: wait p t1)
    (notWaitT2: ~ wait p t2):
    exists t, t1 <= t < t2 /\ exists m, recv p m t /\ snd m <= waitState p t.
  Proof.
    remember (t2 - t1) as td.
    assert (rew: t2 = t1 + td) by crush.
    rewrite rew in *.
    apply (pWaitNoWait2 waitT1 notWaitT2).
  Qed.

  Theorem pWaitNoWait4 {r t1 t2}
    (le: S t1 <= t2)
    (sendrr: sendr p r t1)
    (notWaitT2: ~ wait p t2):
    exists t, S t1 <= t < t2 /\ exists m, recv p m t /\ snd m <= r.
  Proof.
    pose proof (sendrWait sendrr) as [_ [waitT1 waitr]].
    pose proof (pWaitNoWait3 le waitT1 notWaitT2) as ex.
    pose proof (minExists dec ex) as [t [[[t1LtT tLtT2] [m [recvm sndm]]] min]].
    assert (ws: forall x, S t1 <= x < t -> wait p x) by (
      intros x [t1LtX xLtT];
        destruct (dec (wait p x)) as [waiting|notWait]; [
          crush |
            pose proof (pWaitNoWait3 t1LtX waitT1 notWait) as [t' [[tLtT' t'LtX] [n [recvn sndn]]]];
              assert (t'LtT: t' < t) by crush;
                assert (t'LtT2: t' < t2) by crush;
                  generalize min tLtT' t'LtT t'LtT2 sndn recvn; clear; firstorder]).
    assert (nosendr: forall x, S t1 <= x < t -> forall r, ~ sendr p r x) by (
      unfold not; intros x cond rm sendrm;
        pose proof (sendrWait sendrm) as [noWait _];
          firstorder).
    pose proof (pWaitState1 t1LtT nosendr) as seq.
    exists t.
    constructor.
    crush.
    exists m.
    constructor.
    crush.
    unfold nextWaitState in waitr.
    crush.
  Qed.

  Theorem pRespOnlyForReq {r tr1 tr2 m tm1 tm2}
    (sendrr: sendr c r tr1)
    (recvrr: recvr p r tr2)
    (sendm: send p m tm1)
    (recvm: recv c m tm2)
    (tr1LtTm1: tr1 < tm2)
    (tm2LtTr2: tm1 < tr2):
    False.
  Proof.
    assert (ex: exists tr1 r tr2 m tm1 tm2, sendr c r tr1 /\ recvr p r tr2 /\ send p m tm1 /\ recv c m tm2 /\ tr1 < tm2 /\ tm1 < tr2) by (exists tr1; exists r; exists tr2; exists m; exists tm1; exists tm2; crush).
    clear r tr1 tr2 m tm1 tm2 sendrr recvrr sendm recvm tr1LtTm1 tm2LtTr2.
    pose proof (minExists dec ex) as [tr1 [[r [tr2 [m [tm1 [tm2 [sendrr [recvrr [sendm [recvm [tr1LtTm1 tm2LtTr2]]]]]]]]]] min]]; clear ex.
    pose proof (cpr.deqEnqLess sendrr recvrr) as tr1LeTr2.
    pose proof (sendrWait sendrr) as [notWaitTr1 _].
    pose proof (pSendRecvr sendm) as [rm recvrm].
    pose proof (cpr.f.deqImpEnq recvrm) as [t [tLeTm1 sendrm]].
    assert (waitT: wait c (S t)) by (apply (@sendrWait c rm); crush).
    pose proof (cpr.fifo2 sendrr recvrr sendrm recvrm tm2LtTr2) as tLtTr1'.
    assert (tLtTr1: S t <= tr1) by crush.
    pose proof (waitNoWait tLtTr1 waitT notWaitTr1) as [t' [[cond1' cond2] [n recvn]]].
    assert (tLtT': t < t') by crush; clear cond1'.
    assert (t'LtTm2: t' < tm2) by crush; clear cond2.
    pose proof (pc.f.deqImpEnq recvn) as [t'' [_ sendn]].
    pose proof (pc.fifo2 sendm recvm sendn recvn t'LtTm2) as t''LtTm1.
    specialize (min t tLtTr1').
    assert (ex: exists r tr2 m tm1 tm2, sendr c r t /\ recvr p r tr2 /\ send p m tm1 /\ recv c m tm2 /\ t < tm2 /\ tm1 < tr2) by (exists rm; exists tm1; exists n; exists t''; exists t'; crush).
    crush.
  Qed.

  Theorem pRecvrPStateLt {r t}
    (recvrr: recvr p r t):
    r > state p t.
  Proof.
    pose proof (cpr.f.deqImpEnq recvrr) as [t' [le sendr']].
    assert (csendRecv: forall m t1, send c m t1 -> t1 < t' -> exists t2, t2 < t /\ recv p m t2) by ( intros m t1 sendm;  apply (noOvertake sendr' recvrr sendm)).
    assert (psendRecv: forall m t1, send p m t1 -> t1 < t -> exists t2, t2 < t' /\ recv c m t2).
    intros m t1 sendm t1LtT.
    assert (sendrr: sendr c r t') by crush.
    pose proof (sendrWait sendrr) as [notWaitT' _]; clear sendr'.
    pose proof (pSendRecvr sendm) as [rm recvrm].
    pose proof (cpr.f.deqImpEnq recvrm) as [tx [txLeT1 sendrm']].
    assert (sendrm: sendr c rm tx) by crush.
    pose proof (sendrWait sendrm) as [_ [nextWaitTx _]]; clear sendrm'; unfold nextWait in *.
    pose proof (cpr.fifo2 sendrr recvrr sendrm recvrm t1LtT) as txLtT'_.
    assert (txLtT': S tx <= t') by crush; clear txLtT'_.
    pose proof (waitNoWait txLtT' nextWaitTx notWaitT') as [ty [[cond1 cond2] [n recvn]]].
    destruct (dec (exists t2, t2 < t' /\ recv c m t2)) as [easy|hard].
    crush.
    pose proof (pc.f.deqImpEnq recvn) as [tz [_ sendn']].
    assert (sendn: send p n tz) by crush; clear sendn'.
    assert (stuff: t1 < tz \/ t1 = tz \/ tz < t1) by (pose proof Compare_dec.lt_eq_lt_dec t1 tz as stuff'; generalize stuff'; crush).
    destruct stuff as [t1LtTz| [t1EqTz|tzLtT1]].
    pose proof (pc.f.fifo sendn recvn sendm t1LtTz) as [t2 [recvm t2LtTy]].
    assert (t2LtT': t2 < t') by crush.
    exists t2; crush.
    assert (mEqn: m = n) by (pose proof (pc.f.uniqueEnq2 sendm sendn t1EqTz); crush).
    rewrite <- mEqn in recvn.
    exists ty; crush.
    pose proof (pRespOnlyForReq sendrm recvrm sendn recvn cond1 tzLtT1); crush.
    pose proof (creqLemma le psendRecv csendRecv) as stateLess.
    pose proof (sendrChildReq sendr') as sth.
    crush.
  Qed.

  Theorem cRecvCStateLt' {m t}
    (recvm: recv c m t)
    (fstmGtState: fst m > state c t):
    False.
  Proof.
    pose proof (pc.f.deqImpEnq recvm) as [tp [_ sendm']].
    assert (sendm: send p m tp) by crush; clear sendm'.
    destruct (dec (forall t1, t1 < t -> forall n, send c n t1 -> exists t', t' < tp /\ recv p n t')) as [easy|real].
    apply (cRecvNoIntersect sendm recvm easy fstmGtState).
    assert (imp: (~ exists t1, t1 < t /\ exists n, send c n t1 /\ forall t', t' < tp -> ~ recv p n t') -> forall t1, t1 < t -> forall n, send c n t1 -> exists t', t' < tp /\ recv p n t') by (
      intros contra t1 cond n sendn;
        destruct (dec (exists t', t' < tp /\ recv p n t')) as [easy|hard]; [
          firstorder|
            assert (fo: forall t', t' < tp -> ~ recv p n t') by (generalize hard; clear; firstorder);
              generalize cond contra fo sendn; clear; firstorder]).
    assert (opp: ~ ~ exists t1, t1 < t /\ exists n, send c n t1 /\ forall t', t' < tp -> ~ recv p n t') by (generalize real imp; clear; firstorder).
    assert (ex: exists t1, t1 < t /\ exists n, send c n t1 /\ forall t', t' < tp -> ~ recv p n t') by (
      destruct (dec (exists t1, t1 < t /\ exists n, send c n t1 /\ forall t', t' < tp -> ~ recv p n t')); crush).
    clear real imp opp.
    destruct ex as [t1 [t1LtT [n [sendn norecvn]]]].
    pose proof (pSendRecvr sendm) as [rm recvrm].
    destruct (dec (wait c t1)) as [waiting|notWait].
    pose proof (cSendWaitRecvr sendn waiting) as [r recvrr].
    pose proof (pRecvrNoWait recvrm) as noWaitTp.
    pose proof (pc.f.deqImpEnq recvrr) as [t2 [t2LeT1 sendrr']].
    assert (sendrr: sendr p r t2) by crush; clear sendrr'.
    pose proof (sendrWait sendrr) as [_ [nextWaitT2 _]].
    unfold nextWait in *.
    pose proof (pc.fifo2 sendm recvm sendrr recvrr t1LtT) as t2LtTp.
    pose proof (pWaitNoWait4 t2LtTp sendrr noWaitTp) as [t3 [[t2LtT3 t3LtTp] [x [recvx sndx']]]].
    pose proof (cp.f.deqImpEnq recvx) as [t4 [t4LeT3 sendx']].
    assert (sendx: send c x t4) by crush; clear sendx'.
    assert (t1LtT4: ~ t1 < t4) by (
      unfold not; intros t1LtT4;
        pose proof (cp.f.fifo sendx recvx sendn t1LtT4) as [ti [recvn tiLtT3]];
          assert (tiLtTp: ti < tp) by crush;
            apply (norecvn ti tiLtTp recvn)).
    assert (t1NeT4: t1 <> t4) by (
      unfold not; intros t1EqT4;
        pose proof (cp.f.uniqueEnq2 sendn sendx t1EqT4) as xEqN;
          rewrite <- xEqN in recvx;
            apply (norecvn t3 t3LtTp recvx)).
    assert (t4LtT1: t4 < t1) by crush; clear t1LtT4 t1NeT4.
    destruct (dec (exists t', t4 < t' < t1 /\ exists y, recv c y t' /\ fst y <= state c t')) as [[t' [[t4LtT' t'LtT1] [y [recvy fsty]]]]|noEx].
    pose proof (pc.f.deqImpEnq recvy) as [t'' [_ sendy']].
    assert (sendy: send p y t'') by crush; clear sendy'.
    pose proof (pc.fifo2 sendrr recvrr sendy recvy t'LtT1) as t''LtT2.
    pose proof @cRecvIntersect.
    assert (norecvEarly: forall tt, tt <= t'' -> ~ recv p x tt) by (
      unfold not; intros tt ttLeT'' recvtt;
        assert (xEqX: x = x) by crush;
          pose proof (cp.f.uniqueDeq1 recvx recvtt xEqX) as t3EqTt;
            rewrite <- t3EqTt in ttLeT'';
              crush).
    assert (t4LeT': t4 <= t') by crush.
    apply (cRecvIntersect sendx sendy recvy t4LeT' norecvEarly fsty).
    assert (norecv: forall t', t4 < t' < t1 -> forall y, ~ (recv c y t' /\ fst y <= state c t')) by (generalize noEx; clear; firstorder).
    pose proof (noRecvChild0 t4LtT1 norecv) as sT1LeSndx.
    pose proof (sendCommon sendx) as [_ sndx].
    unfold nextState in sndx.
    rewrite sndx in sT1LeSndx; clear sndx.
    assert (st1LeR: state c t1 <= r) by crush.
    pose proof (cRecvrNoSend recvrr sendn) as contra.
    crush.
    pose proof (cpr.f.deqImpEnq recvrm) as [tc [tcLeTp sendrm']].
    assert (sendrm: sendr c rm tc) by crush; clear sendrm'.
    pose proof (sendrWait sendrm) as [_ [nextWaitTc _]].
    assert (notT1LtTc: ~ t1 < tc) by (
      unfold not; intros t1LtTc;
        pose proof (noOvertake sendrm recvrm sendn t1LtTc) as [tfake [tfakeLtTp recvn]];
          generalize norecvn tfakeLtTp recvn; clear; firstorder).
    assert (t1NeTc: t1 <> tc) by (
      unfold not; intros t1EqTc;
        rewrite <- t1EqTc in sendrm; 
          apply (noSendrSend sendrm sendn)).
    assert (tcLtT1: tc < t1) by crush; clear notT1LtTc t1NeTc.
    unfold nextWait in *.
    pose proof (waitNoWait tcLtT1 nextWaitTc notWait) as [t' [[tcLtT' t'LtT1] [x recvx]]].
    pose proof (pc.f.deqImpEnq recvx) as [tx [_ sendx']].
    assert (sendx: send p x tx) by crush; clear sendx'.
    assert (t'LtT: t' < t) by crush.
    pose proof (pc.fifo2 sendm recvm sendx recvx t'LtT) as txLtTp.
    pose proof @pRespOnlyForReq.
    apply (pRespOnlyForReq sendrm recvrm sendx recvx tcLtT' txLtTp).
  Qed.

  Theorem cRecvCStateLt {m t}
    (recvm: recv c m t):
    fst m <= state c t.
  Proof.
    pose proof (cRecvCStateLt' recvm) as stuff.
    apply (Compare_dec.not_gt (fst m) (state c t) stuff).
  Qed.

  Theorem pRecvrAlwaysSend {r t}
    (recvrr: recvr p r t):
    exists m, send p m t /\ snd m >= r.
  Proof.
    pose proof (pRecvrPStateLt recvrr) as lt.
    apply (pRecvrSend recvrr lt).
  Qed.

  Definition state := state.
  Definition nextState := nextState.
  Definition send := send.
  Definition recv := recv.
  Definition sendr := sendr.
  Definition recvr := recvr.
End GetResp.
