Require Import CpdtTactics.
Load Useful.

Definition Time := nat.
Definition State := nat.

Inductive Channel := pc | cp.
Definition Mesg := (State * State)%type.

Inductive enq : Channel -> Mesg -> Time -> Prop :=
  enq_intro : forall s m t, enq s m t.

Inductive deq : Channel -> Mesg -> Time -> Prop :=
  deq_intro : forall s m t, deq s m t.

Inductive Point := p | c.

Definition sendm pt m t :=
  match pt with
    | p => enq pc m t
    | c => enq cp m t
  end.

Definition recvm pt m t :=
  match pt with
    | p => deq cp m t
    | c => deq pc m t
  end.

Section classic.
  Hypothesis dec : forall P, P \/ ~ P.

  Section fifo.
    Hypothesis uniqueEnq:
      forall s m n t1 t2, enq s m t1 -> enq s n t2 -> ((m = n -> t1 = t2) /\ (t1 = t2 -> m = n)).

    Hypothesis uniqueDeq:
      forall s m n t1 t2, deq s m t1 -> deq s n t2 -> ((m = n -> t1 = t2) /\ (t1 = t2 -> m = n)).

    Hypothesis deqImpEnq:
      forall s m t, deq s m t -> exists t', t' <= t /\ enq s m t'.

    Hypothesis fifo:
      forall s m te td, deq s m td -> enq s m te -> forall m' te' td', deq s m' td' -> enq s m' te' -> ((td' < td -> te' < te) /\ (te' < te -> td' < td)).

    Theorem fifo':
      forall {s m te td}, deq s m td -> enq s m te -> forall {m' te' td'}, deq s m' td' -> enq s m' te' -> ((td' <= td -> te' <= te) /\ (te' <= te -> td' <= td)).
      Proof.
        intros.
        pose proof (fifo s m te td H H0 m' te' td' H1 H2).
        destruct H3.
        constructor.
        intros.
        assert (td' < td \/ td' >= td) by crush.
        destruct H6.
        specialize (H3 H6).
        crush.
        assert (td = td') by crush.
        pose proof (uniqueDeq s m m' td td' H H1).
        destruct H8.
        specialize (H9 H7).
        pose proof (uniqueEnq s m m' te te' H0 H2).
        destruct H10.
        specialize (H10 H9).
        crush.
        intros.
        assert (te' < te \/ te' >= te) by crush.
        destruct H6.
        specialize (H4 H6).
        crush.
        assert (te = te') by crush.
        pose proof (uniqueEnq s m m' te te' H0 H2).
        destruct H8.
        specialize (H9 H7).
        pose proof (uniqueDeq s m m' td td' H H1).
        destruct H10.
        specialize (H10 H9).
        crush.
      Qed.

    Theorem send0Fifo:
      forall {s m t}, enq s m 0 -> deq s m t -> forall t', t' < t -> forall {m'}, ~ deq s m' t'.
    Proof.
      unfold not.
      intros.
      specialize (deqImpEnq s m' t' H2).
      destruct deqImpEnq.
      destruct H3.
      specialize (fifo s m 0 t H0 H m' x t' H2 H4).
      crush.
    Qed.

    Section message.
      Parameter state : Point -> Time -> State.

      Definition nextState pt t := state pt (S t).

      Hypothesis init: state p 0 = state c 0.

      Hypothesis stateChange : forall pt t, state pt t <> nextState pt t -> exists m, sendm pt m t \/ recvm pt m t.

      Hypothesis sendCommon: forall pt m t, sendm pt m t -> state pt t = fst m /\ nextState pt t = snd m.

      Hypothesis recvParent: forall m t, recvm p m t -> nextState p t = snd m.

      Hypothesis recvChildChange  : forall m t, recvm c m t -> fst m <= state c t -> nextState c t = snd m.

      Hypothesis recvChildNoChange: forall m t, recvm c m t -> fst m > state c t -> nextState c t = state c t.

      Hypothesis sendParent: forall m t, sendm p m t -> fst m < snd m.

      Hypothesis sendChild: forall m t, sendm c m t -> fst m > snd m.

      Hypothesis enqImpDeq: forall s m t, enq s m t -> exists t', deq s m t'.

      Hypothesis noSimultaneous: forall pt m n t, ~ (sendm pt m t /\ recvm pt n t).

      Section noRecvParent.
        Context {ti : nat}.

        Lemma noRecvParentNow {t} (noRecv : forall m, ~ recvm p m t) : nextState p t >= state p t.
        Proof.
          destruct (dec (state p t = nextState p t)).
          crush.
          pose proof (stateChange p t H).
          destruct H0.
          destruct H0.
          pose proof (sendCommon p x t H0).
          pose proof (sendParent x t H0).
          assert (state p t < nextState p t) by crush.
          crush.
          specialize (noRecv x H0).
          crush.
        Qed.

        Lemma noRecvParent' {td} (noRecv : forall t, ti <= t <= ti + td -> forall m, ~ recvm p m t):
          nextState p (ti + td) >= state p ti.
        Proof.
          induction td.
          assert (forall m, ~ recvm p m ti).
          unfold not.
          intros.
          assert (ti <= ti <= ti + 0) by crush.
          specialize (noRecv ti H0 m).
          crush.
          assert (nextState p ti >= state p ti) by (apply (noRecvParentNow H)).
          assert (ti + 0 = ti) by crush.
          crush.
          assert (forall t, ti <= t <= ti + td -> forall m, ~ recvm p m t).
          intros.
          assert (ti <= t <= ti + S td) by crush.
          apply (noRecv t H0 m).
          specialize (IHtd H).
          clear H.
          assert (forall m, ~ recvm p m (ti + S td)).
          intros.
          assert (ti <= ti + S td <= ti + S td) by crush.
          apply (noRecv (ti + S td) H m).
          pose proof (noRecvParentNow H).
          assert (ti + S td = S (ti + td)) by crush.
          unfold nextState in IHtd.
          assert (state p (S (ti + td)) = state p (ti + S td)) by crush.
          assert (state p (ti + S td) >= state p ti) by crush.
          crush.
        Qed.

        Lemma noRecvParent1 {tf}:
          ti <= tf -> (forall t, ti <= t <= tf -> forall m, ~ recvm p m t) ->
          nextState p tf >= state p ti.
        Proof.
          intros.
          pose proof (@noRecvParent' (tf - ti)).
          assert (ti + (tf - ti) = tf) by crush.
          assert (forall t, ti <= t <= ti + (tf - ti) -> forall m, ~ recvm p m t).
          intros.
          assert (ti <= t <= tf) by crush.
          specialize (H0 t H4 m).
          crush.
          crush.
        Qed.
      End noRecvParent.

      Lemma noRecvParent2 {ti tf}:
        ti <= tf -> (forall t, S ti <= t <= tf -> forall m, ~ recvm p m t) ->
        nextState p tf >= nextState p ti.
      Proof.
        intros.
        assert (S ti <= tf \/ ti = tf) by crush.
        destruct H1.
        apply noRecvParent1; crush.
        crush.
      Qed.

      Lemma zeroRecvParent:
        forall {m t}, sendm c m 0 -> recvm p m t -> forall t', t' <= t -> state p t' >= state p 0.
      Proof.
        intros.
        pose proof (send0Fifo H H0).
        destruct t'.
        crush.
        assert (forall t1, 0 <= t1 <= t' -> forall m', ~ recvm p m' t1) by (intros; assert (t1 < S t) by crush; apply H2; crush).
        apply noRecvParent1; crush.
      Qed.

      Section noRecvChild.
        Context {ti : nat}.

        Lemma noRecvChildNow {t} (noRecv : forall m, ~ (recvm c m t /\ fst m <= state c t)):
          nextState c t <= state c t.
        Proof.
          destruct (dec (state c t = nextState c t)).
          crush.
          pose proof (stateChange c t H).
          destruct H0.
          destruct H0.
          pose proof (sendCommon c x t H0).
          pose proof (sendChild x t H0).
          assert (state c t > nextState c t) by crush.
          crush.
          specialize (noRecv x).
          destruct (dec (fst x <= state c t)).
          crush.
          assert (fst x > state c t) by crush.
          assert (nextState c t = state c t) by (apply (recvChildNoChange x t H0 H2)).
          crush.
        Qed.

        Lemma noRecvChild' {td} (noRecv : forall t, ti <= t <= ti + td -> forall m, ~ (recvm c m t /\ fst m <= state c t)) :
          nextState c (ti + td) <= state c ti.
        Proof.
          induction td.
          assert (forall m, ~ (recvm c m ti /\ fst m <= state c ti)).
          unfold not.
          intros.
          assert (ti <= ti <= ti + 0) by crush.
          specialize (noRecv ti H0 m).
          crush.
          assert (nextState c ti <= state c ti) by (apply (noRecvChildNow H)).
          assert (ti + 0 = ti) by crush.
          crush.
          assert (forall t, ti <= t <= ti + td -> forall m, ~ (recvm c m t /\ fst m <= state c t)).
          intros.
          assert (ti <= t <= ti + S td) by crush.
          apply (noRecv t H0 m).
          specialize (IHtd H).
          clear H.
          assert (forall m, ~ (recvm c m (ti + S td) /\ fst m <= state c (ti + S td))).
          intros.
          assert (ti <= ti + S td <= ti + S td) by crush.
          apply (noRecv (ti + S td) H m).
          pose proof (noRecvChildNow H).
          assert (ti + S td = S (ti + td)) by crush.
          unfold nextState in IHtd.
          assert (state c (S (ti + td)) = state c (ti + S td)) by crush.
          assert (state c (ti + S td) <= state c ti) by crush.
          crush.
        Qed.

        Lemma noRecvChild1 {tf}:
          ti <= tf -> (forall t, ti <= t <= tf -> forall m, ~ (recvm c m t /\ fst m <= state c t)) ->
          nextState c tf <= state c ti.
        Proof.
          intros.
          pose proof (@noRecvChild' (tf - ti)).
          assert (ti + (tf - ti) = tf) by crush.
          assert (forall t, ti <= t <= ti + (tf - ti) -> forall m, ~ (recvm c m t /\ fst m <= state c t)).
          intros.
          assert (ti <= t <= tf) by crush.
          specialize (H0 t H4 m).
          crush.
          crush.
        Qed.
      End noRecvChild.

      Lemma noRecvChild2 {ti tf}:
        ti <= tf -> (forall t, S ti <= t <= tf -> forall m, ~ (recvm c m t /\ fst m <= state c t)) ->
        nextState c tf <= nextState c ti.
      Proof.
        intros.
        assert (S ti <= tf \/ ti = tf) by crush.
        destruct H1.
        apply noRecvChild1; crush.
        crush.
      Qed.

      Lemma childRecv {ti tf}:
        ti <= tf -> nextState c ti < nextState c tf -> exists t, S ti <= t <= tf /\ exists m, recvm c m t /\ fst m <= state c t.
      Proof.
        intros.
        pose proof (noRecvChild2 H).
        assert (~ nextState c tf <= nextState c ti) by crush.
        generalize H2 H1 (dec (exists t, S ti <= t <= tf /\ exists m, recvm c m t /\ fst m <= state c t)).
        clear.
        intros.
        firstorder.
      Qed.

      Lemma zeroRecvChild:
        forall {m t}, sendm p m 0 -> recvm c m t -> forall t', t' <= t -> state c t' <= state c 0.
      Proof.
        intros.
        pose proof (send0Fifo H H0).
        destruct t'.
        crush.
        assert (forall t1, 0 <= t1 <= t' -> forall m', ~ (recvm c m' t1 /\ fst m' <= state c t1)) by (intros; assert (t1 < S t) by crush; unfold not; intro dep; destruct dep as [one two]; generalize one; apply H2; crush).
        apply noRecvChild1; crush.
      Qed.

      Lemma childRecvNoParentRecv {tp tc}:
        (forall m t1 t2, recvm p m t1 -> sendm c m t2 -> t1 <= tp -> t2 <= tc) ->
        (forall m t1 t2, recvm c m t1 -> sendm p m t2 -> t1 <= tc -> t2 <= tp) ->
        forall {tr}, tr <= tc -> forall {m}, (recvm c m tr /\ fst m <= state c tr) ->
          (forall t, S tr <= t <= tc -> ~ exists m', recvm c m' t /\ fst m' <= state c t) ->
          forall {ts}, sendm p m ts -> (forall t', S ts <= t' <= tp -> forall m'', ~ recvm p m'' t') ->
        ~ (nextState c tc > nextState p tp).
        unfold not.
        intros.
        assert (forall t, S tr <= t <= tc -> forall m', ~ (recvm c m' t /\ fst m' <= state c t)) by (generalize H3; clear; firstorder).
        clear H3.
        assert (nextState c tc <= nextState c tr) by (apply (noRecvChild2 H1 H7)).
        assert (ts <= tp) by (apply (H0 m tr); crush).
        assert (nextState p tp >= nextState p ts) by (apply (noRecvParent2 H8 H5)).
        assert (nextState p ts = snd m) by (apply sendCommon; crush).
        assert (nextState c tr = snd m) by (apply recvChildChange; crush).
        crush.
      Qed.

      Theorem strongLess:
        forall tp tc,
          (forall m t1 t2, recvm p m t1 -> sendm c m t2 -> t1 <= tp -> t2 <= tc) ->
          (forall m t1 t2, recvm c m t1 -> sendm p m t2 -> t1 <= tc -> t2 <= tp) ->
          ~ (nextState c tc > nextState p tp).
      Proof.
        apply (notExistForallNot dec).
        unfold not.
        intros exStmt.
        pose proof (minExists2 dec exStmt) as exMin.
        clear exStmt.
        destruct exMin as [tpmin exMin].
        destruct exMin as [tcmin exMin].
        destruct exMin as [ex min].
        destruct min as [tpminHyp' tcminHyp'].
        destruct ex as [pRecvCSend rest].
        destruct rest as [cRecvPSend wrongState].
        assert (tpminHyp: ~ exists x y, x < tpmin /\
          (forall m t1 t2, recvm p m t1 -> sendm c m t2 -> t1 <= x -> t2 <= y) /\
          (forall m t1 t2, recvm c m t1 -> sendm p m t2 -> t1 <= y -> t2 <= x) /\
          nextState c y > nextState p x) by firstorder.
        clear tpminHyp'.
        assert (tcminHyp: ~ exists y, y < tcmin /\
          (forall m t1 t2, recvm p m t1 -> sendm c m t2 -> t1 <= tpmin -> t2 <= y    ) /\
          (forall m t1 t2, recvm c m t1 -> sendm p m t2 -> t1 <= y     -> t2 <= tpmin) /\
          nextState c y > nextState p tpmin) by firstorder.
        clear tcminHyp'.
        destruct (dec (forall t, 0 <= t <= tpmin -> forall m, ~ recvm p m t)) as [pNotRecv | pRecv'].
        destruct (dec (forall t, 0 <= t <= tcmin -> forall m, ~ (recvm c m t /\ fst m <= state c t))) as [cNotRecv | cRecv'].
        assert (zeroLeTpmin: 0 <= tpmin) by crush.
        assert (nsPTpminGeStateP0: nextState p tpmin >= state p 0) by (apply (noRecvParent1 zeroLeTpmin pNotRecv)).
        clear pNotRecv zeroLeTpmin.
        assert (zeroLeTcmin: 0 <= tcmin) by crush.
        assert (nsCTcminLeStateC0: nextState c tcmin <= state c 0) by (apply (noRecvChild1 zeroLeTcmin cNotRecv)).
        assert (nsCTcminLeNsPTpmin: nextState c tcmin <= nextState p tpmin) by crush.
        crush.
        assert (cRecvEx: exists t, 0 <= t <= tcmin /\ exists m, recvm c m t /\ fst m <= state c t) by (generalize (dec (exists t, 0 <= t <= tcmin /\ exists m, recvm c m t /\ fst m <= state c t)) cRecv'; clear; firstorder).
        clear cRecv'.
        destruct cRecvEx as [tcRecv rest].
        assert (cRecv: exists x, x <= tcmin /\ exists m, recvm c m x /\ fst m <= state c x) by (exists tcRecv; crush).
        clear tcRecv rest.
        pose proof (maxExists dec cRecv) as cRecvMax.
        clear cRecv.
        destruct cRecvMax as [tcmax rest].
        destruct rest as [tcmaxLeTcmin rest].
        destruct rest as [cRecvMax noCRecv].
        destruct cRecvMax as [m childRecvCond].
        assert (exTpmax: exists tpmax, tpmax <= tcmax /\ sendm p m tpmax) by (apply deqImpEnq; crush).
        destruct exTpmax as [tpmax rest].
        destruct rest as [useless sendPMTpmax].
        clear useless.
        assert (pNotRecvGtTpmax: forall t, S tpmax <= t <= tpmin -> forall m, ~ recvm p m t) by
          (intros; assert (0 <= t <= tpmin) by crush; apply pNotRecv; crush).
        apply (childRecvNoParentRecv pRecvCSend cRecvPSend tcmaxLeTcmin childRecvCond noCRecv sendPMTpmax pNotRecvGtTpmax wrongState).
        assert (pRecv'': exists t, 0 <= t <= tpmin /\ exists m, recvm p m t) by (generalize (dec (exists t, 0 <= t <= tpmin /\ exists m, recvm p m t)) pRecv'; clear; firstorder).
        clear pRecv'.
        assert (exPRecv: exists t, t <= tpmin /\ exists m, recvm p m t) by (destruct pRecv'' as [t rest]; exists t; crush).
        clear pRecv''.
        pose proof (maxExists dec exPRecv) as exPRecvMax.
        clear exPRecv.
        destruct exPRecvMax as [tp1 rest].
        destruct rest as [tp1LeTpmin rest].
        destruct rest as [exM noRecvGTTp1'].
        destruct exM as [m recvmPMTp1].
        assert (noRecvGTTp1: forall y, S tp1 <= y <= tpmin -> forall m, ~ recvm p m y) by (generalize noRecvGTTp1'; clear; firstorder).
        clear noRecvGTTp1'.
        assert (nsPTpminGeNsPTp1: nextState p tpmin >= nextState p tp1) by (apply noRecvParent2; crush).
        assert (exRest: exists tc1, tc1 <= tp1 /\ sendm c m tc1) by (apply deqImpEnq; crush).
        destruct exRest as [tc1 rest].
        destruct rest as [tc1LeTp1 sendmCMTc1].

        assert (rest: state c tc1 = fst m /\ nextState c tc1 = snd m) by (apply sendCommon; crush).
        destruct rest as [sCTc1EqFstM nsCTc1EqSndM].
        assert (nsCTcminGTNsPTp1: nextState c tcmin > nextState p tp1) by crush.
        assert (nsPTp1EqSndM: nextState p tp1 = snd m) by (apply recvParent; crush).
        assert (nsCTc1LtNsCTcmin: nextState c tc1 < nextState c tcmin) by crush.
        assert (tc1LeTcmin: tc1 <= tcmin) by (apply (pRecvCSend m tp1); crush).
        pose proof (childRecv tc1LeTcmin nsCTc1LtNsCTcmin) as exCRecv.

        assert (sCTc1GtNsCTc1: state c tc1 > nextState c tc1) by (assert (fst m > snd m) by (apply (sendChild m tc1); crush); crush).

        clear nsPTpminGeNsPTp1 sCTc1EqFstM nsCTc1EqSndM nsCTcminGTNsPTp1 nsPTp1EqSndM nsCTc1LtNsCTcmin.

        pose proof (minExists dec exCRecv) as exCRecvMin.

(*        assert (exCRecvUseful: exists t, t <= tcmin /\ exists m, recvm c m t /\ fst m <= state c t) by
          (destruct exCRecv as [t hyp]; assert (t <= tcmin) by crush; generalize hyp; clear; firstorder). *)
        clear exCRecv.
        destruct exCRecvMin as [tc2 rest].
        destruct rest as [rest noCRecvGTTc1'].
        destruct rest as [tc1LtTc2LeTcmin exCRecv].
        generalize exCRecv; intro rest.
        destruct rest as [n rest].
        destruct rest as [cRecvN fstN].
        assert (exPSend: exists tp2, tp2 <= tc2 /\ sendm p n tp2) by (apply deqImpEnq; crush).
        destruct exPSend as [tp2 rest].
        destruct rest as [tp2LeTc2 pSendN].
        assert (fstSndPN: state p tp2 = fst n /\ nextState p tp2 = snd n) by (apply sendCommon; crush).
        destruct fstSndPN as [fstPN sndPN].
        assert (sPTp2LeScTc2: state p tp2 <= state c tc2) by crush.

        destruct tc2.
        crush.
        assert (tc1LeTc2: tc1 <= tc2) by crush.
        assert (noCRecv': forall y, S tc1 <= y <= tc2 -> ~ exists m, recvm c m y /\ fst m <= state c y) by
          (intro; intro hyp; assert (hyp': y < S tc2) by (generalize hyp; clear; crush); specialize (noCRecvGTTc1' y hyp'); assert (S tc1 <= y <= tcmin) by (generalize hyp tc1LtTc2LeTcmin; clear; crush); crush).
        assert (noCRecv: forall y, S tc1 <= y <= tc2 -> forall m, ~ (recvm c m y /\ fst m <= state c y)) by
          (generalize noCRecv'; clear; firstorder).
        clear noCRecv'.
        pose proof (noRecvChild2 tc1LeTc2 noCRecv) as nsCtc2LeNsCTc1.
        assert (sCTc1GtSPTp2: state c tc1 > state p tp2) by (generalize sCTc1GtNsCTc1 sPTp2LeScTc2 nsCtc2LeNsCTc1; clear; unfold nextState in *; crush).
        clear noCRecvGTTc1'.
        clear sCTc1GtNsCTc1 fstPN sndPN sPTp2LeScTc2 nsCtc2LeNsCTc1.

        assert (tp1LeTp2OrNot: tp1 <= tp2 \/ tp2 < tp1) by (clear; crush).
        destruct tp1LeTp2OrNot as [tp1LeTp2 | tp2LtTp1].
        assert (tc2LtTcmin: S tc2 <= tcmin) by crush.
        pose proof (@maxExistsPower dec (fun t => exists m, recvm c m t /\ fst m <= state c t) tcmin (S tc2) tc2LtTcmin exCRecv) as exCRecvMax.
        (* clear exCRecvUseful. *)
        destruct exCRecvMax as [tc3 rest].
        destruct rest as [tc2LtTc3LeTcmin rest].
        destruct rest as [exCRecvTc3 noCRecvGtTc3].
        destruct exCRecvTc3 as [n' cRecvTc3Fst].
        generalize cRecvTc3Fst; intro hyp.
        destruct hyp as [cRecvTc3 fstTc3].
        assert (tc2LtTc3: S tc2 <= tc3) by crush.
        assert (exPRecvTp3: exists tp3, tp3 <= tc3 /\ sendm p n' tp3) by (apply deqImpEnq; crush).
        destruct exPRecvTp3 as [tp3 rest].
        destruct rest as [junk pSendX].
        clear junk.
        pose proof (fifo' cRecvTc3 pSendX cRecvN pSendN) as conj.
        destruct conj as [impTp2LeTp3 junk].
        clear junk.
        specialize (impTp2LeTp3 tc2LtTc3).
        assert (noRecvPLate: forall y, S tp3 <= y <= tpmin -> forall m, ~ recvm p m y) by
          (intros; assert (hyp: S tp1 <= y <= tpmin) by crush; generalize y hyp noRecvGTTp1; clear; firstorder).
        assert (tc3LeTcmin: tc3 <= tcmin) by crush.
        pose proof (childRecvNoParentRecv pRecvCSend cRecvPSend tc3LeTcmin cRecvTc3Fst noCRecvGtTc3 pSendX noRecvPLate).
        crush.

        destruct tp2.
        pose proof @zeroRecvChild.
        assert (tc1LeSTc2: tc1 <= S tc2) by crush.
        pose proof (zeroRecvChild pSendN cRecvN tc1 tc1LeSTc2) as contra1.
        clear tc1LeSTc2.
        crush.

        assert (noRecvGtTp2: forall y, S tp2 <= y <= tpmin -> forall m, ~ recvm p m y) by
          (intros; assert (hyp: S tp1 <= y <= tpmin) by crush; generalize hyp noRecvGTTp1; clear; firstorder).
        assert (tc2LtTcmin: S tc2 <= tcmin) by crush.
        pose proof (@childRecvNoParentRecv).
(*        pose proof (childRecvNoParentRecv pRecvCSend cRecvPSend tc2LtTcmin (conj cRecvN fstN) noCRecv pSendN noRecvGtTp2).*)
        destruct tp2 as [tp2Eq0 | tp2].
        assert (tc1LeSTc2: tc1 <= S tc2) by crush.
        pose proof (zeroRecvChild pSendN cRecvN tc1 tc1LeSTc2) as sCTc1LeSC0.
        crush.
      Admitted.
    End message.
  End fifo.
End classic.
