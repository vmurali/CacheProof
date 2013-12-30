Require Import DataTypes Useful Channel Cache Compatible L1.

Module Type LatestValueAxioms (dt: DataTypes) (ch: ChannelPerAddr dt) (l1: L1Axioms dt).
  Import dt ch l1.

  Axiom toChild: forall {n a t p m}, defined n -> defined p ->
                   parent n p -> 
                   mark mch p n a t m -> from m = In -> dataM m = data p a t.
  Axiom fromParent: forall {n a t p m}, defined n -> defined p ->
                      parent n p -> 
                      recv mch p n a t m -> from m = In -> data n a (S t) = dataM m.
  Axiom toParent: forall {n a t c m}, defined n -> defined c ->
                     parent c n ->
                     mark mch c n a t m -> slt Sh (from m) -> dataM m = data c a t.
  Axiom fromChild: forall {n a t c m}, defined n -> defined c ->
                     parent c n ->
                     recv mch c n a t m -> slt Sh (from m) -> data n a (S t) = dataM m.
  Axiom initLatest: forall {n} a, defined n -> (forall {p}, defined p -> ~ parent n p)
                                  -> data n a 0 = Initial /\ state n a 0 = Mo.

  Axiom deqImpData: forall {n a t l i}, defined n -> deqR n l a St i t ->
                                        data n a (S t) = Store l.

  Axiom changeData:
    forall {n a t}, defined n ->
      data n a (S t) <> data n a t ->
      (exists m, (exists p, defined p /\ parent n p /\ recv mch p n a t m /\ from m = In) \/
                 (exists c, defined c /\ parent c n /\ recv mch c n a t m /\
                            slt Sh (from m))) \/
      exists l i, deqR n l a St i t.


  Axiom deqImpNoSend: forall {c l a d i t}, defined c -> deqR c l a d i t ->
                                            forall {m p}, defined p -> ~ mark mch c p a t m.
  Axiom deqImpNoRecv: forall {c l a d i t}, defined c -> deqR c l a d i t ->
                                            forall {m p}, defined p -> ~ recv mch p c a t m. 
End LatestValueAxioms.

Module LatestValueTheorems (dt: DataTypes) (ch: ChannelPerAddr dt) (c: BehaviorAxioms dt ch)
       (l1: L1Axioms dt) (comp: CompatBehavior dt ch) (lv: LatestValueAxioms dt ch l1).
  Module mbt := mkBehaviorTheorems dt ch c.
  Module cbt := mkCompat dt ch comp c.
  Import dt ch c l1 comp lv mbt cbt.

  Theorem uniqM:
    forall {c a t}, defined c ->
      leaf c ->
      state c a t = Mo -> forall {co}, defined co -> leaf co -> c <> co -> state co a t = In.
  Proof.
    intros c a t cDef leaf_c c_M co coDef leaf_co c_ne_co.
    pose proof (who'Parent c leaf_c) as c_parent.
    pose proof (who'Parent co leaf_co) as co_parent.
    pose proof (conservative defParent cDef c_parent a t) as cLe.
    pose proof (conservative defParent coDef co_parent a t) as coLe.
    pose proof (@compatible Parent defParent a t c cDef c_parent) as [_ comp].
    assert (dirM: dir Parent c a t = Mo) by
        ( unfold sle in *; destruct (state c a t); destruct (dir Parent c a t); firstorder;
          discriminate).
    assert (co_ne_c: co <> c) by auto.
    specialize (comp co coDef co_ne_c co_parent).
    rewrite dirM in comp.
    unfold sle in *; destruct (dir Parent co a t); destruct (state co a t); firstorder.
  Qed.

  Section ForAddr.
    Context {a: Addr}.
    Theorem allLatestValue: forall {t n}, defined n ->
      (sle Sh (state n a t) /\ forall {c}, defined c -> parent c n -> sle (dir n c a t) Sh) ->
      match data n a t with
        | Initial => forall {ti}, 0 <= ti < t -> forall {ci li ii}, defined ci ->
                                                                    ~ deqR ci li a St ii ti
        | Store lb =>
          exists cb ib tb, defined cb /\ tb < t /\ deqR cb lb a St ib tb /\
                           forall {ti}, tb < ti < t ->
                                        forall {ci li ii}, defined ci ->
                                                           ~ deqR ci li a St ii ti
      end.
    Proof.
      pose (fun t => forall n, defined n ->
              sle Sh (state n a t) /\
              (forall c, defined c -> parent c n -> sle (dir n c a t) Sh) ->
                         match data n a t with
                           | Initial =>
                             forall ti : nat,
                               0 <= ti < t ->
                               forall (ci : Cache) (li : Label) (ii : Index),
                                 defined ci -> ~ deqR ci li a St ii ti
                           | Store lb =>
                             exists (cb : Cache) (ib : Index) (tb : nat),
                               defined cb /\ tb < t /\
                               deqR cb lb a St ib tb /\
                               (forall ti : nat,
                                  tb < ti < t ->
                                  forall (ci : Cache) (li : Label) (ii : Index),
                                    defined ci -> ~ deqR ci li a St ii ti)
                         end) as P.
      pose proof (initLatest a defParent noParentHasParent) as [pInit pM].
      apply (@ind P).
      unfold P in *; clear P.
      assert (childIn: forall n, defined (Child n) -> state (Child n) a 0 = In).
      intros c cDef.
      assert (pChilds: parent (Child c) Parent) by
          (unfold parent; auto).
      pose proof (initCompat defParent cDef pChilds a) as dirIn.
      pose proof (conservative defParent cDef pChilds a 0) as sleSt.
      unfold sle in *; destruct (dir Parent (Child c) a 0); destruct (state (Child c) a 0);
      firstorder; discriminate.
      intros n nDef.
      induction n.
      rewrite pInit.
      unfold not; intros.
      assert (ti0: ti = 0) by omega.
      rewrite ti0 in *.
      omega.
(*
      pose proof (deqLeaf nDef H1) as leafC.
      unfold leaf in leafC.
      destruct ci.
      assumption.
      specialize (childIn n).
      pose proof (processDeq H1) as contra.
      rewrite childIn in contra.
      discriminate.
*)
      specialize (childIn n nDef).
      intros H.
      rewrite childIn in H.
      unfold sle in *; firstorder.
      unfold P in *; clear P.
      intros t SIHt n nDef H.
      assert (stEq: forall t, state Parent a t = Mo) by
          (intros t'; pose proof (noParentNoStChange a t' defParent noParentHasParent); rewrite <- pM in *;
          auto).
      destruct n.
      destruct (classical (forall c, defined c -> parent c Parent -> sle (dir Parent c a t) Sh)) as
          [prevLatest|prevNotLatest].
      assert (stM: sle Sh (state Parent a t)) by (specialize (stEq t);
                                                   rewrite stEq; unfold sle; auto).
      assert (cond: t <= t) by omega.
      specialize (SIHt t cond Parent defParent (conj stM prevLatest)); clear cond stM.
      destruct H as [_ dirSmall].
      assert (cSmall: forall c, defined c -> parent c Parent -> sle (state c a t) Sh).
      intros c cDef c_child.
      specialize (prevLatest c cDef c_child).
      pose proof (conservative defParent cDef c_child a t) as help.
      unfold sle in *; destruct (state c a t); destruct (dir Parent c a t); auto.
      assert (noDeq: forall ci li ii, defined ci -> ~ deqR ci li a St ii t) by
          (unfold not; intros ci li ii ciDef H;
           pose proof (processDeq H) as sth; simpl in *;
                                             pose proof (deqLeaf H) as leaf_ci;
           assert (ci_child: parent ci Parent) by (unfold parent; unfold leaf in *;
                                                                  destruct ci; auto);
           specialize (cSmall ci ciDef ci_child); rewrite sth in cSmall; unfold sle; auto).
      destruct (classical (data Parent a (S t) = data Parent a t)) as [e1|e2].
      rewrite e1.
      destruct (data Parent a t).
      intros ti cond.
      assert (H: 0 <= ti < t \/ ti = t) by omega.
      destruct H as [one|two]; [firstorder| rewrite two in *; firstorder].
      destruct SIHt as [cb [ib [tb [cbDef [tb_lt_t [deqTb rest]]]]]].
      exists cb; exists ib; exists tb.
      assert (sth: tb < S t) by omega.
      constructor.
      assumption.
      constructor.
      assumption.
      constructor.
      assumption.
      intros ti cond.
      assert (H: tb < ti < t \/ ti = t) by omega.
      destruct H as [one|two].
      apply (rest ti one).
      rewrite two in *; assumption.
      pose proof (changeData nDef e2) as sth.
      destruct sth as [sth|deqSth].
      destruct sth as [m [[p [defP [parentp _]]]|recvFromC]].
      pose proof (noParentHasParent p defP parentp).
      firstorder.
      destruct recvFromC as [c [cDef [c_child [recvm sltFromM]]]].
      pose proof (recvmCond defParent cDef c_child recvm) as contra.
      specialize (prevLatest c cDef c_child).
      rewrite <- contra in prevLatest.
      unfold sle in *; unfold slt in *; destruct (from m); firstorder; discriminate.
      destruct deqSth as [l [i deqSth]].
      pose proof (deqLeaf deqSth) as H.
      unfold leaf in H; firstorder.
      destruct (classical (exists c, defined c /\ parent c Parent /\
                                     ~ sle (dir Parent c a t) Sh))
               as [[c [cDef [c_child dirHigh]]]|notEx].
      destruct H as [_ cacheLow].
      specialize (cacheLow c cDef c_child).
      assert (downgrade: slt (dir Parent c a (S t)) (dir Parent c a t)) by
          (unfold slt in *; unfold sle in *; destruct (dir Parent c a (S t));
           destruct (dir Parent c a t); auto).
      pose proof (slt_neq' downgrade) as neq.
      pose proof (change (dt defParent cDef c_child) neq) as [[m markm] | [m recvm]].
      pose proof (pSendUpgrade defParent cDef c_child markm) as upg.
      pose proof (slt_slti_false downgrade upg) as f.
      firstorder.
      pose proof (recvImpMark recvm) as [ts [ts_le_t sendm]].


      pose proof (sendmFrom (st defParent cDef c_child) sendm) as fromX.
      pose proof (sendmChange (st defParent cDef c_child) sendm) as toM.
      pose proof (cSendDowngrade defParent cDef c_child sendm) as dgd.
      assert (pHigh: forall tx, ts < tx < S t -> slt In (dir Parent c a tx)).
      intros tx cond; assert (cond2: ts <= tx <= t) by omega;
      pose proof (cSendPGreaterState defParent cDef c_child sendm recvm cond2) as sth.
      rewrite fromX in sth.
      unfold slt in *; unfold sle in *; destruct (state c a (S ts));
      destruct (state c a ts); destruct (dir Parent c a tx); auto.

      assert (cLow: forall tx, ts < tx < S t -> slt (state c a tx) Mo).
      intros tx cond; assert (cond2: ts < tx <= t) by omega;
      pose proof (cSendCSmallerState defParent cDef c_child sendm recvm cond2) as sth.
      rewrite <- toM in sth.
      unfold slt in *; unfold sle in *; destruct (state c a (S ts));
      destruct (state c a tx); auto.



      assert (others: forall tx, ts < tx < S t ->
                                 forall c', defined c' -> c' <> c -> parent c' Parent ->
                                            sle (dir Parent c' a tx)
                                                match dir Parent c a tx with
                                                  | In => Mo
                                                  | Sh => Sh
                                                  | Mo => In
                                                end) by
          (intros tx _; apply (compatible defParent a tx cDef c_child)).
      assert (c'DirLow:
                forall tx,
                  ts < tx < S t -> 
                  forall c', defined c' -> c' <> c ->
                             parent c' Parent -> slt (dir Parent c' a tx) Mo).
      intros tx cond c' c'Def c'_ne_c c'_child.
      specialize (others tx cond c' c'Def c'_ne_c c'_child).
      specialize (pHigh tx cond).
      unfold slt in *; destruct (dir Parent c a tx); destruct (dir Parent c' a tx); auto.
      assert (c'Low: forall tx, ts < tx < S t -> forall c', defined c' ->
                                                   c' <> c ->
                                                   parent c' Parent ->
                                                   slt (state c' a tx) Mo).
      intros tx cond c' c'Def c'_ne_c c'_child.
      specialize (c'DirLow tx cond c' c'Def c'_ne_c c'_child).
      pose proof (conservative defParent c'Def c'_child a tx) as sig.
      unfold slt in *; destruct (dir Parent c' a tx); destruct (state c' a tx); auto.
      assert (allLow: forall tx, ts < tx < S t -> forall c0, defined c0 ->
                                           parent c0 Parent -> slt (state c0 a tx) Mo).
      intros tx cond c0 c0Def c0_child.
      assert (cache: {c0 = c} + {c0 <> c}) by (
                                        decide equality;
                                        decide equality).
      destruct cache as [eq|notEq].
      rewrite eq in *; apply (cLow tx cond).
      apply (c'Low tx cond c0 c0Def notEq c0_child).
      assert (noSt: forall ti, ts < ti < S t ->
                               forall ci li ii, defined ci -> ~ deqR ci li a St ii ti).
      unfold not; intros ti cond ci li ii ciDef deqSt.
      pose proof (deqLeaf deqSt) as leafCi.
      assert(ci_child: parent ci Parent) by (unfold leaf in *; unfold parent in *; auto).
      pose proof (processDeq deqSt) as mustMo.
      simpl in *.
      specialize (allLow ti cond ci ciDef ci_child).
      unfold sle in allLow; destruct (state ci a ti); auto; discriminate.
      pose proof (not_sle_slt dirHigh) as dirHigh'.
      pose proof (recvmCond defParent cDef c_child recvm) as fromM.
      rewrite <- fromM in dirHigh'.
      pose proof (toParent defParent cDef c_child sendm dirHigh') as dM.
      pose proof (fromChild defParent cDef c_child recvm dirHigh') as dM'.
      rewrite <- dM' in dM; rewrite dM.
      assert (le: ts <= t) by omega.
      pose proof (sendmFrom (st defParent cDef c_child) sendm) as fromM'.
      rewrite fromM' in dirHigh'.
      assert (stCond: sle Sh (state c a ts)) by
          (
            destruct (state c a ts); unfold sle in *; unfold slt in *; auto;
            discriminate).
      assert (cond2: forall c0, defined c0 -> parent c0 c -> sle (dir c c0 a ts) Sh) by
          (intros c0 c0Def c0_child; unfold parent in *; destruct c; destruct c0;
           assert (f: False) by auto; firstorder).
      pose proof (SIHt ts le c cDef (conj stCond cond2)) as useful.
      destruct (data c a ts).
      intros ti cond1.




      assert (cond3: 0 <= ti < ts \/ ts < ti < S t \/ ti = ts) by omega.
      destruct cond3 as [e1|[e2|e3]].
      generalize noSt e1 useful; clear; firstorder.
      generalize noSt e2 useful; clear; firstorder.
      unfold not; rewrite e3 in *; intros ci li ii ciDef deqSt.
      assert (eqOrNot: c = ci \/ c <> ci) by (decide equality ; decide equality ).
      destruct eqOrNot as [eq|notEq].
      rewrite eq in *.
      apply (deqImpNoSend ciDef deqSt defParent sendm).
      pose proof (processDeq deqSt) as stte.
      simpl in stte.
      pose proof (deqLeaf deqSt) as leafCi.
      assert (c'_child: parent ci Parent) by (unfold parent; unfold leaf in *; destruct ci;
                                              auto).
      pose proof (conservative defParent ciDef c'_child a ts) as cons.
      rewrite stte in cons.
      assert (dirM: dir Parent ci a ts = Mo) by (unfold sle in cons;
                                                 destruct (dir Parent ci a ts); firstorder).
      pose proof (compatible defParent a ts ciDef c'_child) as [_ otherCaches].
      rewrite dirM in otherCaches.
      specialize (otherCaches c cDef notEq c_child).
      assert (dirIn: dir Parent c a ts = In) by (unfold sle in *; destruct (dir Parent c a ts);
                                                 firstorder).
      pose proof (conservative defParent cDef c_child a ts) as cons2.
      rewrite dirIn in cons2.
      assert (cIn: state c a ts = In) by (unfold sle in cons2; destruct (state c a ts) ;
                                                               firstorder).
      rewrite cIn in stCond.
      unfold sle in stCond; firstorder.




      destruct useful as [cb [ib [tb [cbDef [tbTs [deqTb rest]]]]]].
      exists cb; exists ib; exists tb.
      assert (tsLeSt: ts <= S t) by omega.
      constructor. assumption.
      constructor. 
      assert (tb < S t) by omega.
      assumption.
      constructor. assumption.
      intros ti cond1.
      assert (cond3: tb < ti < ts \/ ts < ti < S t \/ ti = ts) by omega.
      destruct cond3 as [e1|[e2|e3]].
      generalize rest e1 noSt; clear; firstorder.
      generalize rest e2 noSt; clear; firstorder.

      unfold not; rewrite e3 in *; intros ci li ii ciDef deqSt.
      assert (eqOrNot: c = ci \/ c <> ci) by (decide equality ; decide equality ).
      destruct eqOrNot as [eq|notEq].
      rewrite eq in *.
      apply (deqImpNoSend ciDef deqSt defParent sendm).
      pose proof (processDeq deqSt) as stte.
      simpl in stte.
      pose proof (deqLeaf deqSt) as leafCi.
      assert (c'_child: parent ci Parent) by (unfold parent; unfold leaf in *; destruct ci;
                                              auto).
      pose proof (conservative defParent ciDef c'_child a ts) as cons.
      rewrite stte in cons.
      assert (dirM: dir Parent ci a ts = Mo) by (unfold sle in cons;
                                                 destruct (dir Parent ci a ts); firstorder).
      pose proof (compatible defParent a ts ciDef c'_child) as [_ otherCaches].
      rewrite dirM in otherCaches.
      specialize (otherCaches c cDef notEq c_child).
      assert (dirIn: dir Parent c a ts = In) by (unfold sle in *; destruct (dir Parent c a ts);
                                                 firstorder).
      pose proof (conservative defParent cDef c_child a ts) as cons2.
      rewrite dirIn in cons2.
      assert (cIn: state c a ts = In) by (unfold sle in cons2; destruct (state c a ts) ;
                                                               firstorder).
      rewrite cIn in stCond.
      unfold sle in stCond; firstorder.



      assert (contra: forall c, defined c -> parent c Parent ->
                                ~ ~ sle (dir Parent c a t) Sh) by
          firstorder.
      assert (contra2: forall c, defined c -> parent c Parent -> sle (dir Parent c a t) Sh) by
          (intros c cDef parentC;
           specialize (contra c cDef parentC);
           unfold sle in *; destruct (dir Parent c a t); auto).
      firstorder.

      destruct H as [H _].
      assert (noChildren: forall c, defined c -> parent c (Child n) -> False) by
         ( intros c c_parent; unfold parent in *; destruct c; auto ).
      destruct (classical (sle Sh (state (Child n) a t))) as [easy|hard].
      assert (ob: t <= t) by omega.
      assert (contra: forall c, defined c -> 
                                parent c (Child n) -> sle (dir (Child n) c a t) Sh) by
          (generalize noChildren; clear; firstorder).
      specialize (SIHt t ob (Child n) nDef (conj easy contra)).
      assert (c_child: parent (Child n) Parent) by (unfold parent; auto).
      pose proof (conservative defParent nDef c_child a t) as cons.
      pose proof (compatible defParent a t nDef c_child) as [_ dirLow].
      assert (others: forall c', defined c' -> 
                                 c' <> Child n -> leaf c' -> sle (state c' a t) Sh).
      intros c' c'Def c'_ne leaf_c'.
      assert (c'_child: parent c' Parent) by (unfold parent in *; unfold leaf in *; auto).
      specialize (dirLow c' c'Def c'_ne c'_child).
      pose proof (conservative defParent c'Def c'_child a t) as cons2.
      unfold sle in *; destruct (state c' a t); destruct (dir Parent c' a t);
      destruct (state (Child n) a t); destruct (dir Parent (Child n) a t); auto.
      assert (otherDeq: forall c', defined c' ->
                                   c' <> Child n -> forall li ii, ~ deqR c' li a St ii t).
      unfold not; intros c' c'Def c'_ne li ii deqSt.
      pose proof (deqLeaf deqSt) as c'_leaf.
      specialize (others c' c'Def c'_ne c'_leaf).
      pose proof (processDeq deqSt) as M; simpl in *.
      rewrite M in others; unfold sle in others; auto.
      destruct (classical (exists li ii, deqR (Child n) li a St ii t)) as
          [[li [ii deqSt]]|notEx].
      pose proof (deqImpData nDef deqSt) as newData.
      rewrite newData in *.
      exists (Child n); exists ii; exists t.
      assert (t_lt_St: t < S t) by omega.
      constructor. assumption.
      constructor. assumption.
      constructor. assumption.
      intros ti [c1 c2].
      assert (f: False) by omega.
      firstorder.
      assert (forall li ii, ~ deqR (Child n) li a St ii t) by firstorder.
      assert (noDeq: forall c0 li ii, defined c0 -> ~ deqR c0 li a St ii t).
      intros c0 li ii c0Def.
      assert ({c0 = Child n} + {c0 <> Child n}) by (decide equality; decide equality).
      destruct H1 as [eq|neq].
      rewrite eq in *.
      firstorder.
      firstorder.
      destruct (classical (data (Child n) a (S t) = data (Child n) a t)) as [eq|neq].
      rewrite eq.
      destruct (data (Child n) a t).
      intros ti cond.
      assert (mur1: 0 <= ti < t \/ ti = t) by omega.
      destruct mur1 as [easy2|hard].
      apply (SIHt ti easy2).
      rewrite hard in *; firstorder.
      destruct SIHt as [cb [ib [tb [cbDef [tbLt [deqSt rest]]]]]].
      exists cb; exists ib; exists tb.
      constructor. assumption.
      constructor. assert (tb < S t) by omega. assumption.
      constructor. assumption.
      intros ti cond.
      assert (mur1: tb < ti < t \/ ti = t) by omega.
      destruct mur1 as [easy2|hard].
      apply (rest ti easy2).
      rewrite hard in *; firstorder.
      pose proof (changeData nDef neq) as [[m [fromParent|toChild]]| deqSt].
      destruct fromParent as [p [pDef [p_parent [recvm fromM]]]].
      pose proof (recvImpMark recvm) as [ts [ts_le_t sendm]].
      pose proof (sendmFrom (dt pDef nDef p_parent) sendm) as fromM'.
      pose proof (cRecvRespPrevState pDef nDef p_parent recvm sendm) as same.
      rewrite <- fromM' in same.
      rewrite <- same in fromM.
      rewrite fromM in easy.
      unfold sle in easy; firstorder.
      destruct toChild as [c' [c'Def [c'_child _]]].
      unfold parent in c'_child; firstorder.
      destruct deqSt as [l [i deqSt]].
      pose proof (deqImpData nDef deqSt) as newData.
      rewrite newData.
      assert (e1: t < S t) by omega.
      assert (e2: forall ti, t < ti < S t -> forall ci li ii, defined ci ->
                                                              ~ deqR ci li a St ii ti) by
          (intros ti [cond1 cond2]; assert (f: False) by omega; firstorder).
      generalize e1 e2 nDef deqSt; clear; firstorder.
      assert (inv: state (Child n) a t = In) by
          (unfold sle in hard; destruct (state (Child n) a t); firstorder).
      clear hard.
      assert (upgrade: slt (state (Child n) a t) (state (Child n) a (S t))) by
          (rewrite inv; unfold slt in *; unfold sle in *; destruct (state (Child n) a (S t));
           auto).
      pose proof (slt_neq' upgrade) as neq'.
      assert (neq: state (Child n) a (S t) <> state (Child n) a t) by auto.
      assert (c_child: parent (Child n) Parent) by (unfold parent; auto).
      pose proof (change (st defParent nDef c_child) neq) as [[m markm] | [m recvm]].
      pose proof (cSendDowngrade defParent nDef c_child markm) as dwn.
      pose proof (slt_slti_false upgrade dwn) as f.
      firstorder.
      pose proof (recvImpMark recvm) as [ts [ts_le_t sendm]].

      remember (Child n) as c.


      pose proof @pSendCSameState as mui1.
      pose proof @pSendPSameState as mui2.


      pose proof (sendmFrom (dt defParent nDef c_child) sendm) as fromY.
      pose proof (sendmChange (dt defParent nDef c_child) sendm) as toT.
      pose proof (pSendUpgrade defParent nDef c_child sendm) as upd.

      assert (pHigh: forall tx, ts < tx < S t -> slt In (dir Parent c a tx)).
      intros tx cond. assert (cond2: ts < tx <= t) by omega.
      pose proof (pSendPSameState defParent nDef c_child sendm recvm cond2) as sth.
      rewrite <- toT in sth.
      rewrite <- sth in upd.
      unfold slt in *; destruct (dir Parent c a ts); destruct (dir Parent c a tx); auto.
      assert (cLow: forall tx, ts < tx < S t -> slt (state c a tx) Mo).
      intros tx cond. assert (cond2: ts <= tx <= t) by omega.
      pose proof (pSendCSameState defParent nDef c_child sendm recvm cond2) as sth.
      pose proof (conservative defParent nDef c_child a ts) as cons11.
      rewrite <- sth in cons11.
      unfold slt in *; unfold sle in *; destruct (state c a tx); destruct (dir Parent c a ts);
      destruct (dir Parent c a (S ts)); auto.




      assert (others: forall tx, ts < tx < S t ->
                                 forall c', defined c' -> c' <> c -> parent c' Parent ->
                                            sle (dir Parent c' a tx)
                                                match dir Parent c a tx with
                                                  | In => Mo
                                                  | Sh => Sh
                                                  | Mo => In
                                                end) by
          (intros tx _; apply (compatible defParent a tx nDef c_child)).
      assert (c'DirLow:
                forall tx,
                  ts < tx < S t -> 
                  forall c', defined c' ->
                             c' <> c -> parent c' Parent -> slt (dir Parent c' a tx) Mo).
      intros tx cond c' c'Def c'_ne_c c'_child.
      specialize (others tx cond c' c'Def c'_ne_c c'_child).
      specialize (pHigh tx cond).
      unfold slt in *; destruct (dir Parent c a tx); destruct (dir Parent c' a tx); auto.
      assert (c'Low: forall tx, ts < tx < S t -> forall c', defined c' ->
                                                   c' <> c ->
                                                   parent c' Parent ->
                                                   slt (state c' a tx) Mo).
      intros tx cond c' c'Def c'_ne_c c'_child.
      specialize (c'DirLow tx cond c' c'Def c'_ne_c c'_child).
      pose proof (conservative defParent c'Def c'_child a tx) as sig.
      unfold slt in *; destruct (dir Parent c' a tx); destruct (state c' a tx); auto.
      assert (allLow: forall tx, ts < tx < S t -> forall c0, defined c0 ->
                                           parent c0 Parent -> slt (state c0 a tx) Mo).
      intros tx cond c0 c0Def c0_child.
      assert (cache: {c0 = c} + {c0 <> c}) by (
                                        decide equality;
                                        decide equality).
      destruct cache as [eq|notEq].
      rewrite eq in *; apply (cLow tx cond).
      apply (c'Low tx cond c0 c0Def notEq c0_child).
      assert (noSt: forall ti, ts < ti < S t ->
                               forall ci li ii, defined ci -> ~ deqR ci li a St ii ti).
      unfold not; intros ti cond ci li ii ciDef deqSt.
      pose proof (deqLeaf deqSt) as leafCi.
      assert(ci_child: parent ci Parent) by (unfold leaf in *; unfold parent in *; auto).
      pose proof (processDeq deqSt) as mustMo.
      simpl in *.
      specialize (allLow ti cond ci ciDef ci_child).
      unfold sle in allLow; destruct (state ci a ti); auto; discriminate.

      
      pose proof (cRecvRespPrevState defParent nDef c_child recvm sendm) as prevState.
      pose proof (sendmFrom (dt defParent nDef c_child) sendm) as fromM.
      rewrite <- fromM in prevState.
      rewrite prevState in inv.
      pose proof (fromParent nDef defParent c_child recvm inv) as dM.
      pose proof (toChild nDef defParent c_child sendm inv) as dM'.
      rewrite dM' in dM; rewrite dM.
      assert (le: ts <= t) by omega.
      assert (stCond: sle Sh (state Parent a ts)) by
          (
           specialize (stEq ts); rewrite stEq; unfold sle; auto).
      pose proof (sendCCond defParent nDef c_child sendm) as [_ rest].
      pose proof (recvmChange (st defParent nDef c_child) recvm) as newState.
      rewrite <- newState in rest.
      assert (cond1: forall c0, defined c0 ->
                                c0 <> c -> parent c0 Parent -> sle (dir Parent c0 a ts) Sh) by
          (
          intros c0 c0Def cond c0_child; specialize (rest c0 c0Def cond c0_child);
          destruct (state c a (S t)); destruct (dir Parent c0 a ts);
          unfold sle in *; unfold slt in *; auto).
      rewrite inv in fromM.
      assert (cond2: forall c, defined c -> parent c Parent -> sle (dir Parent c a ts) Sh).
          intros c0 c0Def c0_child; assert (H2: {c0 = c} + {c0 <> c}) by 
                                 (decide equality; decide equality);
          destruct H2 as [easy | hard].
          rewrite easy in *; rewrite <- fromM; unfold sle; auto.
          apply (cond1 c0 c0Def hard c0_child).
      pose proof (SIHt ts le Parent defParent (conj stCond cond2)) as useful.
      destruct (data Parent a ts).
      intros ti condx.
      assert (cond3: 0 <= ti < ts \/ ts < ti < S t \/ ti = ts) by omega.
      destruct cond3 as [e1|[e2|e3]].
      generalize noSt e1 useful; clear; firstorder.
      generalize noSt e2 useful; clear; firstorder.
      rewrite e3 in *.
      pose proof (sendCCond defParent nDef c_child sendm) as [_ use].
      pose proof (pSendUpgrade defParent nDef c_child sendm) as upg.
      pose proof (sendmChange (dt defParent nDef c_child) sendm) as upg2.
      rewrite <- fromM in upg; rewrite upg2 in upg.
      assert (othersNot: forall c', defined c' -> c' <> c -> parent c' Parent ->
                                    dir Parent c' a ts <> Mo).
      intros c' c'Def c'_ne c'_child.
      specialize (use c' c'Def c'_ne c'_child).
      destruct (dir Parent c' a ts); destruct (to m); unfold slt in *; unfold sle in *; auto;
      discriminate.
      assert (allNot: forall c', defined c' -> parent c' Parent ->
                                 dir Parent c' a ts <> Mo).
      intros c'.
      assert (eqOrNot: {c' = c} + {c' <> c}) by (decide equality; decide equality).
      destruct eqOrNot as [eq|not].
      rewrite eq in *; rewrite <- fromM; intros; discriminate.
      generalize othersNot not; clear; firstorder.
      assert (allNot': forall c', defined c' -> parent c' Parent -> state c' a ts <> Mo).
      intros c' c'Def parentc'. specialize (allNot c' c'Def parentc').
      pose proof (conservative defParent c'Def parentc' a ts) as slee.
      unfold sle in *; destruct (state c' a ts); destruct (dir Parent c' a ts);
      auto; discriminate.
      unfold not; intros ci li ii ciDef. intros.
      pose proof (deqLeaf H0) as leafc.
      pose proof (processDeq H0) as procc.
      simpl in *.
      assert (parent ci Parent) by (unfold parent; destruct ci; auto).
      generalize allNot' ciDef procc H1; clear; firstorder.


      destruct useful as [cb [ib [tb [cbDef [tbTs [deqTb rest2]]]]]].
      exists cb; exists ib; exists tb.
      constructor. assumption.
      assert (tsLeSt: ts <= S t) by omega.
      constructor. 
      assert (tb < S t) by omega.
      assumption.
      constructor. assumption.
      intros ti condx.
      assert (cond3: tb < ti < ts \/ ts < ti < S t \/ ti = ts) by omega.
      destruct cond3 as [e1|[e2|e3]].
      generalize noSt e1 rest2; clear; firstorder.
      generalize noSt e2 rest2; clear; firstorder.
      rewrite e3 in *.
      pose proof (sendCCond defParent nDef c_child sendm) as [_ use].
      pose proof (pSendUpgrade defParent nDef c_child sendm) as upg.
      pose proof (sendmChange (dt defParent nDef c_child) sendm) as upg2.
      rewrite <- fromM in upg; rewrite upg2 in upg.
      assert (othersNot: forall c', defined c' -> c' <> c -> parent c' Parent ->
                                    dir Parent c' a ts <> Mo).
      intros c' c'Def c'_ne c'_child.
      specialize (use c' c'Def c'_ne c'_child).
      destruct (dir Parent c' a ts); destruct (to m); unfold slt in *; unfold sle in *; auto;
      discriminate.
      assert (allNot: forall c', defined c' -> parent c' Parent ->
                                 dir Parent c' a ts <> Mo).
      intros c'.
      assert (eqOrNot: {c' = c} + {c' <> c}) by (decide equality; decide equality).
      destruct eqOrNot as [eq|not].
      rewrite eq in *; rewrite <- fromM; intros; discriminate.
      generalize othersNot not; clear; firstorder.
      assert (allNot': forall c', defined c' -> parent c' Parent -> state c' a ts <> Mo).
      intros c' c'Def parentc'. specialize (allNot c' c'Def parentc').
      pose proof (conservative defParent c'Def parentc' a ts) as slee.
      unfold sle in *; destruct (state c' a ts); destruct (dir Parent c' a ts);
      auto; discriminate.
      unfold not; intros ci li ii ciDef. intros.
      pose proof (deqLeaf H0) as leafc.
      pose proof (processDeq H0) as procc.
      simpl in *.
      assert (parent ci Parent) by (unfold parent; destruct ci; auto).
      generalize allNot' procc ciDef H1; clear; firstorder.
    Qed.

  End ForAddr.

  Theorem latestValue:
  forall {c a t}, defined c ->
    leaf c ->
    sle Sh (state c a t) ->
    match data c a t with
      | Initial => forall {ti}, 0 <= ti < t -> forall {ci li ii}, 
                                                 defined ci -> ~ deqR ci li a St ii ti
      | Store lb =>
        exists cb ib tb, defined cb /\ tb < t /\ deqR cb lb a St ib tb /\
                         forall {ti}, tb < ti < t -> forall {ci li ii},
                                                       defined ci -> ~ deqR ci li a St ii ti
    end.
  Proof.
    intros c a t cDef leafC more.
    assert (sth: forall c', defined c' -> parent c' c -> sle (dir c c' a t) Sh) by
        ( intros c' c'Def c'_child; unfold parent in *; unfold leaf in *;
                                    destruct c; destruct c';
          firstorder).
    pose proof (allLatestValue cDef (conj more sth)) as useful.
    assumption.
  Qed.

End LatestValueTheorems.