Require Import DataTypes.
Require Import Channel.
Require Import Cache.

Module Type CompatBehavior (dt: DataTypes) (ch: ChannelPerAddr dt).
  Import dt ch.
  Section Node.
    Context {n: Cache}.
    Context {a: Addr}.
    Context {t: Time}.
    Axiom sendPCond: forall {p}, parent n = p ->
                                 forall {m},
                                   mark mch n p a t m ->
                                   forall {c}, parent c = n -> dir n c a t <= to m.
    Axiom sendCCond: forall {c},
                       parent c = n ->
                       forall {m},
                         mark mch n c a t m ->
                         to m <= state n a t /\
                         (to m = Mo ->
                          forall {c'}, c' <> c -> parent c' = n -> dir n c' a t = In)
                         /\ (to m <> Mo ->
                             forall {c'}, c' <> c -> parent c' = n -> dir n c' a t < Mo).
    Axiom oneRespC: forall {c1 c2},
                      parent c1 = n -> parent c2 = n ->
                      forall {m1}, (mark mch n c1 a t m1 \/ recv mch c1 n a t m1) ->
                                   forall {m2},
                                     (mark mch n c2 a t m2 \/ recv mch c2 n a t m2) -> c1 = c2.
    Axiom respPNoRespC: forall {p}, parent n = p ->
                                    forall {m},
                                      (mark mch n p a t m \/ recv mch p n a t m) ->
                                      forall {c}, parent c = n -> forall mc,
                                        ~ (mark mch n c a t mc \/ recv mch c n a t mc).
    Axiom noParentSame: (forall {p}, parent n <> p) -> state n a (S t) = state n a t.
  End Node.
  Axiom oneParent: forall {n p1 p2}, parent n = p1 -> parent n = p2 -> p1 = p2.
  Axiom initCompat:
    forall {n c}, parent c = n -> forall {a}, dir n c a 0 = In.
End CompatBehavior.

Module Type CompatTheorem (dt: DataTypes) (ch: ChannelPerAddr dt).
  Import dt ch.
  Parameter compatible:
    forall {n a t c}, parent c = n ->
                      dir n c a t <= state n a t /\
                      (dir n c a t = Mo ->
                       forall {c'}, c' <> c -> parent c' = n -> dir n c' a t = In).
End CompatTheorem.

Module mkCompat (dt: DataTypes) (ch: ChannelPerAddr dt) (cb: CompatBehavior dt ch) (ba: BehaviorAxioms dt ch)
                : CompatTheorem dt ch.
  Module mbt := mkBehaviorTheorems dt ch ba.
  Import dt ch cb ba mbt.

  Theorem compatible:
    forall {n a t c}, parent c = n ->
                      dir n c a t <= state n a t /\
                      (dir n c a t = Mo ->
                       forall {c'}, c' <> c -> parent c' = n -> dir n c' a t = In).
  Proof.
    intros n a.
    induction t.
    intros c cond.
    constructor.
    pose proof @initCompat n c cond a as c2.
    rewrite c2.
    unfold In.
    omega.
    intros dirM c' c'_ne_c c'Child.
    pose proof @initCompat n c' c'Child a as c2.
    assumption.
    destruct (classical (exists p m,
                           parent n = p /\
                           (mark mch n p a t m \/ recv mch p n a t m))) as [respP|noRespP].
    destruct respP as [p [m [p_parent markOrRecv]]].
    pose proof @respPNoRespC n a t p p_parent m markOrRecv as noChild.
    assert (sameDir: forall c, parent c = n -> dir n c a t = dir n c a (S t)).
    intros c c_child.
    pose proof respPNoRespC p_parent markOrRecv c_child as noRespC.
    assert (st_eq: dir n c a t = dir n c a (S t)).
    assert (stuff: {dir n c a t = dir n c a (S t)} + {dir n c a t <> dir n c a (S t)})
      by decide equality.
    destruct stuff as [eq|neq].
    assumption.
    assert (neq': dir n c a (S t) <> dir n c a t) by auto.
    pose proof (change (@dt n c) neq') as resp.
    generalize noRespC resp; clear; firstorder.
    assumption.
    intros c c_child.
    pose proof (sameDir c c_child) as dir_eq.
    rewrite <- dir_eq in *.
    assert (sameC': forall c', c' <> c -> parent c' = n -> dir n c' a t = dir n c' a (S t))
           by (generalize sameDir; clear; firstorder).
    destruct markOrRecv as [markm | recvm].
    pose proof (sendPCond p_parent markm c_child) as dir_le_to_m.
    pose proof (sendmChange (@st p n) markm) as sth.
    constructor.
    omega.
    intros.
    specialize (sameC' c' H0 H1).
    rewrite <- sameC'.
    generalize IHt c c_child H H0 H1; clear; firstorder.
    constructor.
    pose proof (cRecvUpgrade recvm) as st_lt.
    generalize (IHt c c_child) st_lt; clear; intros; omega.
    intro dirMo.
    intros c' c'Ne c'_child.
    specialize (sameDir c' c'_child).
    rewrite <- sameDir.
    generalize IHt c'_child c'Ne dirMo c_child; clear; firstorder.
    assert (noRespP': forall p, parent n = p -> ~ ((exists m, mark mch n p a t m)
                                                   \/ (exists m, recv mch p n a t m)))
      by (
          generalize noRespP; clear; firstorder).
    assert (st_eq: state n a (S t) = state n a t).
    destruct (classical (exists p, parent n = p)) as [[p p_parent] | nop].
    specialize (noRespP' p p_parent).
    assert (eqOrNot: {state n a (S t) = state n a t} + {state n a (S t) <> state n a t}) by
        decide equality.
    destruct eqOrNot as [eq|not].
    assumption.
    pose proof (noRespP' (change (@st p n) not)) as done.
    firstorder.
    assert (noP: forall p, ~ parent n = p) by firstorder.
    apply (@noParentSame n a t noP).
    rewrite st_eq in *.

    destruct (classical (exists c m, parent c = n /\ (mark mch n c a t m \/ recv mch c n a t m))) as [ex|notEx].
    destruct ex as [c [m [c_child resp]]].
    assert (noneElse: forall c', c' <> c -> parent c' = n ->
                       ~ ((exists m, mark mch n c' a t m) \/ exists m, recv mch c' n a t m)).
    intros c' c'_ne_c c'_child.
    destruct (classical (exists m', mark mch n c' a t m' \/ recv mch c' n a t m'))
      as [ex|notEx].
    destruct ex as [m' sth].
    pose proof (oneRespC c_child c'_child resp sth) as sth2.
    assert (c' = c) by auto.
    firstorder.
    firstorder.
    assert (stEq: forall c', c' <> c -> parent c' = n -> dir n c' a (S t) = dir n c' a t).
    intros c' c'_ne_c c'_child.
    specialize (noneElse c' c'_ne_c c'_child).
    assert (eqOrNot: {dir n c' a (S t) = dir n c' a t} 
                     + {dir n c' a (S t) <> dir n c' a t}) by decide equality.
    destruct eqOrNot as [eq|not].
    assumption.
    specialize (noneElse (change (@dt n c') not)).
    firstorder.
    intros c0 c0_child.
    destruct (classical (c0 = c)) as [c0_eq_c|c0_ne_c].
    rewrite c0_eq_c in *.
    destruct resp as [markm | recvm].
    pose proof (sendmChange (@dt n c) markm) as toM.
    rewrite toM.
    pose proof (sendCCond c_child markm) as [stuff [rest _]].
    constructor.
    intuition.
    intros.
    specialize (stEq c' H0 H1).
    rewrite stEq.
    specialize (rest H c' H0 H1).
    intuition.
    pose proof (pRecvDowngrade recvm) as sth_gt.
    constructor.
    destruct (IHt c c_child) as [good bad].
    omega.
    intro sth.
    pose proof (@maxDir n c a t c_child).
    assert False by omega.
    firstorder.
    pose proof (stEq c0 c0_ne_c c0_child) as stEq'.
    rewrite stEq'.
    constructor.
    generalize IHt c0_child; clear; firstorder.
    intros dirC0 c' c'_ne_c0 c'_child.
    destruct (classical (c' = c)) as [c'_eq_c | c'_ne_c].
    rewrite c'_eq_c in *.
    destruct resp as [markm | recvm].
    pose proof (sendCCond c_child markm) as [_ [toM notToM]].
    assert (eqOrNot: {to m = Mo} + {to m <> Mo}) by decide equality.
    destruct eqOrNot as [eq|not].
    assert (c_ne_c0: c0 <> c) by auto.
    specialize (toM eq c0 c_ne_c0  c0_child).
    rewrite dirC0 in toM.
    discriminate.
    assert (c_ne_c0: c0 <> c) by auto.
    specialize (notToM not c0 c_ne_c0 c0_child).
    assert False by omega.
    intuition.
    pose proof (pRecvDowngrade recvm) as sth_gt.
    assert (gtz: dir n c a t > 0) by omega.
    pose proof (IHt c0 c0_child) as [_ sth1].
    specialize (sth1 dirC0 c c'_ne_c0 c_child).
    unfold In in *.
    omega.
    specialize (stEq c' c'_ne_c c'_child).
    rewrite stEq.
    generalize IHt c0_child dirC0 c'_ne_c0 c'_child; clear; firstorder.
    assert (same: forall c, parent c = n -> dir n c a (S t) = dir n c a t).
    intros c c_child.
    assert (eqOrNot: {dir n c a (S t) = dir n c a t} + {dir n c a (S t) <> dir n c a t})
           by decide equality.
    destruct eqOrNot as [eq|not].
    assumption.
    pose proof (change (@dt n c) not) as ppp.
    generalize notEx c_child ppp; clear; firstorder.
    intros c c_child.
    constructor.
    specialize (same c c_child).
    rewrite same.
    generalize IHt c_child; clear; firstorder.
    intros.
    pose proof (same c' H1) as dunk.
    rewrite dunk.
    pose proof (same c c_child) as dukn.
    rewrite dukn in *.
    generalize IHt c_child H H0 H1; clear; firstorder.
  Qed.
End mkCompat.