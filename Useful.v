Require Import Arith Omega Coq.Logic.Classical List.

Section minExists.
  Context {P : nat -> Prop}.
  Lemma leastOrNone x :
    (exists x, P x /\ forall y, y < x -> ~ P y) \/
                                                forall y, y <= x -> ~ P y.
  Proof.
    induction x.
    destruct (classic (P 0)) as [P0 | notP0].
    left; exists 0; constructor; [intuition | intros; omega].
    right; intros y le; assert (yEq0: y = 0) by omega; rewrite yEq0 in *; intuition.
    destruct IHx as [ex | notEx].
    left; assumption.
    destruct (classic (P (S x))) as [PSx | notPSx].
    left; exists (S x); constructor; [assumption | intros y lt; assert (y <= x) by omega; firstorder].
    right; intros; assert (opts: y <= x \/ y = S x) by omega. destruct opts; [firstorder | congruence].
  Qed.

  Theorem minExists (ex: exists x, P x) : (exists x, P x /\ forall y, y < x -> ~ P y).
  Proof.
    destruct ex as [x Px].
    pose proof (leastOrNone x) as exOrNot.
    destruct exOrNot.
    assumption.
    assert (eq: x <= x) by omega.
    firstorder.
  Qed.

  Theorem minExistsPower {x} (Px: P x): (exists y, y <= x /\ P y /\ forall z, z < y -> ~ P z).
  Proof.
    assert (ex: exists x, P x) by firstorder.
    pose proof (minExists ex) as exMin.
    clear ex.
    destruct exMin as [t rest].
    destruct rest as [Pt notBelow].
    exists t.
    intuition.
    destruct (classic (t <= x)).
    assumption.
    assert (x < t) by omega.
    firstorder.
  Qed.
End minExists.

Section maxExists.
  Context {P: nat -> Prop}.
  Theorem maxExists {max} (exPx: exists x, x <= max /\ P x): exists x, x <= max /\ P x /\ forall y, S x <= y <= max -> ~ P y.
  Proof.
    destruct exPx as [x rest].
    destruct rest as [xLeMax Px].
    pose (fun x => P (max - x)) as Q.
    pose (max - x) as diff.
    assert (xEq: max - (max - x) = x) by omega.
    assert (Qdiff: Q diff) by (unfold Q; unfold diff; rewrite xEq in *; intuition).
    assert (exQdiff: exists d, Q d) by (exists diff; intuition).
    pose proof (minExists exQdiff) as qMin.
    destruct qMin as [y rest].
    destruct rest as [leDiff noLower].
    exists (max - y).
    constructor.
    omega.
    constructor.
    auto.
    intros y0 complx.
    assert (lt: max - y0 < y) by omega.
    unfold Q in noLower.
    specialize (noLower (max - y0) lt).
    assert (eq: max - (max - y0) = y0) by (assert (e: y0 <= max) by omega; generalize e; clear; intuition).
    rewrite eq in noLower.
    intuition.
  Qed.

  Theorem maxExists' {maxi} (exPx: exists x, x < maxi /\ P x): exists x, x < maxi /\ P x /\ forall y, x < y < maxi -> ~ P y.
  Proof.
    destruct exPx as [x [contra Px]].
    destruct maxi.
    omega.
    assert (exPx': exists x, x <= maxi /\ P x) by (exists x; constructor; [omega | intuition]).
    pose proof (maxExists exPx') as this.
    destruct this as [x' [cond1 [Px' forally]]].
    exists x'.
    constructor.
    omega.
    constructor.
    intuition.
    intros y cond.
    assert (S x' <= y <= maxi) by omega.
    firstorder.
  Qed.

  Theorem maxExistsPower {max x} (xLeMax: x <= max) (Px: P x) : (exists y, x <= y <= max /\ P y /\ forall z, S y <= z <= max -> ~ P z).
  Proof.
    assert (exX: exists x, x <= max /\ P x) by firstorder.
    pose proof (maxExists exX) as maxExX.
    destruct maxExX as [t rest].
    destruct rest as [tLeMax rest].
    destruct rest as [Pt noLower].
    exists t.
    destruct (classic (x <= t)) as [xLeT | xGtT].
    firstorder.
    assert (hyp: S t <= x <= max) by omega.
    firstorder.
  Qed.
End maxExists.

Section Induction.
  Context {P: nat -> Type}.
  Hypothesis case_0: P 0.
  Hypothesis case_n: forall {t}, (forall ti, ti <= t -> P ti) -> P (S t).

  Theorem ind t: P t.
  Proof.
    assert (q0: forall ti, ti <= 0 -> P ti) by 
        (intros ti ti_le_0; assert (rew: ti = 0) by omega; rewrite rew; assumption).
    assert (qIHt: forall t, (forall ti, ti <= t -> P ti) -> (forall ti, ti <= S t -> P ti)).
    intros t0 lt_t0.
    specialize (case_n t0 lt_t0).
    intros ti ti_le_S_t0.
    pose proof (le_lt_eq_dec ti (S t0) ti_le_S_t0) as options.
    destruct options as  [hyp|new].
    firstorder.
    rewrite new.
    assumption.
    assert (Hyp: forall t, (forall ti, ti <= t -> P ti)) by (
                                                            induction t0; firstorder).
    specialize (Hyp t t).
    assert (fct: t <= t) by omega.
    firstorder.
  Qed.
End Induction.


    Theorem listNeq: forall {A} (x: A) l, x :: l <> l.
      unfold not; intros A x l eq.
      assert (H: length (x :: l) = length l) by (f_equal; assumption).
      unfold length in *.
      remember ((fix length (l : list A) : nat :=
            match l with
            | nil => 0
            | _ :: l' => S (length l')
            end) l) as y.
      generalize H; clear.
      intros neq.

      assert (H: S y <> y) by auto.
      firstorder.
    Qed.

    Theorem listCond1: forall {A} (l: list A), l <> nil -> length l = S (length (tl l)).
    Proof.
      intros A l lgd.
      unfold tl.
      destruct l.
      firstorder.
      unfold length.
      reflexivity.
    Qed.

    Theorem listCond2: forall {A} (l: list A), l <> nil -> length l = S (length (removelast l)).
    Proof.
      intros A l lgd.
      induction l.
      firstorder.
      destruct l.
      unfold length.
      reflexivity.
      unfold length in *.
      f_equal.
      assert (H: removelast (a :: a0 :: l) = a :: removelast (a0 :: l)) by
          (
            unfold removelast;
            reflexivity).
      rewrite H; clear H.
      assert (H: a0 :: l <> nil) by discriminate.
      specialize (IHl H).
      assumption.
    Qed.

    Theorem notInRemove: forall {A} (a: A) l, In a (removelast l) -> In a l.
    Proof.
      intros A a l inl.
      induction l.
      unfold removelast in *; simpl in *.
      assumption.
      unfold removelast in inl.
      destruct l.
      unfold In in *.
      firstorder.
      unfold In in inl.
      destruct inl.
      unfold In.
      left.
      assumption.
      specialize (IHl H).
      unfold In.
      right.
      assumption.
    Qed.

    Theorem notInTail: forall {A} (a: A) l, In a (tl l) -> In a l.
    Proof.
      intros A a l inl.
      destruct l.
      unfold tl in inl; assumption.
      unfold tl in inl.
      unfold In.
      right.
      assumption.
    Qed.

    Theorem eachProd: forall {A B} {a b: A} {c d: B}, (a, c) = (b, d) -> a = b /\ c = d.
    Proof.
      intros A B a b c d eq.
      injection eq.
      auto.
    Qed.

    Theorem combNil: forall {A} B (l : list A), combine l (@nil B) = nil.
    Proof.
      intros A B l.
      destruct l; unfold combine; reflexivity.
    Qed.

    Theorem removeCombine: forall {A B} (l1: list A) (l2: list B),
                             removelast (combine l1 l2) = combine (removelast l1)
                                                                  (removelast l2).
    Proof.
      intros A B l1.
      induction l1.
      intros l2.
      reflexivity.
      intros l2.
      destruct l2.
      simpl.
      pose proof (combNil B match l1 with
           | nil => nil
           | _ :: _ => a :: removelast l1
           end) as sth.
      rewrite sth.
      reflexivity.
      unfold combine.
      fold (combine l1 l2).
      fold (combine (removelast (a::l1)) (removelast (b::l2))).
      unfold removelast.
      fold (removelast (a :: l1)).
      fold (removelast (b :: l2)).
      fold (removelast (combine l1 l2)).
      destruct l1.
      reflexivity.
      destruct l2.
      reflexivity.
      assert (H: combine (a0::l1) (b0::l2) <> nil).
      unfold not; intros.
      unfold combine in H.
      discriminate.
      remember (combine (a0::l1) (b0::l2)) as  comb.
      destruct comb.
      firstorder.
      rewrite Heqcomb.
      clear Heqcomb p comb H.
      specialize (IHl1 (b0::l2)).
      rewrite IHl1.
      reflexivity.
    Qed.

    Theorem lenEqLastCombine: forall {A B} (a: A) (la: list A) (da: A), la <> nil ->
                                     a = last la da ->
                                     forall (b: B) (lb: list B) (db: B),
                                       length la = length lb -> b = last lb db ->
                                       In (a, b) (combine la lb).
    Proof.
      intros A B a la da lanil lasta.
      induction la.
      firstorder.
      intros b lb db lenEq lastb.
      destruct lb.
      unfold length in lenEq.
      discriminate.
      unfold length in lenEq.
      injection lenEq.
      clear lenEq; intros lenEq.
      destruct la.
      destruct lb.
      unfold last in lasta.
      unfold last in lastb.
      rewrite lasta; rewrite lastb.
      unfold In; unfold combine; simpl.
      left; reflexivity.
      discriminate.
      destruct lb.
      discriminate.
      assert (H: a1 :: la <> nil) by discriminate.
      specialize (IHla H lasta b (b1 :: lb) db lenEq lastb).
      unfold combine; unfold In.
      right.
      apply IHla.
    Qed.

    Theorem eqLen: forall {A B} (la: list A) (lb: list B), length la = length lb ->
                                                           length (removelast la) =
                                                           length (removelast lb).
    Proof.
      intros A B la.
      induction la.
      intros lb cond.
      destruct lb.
      reflexivity.
      unfold length in cond.
      discriminate.
      intros lb cond.
      destruct la.
      destruct lb.
      unfold removelast.
      reflexivity.
      unfold length in cond.
      assert (sim: 1 = S (length lb)) by (apply cond).
      injection sim.
      clear sim cond; intros sim.
      destruct lb.
      reflexivity.
      unfold length in sim.
      discriminate.
      destruct lb.
      simpl in cond.
      discriminate.
      injection cond as cond2.
      specialize (IHla lb cond2).
      destruct lb.
      unfold length in cond2.
      discriminate.
      unfold removelast.
      unfold length.
      f_equal.
      assumption.
    Qed.
