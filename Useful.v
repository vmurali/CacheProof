Require Import Arith Omega.

Section classical.
  Variable dec : forall P, P \/ ~ P.

  Section minExists.
    Context {P : nat -> Prop}.
    Lemma leastOrNone x :
      (exists x, P x /\ forall y, y < x -> ~ P y) \/
      forall y, y <= x -> ~ P y.
    Proof.
      induction x.
      destruct (dec (P 0)) as [P0 | notP0].
      left; exists 0; constructor; [intuition | intros; omega].
      right; intros y le; assert (yEq0: y = 0) by omega; rewrite yEq0 in *; intuition.
      destruct IHx as [ex | notEx].
      left; assumption.
      destruct (dec (P (S x))) as [PSx | notPSx].
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
      destruct (dec (t <= x)).
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
      destruct (dec (x <= t)) as [xLeT | xGtT].
      firstorder.
      assert (hyp: S t <= x <= max) by omega.
      firstorder.
    Qed.
  End maxExists.

End classical.
