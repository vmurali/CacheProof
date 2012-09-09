Axiom cheat : forall t, t.

Require Import CpdtTactics.

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
      left; exists 0; crush.
      right; intros y le; assert (y = 0); crush.
      destruct IHx as [ex | notEx].
      left; assumption.
      destruct (dec (P (S x))) as [PSx | notPSx].
      left; exists (S x); constructor; [assumption | intros y lt; assert (y <= x) by crush; firstorder].
      right; intros; assert (y <= x \/ y = S x) by crush; crush; firstorder.
    Qed.

    Theorem minExists (ex: exists x, P x) : (exists x, P x /\ forall y, y < x -> ~ P y).
    Proof.
      destruct ex as [x Px].
      pose proof (leastOrNone x) as exOrNot.
      destruct exOrNot.
      assumption.
      assert (eq: x <= x) by crush.
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
      crush.
      destruct (dec (t <= x)).
      assumption.
      assert (x < t) by crush.
      firstorder.
    Qed.
  End minExists.

  Section maxExists.
    Context {P : nat -> Prop}.
    Theorem maxExists : forall {max}, (exists x, x <= max /\ P x) -> (exists x, x <= max /\ P x /\ forall y, S x <= y <= max -> ~ P y).
    Proof.
      intros.
      destruct H.
      destruct H.
      pose (fun x => P (max - x)) as Q.
      pose (max - x) as diff.
      assert (max - (max - x) = x) by crush.
      assert (Q diff).
      unfold Q.
      unfold diff.
      crush.
      assert (exists d, Q d /\ forall y, y < d -> ~ Q y).
      assert (exists diff, Q diff) by (exists diff; crush).
      apply minExists; crush.
      destruct H3.
      destruct H3.
      exists (max - x0).
      crush.
      specialize (H4 (max -y)).
      assert (max - y < x0) by crush.
      specialize (H4 H5).
      unfold Q in H4.
      assert (max - (max - y) = y) by crush.
      rewrite H9 in H4.
      crush.
    Qed.

    Theorem maxExistsPower {max x}: x <= max -> P x -> (exists y, x <= y <= max /\ P y /\ forall z, S y <= z <= max -> ~ P z).
    Proof.
      intros.
      assert (exists x, x <= max /\ P x) by (exists x; crush).
      pose proof (maxExists H1).
      destruct H2.
      destruct H2.
      destruct H3.
      exists x0.
      destruct (dec (x <= x0)).
      crush.
      assert (S x0 <= x <= max) by crush.
      firstorder.
    Qed.
  End maxExists.

  Section doubleMinExists.
    Context {Q : nat -> nat -> Prop}.
    Variable exi : exists x y, Q x y.

    Definition temp :
      exists xmin, (exists ymin, Q xmin ymin /\ forall y', y' < ymin -> ~ (Q xmin y')) /\
        forall x', x' < xmin -> ~ (exists y, Q x' y) :=
          let simp := minExists exi in
            match simp with
              | ex_intro x p_m => match p_m with
                                    | conj a b => ex_intro
                                      (fun xmin => (exists ymin, Q xmin ymin /\ forall y', y' < ymin -> ~ (Q xmin y')) /\ forall x', x' < xmin -> ~ (exists y, Q x' y))
                                      x (conj (minExists a) b)
                                  end
            end.

    Theorem minExists2 :
      exists xmin ymin, Q xmin ymin /\ (forall x', x' < xmin -> ~ (exists y, Q x' y)) /\
        forall y', y' < ymin -> ~ (Q xmin y').
    Proof.
      pose proof temp.
      destruct H.
      destruct H.
      destruct H.
      exists x.
      exists x0.
      crush.
    Qed.
      
  End doubleMinExists.

  Lemma notExistForallNot {P Q R: nat -> nat -> Prop} : (~ exists x y, P x y /\ Q x y /\ R x y) -> forall x y, P x y -> Q x y -> ~ R x y.
  Proof.
    intros.
    destruct (dec (exists x y, P x y /\ Q x y /\ R x y)).
    crush.
    firstorder.
  Qed.
End classical.
