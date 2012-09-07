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
      destruct (dec (P 0)).
      left; exists 0; crush.
      right; crush; assert (y = 0); crush.
      destruct IHx.
      left; assumption.
      destruct (dec (P (S x))).
      left.
      exists (S x).      
      crush.
      apply (H y); crush.
      right.
      intros.
      assert (y <= x \/ y = S x) by crush.
      crush.
      firstorder.
    Qed.

    Theorem minExists : (exists x, P x) -> (exists x, P x /\ forall y, y < x -> ~ P y).
    Proof.
      intros.
      destruct H.
      pose proof (leastOrNone x).
      destruct H0.
      assumption.
      assert (x <= x) by crush.
      specialize (H0 x H1).
      crush.
    Qed.

    Theorem minExistsPower {x}: P x -> (exists y, y <= x /\ P y /\ forall z, z < y -> ~ P z).
    Proof.
      intros.
      assert (exists x, P x) by (exists x; crush).
      pose proof (minExists H0).
      clear H0.
      destruct H1.
      destruct H0.
      exists x0.
      crush.
      destruct (dec (x0 <= x)).
      crush.
      assert (x < x0) by crush.
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

  Section notExistForallNot.
    Context {P Q R: nat -> nat -> Prop}.
    Lemma notExistForallNot : (~ exists x y, P x y /\ Q x y /\ R x y) -> forall x y, P x y -> Q x y -> ~ R x y.
    Proof.
      intros.
      destruct (dec (exists x y, P x y /\ Q x y /\ R x y)).
      crush.
      firstorder.
    Qed.
 End notExistForallNot.

  Section notForallNotImpExists.
    Context {P Q: nat -> Prop}.
    Lemma notForallNotImpExists: ~ (forall x, P x -> ~ Q x) -> exists x, P x /\ Q x.
    Proof.
      intros.
      destruct (dec (exists x, P x /\ Q x)).
      crush.
      firstorder.
    Qed.
  End notForallNotImpExists.
End classical.
