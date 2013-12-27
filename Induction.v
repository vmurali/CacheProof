Require Import Omega.
Require Import Useful.

Section Induction.
  Variable classical: forall P, P \/ ~ P.
  Context {P: nat -> Prop}.
  Hypothesis case_0: P 0.
  Hypothesis case_n: forall {t}, (forall ti, ti <= t -> P ti) -> P (S t).
  Theorem ind t: P t.
  Proof.
    assert (q0: forall ti, ti <= 0 -> P ti) by 
        (intros ti ti_le_0; assert (rew: ti = 0) by omega; rewrite rew; assumption).
    assert (qIHt: forall t, (forall ti, ti <= t -> P ti) -> (forall ti, ti <= S t -> P ti)).
    intros t0 lt_t0.
    specialize (case_n t0 lt_t0).
    intros ti ti_lt_S_t0.
    assert (options: ti <= t0 \/ ti = S t0) by omega.
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