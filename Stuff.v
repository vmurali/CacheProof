Require Import CpdtTactics.

Theorem mul0 m n (m1 : m > 1) (n1 : n > 1) : m * n > 1.
  induction m.
  crush.
  induction n.
  crush.
  assert (m <> 1 \/ m = 1) by decide equality.
  assert (n <> 1 \/ n = 1) by decide equality.
  assert (m > 1 \/ m = 1) by crush.
  assert (n > 1 \/ n = 1) by crush.
  destruct H1; destruct H2; crush.
Qed.

Theorem mul1 m n (pf : m * n = 1) : m = 1 /\ n = 1.
  assert (m > 1 -> n > 1 -> m * n > 1) by (apply mul0).
  assert (m = 1 \/ m <> 1) by decide equality.
  assert (n = 1 \/ n <> 1) by decide equality.
  assert (m <> 0) by crush.
  assert (n <> 0) by crush.
  assert (m = 1 \/ m > 1) by crush.
  assert (n = 1 \/ n > 1) by crush.
  crush.
Qed.
