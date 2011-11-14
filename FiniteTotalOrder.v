Set Implicit Arguments.

Require Import CpdtTactics.

Section FiniteTotalOrder.
Variable FinTOrd : Set.

Inductive lt : FinTOrd -> FinTOrd -> Prop := lt_const : forall x y : FinTOrd, lt x y.
Inductive gt : FinTOrd -> FinTOrd -> Prop := gt_const : forall x y : FinTOrd, gt x y.

Notation "x < y" := (lt x y).
Notation "x > y" := (gt x y).

Hypothesis lt_gt : forall x y, x < y -> y > x.
Hypothesis gt_lt : forall x y, y > x -> x < y.

Hypothesis compare : forall x y, {x < y} + {x = y} + {x > y}.

Variables min max : FinTOrd.

Notation "x <= y" := (lt x y \/ x = y).
Notation "x >= y" := (gt x y \/ x = y).

Hypothesis minIsMin : forall x, min <= x.
Hypothesis maxIsMax : forall x, max >= x.

Theorem le_ge : forall x y, x <= y -> y >= x.
  assert (forall x y, x < y -> y > x) by apply (lt_gt); crush.
Qed.

Theorem ge_le : forall x y, y >= x -> x <= y.
  assert (forall x y, y > x -> x < y) by apply (gt_lt); crush.
Qed.

Theorem minIsMin' : forall x, x >= min.
  Hint Resolve le_ge.
  auto.
Qed.

Theorem maxIsMax' : forall x, x <= max.
  Hint Resolve ge_le.
  auto.
Qed.

End FiniteTotalOrder.