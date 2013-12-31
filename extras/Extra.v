Require Import Tree.

Require Import Omega.
Fixpoint eqListNat l1 l2 :=
  match l1, l2 with
    | nil, nil => true
    | nil, y :: ys => false
    | x :: xs, nil => false
    | x :: xs, y :: ys => andb (beq_nat x y) (eqListNat xs ys)
  end.

Fixpoint eqTree t1 t2 :=
  match t1, t2 with
    | C n1 l1, C n2 l2 => andb (eqListNat n1 n2)
        ((fix eqListTree l1 l2 :=
          match l1, l2 with
            | nil, nil => true
            | nil, y :: ys => false
            | x :: xs, nil => false
            | x :: xs, y :: ys => andb (eqTree x y) (eqListTree xs ys)
          end) l1 l2)
  end.

