  Inductive Tree : Set := Node : forall n, (forall i, i < n -> Tree) -> Tree.

  Require Import Omega.
  Definition z_lt_sn n : 0 < S n.
  Proof.
    omega.
  Qed.

  Fixpoint ht t :=
    match t with
      | Node n fn =>
          match n as n0 return (n0 = n -> nat) with
            | 0 => fun _ => 0
            | S k => fun sk_eq_n => ht (fn 0
                                           match sk_eq_n in (_ = n') return (0 < n') with
                                             | eq_refl => z_lt_sn k
                                           end)
          end eq_refl
    end.

