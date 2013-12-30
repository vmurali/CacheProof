Require Import List Coq.Arith.EqNat Coq.Relations.Relation_Operators Coq.Relations.Operators_Properties.

Require Import Omega.

Inductive Tree : Set :=
  | C : list nat -> list Tree -> Tree.

Definition parent c p :=
  match p with
    | C n ls => In c ls
  end.


Definition leaf c := match c with
                       | C _ ls => match ls with
                                     | nil => True
                                     | _ => False
                                   end
                     end.

Definition descendent := clos_refl_trans Tree parent.

Section Tree_ind.
  Variable P : Tree -> Prop.

  Hypothesis Ccase :
    forall n ls, (forall c, parent c (C n ls) -> P c) -> P (C n ls).

  Theorem indCase {t} (Pt: P t) {rest} (Prest: forall c, In c rest -> P c):
    forall c, In c (t::rest) -> P c.
  Proof.
    intros c opts.
    destruct opts as [t_eq_c | forRest].
    rewrite <- t_eq_c; assumption.
    apply (Prest c forRest).
  Qed.

  Fixpoint Tree_ind' (tr : Tree) : P tr :=
    match tr with
      | C n ls => Ccase n ls
                        ((fix list_Tree_ind ls :=
                            match ls as lsl return forall c, In c lsl -> P c with
                              | nil => fun c inNil => False_ind (P c) inNil
                              | tr' :: rest => indCase (Tree_ind' tr') (list_Tree_ind rest)
                            end) ls)
    end.
End Tree_ind.

Definition Cache := Tree.
Parameter hier: Tree.

Definition defined c := descendent c hier.

Axiom treeName1: match hier with
                   | C x _ => x = nil
                 end.

Definition treeNthName nm ls := forall n,
                                  n < length ls -> match nth n ls (C nil nil) with
                                                     | C x _ => x = n :: nm
                                                   end.

Axiom treeName2: forall {p}, descendent p hier ->
                             match p with
                               | C x ls => treeNthName x ls
                             end.

Parameter getSt: list nat -> nat.
Definition state t := match t with
                        | C n ls => getSt n
                      end.

Axiom comp1: forall {c p}, parent c p -> state c <= state p.

Theorem leAncest: forall c a, descendent c a -> state c <= state a.
Proof.
  intros c a ancest.
  unfold descendent in *.
  induction ancest.
  apply (comp1 H).
  omega.
  omega.
Qed.

