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
Definition descn1 := clos_refl_trans_n1 Tree parent.
Definition desc1n := clos_refl_trans_1n Tree parent.

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
Definition treeNthName nm ls := forall n,
                                  n < length ls -> match nth n ls (C nil nil) with
                                                     | C x _ => x = n :: nm
                                                   end.

Parameter getSt: list nat -> nat.
Definition state t := match t with
                        | C n ls => getSt n
                      end.

Fixpoint eqList {A} fEq (l1 l2: list A) :=
  match l1, l2 with
    | nil, nil => true
    | nil, y :: ys => false
    | x :: xs, nil => false
    | x :: xs, y :: ys => andb (fEq x y) (eqList fEq xs ys)
  end.

Fixpoint eqTree t1 t2 :=
  match t1, t2 with
    | C n1 l1, C n2 l2 => match l1, l2 with
                            | nil, nil => eqList beq_nat n1 n2
                            | nil, y :: ys => false
                            | x :: xs, nil => false
                            | x :: xs, y :: ys => andb (eqTree x y) (eqList eqTree xs ys)
                          end
  end.


Theorem hasFork:
  forall {top c1 c2},
    descendent c1 top -> descendent c2 top ->
    ~ descendent c1 c2 -> ~ descendent c2 c1 ->
    exists fork, descendent fork top /\
                 (exists d1, parent d1 fork /\ descendent c1 d1 /\ ~ descendent c2 d1) /\
                 (exists d2, parent d2 fork /\ ~ descendent c1 d2 /\ descendent c2 d2).
Proof.
  induction top using Tree_ind'.
  
  
Parameter hier: Tree.

Definition defined c := descendent c hier.

Axiom treeName1: match hier with
                   | C x _ => x = nil
                 end.

Axiom treeName2: forall {p}, descendent p hier ->
                             match p with
                               | C x ls => treeNthName x ls
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

