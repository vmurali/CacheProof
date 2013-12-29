Require Import List Coq.Arith.EqNat Coq.Relations.Relation_Operators.

Require Import Omega.

Inductive Tree : Set :=
  | C : nat -> list Tree -> Tree.

Definition isParent p c :=
  match p with
    | C n ls => In c ls
  end.


Definition isLeaf c := match c with
                         | C _ ls => match ls with
                                       | nil => True
                                       | _ => False
                                     end
                       end.

Definition isAncest := clos_refl_trans Tree isParent.

Section Tree_ind.
  Variable P : Tree -> Prop.

  Hypothesis Ccase :
    forall n ls, (forall c, isParent (C n ls) c -> P c) -> P (C n ls).

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

Parameter getSt: Tree -> nat.
Definition state (c: Cache) := match c with
                                 | exist v _ => getSt v
                               end.

Fixpoint eq_Tree c1 c2 {struct c1} :=
  match c1, c2 with
    | C n1 l1, C n2 l2 => andb (beq_nat n1 n2)
                               ((fix eqList l1 l2 :=
                                   match l1 with
                                     | nil => match l2 with
                                                | nil => true
                                                | _ => false
                                              end
                                     | x :: xs => match l2 with
                                                    | nil => false
                                                    | y :: ys => andb (eq_Tree x y) (eqList xs ys)
                                                  end
                                  end) l1 l2)
  end.

Fixpoint getNodes t :=
  match t with
    | C n ls => fold_left (fun x t => app x (getNodes t)) ls (n :: nil)
  end.

Fixpoint noFind {A} (t: A) ls :=
  match ls with
    | nil => True
    | x :: xs => x <> t /\ noFind t xs
  end.

Fixpoint noDouble {A} (ls: list A) :=
  match ls with
    | nil => True
    | x :: xs => noFind x xs /\ noDouble xs
  end.

Parameter hier: Tree.
Parameter hierGood: noDouble (getNodes hier).

Definition Cache := {t | isAncest hier t}.

Definition parent (c p: Cache) :=
  match c, p with
    | exist vc _, exist vp _ => isParent vp vc
  end.

Definition leaf (c: Cache) := match c with exist vc _ => isLeaf vc end.

Definition ancestor (c p: Cache) :=
  match c, p with
    | exist vc _, exist vp _ => isAncest vp vc
  end.

Axiom comp1: forall c p, parent c p -> state c <= state p.

Definition getCache := fun n => isAncest hier n.

Theorem leAncest: forall c a, ancestor c a -> state c <= state a.
Proof.
  intros c a ancest.
  destruct c as [vc j1].
  destruct a as [va j2].
  unfold state.
  unfold ancestor in ancest.
  induction ancest.
  apply (comp1 (exist getCache y j1) (exist getCache x j2) H).
  assert (easy: getSt x = getSt x) by reflexivity.
  omega.
  pose proof (rt_trans Tree isParent hier x y j2 ancest1) as ancest_y.
  fold isAncest in *.
  specialize (IHancest1 ancest_y j2); specialize (IHancest2 j1 ancest_y).
  omega.
Qed.
