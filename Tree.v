Require Import List Coq.Relations.Relation_Operators Coq.Relations.Operators_Properties Coq.Logic.Classical.

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

Section Tree_ind1.
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

  Fixpoint Tree_ind1 (tr : Tree) : P tr :=
    match tr with
      | C n ls => Ccase n ls
                        ((fix list_Tree_ind ls :=
                            match ls as lsl return forall c, In c lsl -> P c with
                              | nil => fun c inNil => False_ind (P c) inNil
                              | tr' :: rest => indCase (Tree_ind1 tr') (list_Tree_ind rest)
                            end) ls)
    end.
End Tree_ind1.

Fixpoint decTree (t1 t2: Tree): {t1 = t2} + {t1 <> t2}.
Proof.
  repeat decide equality.
Qed.

Definition treeNthName nm ls := forall n,
                                  n < length ls -> match nth n ls (C nil nil) with
                                                     | C x _ => x = n :: nm
                                                   end.

Theorem hasFork':
  forall {c1 c2},
    ~ descendent c1 c2 -> ~ descendent c2 c1 ->
    forall {top},
      descendent c1 top -> descendent c2 top ->
      exists fork, descendent fork top /\
                              (exists d1, descendent d1 top /\ parent d1 fork /\
                                                     descendent c1 d1 /\ ~ descendent c2 d1) /\
                              (exists d2, descendent d2 top /\
                                                     parent d2 fork /\ ~ descendent c1 d2 /\ descendent c2 d2).
Proof.
  intros c1 c2 c1_no_c2 c2_no_c1.
  induction top using Tree_ind1.
  intros c1_C_n_ls c2_C_n_ls.
  destruct (classic (exists c, parent c (C n ls) /\ descendent c1 c /\ descendent c2 c)) as
           [[c [c_child [c1_c c2_c]]] | noEx].
  specialize (H c c_child c1_c c2_c).
  destruct H as [fork [fork_c use]].
  destruct use as [[d1 [d1_c r1]] [d2 [d2_c r2]]].
  pose proof (rt_step Tree parent c (C n ls) c_child) as c_C_n_ls.
  pose proof (rt_trans Tree parent fork c (C n ls) fork_c c_C_n_ls) as fork_C_n_ls.
  pose proof (rt_trans Tree parent d1 c (C n ls) d1_c c_C_n_ls) as d1_C_n_ls.
  pose proof (rt_trans Tree parent d2 c (C n ls) d2_c c_C_n_ls) as d2_C_n_ls.
  firstorder.
  exists (C n ls).
  constructor. apply (rt_refl Tree parent (C n ls)).
  pose proof (clos_rt_rtn1 Tree parent c1 (C n ls) c1_C_n_ls) as transChange1.
  destruct transChange1 as [easy|d1].
  firstorder.
  pose proof (clos_rtn1_rt Tree parent c1 d1 transChange1) as c1_d1.
  fold descendent in c1_d1.
  pose proof (clos_rt_rtn1 Tree parent c2 z c2_C_n_ls) as transChange2.
  destruct transChange2 as [easy|d2].
  firstorder.
  pose proof (clos_rtn1_rt Tree parent c2 d2 transChange2) as c2_d2.
  fold descendent in c2_d2; clear transChange1 transChange2.
  assert (cond1: ~ descendent c2 d1) by firstorder.
  assert (cond2: ~ descendent c1 d2) by firstorder.
  pose proof (rt_step Tree parent d1 z H0) as p1.
  pose proof (rt_step Tree parent d2 z H1) as p2.
  constructor.
  exists d1; firstorder.
  exists d2; firstorder.
Qed.
