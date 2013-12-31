Require Import Tree.

Module Type Hier.
  Parameter hier: Tree.
  Axiom treeName1: match hier with
                     | C x _ => x = nil
                   end.

  Axiom treeName2: forall {p}, descendent p hier ->
                               match p with
                                 | C x ls => treeNthName x ls
                               end.
End Hier.

Module mkHierProperties (h: Hier).
  Import h.

  Definition Cache := Tree.
  Definition defined c := descendent c hier.

  Theorem hasFork:
    forall {c1 c2},
      defined c1 -> defined c2 ->
      ~ descendent c1 c2 -> ~ descendent c2 c1 ->
      exists fork, defined fork /\
                           (exists d1, defined d1 /\ parent d1 fork /\ descendent c1 d1 /\ ~ descendent c2 d1) /\
                           (exists d2, defined d2 /\ parent d2 fork /\ ~ descendent c1 d2 /\ descendent c2 d2).
  Proof.
    unfold defined.
    pose proof @hasFork'.
    intros c1 c2 p1 p2 x1 x2.
    specialize (H c1 c2 x1 x2 hier p1 p2).
    firstorder.
  Qed.
End mkHierProperties.
  
