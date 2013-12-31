Require Import MsiState Tree Hier.

Export Tree MsiState.

Module Type DataTypes <: Hier.

  Parameter hier: Tree.
  Axiom treeName1: match hier with
                     | C x _ => x = nil
                   end.

  Axiom treeName2: forall {p}, descendent p hier ->
                               match p with
                                 | C x ls => treeNthName x ls
                               end.

  Definition Time := nat.
  Parameter Addr: Set.
  Parameter getSt: list nat -> Addr -> Time -> State.

  Inductive Desc := Ld | St.

  Definition Index := nat.

  Definition Cache := Tree.
  Definition defined c := descendent c hier.

  Definition state c := match c with
                          | C n ls => getSt n
                        end.

  Parameter dir: Cache -> Cache -> Addr -> Time -> State.

  Parameter Mesg: Set.
  Parameter from: Mesg -> State.
  Parameter to: Mesg -> State.
  Parameter addr: Mesg -> Addr.

  Inductive ChannelType := mch | rch.

  Parameter Label : Set.
  Inductive StLabel := Initial | Store : Label -> StLabel.
  Parameter data: Cache -> Addr -> Time -> StLabel.
  Parameter dataM: Mesg -> StLabel.

(*
  Theorem noChildIsParent: forall {c}, defined c -> leaf c -> forall {c'},
                                                                defined c' -> ~ parent c' c.
  Proof.
    intros c defC leafC.
    unfold leaf in leafC.
    destruct c.
    firstorder.
    unfold not; intros c' c'Def parentc'.
    unfold parent in parentc'.
    destruct c'; assumption.
  Qed.

  Theorem defParent: defined Parent.
  Proof.
    unfold defined.
    firstorder.
  Qed.

  Print defParent.

  Theorem noParentHasParent: forall c, defined c -> ~ parent Parent c.
  Proof.
    unfold not; intros c defc parentc.
    unfold parent in parentc.
    assumption.
  Qed.
    
  Theorem whoParent: forall n, parent (Child n) Parent.
  Proof.
    intros.
    unfold parent.
    auto.
  Qed.

  Theorem who'Parent: forall c, leaf c -> parent c Parent.
  Proof.
    intros c leaf_c.
    destruct c; unfold leaf; auto.
  Qed.
*)
End DataTypes.



