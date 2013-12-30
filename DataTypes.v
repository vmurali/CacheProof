Require Import State.

Module Type DataTypes.
  Include MsiState.
  
  Parameter Addr: Set.
  Inductive Desc := Ld | St.

  Definition Index := nat.

  Inductive Cache': Set :=
    | Parent : Cache'
    | Child : nat -> Cache'.

  Definition Cache := Cache'. 

  Definition parent c p := 
    match c with
      | Parent => False
      | Child _ => 
        match p with
          | Parent => True
          | Child _ => False
        end
    end.

  Parameter total : nat.
  Definition defined c := match c with
                            | Parent => True
                            | Child n => n < total
                          end.

  Definition leaf x := match x with
                         | Parent => False
                         | Child _ => True
                       end.

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

  Parameter descendent: Cache -> Cache -> Prop.

  Definition Time := nat.
  Parameter state: Cache -> Addr -> Time -> State.
  Parameter dir: Cache -> Cache -> Addr -> Time -> State.

  Parameter Mesg: Set.
  Parameter from: Mesg -> State.
  Parameter to: Mesg -> State.
  Parameter addr: Mesg -> Addr.

  Parameter ChannelType: Set.

  Parameter mch rch: ChannelType.

  Parameter Label : Set.
  Inductive StLabel := Initial | Store : Label -> StLabel.
  Parameter data: Cache -> Addr -> Time -> StLabel.
  Parameter dataM: Mesg -> StLabel.

End DataTypes.



