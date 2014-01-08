Require Import MsiState Tree.

Export Tree MsiState.

Module Type DataTypes.

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
  Parameter zero: Addr.
  Axiom decAddr: forall a1 a2:Addr, {a1 = a2} + {a1 <> a2}.

  Inductive Desc := Ld | St.

  Definition Index := nat.

  Definition Cache := Tree.
  Definition defined c := descendent c hier.

  Parameter state: Cache -> Addr -> Time -> State.

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

  Parameter deqR: Cache -> Label -> Addr -> Desc -> Index -> Time -> Prop.
  Parameter enqLd: Cache -> Label -> StLabel -> Time -> Prop.
  Parameter enqSt: Cache -> Label -> Time -> Prop.

  Parameter wait: Cache -> Addr -> Time -> bool.
  Parameter waitS: Cache -> Addr -> Time -> State.
  Parameter dwait: Cache -> Cache -> Addr -> Time -> bool.
  Parameter dwaitS: Cache -> Cache -> Addr -> Time -> State.
End DataTypes.



