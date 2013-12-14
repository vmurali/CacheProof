Module Type DataTypes.

  Parameter Addr: Set.
  Inductive Desc := Ld | St.
  Parameter Cache: Set.
  Parameter leaf : Cache -> Prop.
  Definition Proc := {c | leaf c}.
  Definition Index := nat.

  Parameter parent: Cache -> Cache.
  Definition State := nat.
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
End DataTypes.
