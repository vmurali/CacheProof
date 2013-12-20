Module Type DataTypes.

  Parameter classical: forall P, P \/ ~ P.

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

  Definition Mo := 3.
  Definition Ow := 2.
  Definition Sh := 1.
  Definition In := 0.
  Parameter maxState: forall {c a t}, state c a t <= Mo.
  Parameter maxDir: forall {p c a t}, parent c = p -> dir p c a t <= Mo.
End DataTypes.
