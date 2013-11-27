Module Type DataTypes.
  Parameter Cache: Type.
  Parameter Mesg: Type.
  Parameter Addr: Type.

  Parameter parent: Cache -> Cache.
  Definition State := nat.
  Definition Time := nat.
  Parameter state: Cache -> Addr -> Time -> State.
  Parameter dir: Cache -> Cache -> Addr -> Time -> State.

  Parameter from: Mesg -> State.
  Parameter to: Mesg -> State.
  Parameter time: Mesg -> Time.
  Parameter addr: Mesg -> Addr.

  Parameter timeStamp: Cache -> Addr -> Time -> Time.
  Parameter Channel: Type.

  Parameter mch rch: Channel.
End DataTypes.

