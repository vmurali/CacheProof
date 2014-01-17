Require Import MsiState Tree Coq.Lists.Streams.

Export Tree.

Parameter hier: Tree.

Axiom treeName1: match hier with
                   | C x _ => x = nil
                 end.

Axiom treeName2: forall {p}, descendent p hier ->
                             match p with
                               | C x ls => treeNthName x ls
                             end.

Parameter Addr: Set.
Parameter zero: Addr.
Axiom decAddr: forall a1 a2:Addr, {a1 = a2} + {a1 <> a2}.

Definition defined c := descendent c hier.

Definition Time := nat.

Inductive Desc := Ld | St.

Definition Index := nat.

Definition Cache := Tree.

Inductive ChannelType := mch | rch.

Theorem decCh: forall (x y: ChannelType), {x = y} + {x <> y}.
Proof.
  intros. decide equality.
Qed.

Parameter Label : Set.
Axiom decLabel: forall (l1 l2: Label), {l1 = l2} + {l1 <> l2}.
Inductive StLabel := Initial | Store : Label -> StLabel.

Definition MLabel := Time.
Record Mesg := {
              from: State;
              to: State;
              addr: Addr;
              dataM: StLabel;
              msgId: MLabel
            }.



Module Type DataTypes.
  Parameter state: Cache -> Addr -> Time -> State.
  Parameter dir: Cache -> Cache -> Addr -> Time -> State.

  Parameter data: Cache -> Addr -> Time -> StLabel.

  Parameter wait: Cache -> Addr -> Time -> bool.
  Parameter waitS: Cache -> Addr -> Time -> State.
  Parameter dwait: Cache -> Cache -> Addr -> Time -> bool.
  Parameter dwaitS: Cache -> Cache -> Addr -> Time -> State.

  Parameter deqR: Cache -> Label -> Addr -> Desc -> Index -> Time -> Prop.
  Parameter enqLd: Cache -> Label -> StLabel -> Time -> Prop.
  Parameter enqSt: Cache -> Label -> Time -> Prop.

  Parameter mark: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
  Parameter send: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
  Parameter recv: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
  Parameter proc: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
  Parameter deq: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
End DataTypes.



