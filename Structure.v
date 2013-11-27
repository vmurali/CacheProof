Require Import DataTypes.
Require Import Channel.

Module Type Parent (dt: DataTypes) (chAll: Channel dt).
  Import dt.
  Module ch := mkChannelPerAddr dt chAll.
  Import ch.

  Parameter rProcPres: Cache -> Addr -> Time -> Mesg -> Prop.
  Parameter rProcAbs: Cache -> Addr -> Time -> Mesg -> Prop.
  Parameter p: Cache.
  Parameter pp: Cache.
  Axiom ppParent: parent p = pp.
  Section Req.
    Context {a: Addr} {c: Cache} {t: Time} {r: Mesg}.
    Axiom procChoice: proc rch c p a t r -> rProcPres c a t r \/ rProcAbs c a t r.
    Axiom finishPres: rProcPres c a t r ->
                      forall tf, (forall ti, t <= ti < tf -> ~ deq rch c a t r)
                                   /\ (forall i r1 t1, t <= t1 <= tf -> marksend rch p i r1 t1->
                                                       exists m1 t2, deq mch i p m1 t2 /\ to m1 <= to r1)
                                   /\ (forall r1 t1, t <= t1 <= tf -> marksend rch p pp r1 t1 ->
                                                     exists m1 t2, deq mch pp p m1 t2 /\ to 
    Axiom presImp: rProcPres c a t r ->
                   (exists i r t1, marksend rch p pp r1 t1 -> exists m1 t2, deq
  End Pair.
                                        
End Parent.
