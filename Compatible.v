Require Import DataTypes.
Require Import Channel.
Require Import Cache.

Module Type CompatBehavior (dt: DataTypes) (ch: ChannelPerAddr dt).
  Import dt ch.
  Section Node.
    Context {n: Cache}.
    Context {a: Addr}.
    Context {t: Time}.
    Axiom sendPCond: forall {p}, parent n = p ->
                                 forall {m},
                                   mark mch n p a t m ->
                                   forall {c}, parent c = n -> dir n c a t <= to m.
    Axiom sendCCond: forall {c}, parent c = n ->
                                 forall {m},
                                   mark mch n c a t m ->
                                   (to m = Mo -> forall {c'}, c' <> c -> parent c' = n -> dir n c' a t = In)
                                     /\ (to m = Sh -> forall {c'}, c' <> c -> parent c' = n -> dir n c' a t < Mo).
  End Node.                                                                              
End CompatBehavior.

Module Type CompatTheorem (dt: DataTypes) (ch: ChannelPerAddr dt).
  Import dt ch.
  Parameter compatible: forall {n a t},
    (forall {c}, parent c = n -> dir n c a t <= state n a t)
      /\ forall c, parent c = n -> dir n c a t = Mo ->
                   forall {c'}, c' <> c -> parent c' = n -> dir n c' a t = In.
End CompatTheorem.

Module mkCompat (dt: DataTypes) (ch: ChannelPerAddr dt) (cb: CompatBehavior dt ch) (ba: BehaviorAxioms dt ch)
                : CompatTheorem dt ch.
  
End mkCompat.
