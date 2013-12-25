Require Import DataTypes Channel L1 Cache Compatible.

Module Type LatestValueAxioms (dt: DataTypes) (ch: ChannelPerAddr dt) (l1: L1Axioms dt).
  Import dt ch l1.

  Section ForAddr.
    Context {a: Addr}.
    Context {n: Cache}.
    Context {t: Time}.
    Context {c: Cache}.
    Context {p: Cache}.
    Context {m: Mesg}.
    Axiom fromParent: parent n = p -> 
                      recv mch p n a t m -> from m = In -> data n a t = dataM m.
    Axiom fromChild: parent c = n ->
                     recv mch c n a t m -> slt Sh (from m) -> data n a t = dataM m.
    Axiom initLatest: (forall {p}, parent n <> p) -> data n a t = Initial.
    Axiom change:
      data n a (S t) <> data n a t ->
      (exists m, (exists p, parent n = p /\ recv mch p n a t m /\ from m = In) \/
                 (exists c, parent c = n /\ recv mch c n a t m /\ slt Sh (from m))) \/
      exists l i, deqR n l a St i t.
  End ForAddr.
End LatestValueAxioms.

Module LatestValueTheorems (dt: DataTypes) (ch: ChannelPerAddr dt) (c: BehaviorAxioms dt ch)
       (l1: L1Axioms dt) (comp: CompatBehavior dt ch).
  Import dt ch c l1 comp.
  Section ForAddr.
    Context {a: Addr}.
    Context {n: Cache}.
    Context {t: Time}.
    Theorem allLatestValue:
      (state n a t = Sh \/
       slt (state n a t) Sh /\ forall {c}, parent c = n -> sle (dir n c a t) Sh) ->
      match data n a t with
        | Initial => forall {ti}, 0 <= ti <= t -> forall {ci li ii}, ~ deqR ci li a St ii ti
        | Store lb =>
          exists cb ib tb, tb < t /\ deqR cb lb a St ib tb /\
                           forall {ti}, tb < ti <= t ->
                                        forall {ci li ii}, ~ deqR ci li a St ii ti
      end.
    Proof.
      admit.
    Qed.

End LatestValueTheorems.