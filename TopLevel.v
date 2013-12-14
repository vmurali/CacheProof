Require Import DataTypes.

Require Import StoreAtomicity.

Module Type TopLevel (d: DataTypes) (ai: Input d) (sa: StoreAtomicity d ai).
  Import d ai sa.

  Parameter latest:
  forall {n a t}, state n a t >= S ->
                  match data n a t with
                    | Initial => forall ti, 0 <= ti <= t -> ~ deqR n r ti /\ addr r = a /\ desc r = St
                    | Store st => addr st = a /\ desc st = St /\
                        exists tb, tb < t /\ deqR n r tb /\ addr r = a /\ desc r = St /\
                          forall ti, tb <= ti <= t -> ~ deqR n ri ti /\ addr ri = a /\ desc ri = St
                  end.
                  exists sl, data n a t = sl /\ addr sl = a /\ desc sl = St /\
                    forall ti, 
End TopLevel.