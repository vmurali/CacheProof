Require Import Compatible DataTypes Rules Channel MsiState List.

Module mkCompatBehavior (ch: ChannelPerAddr mkDataTypes): CompatBehavior mkDataTypes ch.
  Import mkDataTypes ch.
  Section Node.
    Context {n: Cache}.
    Context {a: Addr}.
    Context {t: Time}.

    Theorem listNeq: forall {A} (x: A) l, x :: l <> l.
      unfold not; intros A x l eq.
      assert (H: length (x :: l) = length l) by (f_equal; assumption).
      unfold length in *.
      remember ((fix length (l : list A) : nat :=
            match l with
            | nil => 0
            | _ :: l' => S (length l')
            end) l) as y.
      generalize H; clear.
      intros neq.

      assert (H: S y <> y) by auto.
      firstorder.
    Qed.

    Theorem sendPCond: forall {p}, defined n -> defined p -> parent n p ->
                                   forall {m},
                                     mark mch n p a t m ->
                                     forall {c}, defined c -> parent c n ->
                                                 sle (dir n c a t) (to m).
    Proof.
      intros p defn defp n_p m markm c defc c_n.
      unfold dir in *.
      unfold mark in *.
      unfold mkDataTypes.mark in *.
      destruct oneBeh as [fn [init trans]].
      destruct (trans t).

      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].

      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].

      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].

      simpl in *.
      destruct (decTree n p0) as [neq|nneq].
      rewrite <- neq in *.
      
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].
      
    Axiom sendCCond: forall {c}, defined n -> defined c ->
                       parent c n ->
                       forall {m},
                         mark mch n c a t m ->
                         sle (to m) (state n a t) /\
                         forall {c'}, defined c' -> 
                                      c' <> c -> parent c' n -> sle (dir n c' a t)
                                      match to m with
                                        | Mo => In
                                        | Sh => Sh
                                        | In => Mo
                                      end.
    Axiom oneRespC: forall {c1 c2}, defined n -> defined c1 -> defined c2 ->
                      parent c1 n -> parent c2 n ->
                      forall {m1}, (mark mch n c1 a t m1 \/ recv mch c1 n a t m1) ->
                                   forall {m2},
                                     (mark mch n c2 a t m2 \/ recv mch c2 n a t m2) -> c1 = c2.
    Axiom respPNoRespC: forall {p}, defined n -> defined p -> parent n p ->
                                    forall {m},
                                      (mark mch n p a t m \/ recv mch p n a t m) ->
                                      forall {c}, defined c -> parent c n -> forall mc,
                                        ~ (mark mch n c a t mc \/ recv mch c n a t mc).
  End Node.
  Axiom initCompat:
    forall {n c}, defined n -> defined c -> parent c n -> forall a, dir n c a 0 = In.
