Require Import Compatible DataTypes Rules Channel MsiState List Useful.

Module mkCompatBehavior (ch: ChannelPerAddr mkDataTypes): CompatBehavior mkDataTypes ch.
  Import mkDataTypes ch.
  Section Node.
    Context {n: Cache}.
    Context {a: Addr}.
    Context {t: Time}.

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
      destruct (trans t) as [transx _].
      destruct transx.

      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l0); firstorder].

      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l0); firstorder].

      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder |
      pose proof (listNeq hard l); firstorder].

      simpl in *.
      destruct (decTree n p0) as [neq|nneq].
      rewrite <- neq in *.
      destruct (decTree p c0) as [peq|pneq].
      rewrite <- peq in *.
      pose proof (noCycle p1 n_p) as f.
      firstorder.
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].
      
      simpl in *.
      destruct (decTree n p0) as [neq|nneq].
      rewrite <- neq in *.
      destruct (decTree p c0) as [peq|pneq].
      rewrite <- peq in *.
      pose proof (noCycle p1 n_p) as f.
      firstorder.
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].

      simpl in *.
      destruct (decTree n p0) as [neq|nneq].
      rewrite <- neq in *.
      destruct (decTree p c0) as [peq|pneq].
      rewrite <- peq in *.
      pose proof (noCycle p1 n_p) as f.
      firstorder.
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].

      simpl in *.
      destruct (decTree n c0) as [neq|nneq].
      rewrite <- neq in *.
      destruct (decTree p p0) as [peq|pneq].
      rewrite <- peq in *.
      simpl in *.
      destruct markm as [[_ [_ [_ [use1 [use2 _]]]]] use3].
      rewrite use1; rewrite <- use3; rewrite use2.
      apply (s0 c defc c_n).
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].

      simpl in *.
      destruct (decTree n c0) as [neq|nneq].
      rewrite <- neq in *.
      destruct (decTree p p0) as [peq|pneq].
      rewrite <- peq in *.
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n p) as sth.
      assert (gd: length sth = length (tl (removelast sth))) by (f_equal; assumption).
      pose proof (listCond1 (removelast sth) use1) as gd2.
      pose proof (listCond2 sth n0) as gd3.
      omega.
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].

      simpl in *.
      destruct (decTree n c0) as [neq|nneq].
      rewrite <- neq in *.
      destruct (decTree p p0) as [peq|pneq].
      rewrite <- peq in *.
      simpl in *.
      destruct markm as [[_ [_ [_ [use1 [use2 _]]]]] use3].
      rewrite use1; rewrite <- use3; rewrite use2.
      apply (s0 c defc c_n).
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].

      simpl in *.
      destruct (decTree n p0) as [neq|nneq].
      rewrite <- neq in *.
      destruct (decTree p c0) as [peq|pneq].
      rewrite <- peq in *.
      pose proof (noCycle p1 n_p) as f.
      firstorder.
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n p) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].
      
    Qed.
 
    Theorem sendCCond: forall {c}, defined n -> defined c ->
                                   parent c n ->
                                   forall {m},
                                     mark mch n c a t m ->
                                     sle (to m) (state n a t) /\
                                     forall {c'},
                                       defined c' -> 
                                       c' <> c ->
                                       parent c' n ->
                                       sle (dir n c' a t)
                                           match to m with
                                             | Mo => MsiState.In
                                             | Sh => Sh
                                             | MsiState.In => Mo
                                           end.
    Proof.
      intros c defn defc c_n m markm.
      unfold dir in *.
      unfold state in *.
      unfold mark in *.
      unfold mkDataTypes.mark in *.
      destruct oneBeh as [fn [init trans]].
      destruct (trans t) as [transx _].
      destruct transx.

      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n c) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l0); firstorder].

      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n c) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l0); firstorder].
      
      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n c) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].

      simpl in *.
      destruct (decTree n p) as [neq|nneq].
      rewrite <- neq in *.
      destruct (decTree c c0) as [ceq|cneq].
      rewrite <- ceq in *.
      simpl in *.
      destruct markm as [[_ [_ [_ [use1 [use2 _]]]]] use3].
      rewrite use1 in *; rewrite use2 in *; rewrite use3 in *.
      firstorder.
      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n c) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].
      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n c) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].

      simpl in *.
      destruct (decTree n p) as [neq|nneq].
      rewrite <- neq in *.
      destruct (decTree c c0) as [ceq|cneq].
      rewrite <- ceq in *.
      simpl in *.
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n c) as sth.
      assert (gd: length sth = length (tl (removelast sth))) by (f_equal; assumption).
      pose proof (listCond1 (removelast sth) use1) as gd2.
      pose proof (listCond2 sth n0) as gd3.
      assert False by omega.
      firstorder.
      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n c) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].
      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n c) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].

      simpl in *.
      destruct (decTree n p) as [neq|nneq].
      rewrite <- neq in *.
      destruct (decTree c c0) as [ceq|cneq].
      rewrite <- ceq in *.
      simpl in *.
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n c) as sth.
      assert (gd: length sth = length (tl sth)) by (f_equal; assumption).
      pose proof (listCond1 sth use1) as gd2.
      assert False by omega.
      firstorder.
      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n c) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].
      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n c) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].

      simpl in *.
      destruct (decTree n c0) as [neq|nneq].
      rewrite <- neq in *.
      destruct (decTree c p) as [ceq|cneq].
      rewrite <- ceq in *.
      simpl in *.
      pose proof (noCycle p0 c_n) as f.
      firstorder.
      destruct markm as [[use1 [use2 _]] _].
      unfold List.tl in use2;
      destruct (ch (fn t) mch n c) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].
      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n c) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].

      simpl in *.
      destruct (decTree n c0) as [neq|nneq].
      rewrite <- neq in *.
      destruct (decTree c p) as [ceq|cneq].
      rewrite <- ceq in *.
      simpl in *.
      destruct markm as [[use1 [use2 _]] _];
      remember (ch (fn t) mch n c) as sth.
      assert (gd: length sth = length (tl (removelast sth))) by (f_equal; assumption).
      pose proof (listCond1 (removelast sth) use1) as gd2.
      pose proof (listCond2 sth n0) as gd3.
      assert False by omega; firstorder.
      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n c) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].
      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n c) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].

      simpl in *.
      destruct (decTree n c0) as [neq|nneq].
      rewrite <- neq in *.
      destruct (decTree c p) as [ceq|cneq].
      rewrite <- ceq in *.
      simpl in *.
      pose proof (noCycle p0 c_n) as f.
      firstorder.
      destruct markm as [[use1 [use2 _]] _].
      unfold List.tl in use2;
      destruct (ch (fn t) mch n c) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].
      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n c) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].


      simpl in *;
      destruct markm as [[use1 [use2 _]] _];
      unfold List.tl in use2;
      destruct (ch (fn t) mch n c) as [easy | hard]; [
      firstorder|
      pose proof (listNeq hard l); firstorder].
    Qed.

    Theorem oneRespC: forall {c1 c2}, defined n -> defined c1 -> defined c2 ->
                      parent c1 n -> parent c2 n ->
                      forall {m1}, (mark mch n c1 a t m1 \/ recv mch c1 n a t m1) ->
                                   forall {m2},
                                     (mark mch n c2 a t m2 \/ recv mch c2 n a t m2) -> c1 = c2.
    Proof.
      intros c1 c2 defn defc1 defc2 c1_n c2_n m1 sthm1 m2 sthm2.
      unfold mark in *.
      unfold mkDataTypes.mark in *.
      unfold recv in *; unfold mkDataTypes.recv in *.
      destruct oneBeh as [fn [init trans]].
      destruct (trans t) as [transx _].
      destruct transx.

      simpl in *.
      destruct sthm1 as [markm | markm].
      destruct markm as [[use1 [use2 _]] _].
      unfold List.tl in use2.
      destruct (ch (fn t) mch n c1) as [easy | hard].
      firstorder.
      pose proof (listNeq hard l0); firstorder.
      destruct markm as [[use1 [use2 _]] _].
      unfold List.tl in use2.
      destruct (ch (fn t) mch c1 n) as [easy | hard].
      firstorder.
      pose proof (listCond2 (hard::l0) use1) as j1.
      assert (j2: length (hard::l0) = length (removelast (hard::l0))) by
          (f_equal; assumption).
      rewrite j2 in j1; omega.

      simpl in *.
      destruct sthm1 as [markm | markm].
      destruct markm as [[use1 [use2 _]] _].
      unfold List.tl in use2.
      destruct (ch (fn t) mch n c1) as [easy | hard].
      firstorder.
      pose proof (listNeq hard l0); firstorder.
      destruct markm as [[use1 [use2 _]] _].
      unfold List.tl in use2.
      destruct (ch (fn t) mch c1 n) as [easy | hard].
      firstorder.
      pose proof (listCond2 (hard::l0) use1) as j1.
      assert (j2: length (hard::l0) = length (removelast (hard::l0))) by
          (f_equal; assumption).
      rewrite j2 in j1; omega.

      simpl in *.
      destruct sthm1 as [markm | markm].
      destruct markm as [[use1 [use2 _]] _].
      unfold List.tl in use2.
      destruct (ch (fn t) mch n c1) as [easy | hard].
      firstorder.
      pose proof (listNeq hard l); firstorder.
      destruct markm as [[use1 [use2 _]] _].
      unfold List.tl in use2.
      destruct (ch (fn t) mch c1 n) as [easy | hard].
      firstorder.
      pose proof (listCond2 (hard::l) use1) as j1.
      assert (j2: length (hard::l) = length (removelast (hard::l))) by
          (f_equal; assumption).
      rewrite j2 in j1; omega.




      simpl in *.
      destruct (decTree n p) as [neq|nneq].
      rewrite <- neq in *.
      destruct (decTree c1 c) as [c1eq|c1neq].
      rewrite <- c1eq in *.
      simpl in *.
      destruct (decTree c2 c1) as [c2eq|c2neq].
      rewrite <- c2eq in *.
      reflexivity.

      simpl in *.
      destruct sthm2 as [markm | recvm].
      destruct markm as [[use1 [use2 _]] _].
      unfold List.tl in use2.
      destruct (ch (fn t) mch n c2) as [easy | hard].
      firstorder.
      pose proof (listNeq hard l); firstorder.

      destruct recvm as [[use1 [use2 _]] _].
      unfold List.tl in use2.
      destruct (ch (fn t) mch c2 n) as [easy | hard].
      firstorder.
      destruct (decTree c2 n) as [cond1|cond2]; [
      pose proof (noParentChild cond1 c2_n); firstorder|
      pose proof (listCond2 (hard::l) use1) as j1;
      assert (j2: length (hard::l) = length (removelast (hard::l))) by
          (f_equal; assumption);
      rewrite j2 in j1; omega].

      destruct (decTree c2 c) as [c2eq|c2neq].
      rewrite <- c2eq in *.

      destruct sthm1 as [markm | recvm].
      destruct markm as [[use1 [use2 _]] _].
      unfold List.tl in use2.
      destruct (ch (fn t) mch n c1) as [easy | hard].
      firstorder.
      pose proof (listNeq hard l); firstorder.

      destruct recvm as [[use1 [use2 _]] _].
      unfold List.tl in use2.
      destruct (ch (fn t) mch c1 n) as [easy | hard].
      firstorder.
      destruct (decTree c1 n) as [cond1|cond2]; [
      pose proof (noParentChild cond1 c1_n); firstorder|
      pose proof (listCond2 (hard::l) use1) as j1;
      assert (j2: length (hard::l) = length (removelast (hard::l))) by
          (f_equal; assumption);
      rewrite j2 in j1; omega].


      destruct sthm1 as [markm | recvm].
      destruct markm as [[use1 [use2 _]] _].
      unfold List.tl in use2.
      destruct (ch (fn t) mch n c1) as [easy | hard].
      firstorder.
      pose proof (listNeq hard l); firstorder.
      destruct recvm as [[use1 [use2 _]] _].
      unfold List.tl in use2.
      destruct (ch (fn t) mch c1 n) as [easy | hard].
      firstorder.
      destruct (decTree c1 n) as [cond1|cond2]; [
      pose proof (noParentChild cond1 c1_n); firstorder|
      pose proof (listCond2 (hard::l) use1) as j1;
      assert (j2: length (hard::l) = length (removelast (hard::l))) by
          (f_equal; assumption);
      rewrite j2 in j1; omega].

      destruct sthm1 as [markm | recvm].
      destruct markm as [[use1 [use2 _]] _].
      unfold List.tl in use2.
      destruct (ch (fn t) mch n c1) as [easy | hard].
      firstorder.
      pose proof (listNeq hard l); firstorder.
      destruct (decTree c1 p) as [c1eq|c1neq].
      rewrite <- c1eq in *.
      destruct (decTree n c) as [neq'|nneq'].
      rewrite <- neq' in *.
      pose proof (noCycle p0 c1_n) as f.
      firstorder.

      destruct recvm as [[use1 [use2 _]] _].
      unfold List.tl in use2.
      destruct (ch (fn t) mch c1 n) as [easy | hard].
      firstorder.
      destruct (decTree c1 n) as [cond1|cond2]; [
      pose proof (noParentChild cond1 c1_n); firstorder|
      pose proof (listCond2 (hard::l) use1) as j1;
      assert (j2: length (hard::l) = length (removelast (hard::l))) by
          (f_equal; assumption);
      rewrite j2 in j1; omega].

      destruct recvm as [[use1 [use2 _]] _].
      unfold List.tl in use2.
      destruct (ch (fn t) mch c1 n) as [easy | hard].
      firstorder.
      destruct (decTree c1 n) as [cond1|cond2]; [
      pose proof (noParentChild cond1 c1_n); firstorder|
      pose proof (listCond2 (hard::l) use1) as j1;
      assert (j2: length (hard::l) = length (removelast (hard::l))) by
          (f_equal; assumption);
      rewrite j2 in j1; omega].






      simpl in *.
      destruct (decTree n p) as [neq|nneq].
      rewrite <- neq in *.
      destruct (decTree c1 c) as [c1eq|c1neq].
      rewrite <- c1eq in *.

      destruct sthm1 as [markm | recvm]; clear sthm2.
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n c1) as sth.
      assert (gd: length sth = length (tl (removelast sth))) by (f_equal; assumption).
      pose proof (listCond1 (removelast sth) use1) as gd2.
      pose proof (listCond2 sth n0) as gd3.
      assert False by omega.
      firstorder.

      destruct (decTree c1 n) as [c1Eq|c1Neq].
      pose proof (noParentChild c1Eq p0) as f; firstorder.
      destruct recvm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch c1 n) as sth.
      assert (gd: length sth = length (removelast sth)) by (f_equal; assumption).
      pose proof (listCond2 sth use1) as gd3.
      assert False by omega.
      firstorder.

      destruct sthm1 as [markm | recvm]; clear sthm2.
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n c1) as sth.
      assert (gd: length sth = length (tl sth)) by (f_equal; assumption).
      pose proof (listCond1 sth use1) as gd3.
      assert False by omega.
      firstorder.

      destruct (decTree c1 n) as [c1Eq| c1Neq].
      pose proof (noParentChild c1Eq c1_n) as f; firstorder.
      destruct recvm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch c1 n) as sth.
      assert (gd: length sth = length (removelast sth)) by (f_equal; assumption).
      pose proof (listCond2 sth use1) as gd3.
      assert False by omega.
      firstorder.

      destruct sthm1 as [markm | recvm]; clear sthm2.
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n c1) as sth.
      assert (gd: length sth = length (tl sth)) by (f_equal; assumption).
      pose proof (listCond1 sth use1) as gd3.
      assert False by omega.
      firstorder.

      destruct (decTree c1 p) as [c1Eq | c1Neq].
      rewrite <- c1Eq in *.
      destruct (decTree n c) as [nEq | nNeq].
      rewrite <- nEq in *.
      pose proof (noCycle p0 c1_n) as f; firstorder.
      destruct recvm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch c1 n) as sth.
      assert (gd: length sth = length (removelast sth)) by (f_equal; assumption).
      pose proof (listCond2 sth use1) as gd3.
      assert False by omega.
      firstorder.
      destruct recvm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch c1 n) as sth.
      assert (gd: length sth = length (removelast sth)) by (f_equal; assumption).
      pose proof (listCond2 sth use1) as gd3.
      assert False by omega.
      firstorder.





      simpl in *. clear sthm2.
      destruct sthm1 as [markm | recvm].
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n c1) as sth.
      assert (gd: length sth = length (tl sth)) by (f_equal; assumption).
      pose proof (listCond1 sth use1) as gd3.
      assert False by omega.
      firstorder.
      destruct recvm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch c1 n) as sth.
      assert (gd: length sth = length (removelast sth)) by (f_equal; assumption).
      pose proof (listCond2 sth use1) as gd3.
      assert False by omega.
      firstorder.





      simpl in *.
      destruct (decTree n p) as [neq|nneq].
      rewrite <- neq in *.
      destruct (decTree c1 c) as [c1eq|c1neq].
      rewrite <- c1eq in *.
      destruct (decTree n c1) as [nEq|nNeq].
      destruct (decTree c1 n) as [c1Eq|c1Neq].
      pose proof (noParentChild c1Eq p0); firstorder.
      assert (c1 = n) by auto; firstorder.

      clear sthm2.
      destruct sthm1 as [markm | recvm].
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n c1) as sth.
      assert (gd: length sth = length (tl sth)) by (f_equal; assumption).
      pose proof (listCond1 sth use1) as gd3.
      assert False by omega.
      firstorder.

      destruct recvm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch c1 n) as sth.
      pose proof (listCond2 sth use1) as gd3.
      assert (gd: length ({|
         fromB := st (fn t) c1 a0;
         toB := toR;
         addrB := a0;
         dataBM := dt (fn t) c1 a0 |} :: sth) = S (length sth)) by (unfold length; reflexivity).
      assert (gd2: length ({|
         fromB := st (fn t) c1 a0;
         toB := toR;
         addrB := a0;
         dataBM := dt (fn t) c1 a0 |} :: sth) = length (removelast sth)) by (f_equal; assumption).
      omega.

      destruct (decTree n c) as [nEq|nNeq].
      assert (X: c = n) by auto.
      pose proof (noParentChild X p0); firstorder.
      destruct sthm1 as [markm | recvm].
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n c1) as sth.
      assert (gd: length sth = length (tl sth)) by (f_equal; assumption).
      pose proof (listCond1 sth use1) as gd3.
      assert False by omega.
      firstorder.
      destruct recvm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch c1 n) as sth.
      assert (gd: length sth = length (removelast sth)) by (f_equal; assumption).
      pose proof (listCond2 sth use1) as gd3.
      assert False by omega.
      firstorder.

      destruct (decTree n c) as [nEq|nNeq].
      rewrite <- nEq in *.
      destruct (decTree c1 p) as [c1Eq | c1Neq].
      rewrite <- c1Eq in *.
      pose proof (noCycle p0 c1_n) as f; firstorder.
      clear sthm2.
      destruct sthm1 as [markm | recvm].
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n c1) as sth.
      assert (gd: length sth = length (tl sth)) by (f_equal; assumption).
      pose proof (listCond1 sth use1) as gd3.
      assert False by omega.
      firstorder.
      destruct (decTree c1 n) as [c1Eq|c1Neq'];
      destruct recvm as [[use1 [use2 _]] _];
      remember (ch (fn t) mch c1 n) as sth;
      assert (gd: length sth = length (removelast sth)) by (f_equal; assumption);
      pose proof (listCond2 sth use1) as gd3;
      assert False by omega;
      firstorder.
      destruct sthm1 as [markm | recvm].
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n c1) as sth.
      assert (gd: length sth = length (tl sth)) by (f_equal; assumption).
      pose proof (listCond1 sth use1) as gd3.
      assert False by omega.
      firstorder.
      destruct (decTree c1 c) as [c1Eq|c1Neq'];
      destruct recvm as [[use1 [use2 _]] _];
      remember (ch (fn t) mch c1 n) as sth;
      assert (gd: length sth = length (removelast sth)) by (f_equal; assumption);
      pose proof (listCond2 sth use1) as gd3;
      assert False by omega;
      firstorder.






      simpl in *.
      destruct (decTree n c) as [neq | nneq].
      rewrite <- neq in *.
      destruct (decTree c1 p) as [c1eq |c1neq].
      rewrite <- c1eq in *.

      clear sthm2.
      destruct sthm1 as [markm | recvm].
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n c1) as sth.
      assert (gd: length sth = length (tl (removelast sth))) by (f_equal; assumption).
      pose proof (listCond1 (removelast sth) use1) as gd1.
      pose proof (listCond2 sth n0) as gd2.
      assert False by omega.
      firstorder.
      destruct (decTree c1 n) as [c1Eq | c1Neq].
      destruct (decTree n c1) as [nEq | nNeq].
      pose proof (noParentChild nEq p0) as f; firstorder.
      assert (n = c1) by auto; firstorder.
      destruct recvm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch c1 n) as sth.
      assert (gd: length sth = length (removelast sth)) by (f_equal; assumption).
      pose proof (listCond2 sth use1) as gd1.
      assert False by omega.
      firstorder.

      destruct sthm1 as [markm | recvm]. clear sthm2.
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n c1) as sth.
      assert (gd: length sth = length (tl sth)) by (f_equal; assumption).
      pose proof (listCond1 sth use1) as gd2.
      assert False by omega.
      firstorder.
      clear sthm2.
      destruct (decTree c1 n) as [c1Eq | c1Neq].
      pose proof (noParentChild c1Eq c1_n); firstorder.
      destruct recvm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch c1 n) as sth.
      assert (gd: length sth = length (removelast sth)) by (f_equal; assumption).
      pose proof (listCond2 sth use1) as gd1.
      assert False by omega.
      firstorder.

      destruct (decTree n p) as [nEq | nNeq].
      rewrite <- nEq in *.
      destruct (decTree c1 c) as [c1Eq | c1Neq].
      rewrite <- c1Eq in *.
      destruct (decTree c2 c1) as [c2Eq | c2Neq].
      auto.

      destruct sthm2 as [markm | recvm].
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n c2) as sth.
      assert (gd: length sth = length (tl sth)) by (f_equal; assumption).
      pose proof (listCond1 sth use1) as gd2.
      assert False by omega.
      firstorder.
      destruct recvm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch c2 n) as sth.
      assert (gd: length sth = length (removelast sth)) by (f_equal; assumption).
      pose proof (listCond2 sth use1) as gd1.
      assert False by omega.
      firstorder.

      destruct sthm1 as [markm | recvm].
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n c1) as sth.
      assert (gd: length sth = length (tl sth)) by (f_equal; assumption).
      pose proof (listCond1 sth use1) as gd2.
      assert False by omega.
      firstorder.
      destruct recvm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch c1 n) as sth.
      assert (gd: length sth = length (removelast sth)) by (f_equal; assumption).
      pose proof (listCond2 sth use1) as gd1.
      assert False by omega.
      firstorder.

      destruct sthm1 as [markm | recvm].
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n c1) as sth.
      assert (gd: length sth = length (tl sth)) by (f_equal; assumption).
      pose proof (listCond1 sth use1) as gd2.
      assert False by omega.
      firstorder.
      destruct (decTree c1 c); 
      destruct recvm as [[use1 [use2 _]] _];
      remember (ch (fn t) mch c1 n) as sth;
      assert (gd: length sth = length (removelast sth)) by (f_equal; assumption);
      pose proof (listCond2 sth use1) as gd1;
      assert False by omega;
      firstorder.





      simpl in *.
      destruct (decTree n c) as [nEq | nNeq].
      rewrite <- nEq in *.
      destruct (decTree c1 p) as [c1Eq | c1Neq].
      rewrite <- c1Eq in *.
      pose proof (noCycle p0 c1_n); firstorder.
      destruct sthm1 as [markm | recvm].
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n c1) as sth.
      assert (gd: length sth = length (tl sth)) by (f_equal; assumption).
      pose proof (listCond1 sth use1) as gd2.
      assert False by omega.
      firstorder.
      destruct (decTree c1 n) as [c1eq | c1neq].
      pose proof (noParentChild c1eq c1_n). firstorder.
      destruct recvm as [[use1 [use2 _]] _];
      remember (ch (fn t) mch c1 n) as sth;
      assert (gd: length sth = length (removelast sth)) by (f_equal; assumption);
      pose proof (listCond2 sth use1) as gd1;
      assert False by omega;
      firstorder.
      destruct sthm1 as [markm | recvm].
      destruct markm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch n c1) as sth.
      assert (gd: length sth = length (tl sth)) by (f_equal; assumption).
      pose proof (listCond1 sth use1) as gd2.
      assert False by omega.
      firstorder.
      destruct (decTree c1 c) as [c1eq | c1neq].
      rewrite <- c1eq in *.
      destruct (decTree n p) as [neq | nneq].
      rewrite <- neq in *.
      destruct recvm as [[use1 [use2 _]] _].
      remember (ch (fn t) mch c1 n) as sth.
      pose proof (listCond2 sth use1) as gd1.
      assert (length ({|
         fromB := st (fn t) c1 a0;
         toB := x;
         addrB := a0;
         dataBM := dt (fn t) c1 a0 |} :: sth) = S (length sth)) by (unfold length; reflexivity).
      assert (length ({|
         fromB := st (fn t) c1 a0;
         toB := x;
         addrB := a0;
         dataBM := dt (fn t) c1 a0 |} :: sth) = (length (removelast sth))) by
          (f_equal; assumption).
      omega.
      destruct recvm as [[use1 [use2 _]] _];
      remember (ch (fn t) mch c1 n) as sth;
      assert (gd: length sth = length (removelast sth)) by (f_equal; assumption);
      pose proof (listCond2 sth use1) as gd1;
      assert False by omega;
      firstorder.
      destruct recvm as [[use1 [use2 _]] _];
      remember (ch (fn t) mch c1 n) as sth;
      assert (gd: length sth = length (removelast sth)) by (f_equal; assumption);
      pose proof (listCond2 sth use1) as gd1;
      assert False by omega;
      firstorder.

      simpl in *.
      destruct sthm1 as [markm | markm].
      destruct markm as [[use1 [use2 _]] _].
      unfold List.tl in use2.
      destruct (ch (fn t) mch n c1) as [easy | hard].
      firstorder.
      pose proof (listNeq hard l); firstorder.
      destruct markm as [[use1 [use2 _]] _].
      unfold List.tl in use2.
      destruct (ch (fn t) mch c1 n) as [easy | hard].
      firstorder.
      pose proof (listCond2 (hard::l) use1) as j1.
      assert (j2: length (hard::l) = length (removelast (hard::l))) by
          (f_equal; assumption).
      rewrite j2 in j1; omega.
    Qed.

    Theorem respPNoRespC: forall {p}, defined n -> defined p -> parent n p ->
                                    forall {m},
                                      (mark mch n p a t m \/ recv mch p n a t m) ->
                                      forall {c}, defined c -> parent c n -> forall mc,
                                        ~ (mark mch n c a t mc \/ recv mch c n a t mc).
    Proof.
      admit.
    Qed.
  End Node.
  Theorem initCompat:
    forall {n c}, defined n -> defined c -> parent c n -> forall a, dir n c a 0 = MsiState.In.
  Proof.
    intros n c defn defc c_n a.
    unfold dir.
    destruct oneBeh as [fn [init _]].
    rewrite init; clear init fn.
    unfold initGlobalState.
    simpl; reflexivity.
  Qed.
End mkCompatBehavior.