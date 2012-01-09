Require Import Compare_dec.

Require Import CpdtTactics.

Set Implicit Arguments.

(*
Section exist.
  Variable A : Set.
  Variable P : A -> Prop.

  Definition exists_neg : (exists i, ~ P i) -> ~ (forall j, P j) :=
    fun (ex : exists i, ~ P i) (f : forall j, P j) =>
      match ex with
        | ex_intro i not_P_i => not_P_i (f i)
      end.

  Definition exists_pos : (exists i, P i) -> ~ (forall j, ~ P j) :=
    fun (ex : exists i, P i) (f : forall j, ~ P j) =>
      match ex with
        | ex_intro i P_i => (f i) P_i
      end.

  Definition neg_exists : ~ (exists i, P i) -> forall j, ~ P j :=
    fun (f : ~ (exists i, P i)) j (P_j : P j) =>
      f (ex_intro (fun i => P i) j P_j).
End exist.
*)

Section induction.
  Variable P : nat -> Prop.
  
  Lemma sub_ind : (forall n, (forall i, i < n -> P i) -> P n) -> forall n i, i < n -> P i.
    Hint Resolve le_lt_eq_dec : cpdt.
    intros H n;
      induction n;
        [
          crush
          |
            intros i j; intros;
              assert ({i < n} + { i = n}) as dec by crush;
                destruct dec; crush
        ].
  Qed.


  Lemma ob_ind : (forall k i, i < k -> P i) -> forall n, P n.
    intros H n; assert (n < S n) as H1 by crush; apply (H (S n) n H1).
  Qed.

  Theorem strong_ind : (forall k, (forall i, i < k -> P i) -> P k) -> forall n, P n.
    Hint Resolve sub_ind.
    Hint Resolve ob_ind.
    eauto.
  Qed.
End induction.

Section crap.
  Variable P : nat -> nat -> Prop.
  Print strong_ind.
  Definition double_ind : (forall m, (forall i, i < m -> forall n, P i n) -> forall n, P m n) -> forall m n, P m n :=
    fun hyp m => strong_ind (fun x => forall n, P x n) hyp m.
    Print strong_ind.
    fun 
End crap.

Definition imp_neg (A B : Prop) (f : A -> B) : ~ B -> ~ A := fun g a => g (f a).

Section double_induction.
  Variable P : nat -> nat -> Prop.

  Lemma sub_double_ind : (forall m n, (forall i j, i < m -> j < n -> P i j) -> P m n) -> forall m n i j, i < m -> j < n -> P i j.
    Hint Resolve le_lt_eq_dec : cpdt.
    intros H m n;
      induction m;
        [
          crush
          |
            induction n;
              [
                crush
                |
                  intros i j; intros;
                    assert ({i < m} + {i = m}) as dec1 by crush;
                      assert ({j < n} + {j = n}) as dec2 by crush;
                        destruct dec1; destruct dec2; crush
              ]
        ].
  Qed.

  Lemma ob_double_ind : (forall m n i j, i < m -> j < n -> P i j) -> forall m n, P m n.
    intros H m n;
      assert (m < S m) as lt1 by crush;
        assert (n < S n) as lt2 by crush;
          apply (H (S m) (S n) m n lt1 lt2).
  Qed.

  Theorem strong_double_ind : (forall m n, (forall i j, i < m -> j < n -> P i j) -> P m n) -> forall m n, P m n.
    Hint Resolve sub_double_ind.
    Hint Resolve ob_double_ind.
    eauto.
  Qed.

End double_induction.

Section double_prop.
  Variable P : nat -> nat -> Prop.

  Definition prop_exists_less_pos' m n (f1 : P m n -> exists i, exists j, i < m /\ j < n /\ P i j) (f2 : forall i j, i < m -> j < n -> ~ P i j) (p : P m n) : False :=
    match f1 p with
      | ex_intro i ex_j => match ex_j with
                             | ex_intro j c => f2 i j (proj1 c) (proj1 (proj2 c)) (proj2 (proj2 c))
                           end
    end.

  Definition prop_exists_less_pos (f1 : forall m n, P m n -> exists i, exists j, i < m /\ j < n /\ P i j) m n (f2 : forall i j, i < m -> j < n -> ~ P i j) (p : P m n) : False :=
    prop_exists_less_pos' (f1 m n) f2 p.

  Definition prop_exists_less_ind
    (f : forall m n, P m n -> exists i, exists j, i < m /\ j < n /\ P i j)
    : forall m n, ~ P m n:=
    strong_double_ind (fun m n => ~ P m n) (prop_exists_less_pos f).

  Definition zero_case
    (f : forall m n, m > 0 -> n > 0 -> P m n ->
                       exists i, exists j, i < m /\ j < n /\ P i j)
    (p0 : ~ P 0 0)
    (m0 : forall m, m > 0 -> ~ P m 0)
    (n0 : forall n, n > 0 -> ~ P 0 n)
    m n
    (p : P m n)
    : exists i, (exists j, i < m /\ j < n /\ P i j).
    induction m; induction n; crush.
    specialize (n0 (S n)); crush.
    specialize (m0 (S m)); crush.
  Qed.

  Definition required_induction :
    (forall m n, m > 0 -> n > 0 -> P m n ->
                    exists i, exists j, i < m /\ j < n /\ P i j) ->
      (~ P 0 0) ->
      (forall m, m > 0 -> ~ P m 0) ->
      (forall n, n > 0 -> ~ P 0 n) ->
      forall m n, ~ P m n :=
    fun f p0 m0 n0 => prop_exists_less_ind (zero_case f p0 m0 n0).
End double_prop.

Section fuck