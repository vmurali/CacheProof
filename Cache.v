Set Implicit Arguments.

Axiom cheat : forall t, t.

Require Import CpdtTactics.

Load Fifo.

(* useful lemmas about natural numbers *)

Print le_n.

Lemma leS_neS_le (n m : nat) : n <= S m -> n <> S m -> n <= m.
  intuition.
Qed.

(* useful lemma about decidability of option types *)
Section option.
  Variable A : Type.

  Hypothesis eq_dec_hyp : forall (x y : A), {x = y} + {x <> y}.

  Definition option_dec (x : option A) : {x <> None} + {x = None}.
    decide equality.
  Qed.
End option.

(* create an environment containining an ordered set of values, Ord;
   various theorems related to ordered set;
   start with basic lemmas about less than not being reflexive and not being transitive;
   also assume that comparison of less than, greater than and equal to is decidable;
   prove somem lemmas (about symmetric, less than implies not equal etc
 *)

Section All.

Variable Ord : Set.

Hypothesis lt : Ord -> Ord -> Prop.

Notation "x >> y" := (lt y x) (at level 70, no associativity).
Notation "x << y" := (lt x y) (at level 70, no associativity).

Hypothesis lt_not_refl : forall x, x << x -> False.
Hypothesis lt_trans : forall x y z, x << y -> y << z -> x << z.

Hypothesis compare_dec : forall x y, {x << y} + {x = y} + {x >> y}.

Notation "x <<= y" := (lt x y \/ x = y) (at level 70, no associativity).
Notation "x >>= y" := (lt y x \/ x = y) (at level 70, no associativity).

(* I have defined more lemmas than I have currently used *)
Lemma le_ge : forall x y, x <<= y -> y >>= x.
  crush.
Qed.

Lemma ge_le : forall x y, x >>= y -> y <<= x.
  crush.
Qed.

Lemma less_not_eq : forall x y, x << y -> x = y -> False.
  crush.
  apply (lt_not_refl H).
Qed.

Lemma lt_not_sym : forall x y, x << y -> x >> y -> False.
  intros.
  specialize lt_not_refl with x.
  specialize lt_trans with x y x.
  intuition.
Qed.

Lemma eq_Ord_dec: forall (x y : Ord), {x = y} + {x <> y}.
  intros.
  assert (x << y -> x <> y) by (intro H1; crush; apply (lt_not_refl H1)).
  assert (x >> y -> x <> y) by (intro H2; crush; apply (lt_not_refl H2)).
  destruct (compare_dec x y) as [l | r].
  destruct l; crush.
  crush.
Qed.

(* start the environment for the cache node, and parent-child-network system *)
Section Cache.

  Record p_c_msg : Set := mk_p_c_msg
  { p_c_prev : Ord
  ; p_c_next : Ord
  ; p_c_time : nat
  }.

  Record c_p_msg : Set := mk_c_p_msg
  { c_p_next : Ord
  ; c_p_time : nat
  }.

  Section eq_msg_hint.
    Hint Resolve eq_nat_dec.
    Hint Resolve eq_Ord_dec.

    Lemma p_c_dec (x y : p_c_msg) : {x = y} + {x <> y}.
      decide equality.
    Qed.

    Lemma c_p_dec (x y : c_p_msg) : {x = y} + {x <> y}.
      decide equality.
    Qed.

  End eq_msg_hint.
  
  Record node : Set := mkNode
  { state : Ord
  ; change_time : nat
  }.

  Variable p_c_size c_p_size : nat.

  Record system : Set := mkSyste
  { child : node
  ; parent : node
  ; p_c : fifo p_c_msg p_c_size
  ; c_p : fifo c_p_msg c_p_size
  }.

  Print enq.

  (* parent, child *)
  Inductive systemStep (time : nat) (s : system) : system -> Prop :=
  | Nothing : systemStep time s s
  | Enq_p_c : forall (x : Ord) (notFull : num (p_c s) < p_c_size), x >> state (child s) -> systemStep time s
      {| child := child s
       ; parent := {| state := x; change_time := change_time (parent s) |}
       ; p_c := (enq {| p_c_prev := state (child s)
                      ; p_c_next := x
                      ; p_c_time := S time
                      |} (p_c s) notFull)
       ; c_p := c_p s
       |}
  | Enq_c_p : forall (x : Ord) (notFull : num (c_p s) < c_p_size), x << state (child s) -> systemStep time s
      {| child := {| state := x; change_time := change_time (child s) |}
       ; parent := parent s
       ; p_c := p_c s
       ; c_p := (enq {| c_p_next := x
                      ; c_p_time := S time
                      |} (c_p s) notFull)
       |}
  | Deq_p_c : forall m (notEmpty : S m = num (p_c s)), systemStep time s
      {| child := if compare_dec (p_c_next (first (p_c s) notEmpty)) (state (child s))
                    then {| state := p_c_next (first (p_c s) notEmpty); change_time := p_c_time (first (p_c s) notEmpty) |}
                    else child s
       ; parent := parent s
       ; p_c := deq (p_c s) notEmpty
       ; c_p := c_p s
       |}
  | Deq_c_p : forall m (notEmpty : S m = num (c_p s)), systemStep time s
      {| child := child s
       ; parent := {| state := c_p_next (first (c_p s) notEmpty); change_time := c_p_time (first (c_p s) notEmpty) |}
       ; p_c := p_c s
       ; c_p := deq (c_p s) notEmpty
       |}.

  Variable init_state : Ord.

  Definition init_node :=
  {| state := init_state
   ; change_time := 0
   |}.

  Definition init_system :=
  {| child := init_node
   ; parent := init_node
   ; p_c := emptyFifo p_c_msg p_c_size
   ; c_p := emptyFifo c_p_msg c_p_size
   |}.

  Inductive fin : nat -> Set :=
  | Last : forall n, fin n
  | Prev : forall n, fin n -> fin (S n).

  Fixpoint getNum n (f : fin n) : nat :=
    match f with
    | Last x => x
    | Prev _ f' => getNum f'
    end.

  (* defining a list of system state transitions *)
  Inductive systemList : nat -> system -> Set :=
  | Init : systemList 0 init_system
  | Next : forall t ss next_ss, systemList t ss -> systemStep t ss next_ss -> systemList (S t) next_ss.

  (* function to get the n^th element of the system state transition list *)
  Fixpoint get max last_ss (sl : systemList max last_ss) : fin max -> system :=
    match sl in systemList max last_ss return fin max -> system with
    | Init => fun _ => init_system
    | Next t _ next_ss ss_list _ => fun f =>
        match f in fin n0 return (fin (pred n0) -> system) -> system with
        | Last _ => fun _ => next_ss
        | Prev _ f' => fun val => val f'
        end (get ss_list)
    end.

  (* Correctness theorem, as stated in the document *)
  Theorem correctness max (last_s : system) (sl : systemList max last_s) (p c : fin max) : change_time (child (get sl c)) <= getNum p -> change_time (parent (get sl p)) <= getNum c -> state (child (get sl c)) <<= state (parent (get sl p)).
  Admitted.

  Lemma change_time_child_less (n : nat) (ss : system) (sl : systemList n ss) : change_time (child (get sl (Last n))) <= n.
  Admitted.

  Lemma change_time_parent_less (n : nat) (ss : system) (sl : systemList n ss) : change_time (parent (get sl (Last n))) <= n.
  Admitted.

  (* Correctness corollary, as stated in the document *)
  Corollary coherence (n : nat) (ss : system) (sl : systemList n ss) : state (child (get sl (Last n))) <<= state (parent (get sl (Last n))).
    apply correctness.
    apply change_time_child_less.
    apply change_time_parent_less.
  Qed.
End Cache.

End All.


  Print not.

  Variable A : Set.
  Variable Q : A -> Prop.
  Variable R : A -> Prop.

(*  Definition exists_neg : forall i, ~ (Q i) -> ~ (exists j, Q j).
   intros.
   unfold not.
   destruct 1.
   crush.

  Lemma stuff : forall i, Q i -> ~ (R i) -> ~ (exists j, Q j /\ R j).
    intros.
    unfold not.
    destruct 1.
    intros.
    unfold not in H.
    destruct H.
*)
  Locate "exists".

  Print exists_neg'.

  Print exists_neg'.
  Print ex.
    intros.

  

  Lemma stuff : forall k, (k > 0 -> (forall i, i < k -> ~ (P i)) -> ~ (P k)) ->
                forall n, (n > 0 -> (P n -> exists j, j < n /\ P j)).


  Lemma stuff : forall k, (k > 0 -> ((forall i, i < k -> (P i -> False)) -> (P k -> False))) -> (forall n > 0, P k -> exists i, i < k -> P i).

  Lemma stuff : (forall k, P k -> exists i, i < k -> P i) -> (P 0 -> False) -> forall n, P n -> False.
    intros.
  Admitted.
End proof.

