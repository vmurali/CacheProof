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

  Record p_to_c_msg : Set := mk_p_to_c_msg
  { p_to_c_prev : Ord
  ; p_to_c_next : Ord
  ; p_to_c_time : nat
  }.

  Record c_to_p_msg : Set := mk_c_to_p_msg
  { c_to_p_next : Ord
  ; c_to_p_time : nat
  }.

  (* a node defines a child as well as a parent;
     state denotes the coherence state;
     p_to_c denotes the response message from parent to child
       (sent in the case of parent, and received in the case of child)
     c_to_p denotes the response message from child to parent
       (sent in the case of child, and received in the case of parent)
     change_time denotes the time at which a "forced" state change occurs
       a forced state change occurs when a node changes child because of receiving a message
   *)

  Record node : Set := mkNode
  { state : Ord
  ; p_to_c : option p_to_c_msg
  ; c_to_p : option c_to_p_msg
  ; change_time : nat
  }.

  Section eq_msg_hint.
    Hint Resolve eq_nat_dec.
    Hint Resolve eq_Ord_dec.

    Lemma p_to_c_dec (x y : p_to_c_msg) : {x = y} + {x <> y}.
      decide equality.
    Qed.

    Lemma c_to_p_dec (x y : c_to_p_msg) : {x = y} + {x <> y}.
      decide equality.
    Qed.

  End eq_msg_hint.
  
  (* a legal step of a child:
       a) it need not do anything (simulates the rest of the stuff happening in the child node)
       b) it receives response from parent and if necessary, changes state (and hence changes change_time)
       c) it sends response to parent, changing state
   *)
  Inductive childStep (time : nat) c : node -> Prop :=
  | CNothing :
      childStep time c c
  | CReceive :
      forall p_to_c_m, p_to_c c = Some p_to_c_m ->
        childStep time c
          {| state := if compare_dec (p_to_c_prev (p_to_c_m)) (state c) then p_to_c_next (p_to_c_m) else state c
           ; p_to_c := None
           ; c_to_p := c_to_p c
           ; change_time := if compare_dec (p_to_c_prev (p_to_c_m)) (state c) then p_to_c_time (p_to_c_m) else change_time c
           |}
  | CSend :
      forall new_state, new_state << state c -> c_to_p c = None ->
        childStep time c
          {| state := new_state
           ; p_to_c := p_to_c c
           ; c_to_p := Some {| c_to_p_next := new_state
                             ; c_to_p_time := S time
                             |}
           ; change_time := change_time c
           |}.

  (* a legal step of a parent:
       a) it need not do anything
       b) it receives response from child and changes state (and hence changes change_time)
       c) it sends response to child, changing state
   *)
  Inductive parentStep (time : nat) c : node -> Prop :=
  | PNothing :
      parentStep time c c
  | PReceive :
      forall c_to_p_m, c_to_p c = Some c_to_p_m ->
        parentStep time c
          {| state := c_to_p_next c_to_p_m
           ; p_to_c := p_to_c c
           ; c_to_p := None
           ; change_time := c_to_p_time c_to_p_m
           |}
  | PSend :
      forall new_state, new_state >> state c -> p_to_c c = None ->
        parentStep time c
          {| state := new_state
           ; p_to_c := Some {| p_to_c_prev := state c
                             ; p_to_c_next := new_state
                             ; p_to_c_time := S time
                             |}
           ; c_to_p := c_to_p c
           ; change_time := change_time c
           |}.

  (* network buffer sizes *)
  Variable p_to_c_size : nat.
  Variable c_to_p_size : nat.

  (* full system state
       p_to_c_fifo : fifo from parent to child
       c_to_p_fifo : fifo from child to parent
   *)
  Record systemState : Set := mkSystemState
  { child : node
  ; parent : node
  ; p_to_c_fifo : fifo p_to_c_msg p_to_c_size
  ; c_to_p_fifo : fifo c_to_p_msg c_to_p_size
  }.

  Variable init_state : Ord.

  Definition init_node :=
  {| state := init_state
   ; p_to_c := None
   ; c_to_p := None
   ; change_time := 0
   |}.

  Definition init_system :=
  {| child := init_node
   ; parent := init_node
   ; p_to_c_fifo := emptyFifo p_to_c_msg p_to_c_size
   ; c_to_p_fifo := emptyFifo c_to_p_msg c_to_p_size
   |}.

  (* a full system step. Contains 4 mini-steps:
       a) child transition
       b) parent transition
       c) p_to_c fifo transition (based on old values of message states)
       d) c_to_p fifo transition (based on old values of message states)

     The notion where I change state based on old values is called parallel composition in hardware.
     A small example would be swapping two numbers in parallel:
       x := y (parallel compose) y := x
     There is no direct sequential counterpart to this operation.

     In this particular example, the message at the node is being modified by two entities:
       a) the node itself (it makes a Some-message into a None)
       b) the fifo network (it makes a None into a Some-message)

     In order to simulate a parallel composition because of this interaction correctly,
     I should figure out the effect (got from higher level knowledge - I can be sure that
     the message is None if the fifo network enqueues it, and hence the node could not have
     processed a some message - which means I can discard the message update done by the node)

     This reasoning shows up in the if-then-else clause in updating the message of the nodes
   *)
  Inductive systemStep (time : nat) (ss : systemState) : systemState -> Prop :=
  | SystemStep :
     forall c' p' 
            p_to_c_fifo' parent_p_to_c' child_p_to_c'
            c_to_p_fifo' parent_c_to_p' child_c_to_p',
       childStep time (child ss) c' ->
       parentStep time (parent ss) p' ->
       fifoStep (p_to_c_fifo ss) (p_to_c (parent ss)) (p_to_c (child ss))
                 p_to_c_fifo' parent_p_to_c' child_p_to_c' ->
       fifoStep (c_to_p_fifo ss) (c_to_p (child ss)) (c_to_p (parent ss))
                 c_to_p_fifo' child_c_to_p' parent_c_to_p' ->
         systemStep time ss
           {| child :=
                {| state := state c'
                 ; p_to_c := if option_dec p_to_c_dec (p_to_c (child ss)) then p_to_c c' else child_p_to_c'
                 ; c_to_p := if option_dec c_to_p_dec (c_to_p (child ss)) then child_c_to_p' else c_to_p c'
                 ; change_time := change_time c'
                 |}
            ; parent :=
                {| state := state p'
                 ; p_to_c := if option_dec p_to_c_dec (p_to_c (parent ss)) then parent_p_to_c' else p_to_c p'
                 ; c_to_p := if option_dec c_to_p_dec (c_to_p (parent ss)) then c_to_p p' else parent_c_to_p'
                 ; change_time := change_time p'
                 |}
            ; p_to_c_fifo := p_to_c_fifo'
            ; c_to_p_fifo := c_to_p_fifo'
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
  Inductive systemList : nat -> systemState -> Set :=
  | Init : systemList 0 init_system
  | Next : forall t ss next_ss, systemList t ss -> systemStep t ss next_ss -> systemList (S t) next_ss.

  (* function to get the n^th element of the system state transition list *)
  Fixpoint get max last_ss (sl : systemList max last_ss) : fin max -> systemState :=
    match sl in systemList max last_ss return fin max -> systemState with
    | Init => fun _ => init_system
    | Next t _ next_ss ss_list _ => fun f =>
        match f in fin n0 return (fin (pred n0) -> systemState) -> systemState with
        | Last _ => fun _ => next_ss
        | Prev _ f' => fun val => val f'
        end (get ss_list)
    end.

  (* Correctness theorem, as stated in the document *)
  Theorem correctness max (last_s : systemState) (sl : systemList max last_s) (p c : fin max) : change_time (child (get sl c)) <= getNum p -> change_time (parent (get sl p)) <= getNum c -> state (child (get sl c)) <<= state (parent (get sl p)).
  Admitted.

  Lemma p2c_St t ss next_ss (st : systemStep t ss next_ss) :
    match p_to_c (parent ss) with
    | None => match p_to_c (parent next_ss) with
              | None => True
              | Some y => p_to_c_time y = S t
              end
    | Some z => match p_to_c (parent next_ss) with
                | None => True
                | Some y => y = z
                end
    end.
    destruct st; destruct (option_dec p_to_c_dec (p_to_c (parent ss)));
    repeat match goal with
    | [ H : parentStep ?t ?p ?p' |- _ ] => destruct H
    | [ H : fifoStep (p_to_c_fifo _) _ _ _ _ _ |- _ ] => destruct H
    | [ |- match ?enqVal with Some _ => _ | None => _ end ] => destruct enqVal; reflexivity
    | _ => crush
    end.
  Qed.

  Lemma get_last n ss (sl : systemList n ss) : get sl (Last n) = ss.
   destruct sl; reflexivity.
  Qed.

  Lemma p2c_le_t t ss (sl : systemList t ss) :
    match p_to_c (parent (get sl (Last t))) with
    | None => True
    | Some y => p_to_c_time y <= t
    end.
    induction sl;
    [
    crush
    |
    simpl;
    repeat match goal with
    | [ H : context [get _ _] |- _ ] => rewrite get_last in H
    | [ H : systemStep _ _ _ |- _ ] => destruct H; destruct (option_dec p_to_c_dec (p_to_c (parent ss)))
    | [ H : parentStep ?t ?p ?p' |- _ ] => destruct H
    | [ H : fifoStep (p_to_c_fifo _) _ _ _ _ _ |- _ ] => destruct H; crush
    | [ |- match ?enqVal with Some _ => _ | None => _ end ] => destruct enqVal; crush
    end
    ].
  Qed.

  Lemma p2c_n_le_t t ss (sl : systemList t ss) (f : fin t) :
    match p_to_c (parent (get sl f)) with
    | None => True
    | Some y => p_to_c_time y <= t
    end.
    induction sl;
    [ crush |

    dep_destruct f;
    [ apply p2c_le_t |
    simpl;
    repeat match goal with
    | [ H1 : fin ?t, H2 : (forall (f : fin ?t), _) |- _ ] => specialize H2 with H1
    | [ |- match p_to_c (parent ?p) with Some _ => _ | None => _ end ] => destruct (p_to_c (parent p))
    | _ => crush
    end] ].
  Qed.

  Print systemList.

  Lemma p2c_f_enq_le_t t s (sl : systemList t s) (f : fin t) :
  match obj (p_to_c_fifo s) with
  | null => True
  | store x _ _ => p_to_c_time x <= t
  end.
    destruct sl.
    crush.
    destruct s; simpl.
    simpl.
    induction sl.
    crush.
    destruct s; simpl.
    destruct H0.
    destruct H1.
    simpl.

  (*
  Definition deq_time_p_to_c_less (n : nat) (ss : systemState) (sl : systemList n ss) (m : nat) (pf: S m = p_to_c_n (get (le_n n) sl)) : p_to_c_time (first' (p_to_c_fifo (get (le_n n) sl)) pf) <= n.
    destruct (get (le_n n) sl).
    simpl.
    simpl in pf.
    destruct (first' p_to_c_fifo0 pf).
  simpl.
  crush.
  Check deq_time_p_to_c_less.
  *)

  Lemma change_time_child_less (n : nat) (ss : systemState) (sl : systemList n ss) : change_time (child (get sl (Last n))) <= n.
  Admitted.

  Lemma change_time_parent_less (n : nat) (ss : systemState) (sl : systemList n ss) : change_time (parent (get sl (Last n))) <= n.
  Admitted.

  (* Correctness corollary, as stated in the document *)
  Corollary coherence (n : nat) (ss : systemState) (sl : systemList n ss) : state (child (get sl (Last n))) <<= state (parent (get sl (Last n))).
    apply correctness.
    apply change_time_child_less.
    apply change_time_parent_less.
  Qed.
End Cache.

End All.
