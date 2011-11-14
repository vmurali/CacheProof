Set Implicit Arguments.

Require Import CpdtTactics.
Require Import Arith.

(* basic nat lemma *)
Definition predLess (n m : nat) : n < m -> pred n < m.
  crush.
Qed.

(* Fifo environment *)
Section Fifo.
Variable A : Set.

(* size of Fifo *)
Variable size : nat.

(* enq is protected to not exceed size *)
Inductive Fifo : nat -> Set :=
| emptyFifo : Fifo 0
| enq : A -> forall n, Fifo n -> n < size -> Fifo (S n).

(*
Definition unitA n := match n with
                      | 0 => unit
                      | S _ => A
                      end.

Fixpoint first' n (f : Fifo n) : unitA n :=
  match f in Fifo n return unitA n with
  | emptyFifo => tt
  | enq x _ f _ => match f in Fifo n return (unitA n) -> A with
                   | emptyFifo => fun _ => x
                   | enq _ _ _ _ => fun first_f => first_f
                   end (first' f)
  end.

Definition first n (f : Fifo (S n)) : A := first' f.
*)

Definition s_n_0 n (pf : S n = 0) : False :=
  match pf in (_ = e) return match e with
                             | 0 => False
                             | S _ => True
                             end with
  | eq_refl => I
  end.

Fixpoint first' n (f : Fifo n) : forall m, S m = n -> A :=
  match f in Fifo n0 return forall m, S m = n0 -> A with
  | emptyFifo => fun _ pf0 => match s_n_0 pf0 with end
  | enq x _ f1 _ => fun _ _ => match f1 in (Fifo n2) return (forall m, S m = n2 -> A) -> A with
                               | emptyFifo => fun _ => x
                                 | enq _ n3 _ _ => fun val_pf => val_pf n3 eq_refl
                               end (first' f1)
  end.

Definition first n (f : Fifo (S n)) : A := first' f eq_refl.

(*
Fixpoint first n (f : Fifo n) : n <> 0 -> A :=
  match f in Fifo n0 return n0 <> 0 -> A with
  | emptyFifo => fun pf0 => match pf0 eq_refl with end
  | enq x _ f1 _ => fun _ => match f1 in (Fifo n2) return (n2 <> 0 -> A) -> A with
                             | emptyFifo => fun _ => x
                             | enq _ n3 _ _ => fun val_pf => val_pf (s_n_0 (n := n3))
                             end (first f1)
  end.
*)

(*
Definition unitFifoPredN n := match n with
                              | 0 => unit
                              | S n' => Fifo n'
                              end.

Fixpoint deq' n (f : Fifo n) : unitFifoPredN n :=
  match f in Fifo n return unitFifoPredN n with
  | emptyFifo => tt
  | enq x n' f' p =>  match n' return unitFifoPredN n' -> (pred n' < size) -> Fifo n' with
                      | 0 => fun _ _ => emptyFifo
                      | S _ => fun deq_f p' => enq x deq_f p'
                      end (deq' f') (predLess p)
  end.

Definition deq n (f : Fifo (S n)) := deq' f.
*)

(*
Fixpoint deq' n (f : Fifo n) : forall m, S m = n -> Fifo (pred n) :=
  match f in Fifo n0 return forall m, S m = n0 -> Fifo (pred n0) with
  | emptyFifo => fun _ pf0 => match s_n_0 pf0 with end
  | enq x _ f1 p => fun _ _ => match f1 in (Fifo n2) return (forall m, S m = n2 -> Fifo (pred n2)) -> forall p' : pred n2 < size, Fifo n2 with
                               | emptyFifo => fun _ _ => emptyFifo
                               | enq _ n3 _ _ => fun val_pf p'  => enq x (val_pf n3 eq_refl) p'
                               end (deq' f1) (predLess p)
  end.
*)

Fixpoint deq' n (f : Fifo n) : forall m, S m = n -> Fifo (pred n) :=
  match f in Fifo n0 return forall m, S m = n0 -> Fifo (pred n0) with
  | emptyFifo => fun _ pf0 => match s_n_0 pf0 with end
  | enq x _ f1 _ => fun _ _ => match f1 in (Fifo n2) return (forall m, S m = n2 -> Fifo (pred n2)) -> Fifo n2 with
                               | emptyFifo => fun _ => emptyFifo
                               | enq _ n3 _ pless => fun val_pf => enq x (val_pf n3 eq_refl) pless
                               end (deq' f1)
  end.

Definition deq n (f : Fifo (S n)) : Fifo n := deq' f eq_refl.

(*
Fixpoint deq n (f : Fifo n) : n <> 0 -> Fifo (pred n) :=
  match f in Fifo n0 return n0 <> 0 -> Fifo (pred n0) with
  | emptyFifo => fun pf0 => match pf0 eq_refl with end
  | enq x _ f1 p => fun _ => match f1 in (Fifo n2) return (n2 <> 0 -> Fifo (pred n2)) -> Fifo n2 with
                             | emptyFifo => fun _ => emptyFifo
                             | enq _ n3 _ pless => fun deq_pf => enq x (deq_pf (s_n_0 (n := n3))) pless
                             end (deq f1)
  end.
*)

Definition isEmpty n (f : Fifo n) : {n = 0} + {n > 0}.
  refine (match n with
  | 0 => left _ _
  | S _ => right _ _
  end); crush.
Qed.

(* very trivial lemma *)
Lemma fifoLessThanSize : forall n, Fifo n -> n <= size.
  intro; induction 1; intuition.
Qed.

Definition isFull n (f : Fifo n) : {n = size} + {n < size}.
  assert ({n = size} + {n <> size}) by (apply eq_nat_dec).
  assert (n <= size) by (induction f; crush).
  crush.
Qed.

(* random lemmas just to fill pages *)
Lemma enq_first n (f : Fifo (S n)) (notFull : S n < size) (enqVal : A) : first (enq enqVal f notFull) = first f.
  dep_destruct f; crush.
Qed.

(* a step in a fifo, which contains a source and a sink
     a) enq: only enqueue from source happens (source changes from Some to None)
     b) deq: only dequeu from sink (sink changes from None to Some)
     c) enq-deq parallel composition : explained better in Cache.v. Basically both enq and deq happens.
          State of the FIFO must be maintained correctly
     d) nothing : nothing happens, simulates other activities happening in the network
 *)
Inductive fifoStep : forall n, Fifo n -> option A -> option A -> forall n', Fifo n' -> option A -> option A -> Prop :=
| Enq : forall n (f : Fifo n) (notFull : n < size) (enqVal : A) (deqVal : option A), fifoStep f (Some enqVal) deqVal (enq enqVal f notFull) None deqVal
| Deq : forall n (f : Fifo (S n)) (enqVal : option A), fifoStep f enqVal None (deq f) enqVal (Some (first f))
| EnqDeq : forall n (f : Fifo (S n)) (notFull : S n < size) (enqVal : A), fifoStep f (Some enqVal) None (deq (enq enqVal f notFull)) None (Some (first f))
| NoFifoAction : forall n (f : Fifo n) (enqVal deqVal : option A), fifoStep f enqVal deqVal f enqVal deqVal.
End Fifo.