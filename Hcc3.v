Require Import Eqdep_dec List.

Set Implicit Arguments.

Section Hcc3.
  (** * Basic parameters *)

  Variable address : Set.
  (* The domain of memory addresses *)

  Variable address_eq : forall x y : address, {x = y} + {x <> y}.
  (* We must assume decidable equality on addresses. *)

  Variable data : Set.
  (* The domain of values stored at memory addresses *)
  Variable default : data.
  (* Memory cells start initialized to this value. *)

  Inductive cache := L1_0 | L1_1.
  (* The domain of cache names *)

  Variable line : cache -> Set.
  (* Each cache has a set of available lines. *)

  Variable line_eq : forall c (x y : line c), {x = y} + {x <> y}.
  (* We must assume decidable equality on lines. *)

  Variable cacheLine : address -> forall i : cache, line i.
  (* Each address corresponds to some line for every cache. *)


  (** * Cache state *)

  (* Information about a location in a cache *)
  Inductive locationState :=
  | M (* write permission *)
  | S (* read permission *)
  | I (* invalidated *).

  (* Information a node keeps on one of its children *)
  Inductive childState :=
  | CL : locationState -> childState
  (* Child known to be in a quiescent state *)
  | CP (* Pending (awaiting reply from child to your earlier request) *)
  | WS (* Waiting (the child awaits your reply to its earlier read request) *)
  | WM (* Waiting (the child awaits your reply to its earlier write request) *).

  Coercion CL : locationState >-> childState.

  (* Information a node keeps on its parent *)
  Inductive parentState :=
  | PP (* Pending (awaiting reply from parent to your earlier request) *)
  | W (* Waiting (awaiting reply from parent to your earlier reply (i.e., request made on reply wire) *)
  | N (* Empty (quiescent state) *).


  (** * Messages *)

  (* Messages a running program on a core sends to its L1 cache *)
  Inductive progToL1 :=
  | PrM : address -> progToL1
  (* Memory write instruction *)
  | PrS : address -> progToL1
  (* Memory read instruction *).

  (* Messages an L1 cache sends to memory, split between requests and replies *)
  Inductive l1ToMemQ :=
  | CQm : address -> l1ToMemQ
  (* Please give me the write lock for this address. *)
  | CQs : address -> l1ToMemQ
  (* Please grant me read access to this address. *).

  Inductive l1ToMemY :=
  | CYiS : address -> l1ToMemY
  (* You asked me to invalidate this address, so I did so, relinquishing my read privilege. *)
  | CYiM : address -> data -> l1ToMemY
  (* You asked me to invalidate this address, so I did so, relinquishing my write lock.
   * Here's the data value I was storing. *)
  | CYs : address -> data -> l1ToMemY
  (* You asked me to downgrade my write lock to a read permission, so I did that.
   * Here's the data value I was storing. *).

  Inductive l1ToMem :=
  | L1Q : l1ToMemQ -> l1ToMem
  | L1Y : l1ToMemY -> l1ToMem.

  (* Messages memory sends to an L1 cache *)
  Inductive memToL1 :=
  | PQi : address -> memToL1
  (* Please invalidate this address in your cache. *)
  | PQs : address -> memToL1
  (* Please downgrade your write lock to a read permisison. *)
  | PYm : address -> data -> memToL1
  (* I've granted your request for a write lock.
   * Here's the current datum stored at the address. *)
  | PYs : address -> data -> memToL1
  (* I've granted your request for a read permission.
   * Here's the current datum stored at the address. *).


  (** * System states *)

  Record memoryState := {
    A : address -> data;
    CS : forall c : cache, line c -> childState
  }.

  Definition memorySteady (ms : memoryState) :=
    forall (c : cache) (l : line c), exists ls : locationState, CS ms l = ls.

  (* This function maps a [locationState] to the appropriate type for storing data. *)
  Definition maybeData (ls : locationState) :=
    match ls with
      | I => unit (* The singleton type, appropriate because invalid lines don't store meaningful data. *)
      | _ => address * data
    end%type.

  Record lineState (c : cache) := {
    LS : locationState;
    D : maybeData LS;
    PS : parentState
  }.

  Definition l1State (c : cache) := line c -> lineState c.

  Definition lineSteady (c : cache) (lns : lineState c) := PS lns = N.

  Record systemState := {
    Memory : memoryState;
    L1 : forall c : cache, l1State c;
    ProgToL1 : cache -> option progToL1;
    L1ToMemQ : cache -> option l1ToMemQ;
    L1ToMemY : cache -> option l1ToMemY;
    MemToL1 : cache -> option memToL1
  }.

  Definition state0 := {|
    Memory := {| A := fun _ => default;
      CS := fun _ _ => I |};
    L1 := fun _ _ => {| LS := I; D := tt; PS := N |};
    ProgToL1 := fun _ => None;
    L1ToMemQ := fun _ => None;
    L1ToMemY := fun _ => None;
    MemToL1 := fun _ => None
  |}.


  (** * The types of node rules (i.e., transition tables) *)

  (* What the memory can do in one computation step *)
  Record memoryAction := {
    MSendTo : cache;
    MMessage : memToL1;
    (* Message sent to a child cache *)
    MNewState : memoryState
    (* Change to memory state *)
  }.

  (* Action of memory upon processing a message from an L1 *)
  Definition l1ToMemRule := memoryState
    -> l1ToMem
    -> option memoryAction.

  (* What an L1 cache can do in one computation step *)
  Record l1Action (c : cache) := {
    LSend : option l1ToMem;
    (* Optional message send to main memory *)
    LWhichLine : line c;
    (* Which line's state do we change? *)
    LNewState : lineState c
    (* Change to that line's state *)
  }.

  (* Action of L1 upon processing a message from program *)
  Definition progToL1Rule (c : cache) := l1State c
    -> progToL1
    -> option (l1Action c).

  (* Action of L1 upon processing a message from memory *)
  Definition memToL1Rule (c : cache) := l1State c
    -> memToL1
    -> option (l1Action c).


  (** * The one-step, nondeterministic execution relation *)

  (* Some useful decidable equality procedures *)
  Definition cache_eq : forall x y : cache, {x = y} + {x <> y}.
    decide equality.
  Defined.

  (* Generic updating of functional maps *)
  Section upd.
    Variable dom : Set.
    Variable eq_dec : forall x y : dom, {x = y} + {x <> y}.
    Variable ran : dom -> Set.
    (* The range type of the map is allowed to depend on the concrete key value. *)

    Variable f : forall key : dom, ran key.

    Section key_value.
      Variable key : dom.
      Variable value : ran key.

      (* The definition of updating gets a little tricky, to handle the dependent typing. *)
      Definition upd : forall key : dom, ran key := fun key' =>
        match eq_dec key key' with
          | left Heq => match Heq in _ = k return ran k with
                          | refl_equal => value
                        end
          | right _ => f key'
        end.
    End key_value.

    Implicit Arguments upd [].

    Theorem upd_eq : forall k v, upd k v k = v.
      unfold upd; intros; destruct (eq_dec k k); intuition;
        match goal with
          | [ e : _ = _ |- _ ] => rewrite (UIP_dec eq_dec e (refl_equal _)); reflexivity
        end.
    Qed.

    Theorem upd_ne : forall k k' v, k <> k' -> upd k v k' = f k'.
      unfold upd; intros; destruct (eq_dec k k'); intuition.
    Qed.
  End upd.

  Hint Rewrite upd_eq upd_ne using congruence : upd.

  Implicit Arguments upd [dom ran].

  Section rules.
    Variable L1ToMemRule : cache -> l1ToMemRule.
    Variable ProgToL1Rule : forall c : cache, progToL1Rule c.
    Variable MemToL1Rule : forall c : cache, memToL1Rule c.

    Inductive step : systemState -> systemState -> Prop :=
    | CoreSteps : forall ss c msg,
      (* The core owning cache [c] sends message [msg]. *)
      ProgToL1 ss c = None
      -> step ss {| Memory := Memory ss;
        L1 := L1 ss;
        ProgToL1 := upd cache_eq (ProgToL1 ss) c (Some msg);
        L1ToMemQ := L1ToMemQ ss;
        L1ToMemY := L1ToMemY ss;
        MemToL1 := MemToL1 ss |}
      
    | L1StepsCore : forall ss c msg a,
      (* An L1 cache processes a message from its core. *)
      ProgToL1 ss c = Some msg
      -> ProgToL1Rule (L1 ss (c := c)) msg = Some a
      -> (forall msg, LSend a = Some (L1Q msg) -> L1ToMemQ ss c = None)
      -> (forall msg, LSend a = Some (L1Y msg) -> L1ToMemY ss c = None)
      -> step ss {| Memory := Memory ss;
        L1 := upd cache_eq (L1 ss) c
        (upd (line_eq (c := c)) (L1 ss (c := c)) (LWhichLine a) (LNewState a));
        ProgToL1 := upd cache_eq (ProgToL1 ss) c None;
        L1ToMemQ := match LSend a with
                      | Some (L1Q msg) => upd cache_eq (L1ToMemQ ss) c (Some msg)
                      | _ => L1ToMemQ ss
                    end;
        L1ToMemY := match LSend a with
                      | Some (L1Y msg) => upd cache_eq (L1ToMemY ss) c (Some msg)
                      | _ => L1ToMemY ss
                    end;
        MemToL1 := MemToL1 ss |}

    | L1StepsMem : forall ss c msg a,
      (* An L1 cache processes a message from memory. *)
      MemToL1 ss c = Some msg
      -> MemToL1Rule (L1 ss (c := c)) msg = Some a
      -> (forall msg, LSend a = Some (L1Q msg) -> L1ToMemQ ss c = None)
      -> (forall msg, LSend a = Some (L1Y msg) -> L1ToMemY ss c = None)
      -> step ss {| Memory := Memory ss;
        L1 := upd cache_eq (L1 ss) c
        (upd (line_eq (c := c)) (L1 ss (c := c)) (LWhichLine a) (LNewState a));
        ProgToL1 := ProgToL1 ss;
        L1ToMemQ := match LSend a with
                      | Some (L1Q msg) => upd cache_eq (L1ToMemQ ss) c (Some msg)
                      | _ => L1ToMemQ ss
                    end;
        L1ToMemY := match LSend a with
                      | Some (L1Y msg) => upd cache_eq (L1ToMemY ss) c (Some msg)
                      | _ => L1ToMemY ss
                    end;
        MemToL1 := upd cache_eq (MemToL1 ss) c None |}

    | MemStepsQ : forall ss c msg a,
      (* Memory processes a request from an L1 cache. *)
      L1ToMemY ss c = None
      -> L1ToMemQ ss c = Some msg
      -> L1ToMemRule c (Memory ss) (L1Q msg) = Some a
      -> MemToL1 ss (MSendTo a) = None
      -> step ss {| Memory := MNewState a;
        L1 := L1 ss;
        ProgToL1 := ProgToL1 ss;
        L1ToMemQ := upd cache_eq (L1ToMemQ ss) c None;
        L1ToMemY := L1ToMemY ss;
        MemToL1 := upd cache_eq (MemToL1 ss) (MSendTo a) (Some (MMessage a)) |}

    | MemStepsY : forall ss c msg a,
      (* Memory processes a reply from an L1 cache. *)
      L1ToMemY ss c = Some msg
      -> L1ToMemRule c (Memory ss) (L1Y msg) = Some a
      -> MemToL1 ss (MSendTo a) = None
      -> step ss {| Memory := MNewState a;
        L1 := L1 ss;
        ProgToL1 := ProgToL1 ss;
        L1ToMemQ := L1ToMemQ ss;
        L1ToMemY := upd cache_eq (L1ToMemY ss) c None;
        MemToL1 := upd cache_eq (MemToL1 ss) (MSendTo a) (Some (MMessage a)) |}.

    Lemma L1StepsMem' : forall ss c,
      (exists msg,
        MemToL1 ss c = Some msg
        /\ exists a, MemToL1Rule (L1 ss (c := c)) msg = Some a
          /\ (forall msg, LSend a = Some (L1Q msg) -> L1ToMemQ ss c = None)
          /\ (forall msg, LSend a = Some (L1Y msg) -> L1ToMemY ss c = None))
      -> exists ss', step ss ss'.
      firstorder; eexists; apply (@L1StepsMem ss c x x0); auto.
    Qed.

    Lemma L1StepsCore' : forall ss,
      (exists c, exists msg,
        ProgToL1 ss c = Some msg
        /\ exists a, ProgToL1Rule (L1 ss (c := c)) msg = Some a
          /\ (forall msg, LSend a = Some (L1Q msg) -> L1ToMemQ ss c = None)
          /\ (forall msg, LSend a = Some (L1Y msg) -> L1ToMemY ss c = None))
      -> exists s', step ss s'.
      firstorder; eexists; apply (@L1StepsCore ss x x0 x1); auto.
    Qed.

    Lemma MemStepsQ' : forall ss,
      (exists c, exists msg,
        L1ToMemY ss c = None
        /\ L1ToMemQ ss c = Some msg
        /\ exists a, L1ToMemRule c (Memory ss) (L1Q msg) = Some a
          /\ MemToL1 ss (MSendTo a) = None)
      -> exists s', step ss s'.
      firstorder; eexists; apply (@MemStepsQ ss x x0 x1); auto.
    Qed.

    Lemma MemStepsY' : forall ss,
      (exists c, exists msg,
        L1ToMemY ss c = Some msg
        /\ exists a, L1ToMemRule c (Memory ss) (L1Y msg) = Some a
        /\ MemToL1 ss (MSendTo a) = None)
      -> exists s', step ss s'.
      firstorder; eexists; apply (@MemStepsY ss x x0 x1); auto.
    Qed.

    (* The definition of deadlock-freeness folds in a state invariant. *)
    Variable invariant : systemState -> Prop.

    Definition deadlockFree := invariant state0
      /\ (forall s, invariant s -> exists s', step s s')
      /\ (forall s, invariant s -> forall s', step s s' -> invariant s').

    Ltac prime lemma := firstorder; repeat (esplit || red); eauto; eapply lemma; eauto.

    (* Some useful lemmas for proving deadlock freedom *)

  End rules.


  (** * A correct set of rules *)

  Definition L1ToMemRule (this : cache) : l1ToMemRule := fun ms msg =>
    let other := match this with L1_0 => L1_1 | L1_1 => L1_0 end in
      let updateThis z x := upd cache_eq (CS ms) this (upd (line_eq (c := this)) (CS ms (c := this)) (cacheLine z this) x) in
      let updateOther z x := upd cache_eq (CS ms) other (upd (line_eq (c := other)) (CS ms (c := other)) (cacheLine z other) x) in
      let updateThisOther z x1 x2 :=
        upd cache_eq (upd cache_eq (CS ms) this (upd (line_eq (c := this)) (CS ms (c := this)) (cacheLine z this) x1))
          other (upd (line_eq (c := other)) (CS ms (c := other)) (cacheLine z other) x2) in
       match msg with
         | L1Q (CQm z) =>
           match CS ms (cacheLine z this) with
             | I =>
               match CS ms (cacheLine z other) with
                 | I => Some {| MSendTo := this;
                   MMessage := PYm z (A ms z);
                   MNewState := {| A := A ms;
                     CS := updateThis z M |} |}
                 | CL _ => Some {| MSendTo := other;
                   MMessage := PQi z;
                   MNewState := {| A := A ms;
                     CS := updateThisOther z WM CP |} |}
                 | _ => None
               end
             | S =>
               match CS ms (cacheLine z other) with
                 | I => Some {| MSendTo := this;
                   MMessage := PYm z (A ms z);
                   MNewState := {| A := A ms;
                     CS := updateThis z M |} |}
                 | S => Some {| MSendTo := other;
                   MMessage := PQi z;
                   MNewState := {| A := A ms;
                     CS := updateThisOther z WM CP |} |}
                 | _ => None
               end
             | _ => None
           end

         | L1Q (CQs z) =>
           match CS ms (cacheLine z this) with
             | I =>
               match CS ms (cacheLine z other) with
                 | I => Some {| MSendTo := this;
                   MMessage := PYs z (A ms z);
                   MNewState := {| A := A ms;
                     CS := updateThis z S |} |}
                 | M => Some {| MSendTo := this;
                   MMessage := PQs z;
                   MNewState := {| A := A ms;
                     CS := updateThisOther z WS CP |} |}
                 | S => Some {| MSendTo := other;
                   MMessage := PYs z (A ms z);
                   MNewState := {| A := A ms;
                     CS := updateThis z S |} |}
                 | _ => None
               end
             | _ => None
           end

         | L1Y (CYiM z d) =>
           match CS ms (cacheLine z this) with
             | M =>
               match CS ms (cacheLine z other) with
                 | I =>
                   Some {| MSendTo := this;
                     MMessage := PQi z;
                     MNewState := {| A := upd address_eq (A ms) z d;
                       CS := updateThis z I |} |}
                 | _ => None
               end
             | CP =>
               match CS ms (cacheLine z other) with
                 | WM =>
                   Some {| MSendTo := other;
                     MMessage := PYm z d;
                     MNewState := {| A := upd address_eq (A ms) z d;
                       CS := updateThisOther z I M |} |}
                 | WS =>
                   Some {| MSendTo := other;
                     MMessage := PYm z d;
                     MNewState := {| A := upd address_eq (A ms) z d;
                       CS := updateThisOther z I S |} |}
                 | _ => None
               end
             | _ => None
           end

         | L1Y (CYiS z) =>
           match CS ms (cacheLine z this) with
             | CP =>
               match CS ms (cacheLine z other) with
                 | WM => Some {| MSendTo := other;
                   MMessage := PYm z (A ms z);
                   MNewState := {| A := A ms;
                     CS := updateThisOther z I M |} |}
                 | _ => None
               end
             | S =>
               match CS ms (cacheLine z other) with
                 | I =>
                   Some {| MSendTo := this;
                     MMessage := PQi z;
                     MNewState := {| A := A ms;
                       CS := updateThis z I |} |}
                 | S =>
                   Some {| MSendTo := this;
                     MMessage := PQi z;
                     MNewState := {| A := A ms;
                       CS := updateThis z I |} |}
                 | _ => None
               end
             | _ => None
           end

         | L1Y (CYs z d) =>
           match CS ms (cacheLine z this) with
             | CP =>
               match CS ms (cacheLine z other) with
                 | WS =>
                   Some {| MSendTo := other;
                     MMessage := PYs z d;
                     MNewState := {| A := upd address_eq (A ms) z d;
                       CS := updateThisOther z S S |} |}
                 | _ => None
               end
             | _ => None
           end
       end.

  Definition ProgToL1Rule (c : cache) : progToL1Rule c := fun l1s msg =>
    match msg with
      | PrM z =>
        let ln := cacheLine z c in
        let s := l1s ln in
          match PS s with
            | N =>
              match LS s as st return maybeData st -> _ with
                | I => fun _ => Some {| LSend := Some (L1Q (CQm z));
                  LWhichLine := ln;
                  LNewState := {| LS := I;
                    D := tt;
                    PS := PP |} |}
                | M => fun ad =>
                  if address_eq z (fst ad) then
                    Some {| LSend := None;
                      LWhichLine := ln;
                      LNewState := s |}
                  else
                    Some {| LSend := Some (L1Y (CYiM (fst ad) (snd ad)));
                      LWhichLine := ln;
                      LNewState := {| LS := I;
                        D := tt;
                        PS := W |}|}
                | S => fun ad =>
                  if address_eq z (fst ad) then
                    Some {| LSend := Some (L1Q (CQm z));
                      LWhichLine := ln;
                      LNewState := {| LS := S;
                        D := ad;
                        PS := PP |} |}
                  else
                    Some {| LSend := Some (L1Y (CYiS (fst ad)));
                      LWhichLine := ln;
                      LNewState := {| LS := I;
                        D := tt;
                        PS := W |} |}
              end (D s)
            | _ => None
          end

      | PrS z =>
        let ln := cacheLine z c in
        let s := l1s ln in
          match PS s with
            | N =>
              match LS s as st return maybeData st -> _ with
                | I => fun _ => Some {| LSend := Some (L1Q (CQs z));
                  LWhichLine := ln;
                  LNewState := {| LS := I;
                    D := tt;
                    PS := PP |} |}
                | M => fun ad =>
                  if address_eq z (fst ad) then
                    Some {| LSend := None;
                      LWhichLine := ln;
                      LNewState := s |}
                  else
                    Some {| LSend := Some (L1Y (CYiM (fst ad) (snd ad)));
                      LWhichLine := ln;
                      LNewState := {| LS := I;
                        D := tt;
                        PS := W |}|}
                | S => fun ad =>
                  if address_eq z (fst ad) then
                    Some {| LSend := None;
                      LWhichLine := ln;
                      LNewState := s |}
                  else
                    Some {| LSend := Some (L1Y (CYiS (fst ad)));
                      LWhichLine := ln;
                      LNewState := {| LS := I;
                        D := tt;
                        PS := W |} |}
              end (D s)
            | _ => None
          end
    end.

  Definition MemToL1Rule (c : cache) : memToL1Rule c := fun l1s msg =>
    match msg with
      | PQi z =>
        let ln := cacheLine z c in
        let s := l1s ln in
          match LS s as st return maybeData st -> _ with
            | I => fun _ =>
              match PS s with
                | W => Some {| LSend := None;
                  LWhichLine := ln;
                  LNewState := {| LS := I;
                    D := tt;
                    PS := N |} |}
                | PP => Some {| LSend := None;
                  LWhichLine := ln;
                  LNewState := s |}
                | _ => None
              end
            | M => fun ad =>
              if address_eq z (fst ad) then
                match PS s with
                  | N => Some {| LSend := Some (L1Y (CYiM z (snd ad)));
                    LWhichLine := ln;
                    LNewState := {| LS := I;
                      D := tt;
                      PS := N |} |}
                  | _ => None
                end
              else
                None
            | S => fun ad =>
              if address_eq z (fst ad) then
                match PS s with
                  | N => Some {| LSend := Some (L1Y (CYiS z));
                    LWhichLine := ln;
                    LNewState := {| LS := I;
                      D := tt;
                      PS := N |} |}
                  | PP => Some {| LSend := Some (L1Y (CYiS z));
                    LWhichLine := ln;
                    LNewState := {| LS := I;
                      D := tt;
                      PS := PP |} |}
                  | _ => None
                end
              else
                None
          end (D s)

      | PQs z =>
        let ln := cacheLine z c in
        let s := l1s ln in
          match LS s as st return maybeData st -> _ with
            | I => fun _ =>
              match PS s with
                | W => Some {| LSend := None;
                  LWhichLine := ln;
                  LNewState := {| LS := I;
                    D := tt;
                    PS := N |} |}
                | _ => None
              end
            | M => fun ad =>
              if address_eq z (fst ad) then
                match PS s with
                  | N => Some {| LSend := Some (L1Y (CYs z (snd ad)));
                    LWhichLine := ln;
                    LNewState := {| LS := S;
                      D := ad;
                      PS := N |} |}
                  | _ => None
                end
              else
                None
            | _ => fun _ => None
          end (D s)

      | PYm z d =>
        let ln := cacheLine z c in
        let s := l1s ln in
          match PS s with
            | PP =>
              match LS s as st return maybeData st -> _ with
                | I => fun _ => Some {| LSend := None;
                  LWhichLine := ln;
                  LNewState := {| LS := M;
                    D := (z, d);
                    PS := N |} |}
                | S => fun ad =>
                  if address_eq z (fst ad) then
                    Some {| LSend := None;
                      LWhichLine := ln;
                      LNewState := {| LS := M;
                        D := (z, d);
                        PS := N |} |}
                  else
                    None
                | _ => fun _ => None
              end (D s)
            | _ => None
          end

      | PYs z d =>
        let ln := cacheLine z c in
        let s := l1s ln in
          match PS s with
            | PP =>
              match LS s as st return maybeData st -> _ with
                | I => fun _ => Some {| LSend := None;
                  LWhichLine := ln;
                  LNewState := {| LS := S;
                    D := (z, d);
                    PS := N |} |}
                | _ => fun _ => None
              end (D s)
            | _ => None
          end
    end.


  (** * Proving correctness *)

  (* Invariant connecting child states *)
  Definition childChild (s : systemState) (z : address) :=
    let cs0 := CS (Memory s) (cacheLine z L1_0) in
    let cs1 := CS (Memory s) (cacheLine z L1_1) in
    (cs0 = CL M -> cs1 = CL I)
    /\ (cs1 = CL M -> cs0 = CL I)
    /\ (cs0 = CP -> cs1 <> WS -> cs1 = WM)
    /\ (cs1 = CP -> cs0 <> WS -> cs0 = WM)
    /\ (cs0 = WS -> cs1 = CP)
    /\ (cs0 = WM -> cs1 = CP)
    /\ (cs1 = WS -> cs0 = CP)
    /\ (cs1 = WM -> cs0 = CP).

  (* Invariant connecting location and parent states *)
  Definition locationParent (s : systemState) (z : address) (c : cache) :=
    let ls := LS (L1 s (cacheLine z c)) in
    let ps := PS (L1 s (cacheLine z c)) in
      (ls = M -> ps = N)
      /\ (ls = S -> ps <> W).

  (* Invariant connecting corresponding parent and child states *)
  Definition parentChild (s : systemState) (z : address) (c : cache) :=
    let cs := CS (Memory s) (cacheLine z c) in
    let ls := LS (L1 s (cacheLine z c)) in
    let ps := PS (L1 s (cacheLine z c)) in
      (cs = S -> ls <> M)
      /\ (cs = I -> ls = I).

  (* When do we know that a wire is free? *)
  Definition wireFree (s : systemState) (z : address) (c : cache) :=
    (MemToL1 s c = Some (PQi z)
      -> L1ToMemY s c = None)
    /\ (MemToL1 s c = Some (PQs z)
      -> L1ToMemY s c = None).

  (* We know the memory won't ask an L1 about an irrelevant address. *)
  Definition noIrrelevant (s : systemState) (z : address) (c : cache) :=
    forall msg, MemToL1 s c = Some msg
      -> (msg = PQi z \/ msg = PQs z \/ exists d, msg = PYm z d \/ msg = PYs z d)
      -> match LS (L1 s (cacheLine z c)) as L return maybeData L -> _ with
        | I => fun _ => True
        | _ => fun md => fst md = z
      end (D (L1 s (cacheLine z c))).

  (* Some messages are only sent to receivers in certain states. *)
  Definition legalStates (s : systemState) (z : address) (c c' : cache) :=
    (MemToL1 s c = Some (PQi z)
      -> LS (L1 s (cacheLine z c)) = I
      -> PS (L1 s (cacheLine z c)) = N
      -> False)
    /\ (MemToL1 s c = Some (PQs z)
      -> LS (L1 s (cacheLine z c)) = S
      -> False)
    /\ (MemToL1 s c = Some (PQs z)
      -> LS (L1 s (cacheLine z c)) = I
      -> PS (L1 s (cacheLine z c)) <> W
      -> False)
    /\ ((exists d, MemToL1 s c = Some (PYm z d))
      -> PS (L1 s (cacheLine z c)) = PP)
    /\ ((exists d, MemToL1 s c = Some (PYs z d))
      -> LS (L1 s (cacheLine z c)) = I
      /\ PS (L1 s (cacheLine z c)) = PP)
    /\ ((exists d, L1ToMemY s c = Some (CYiM z d))
      -> CS (Memory s) (cacheLine z c) <> M
      -> CS (Memory s) (cacheLine z c) = CP)
    /\ (L1ToMemY s c = Some (CYiS z)
      -> CS (Memory s) (cacheLine z c) <> S
      -> CS (Memory s) (cacheLine z c') = WM)
    /\ ((exists d, L1ToMemY s c = Some (CYs z d))
      -> CS (Memory s) (cacheLine z c) = CP
      /\ CS (Memory s) (cacheLine z c') = WS).

  Definition invariant' (s : systemState) (z : address) (c c' : cache) :=
    locationParent s z c
    /\ parentChild s z c
    /\ wireFree s z c
    /\ noIrrelevant s z c
    /\ legalStates s z c c'.

  Definition invariant (s : systemState) :=
    forall z, childChild s z
      /\ invariant' s z L1_0 L1_1
      /\ invariant' s z L1_1 L1_0.

  Ltac unfolder := unfold invariant, invariant', childChild, locationParent, parentChild, wireFree, noIrrelevant, legalStates in *.

  Hint Extern 1 (_ = _ -> False) => discriminate.
  Hint Extern 1 (_ = _) => congruence.
  Hint Extern 1 (_ <> _) => congruence.

  Lemma upd_split : forall T c cs ln1 v ln2 v',
    upd (ran := fun _ => T) (@line_eq c) cs ln1 v ln2 = v'
    -> (ln1 = ln2 /\ v = v') \/ cs ln2 = v'.
    intros; destruct (line_eq ln1 ln2); subst; autorewrite with upd; tauto.
  Qed.

  Ltac cautious_eq E :=
    match E with
      | context[Build_memoryAction] => fail 1
      | context[Build_l1Action] => fail 1
      | LS ?E => case_eq E
      | PS ?E => case_eq E
      | _ =>
        match goal with
          | [ x : _ |- _ ] =>
            match x with
              | E => destruct x
            end
          | _ => case_eq E
        end
    end.

  Ltac oneSplit :=
    match goal with
      | [ |- exists a, ?E = _ /\ _ ] =>
        match E with
          | if ?E then _ else _ => destruct E
          | match ?E with None => _ | Some _ => _ end => cautious_eq E
          | match ?E with M => _ | S => _ | I => _ end => cautious_eq E
          | match ?E with M => _ | S => _ | I => _ end _ => cautious_eq E
          | match ?E with CL _ => _ | CP => _ | WS => _ | WM => _ end => cautious_eq E
          | match ?E with PP => _ | W => _ | N => _ end => cautious_eq E
          | match ?E with PrM _ => _ | PrS _ => _ end => cautious_eq E
          | match ?E with CQm _ => _ | CQs _ => _ end => cautious_eq E
          | match ?E with CYiS _ => _ | CYiM _ _ => _ | CYs _ _ => _ end => cautious_eq E
          | match ?E with L1Q _ => _ | L1Y _ => _ end => cautious_eq E
          | match ?E with PQi _ => _ | PQs _ => _ | PYm _ _ => _ | PYs _ _ => _ end => cautious_eq E
        end
    end; intros; subst; simpl; try solve [ congruence ].

  Ltac upd :=
    let doDestr x := let Heq := fresh "Heq" in case_eq x; intros ? ? ? Heq; try rewrite Heq in *; simpl in *; subst in
      repeat match goal with
               | [ _ : PS ?x = _ |- _ ] => doDestr x
               | [ _ : LS ?x = _ |- _ ] => doDestr x
               | [ |- context[PS ?x] ] => doDestr x
               | [ |- context[LS ?x] ] => doDestr x
             end;
      repeat (match goal with
                | [ H : _ |- _ ] => apply upd_split in H
              end; intuition; try discriminate; autorewrite with upd in *).

  Ltac useInv' := match goal with
                    | [ H : invariant _|- _ ] =>
                      try match goal with
                            | [ z : address |- _ ] => generalize (H z); intro
                            | [ _ : context[cacheLine ?z _] |- _ ] => generalize (H z); intro
                          end;
                      try match goal with
                            | [ x : maybeData _ |- _ ] => generalize (H (fst x)); intro
                          end; clear H; unfolder;
                      repeat match goal with
                               | [ H : L1 _ _ = _ |- _ ] => progress rewrite H in *; simpl in *
                               | [ H : L1 _ _ = _, H' : cacheLine _ _ = cacheLine _ _ |- _ ] => rewrite <- H' in *; clear H';
                                 progress rewrite H in *; simpl in *
                               | [ H : _ /\ _ |- _ ] => destruct H
                               | [ H : ?P -> _ |- _ ] =>
                                 let H' := fresh "H'" in assert (H' : P) by solve [ congruence | eauto 2 ]; specialize (H H'); clear H'
                               | [ H : forall x, _ -> _, H' : _ |- _ ] => specialize (H _ H')
                             end
                  end.

  Ltac useInv := solve [ elimtype False; eauto with irrelevant | useInv'; tauto || congruence ].

  Ltac knownStep := repeat (esplit || (progress unfold noIrrelevant, legalStates));
    simpl; intros; autorewrite with upd in *; upd; try congruence; try useInv.

  Ltac msgCase f c l :=
    match goal with
      | [ s : systemState |- _ ] =>
        case_eq (f s c); intros; [ eapply l;
          repeat match goal with
                   | [ |- ex _ ] => eexists
                 end;
          repeat match goal with
                   | [ |- _ /\ _ ] => esplit; [ eassumption | ]
                 end;
          unfold MemToL1Rule, L1ToMemRule, ProgToL1Rule | ]
    end.

  Ltac irrelevant := unfold invariant, invariant', noIrrelevant; intuition;
    match goal with
      | [ _ : ?x = ?y -> False |- _ ] => assert (y = x -> False) by congruence;
        match goal with
          | [ z : address, H : _, c : cache |- _ ] => specialize (H z); intuition;
            destruct c; match goal with
                          | [ H : L1 _ _ = _ |- _ ] => rewrite H in *
                        end; simpl in *; eauto 7
        end
    end.

  Lemma irrelevantPQiM : forall s c z d ps,
    invariant s
    -> MemToL1 s c = Some (PQi z)
    -> L1 s (cacheLine z c) = {| LS := M; D := d; PS := ps |}
    -> z <> fst d
    -> False.
    irrelevant.
  Qed.

  Lemma irrelevantPQiS : forall s c z d ps,
    invariant s
    -> MemToL1 s c = Some (PQi z)
    -> L1 s (cacheLine z c) = {| LS := S; D := d; PS := ps |}
    -> z <> fst d
    -> False.
    irrelevant.
  Qed.

  Lemma irrelevantPQsM : forall s c z d ps,
    invariant s
    -> MemToL1 s c = Some (PQs z)
    -> L1 s (cacheLine z c) = {| LS := M; D := d; PS := ps |}
    -> z <> fst d
    -> False.
    irrelevant.
  Qed.

  Lemma irrelevantPQsS : forall s c z d ps,
    invariant s
    -> MemToL1 s c = Some (PQs z)
    -> L1 s (cacheLine z c) = {| LS := S; D := d; PS := ps |}
    -> z <> fst d
    -> False.
    irrelevant.
  Qed.

  Lemma irrelevantPYmM : forall s c z d' d ps,
    invariant s
    -> MemToL1 s c = Some (PYm z d')
    -> L1 s (cacheLine z c) = {| LS := M; D := d; PS := ps |}
    -> z <> fst d
    -> False.
    irrelevant.
  Qed.

  Lemma irrelevantPYmS : forall s c z d' d ps,
    invariant s
    -> MemToL1 s c = Some (PYm z d')
    -> L1 s (cacheLine z c) = {| LS := S; D := d; PS := ps |}
    -> z <> fst d
    -> False.
    irrelevant.
  Qed.

  Lemma irrelevantPYsM : forall s c z d' d ps,
    invariant s
    -> MemToL1 s c = Some (PYs z d')
    -> L1 s (cacheLine z c) = {| LS := M; D := d; PS := ps |}
    -> z <> fst d
    -> False.
    irrelevant.
  Qed.

  Lemma irrelevantPYsS : forall s c z d' d ps,
    invariant s
    -> MemToL1 s c = Some (PYs z d')
    -> L1 s (cacheLine z c) = {| LS := S; D := d; PS := ps |}
    -> z <> fst d
    -> False.
    irrelevant.
  Qed.

  Hint Immediate irrelevantPQiM irrelevantPQiS irrelevantPQsM irrelevantPQsS
    irrelevantPYmM irrelevantPYmS irrelevantPYsM irrelevantPYsS : irrelevant.

  Theorem noDeadlock : deadlockFree L1ToMemRule ProgToL1Rule MemToL1Rule invariant.
    unfold deadlockFree; intuition.

    unfolder; unfold state0; simpl; intuition (repeat match goal with
                                                        | [ H : ex _ |- _ ] => destruct H
                                                      end; congruence).

    msgCase MemToL1 L1_0 L1StepsMem'.
    repeat oneSplit.
    useInv.
    useInv.
    knownStep.
    useInv.
    knownStep.
    useInv.
    knownStep.
    useInv.
    knownStep.
    knownStep.
    useInv.
    useInv.
    useInv.
    knownStep.
    useInv.
    useInv.
    useInv.
    knownStep.
    useInv.
    useInv.
    knownStep.
    useInv.
    knownStep.
    useInv.
    useInv.
    useInv.
    useInv.
    knownStep.
    useInv.
    useInv.
    
    msgCase MemToL1 L1_1 L1StepsMem'.
    repeat oneSplit.
    useInv.
    useInv.
    knownStep.
    useInv.
    knownStep.
    useInv.
    knownStep.
    useInv.
    knownStep.
    knownStep.
    useInv.
    useInv.
    useInv.
    knownStep.
    useInv.
    useInv.
    useInv.
    knownStep.
    useInv.
    useInv.
    knownStep.
    useInv.
    knownStep.
    useInv.
    useInv.
    useInv.
    useInv.
    knownStep.
    useInv.
    useInv.

    msgCase L1ToMemY L1_0 MemStepsY'.
    repeat oneSplit.
    useInv.
    useInv.
    knownStep.
    knownStep.
    useInv.
    useInv.
    useInv.
    useInv.
    useInv.
    useInv.
    useInv.
    knownStep.
    useInv.
    useInv.
    useInv.
    useInv.
    knownStep.
    useInv.
    useInv.
    useInv.
    useInv.
    useInv.
    useInv.
    useInv.
    knownStep.
    knownStep.
    useInv.
    useInv.
    useInv.
    useInv.
    useInv.
    knownStep.
    useInv.
    useInv.
    useInv.

    msgCase L1ToMemY L1_1 MemStepsY'.
    repeat oneSplit.
    useInv.
    useInv.
    knownStep.
    knownStep.
    useInv.
    useInv.
    useInv.
    useInv.
    useInv.
    useInv.
    useInv.
    knownStep.
    useInv.
    useInv.
    useInv.
    useInv.
    knownStep.
    useInv.
    useInv.
    useInv.
    useInv.
    useInv.
    useInv.
    useInv.
    knownStep.
    knownStep.
    useInv.
    useInv.
    useInv.
    useInv.
    useInv.
    knownStep.
    useInv.
    useInv.
    useInv.

    admit.

    admit.
  Qed.
  
End Hcc3.
