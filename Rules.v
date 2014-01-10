Require Import DataTypes Coq.Lists.Streams Coq.Logic.Classical_Prop Tree List MsiState Coq.Relations.Relation_Operators.

Record BaseMesg :=
  { fromB: State;
    toB: State;
    addrB: Addr;
    dataBM: StLabel
  }.

Record BaseReq :=
  { lbl: Label;
    lct: Addr;
    dsc: DataTypes.Desc;
    idx: Index
  }.

Record GlobalState :=
  { dt: Cache -> Addr -> StLabel;
    ch: ChannelType -> Cache -> Cache -> list BaseMesg;
    st: Cache -> Addr -> State;
    dirSt: Cache -> Cache -> Addr -> State;
    wt: Cache -> Addr -> bool;
    wtS: Cache -> Addr -> State;
    dirWt: Cache -> Cache -> Addr -> bool;
    dirWtS: Cache -> Cache -> Addr -> State;
    req: Cache -> Stream BaseReq;
    resp: Cache -> option BaseReq
  }.

Definition dmy := Build_BaseMesg In In zero Initial.

Inductive Transition (s: GlobalState) : GlobalState -> Prop :=
| LoadReq: forall {c}, defined c -> leaf c -> dsc (Streams.hd (req s c)) = Ld ->
                       sle Sh (st s c (lct (Streams.hd (req s c)))) -> 
                       Transition s {|
                                    dt := dt s;
                                    ch := ch s;
                                    st := st s;
                                    dirSt := dirSt s;
                                    wt := wt s;
                                    wtS := wtS s;
                                    dirWt := dirWt s;
                                    dirWtS := dirWtS s;
                                    req := fun t => match decTree t c with
                                                      | left _ => Streams.tl (req s t)
                                                      | right _ => req s t
                                                    end;
                                    resp := fun t => match decTree t c with
                                                       | left _ => Some (Streams.hd (req s c))
                                                       | right _ => None
                                                     end
                                  |}
| StoreReq: forall {c}, defined c -> leaf c -> dsc (Streams.hd (req s c)) = St ->
                        (st s c (lct (Streams.hd (req s c))) = Mo) ->
                        Transition s {|
                                     dt := dt s;
                                     ch := ch s;
                                     st := st s;
                                     dirSt := dirSt s;
                                     wt := wt s;
                                     wtS := wtS s;
                                     dirWt := dirWt s;
                                     dirWtS := dirWtS s;
                                     req := fun t => match decTree t c with
                                                       | left _ => Streams.tl (req s t)
                                                       | right _ => req s t
                                                     end;
                                     resp := fun t => match decTree t c with
                                                        | left _ => Some (Streams.hd (req s c))
                                                        | right _ => None
                                                      end
                                   |}
| ChildSendReq: forall {p c}, defined p -> defined c -> parent c p ->
                              forall {x a}, slt (st s c a) x -> wt s c a = false ->
                                            Transition s {|
                                                         dt := dt s;
                                                         ch := fun t w z =>
                                                                 match t, decTree w c,
                                                                       decTree z p with
                                                                   | rch, left _, left _ =>
                                                                       (Build_BaseMesg
                                                                          (st s z a)
                                                                          x a Initial)
                                                                         :: ch s t w z
                                                                   | _, _, _ => ch s t w z
                                                                 end;
                                                         st := st s;
                                                         dirSt := dirSt s;
                                                         wt := fun t w => match decTree t c, decAddr w a with
                                                                            | left _, left _ => true
                                                                            | _, _ => wt s t w
                                                                          end;
                                                         wtS := fun t w => match decTree t c, decAddr w a with
                                                                             | left _, left _ => x
                                                                             | _, _ => wtS s t w
                                                                           end;
                                                         dirWt := dirWt s;
                                                         dirWtS := dirWtS s;
                                                         req := req s;
                                                         resp := fun t => None
                                                       |}
| ParentRecvReq: forall {p c}, defined p -> defined c -> parent c p ->
                               ch s rch c p <> nil -> let r := last (ch s rch c p) dmy in
                                                        let fromR := fromB r in
                                                          let toR := toB r in
                                                            let a := addrB r in
                                                              sle toR (st s p a) ->
                               (forall i, defined i -> i <> c -> parent i p ->
                                          sle (dirSt s p i a)
                                              match toR with
                                                | Mo => In
                                                | Sh => Sh
                                                | In => Mo
                                              end) ->
                               dirWt s p c a = false ->
                               sle (dirSt s p c a) fromR ->
                               Transition s {| ch := fun t w z =>
                                                       match t, decTree w p,
                                                             decTree z c with
                                                         | mch, left _, left _ =>
                                                             (Build_BaseMesg
                                                                (dirSt s w z a) toR a (dt s w a))
                                                               :: ch s t w z
                                                         | _, _, _ =>
                                                             match t, decTree w c,
                                                                   decTree z p with
                                                               | rch, left _, left _ => removelast
                                                                                          (ch s t w z)
                                                               | _, _, _ => ch s t w z
                                                             end
                                                       end;
                                               dt := dt s;
                                               st := st s;
                                               dirSt := fun t w z => match decTree t p, decTree w c,
                                                                           decAddr z a with
                                                                       | left _, left _, left _ => toR
                                                                       | _, _, _ => dirSt s t w z
                                                                     end;
                                               wt := wt s;
                                               wtS := wtS s;
                                               dirWt := dirWt s;
                                               dirWtS := dirWtS s;
                                               req := req s;
                                               resp := fun t => None
                                            |}
| ChildRecvResp: forall {p c}, defined p -> defined c -> parent c p ->
                               ch s mch p c <> nil ->
                               let m := last (ch s mch p c) dmy in
                                 let fromM := fromB m in
                                   let toM := toB m in
                                     let a := addrB m in
                                       let d := dataBM m in
                                         Transition s {| dt := fun t w => match decTree t c, decAddr w a with
                                                                            | left _, left _ =>
                                                                                match st s t w with
                                                                                  | In => d
                                                                                  | _ => dt s t w
                                                                                end
                                                                            | _, _ => dt s t w
                                                                          end;
                                                         ch := fun t w z =>
                                                                 match t, decTree w p,
                                                                       decTree z c with
                                                                   | mch, left _, left _ => removelast (ch s t w z)
                                                                   | _, _, _ => ch s t w z
                                                                 end;
                                                         st := fun t w => match decTree t c, decAddr w a with
                                                                            | left _, left _ => toM
                                                                            | _, _ => st s t w
                                                                          end;
                                                         dirSt := dirSt s;
                                                         wt := fun t w => match decTree t c, decAddr w a with
                                                                            | left _, left _ =>
                                                                                match decSle (wtS s t w) toM with
                                                                                  | true => false
                                                                                  | _ => wt s t w
                                                                                end
                                                                            | _, _ => wt s t w
                                                                          end;
                                                         wtS := wtS s;
                                                         dirWt := dirWt s;
                                                         dirWtS := dirWtS s;
                                                         req := req s;
                                                         resp := fun t => None
                                                      |}
| ParentSendReq: forall {p c}, defined p -> defined c -> parent c p ->
                               forall {x a}, slt (dirSt s p c a) x -> dirWt s p c a = false ->
                                             Transition s {|
                                                          dt := dt s;
                                                          ch := fun t w z =>
                                                                  match t, decTree w p,
                                                                        decTree z c with
                                                                    | rch, left _, left _ =>
                                                                        (Build_BaseMesg
                                                                           (dirSt s w z a)
                                                                           x a Initial)
                                                                          :: ch s t w z
                                                                    | _, _, _ => ch s t w z
                                                                  end;
                                                          st := st s;
                                                          dirSt := dirSt s;
                                                          wt := wt s;
                                                          wtS := wtS s;
                                                          dirWt := fun t w z => match decTree t p, decTree w c,
                                                                                      decAddr z a
                                                                                with
                                                                                  | left _, left _, left _ =>
                                                                                      true
                                                                                  | _, _, _ => dirWt s t w z
                                                                                end;
                                                          dirWtS := fun t w z => match decTree t p, decTree w c,
                                                                                       decAddr z a with
                                                                                   | left _, left _, left _ => x
                                                                                   | _, _, _ => dirWtS s t w z
                                                                                 end;
                                                          req := req s;
                                                          resp := fun t => None
                                                        |}
| ChildRecvReq: forall {p c}, defined p -> defined c -> parent c p ->
                              ch s rch p c <> nil ->
                              let r := last (ch s rch p c) dmy in
                                let fromR := fromB r in
                                  let toR := toB r in
                                    let a := addrB r in
                                      let d := dataBM r in
                                        slt toR (st s c a) ->
                              (forall {i}, defined i -> parent i c -> sle (dirSt s c i a) toR) ->
                              Transition s {| ch := fun t w z =>
                                                      match t, decTree w c,
                                                            decTree z p with
                                                        | mch, left _, left _ =>
                                                            (Build_BaseMesg
                                                               (st s w a) toR a (dt s w a))
                                                              :: ch s t w z
                                                        | _, _, _ =>
                                                            match t, decTree w p,
                                                                  decTree z c with
                                                              | rch, left _, left _ => removelast
                                                                                         (ch s t w z)
                                                              | _, _, _ => ch s t w z
                                                            end
                                                      end;
                                              dt := dt s;
                                              st := fun t w => match decTree t c, decAddr w a with
                                                                 | left _, left _ => toR
                                                                 | _, _ => st s t w
                                                               end;
                                              dirSt := dirSt s;
                                              wt := wt s;
                                              wtS := wtS s;
                                              dirWt := dirWt s;
                                              dirWtS := dirWtS s;
                                              req := req s;
                                              resp := fun t => None
                                           |}
| ParentRecvResp: forall {p c}, defined p -> defined c -> parent c p ->
                                ch s mch c p <> nil ->
                                let m := last (ch s mch c p) dmy in
                                  let fromM := fromB m in
                                    let toM := toB m in
                                      let a := addrB m in
                                        let d := dataBM m in
                                          Transition s {| dt := fun t w => match decTree t p, decAddr w a with
                                                                             | left _, left _ =>
                                                                                 match dirSt s t c w with
                                                                                   | Mo => d
                                                                                   | _ => dt s t w
                                                                                 end
                                                                             | _, _ => dt s t w
                                                                           end;
                                                          ch := fun t w z =>
                                                                  match t, decTree w c,
                                                                        decTree z p with
                                                                    | mch, left _, left _ => removelast (ch s t w z)
                                                                    | _, _, _ => ch s t w z
                                                                  end;
                                                          st := st s;
                                                          dirSt := fun t w z => match decTree t p, decTree w c,
                                                                                      decAddr z a with
                                                                                  | left _, left _, left _ => toM
                                                                                  | _, _, _ => dirSt s t w z
                                                                                end;
                                                          wt := wt s;
                                                          wtS := wtS s;
                                                          dirWt := fun t w z => match decTree t p, decTree w c,
                                                                                      decAddr z a with
                                                                                  | left _, left _, left _ =>
                                                                                      match decSle toM (dirWtS s t w z)
                                                                                      with
                                                                                        | true => false
                                                                                        | _ => dirWt s t w z
                                                                                      end
                                                                                  | _, _, _ => dirWt s t w z
                                                                                end;
                                                          dirWtS := dirWtS s;
                                                          req := req s;
                                                          resp := fun t => None
                                                       |}

| ChildVolResp: forall {p c}, defined p -> defined c -> parent c p ->
                              forall {x a},
                                slt x (st s c a) ->
                                (forall {i}, defined i -> parent i c -> sle (dirSt s c i a) x) ->
                                wt s c a = false ->
                                Transition s {| ch := fun t w z =>
                                                        match t, decTree w c,
                                                              decTree z p with
                                                          | mch, left _, left _ =>
                                                              (Build_BaseMesg
                                                                 (st s w a) x a (dt s w a))
                                                                :: ch s t w z
                                                          | _, _, _ => ch s t w z
                                                        end;
                                                dt := dt s;
                                                st := fun t w => match decTree t c, decAddr w a with
                                                                   | left _, left _ => x
                                                                   | _, _ => st s t w
                                                                 end;
                                                dirSt := dirSt s;
                                                wt := wt s;
                                                wtS := wtS s;
                                                dirWt := dirWt s;
                                                dirWtS := dirWtS s;
                                                req := req s;
                                                resp := fun t => None
                                             |}
| ChildDropReq: forall {p c}, defined p -> defined c -> parent c p ->
                              ch s rch p c <> nil ->
                              let r := last (ch s rch p c) dmy in
                                let fromR := fromB r in
                                  let toR := toB r in
                                    let a := addrB r in
                                      let d := dataBM r in
                                        sle (st s c a) toR ->
                              Transition s {| ch := fun t w z =>
                                                      match t, decTree w p,
                                                            decTree z c with
                                                        | rch, left _, left _ => removelast
                                                                                   (ch s t w z)
                                                        | _, _, _ => ch s t w z
                                                      end;
                                              dt := dt s;
                                              st := st s;
                                              dirSt := dirSt s;
                                              wt := wt s;
                                              wtS := wtS s;
                                              dirWt := dirWt s;
                                              dirWtS := dirWtS s;
                                              req := req s;
                                              resp := fun t => None
                                           |}.

Parameter reqs: Cache -> Stream BaseReq.

Definition tlStr {A} (l l': Stream A) := l' = Streams.tl l.

Definition subStr := clos_refl_trans (Stream BaseReq) tlStr.

Axiom reqsGood: forall {l1 l2}, subStr l1 l2 -> l1 <> l2 ->
                                idx (Streams.hd l1) < idx (Streams.hd l2).

Definition initGlobalState :=
  {| dt := fun t w => Initial;
     ch := fun t w z => nil;
     st := fun t w => match decTree t hier with
                        | left _ => Mo
                        | right _ => In
                      end;
     dirSt := fun t w z => In;
     wt := fun t w => false;
     wtS := fun t w => In;
     dirWt := fun t w z => false;
     dirWtS := fun t w z => In;
     req := reqs;
     resp := fun t => None
  |}.

Definition Behavior := {sys: (Time -> GlobalState)|
                        sys 0 = initGlobalState /\
                                                (forall {t}, Transition (sys t) (sys (S t)))
                       }.

Parameter oneBeh: Behavior.


Module mkDataTypes <: DataTypes.

  Definition state c a t := match oneBeh with
                              | exist sys _ => st (sys t) c a
                            end.
  Definition dir p c a t := match oneBeh with
                              | exist sys _ => dirSt (sys t) p c a
                            end.
  Definition wait c a t := match oneBeh with
                             | exist sys _ => wt (sys t) c a
                           end.
  Definition waitS c a t := match oneBeh with
                              | exist sys _ => wtS (sys t) c a
                            end.
  Definition dwait p c a t := match oneBeh with
                                | exist sys _ => dirWt (sys t) p c a
                              end.
  Definition dwaitS p c a t := match oneBeh with
                                 | exist sys _ => dirWtS (sys t) p c a
                               end.
  Definition data c a t := match oneBeh with
                             | exist sys _ => dt (sys t) c a
                           end.

  Definition mark c src dst t m := match oneBeh with
                                     | exist sys _ =>
                                         ch (sys (S t)) c src dst <> nil /\
                                            ch (sys t) c src dst = tl (ch (sys (S t)) c src dst) /\
                                                                      let m' := hd dmy (ch (sys (S t)) c src dst) in
                                                                        from m = fromB m' /\ to m = toB m' /\ addr m = addrB m' /\
                                                                                                                             dataM m = dataBM m' /\ msgId m = t
                                   end.

  Definition recv c src dst t m := match oneBeh with
                                     | exist sys _ =>
                                         ch (sys t) c src dst <> nil /\
                                            ch (sys (S t)) c src dst = removelast (ch (sys t) c src dst) /\
                                                                                  let m' := last (ch (sys t) c src dst) dmy in
                                                                                    from m = fromB m' /\ to m = toB m' /\ addr m = addrB m' /\
                                                                                                                                         dataM m = dataBM m' /\ msgId m = t
                                   end.

  Definition send := mark.
  Definition proc := recv.
  Definition deq := recv.


  Definition deqR c l a d i t
    := match oneBeh with
         | exist sys _ =>
             match (resp (sys (S t)) c) with
               | Some r => lbl r = l /\ lct r = a /\ dsc r = d /\ idx r = i
               | None => False
             end
       end.

  Definition enqLd c l sl t :=
    match oneBeh with
      | exist sys _ =>
          match (resp (sys (S t)) c) with
            | Some r => lbl r = l /\ dt (sys t) c (lct r) = sl /\ dsc r = Ld
            | None => False
          end
    end.

  Definition enqSt c l t :=
    match oneBeh with
      | exist sys _ =>
          match (resp (sys (S t)) c) with
            | Some r => lbl r = l /\ dsc r = St
            | None => False
          end
    end.

  
End mkDataTypes.
