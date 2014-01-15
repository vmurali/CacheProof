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
    req: Cache -> Stream BaseReq
  }.

Definition dmy := Build_BaseMesg In In zero Initial.

Inductive Transition (s: GlobalState) : GlobalState -> Set :=
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
                                                    end
                                  |}
| StoreReq: forall {c}, defined c -> leaf c -> dsc (Streams.hd (req s c)) = St ->
                        (st s c (lct (Streams.hd (req s c))) = Mo) ->
                        Transition s {|
                                     dt := fun t w => match decTree t c with
                                                      | left _ => match decAddr w (lct (Streams.hd (req s t))) with
                                                                    | left _ => Store (lbl (Streams.hd (req s t)))
                                                                    | right _ => dt s t w
                                                                  end
                                                      | right _ => dt s t w
                                                      end;
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
                                                         req := req s
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
                                               req := req s
                                            |}
| ChildRecvResp: forall {p c}, defined p -> defined c -> parent c p ->
                               ch s mch p c <> nil ->
                               let m := last (ch s mch p c) dmy in
                                 let fromM := fromB m in
                                   let toM := toB m in
                                     let a := addrB m in
                                       let d := dataBM m in
                                         Transition s {| dt := fun t w =>
                                                                 match decTree t c,
                                                                       decAddr w a with
                                                                   | left _, left _ =>
                                                                     match fromB m with
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
                                                         req := req s
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
                                                          req := req s
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
                                              req := req s
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
                                                                                 match fromB m with
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
                                                          req := req s
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
                                                req := req s
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
                                              req := req s
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
     req := reqs
  |}.

Record Behavior := {
                    sys: Time -> GlobalState;
                    init: sys 0 = initGlobalState;
                    trans: forall t, Transition (sys t) (sys (S t))
                  }.

Parameter oneBeh: Behavior.

Fixpoint labelCh t ch src dst :=
  match t with
    | 0 => nil
    | S t => match (trans oneBeh) t with
               | ChildSendReq p c _ _ _ _ _ _ _ =>
                 match ch with
                   | rch =>
                     if (decTree c src)
                     then if (decTree p dst)
                          then t :: labelCh t ch src dst
                          else labelCh t ch src dst
                     else labelCh t ch src dst
                   | mch => labelCh t ch src dst
                 end
               | ParentRecvReq p c _ _ _ _ _ _ _ _ =>
                 match ch with
                   | rch =>
                     if (decTree p dst)
                     then if (decTree c src)
                          then removelast (labelCh t ch src dst)
                          else labelCh t ch src dst
                     else labelCh t ch src dst
                   | mch =>
                     if (decTree c dst)
                     then if (decTree p src)
                          then t :: labelCh t ch src dst
                          else labelCh t ch src dst
                     else labelCh t ch src dst
                 end
               | ChildRecvResp p c _ _ _ _ =>
                 match ch with
                   | mch =>
                     if (decTree p src)
                     then if (decTree c dst)
                          then removelast (labelCh t ch src dst)
                          else labelCh t ch src dst
                     else labelCh t ch src dst
                   | rch => labelCh t ch src dst
                 end
               | ParentSendReq p c _ _ _ _ _ _ _ =>
                 match ch with
                   | rch =>
                     if (decTree p src)
                     then if (decTree c dst)
                          then t :: labelCh t ch src dst
                          else labelCh t ch src dst
                     else labelCh t ch src dst
                   | mch => labelCh t ch src dst
                 end
               | ChildRecvReq p c _ _ _ _ _ _ =>
                 match ch with
                   | rch =>
                     if (decTree c dst)
                     then if (decTree p src)
                          then removelast (labelCh t ch src dst)
                          else labelCh t ch src dst
                     else labelCh t ch src dst
                   | mch =>
                     if (decTree p dst)
                     then if (decTree c src)
                          then t :: labelCh t ch src dst
                          else labelCh t ch src dst
                     else labelCh t ch src dst
                 end
               | ParentRecvResp p c _ _ _ _ =>
                 match ch with
                   | mch =>
                     if (decTree c src)
                     then if (decTree p dst)
                          then removelast (labelCh t ch src dst)
                          else labelCh t ch src dst
                     else labelCh t ch src dst
                   | rch => labelCh t ch src dst
                 end
               | ChildVolResp p c _ _ _ _ _ _ _ _ =>
                 match ch with
                   | mch =>
                     if (decTree c src)
                     then if (decTree p dst)
                          then t :: labelCh t ch src dst
                          else labelCh t ch src dst
                     else labelCh t ch src dst
                   | rch => labelCh t ch src dst
                 end
               | ChildDropReq p c _ _ _ _ _ =>
                 match ch with
                   | rch =>
                     if (decTree p src)
                     then if (decTree c dst)
                          then removelast (labelCh t ch src dst)
                          else labelCh t ch src dst
                     else labelCh t ch src dst
                   | mch => labelCh t ch src dst
                 end
               | _ => labelCh t ch src dst
             end
  end.

Module mkDataTypes <: DataTypes.

  Definition state c a t := st ((sys oneBeh) t) c a.
  Definition dir p c a t := dirSt ((sys oneBeh) t) p c a.
  Definition wait c a t := wt ((sys oneBeh) t) c a.
  Definition waitS c a t := wtS ((sys oneBeh) t) c a.
  Definition dwait p c a t := dirWt ((sys oneBeh) t) p c a.
  Definition dwaitS p c a t := dirWtS ((sys oneBeh) t) p c a.
  Definition data c a t := dt ((sys oneBeh) t) c a.

  
  Definition mark chn src dst t m := match ((trans oneBeh) t) with
                                       | ChildSendReq p c _ _ _ x a _ _ =>
                                         c = src /\ p = dst /\ chn = rch /\
                                         from m = (st ((sys oneBeh) t) c a) /\
                                         to m = x /\ addr m = a /\
                                         msgId m = t
                                       | ParentRecvReq p c _ _ _ _ _ _ _ _ =>
                                         p = src /\ c = dst /\ chn = mch /\
                                         let r := last (ch ((sys oneBeh) t) rch c p) dmy in
                                         let a := addrB r in
                                         from m = (dirSt ((sys oneBeh) t) p c a) /\
                                         to m = toB r /\
                                         addr m = a /\
                                         dataM m = dt ((sys oneBeh) t) p a /\
                                         msgId m = t
                                       | ParentSendReq p c _ _ _ x a _ _ =>
                                         p = src /\ c = dst /\ chn = rch /\
                                         from m = (dirSt ((sys oneBeh) t) p c a) /\
                                         to m = x /\ addr m = a /\
                                         msgId m = t
                                       | ChildRecvReq p c _ _ _ _ _ _ =>
                                         c = src /\ p = dst /\ chn = mch /\
                                         let r := last (ch ((sys oneBeh) t) rch p c) dmy in
                                         let a := addrB r in
                                         from m = (st ((sys oneBeh) t) c a) /\
                                         to m = toB r /\
                                         addr m = a /\
                                         dataM m = dt ((sys oneBeh) t) c a /\
                                         msgId m = t
                                       | ChildVolResp p c _ _ _ x a _ _ _ =>
                                         c = src /\ p = dst /\ chn = mch /\
                                         from m = (st ((sys oneBeh) t) c a) /\
                                         to m = x /\ addr m = a /\
                                         dataM m = dt (sys oneBeh t) c a /\
                                         msgId m = t
                                       | _ => False
                                     end.

  Definition recv chn src dst t m := match ((trans oneBeh) t) with
                                       | ParentRecvReq p c _ _ _ _ _ _ _ _ =>
                                         c = src /\ p = dst /\ chn = rch /\
                                         let r := last (ch ((sys oneBeh) t) rch c p) dmy in
                                         from m = fromB r /\
                                         to m = toB r /\ addr m = addrB r /\
                                         msgId m = last (labelCh t rch c p) 0
                                       | ChildRecvResp p c _ _ _ _ =>
                                         p = src /\ c = dst /\ chn = mch /\
                                         let r := last (ch ((sys oneBeh) t) mch p c) dmy in
                                         from m = fromB r /\
                                         to m = toB r /\ addr m = addrB r /\
                                         dataM m = dataBM r /\
                                         msgId m = last (labelCh t mch p c) 0
                                       | ChildRecvReq p c _ _ _ _ _ _ =>
                                         p = src /\ c = dst /\ chn = rch /\
                                         let r := last (ch ((sys oneBeh) t) rch p c) dmy in
                                         from m = fromB r /\
                                         to m = toB r /\ addr m = addrB r /\
                                         msgId m = last (labelCh t rch p c) 0
                                       | ParentRecvResp p c _ _ _ _ =>
                                         c = src /\ p = dst /\ chn = mch /\
                                         let r := last (ch ((sys oneBeh) t) mch c p) dmy in
                                         from m = fromB r /\
                                         to m = toB r /\ addr m = addrB r /\
                                         dataM m = dataBM r /\
                                         msgId m = last (labelCh t mch c p) 0
                                       | ChildDropReq p c _ _ _ _ _ =>
                                         p = src /\ c = dst /\ chn = rch /\
                                         let r := last (ch ((sys oneBeh) t) rch p c) dmy in
                                         from m = fromB r /\
                                         to m = toB r /\ addr m = addrB r /\
                                         msgId m = last (labelCh t rch p c) 0
                                       | _ => False
                                     end.

  Definition send := mark.
  Definition proc := recv.
  Definition deq := recv.

  Definition deqR c l a d i t := match (trans oneBeh) t with
                                   | LoadReq ca _ _ _ _ =>
                                     ca = c /\ let r := Streams.hd
                                                          (req ((sys oneBeh) t) ca) in
                                               lbl r = l /\ lct r = a /\ dsc r = d /\ idx r = i
                                   | StoreReq ca _ _ _ _ =>
                                     ca = c /\ let r := Streams.hd (req ((sys oneBeh) t) ca) in
                                               lbl r = l /\ lct r = a /\ dsc r = d /\ idx r = i
                                   | _ => False
                                 end.

  Definition enqLd c l sl t := match (trans oneBeh) t with
                                 | LoadReq ca _ _ _ _ =>
                                   ca = c /\ let r := Streams.hd
                                                        (req ((sys oneBeh) t) ca) in
                                             lbl r = l /\ dt ((sys oneBeh) t) c (lct r) = sl /\
                                             dsc r = Ld
                                 | _ => False
                               end.

  Definition enqSt c l t := match (trans oneBeh) t with
                              | StoreReq ca _ _ _ _ =>
                                ca = c /\ let r := Streams.hd
                                                     (req ((sys oneBeh) t) ca) in
                                          lbl r = l /\ dsc r = St
                              | _ => False
                            end.
  
End mkDataTypes.
