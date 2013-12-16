Require Import DataTypes.

Module Type InputTypes (d: DataTypes).
  Import d.

  Parameter Req: Set.
  Parameter Def: Req -> Prop.
  (*
   label q: Label of the request
   proc q: Processor the label got generated
   loc q: Address corresponding to label
   desc q: Ld or St
   index q: The integer for ordering labels within a processor
  *)
  Parameter label: {q| Def q} -> Label.
  Parameter proc: {q| Def q} -> Cache.
  Parameter loc: {q| Def q} -> Addr.
  Parameter desc: {q| Def q} -> Desc.
  Parameter index: {q| Def q} -> Index.

  Parameter Resp: Set.
  Parameter DefR: Resp -> Prop.
  (*
   labelR q: Original label of request
   procR q: Processor the label got generated
   stl r: In case of a load, (Store label) for the response or Initial
   time r: Integer representing order at which response is generated for load, or the order of store
  *)
  Parameter labelR: {r| DefR r} -> Label.
  Parameter procR: {r| DefR r} -> Cache.
  Parameter stl: {r| DefR r} -> StLabel.
  Parameter time: {r| DefR r} -> nat.
End InputTypes.

Module Type Input (d: DataTypes) (it: InputTypes d).
  Import d it.
  Axiom uniqReqLabels:
  forall {q1 q2},
    label q1 = label q2 ->
    let (v1, _) := q1 in
    let (v2, _) := q2 in
    v1 = v2.

  Axiom uniqIndicesPerProc:
  forall {q1 q2},
    proc q1 = proc q2 -> index q1 = index q2 ->
    let (v1, _) := q1 in
    let (v2, _) := q2 in
    v1 = v2.
End Input.

(*
0) Response label corresponds to a request label
1) Responses come from same processor as request
2) Response labels are unique
3) Timestamps for store responses for an address is unique
4) Timestamps for two labels must not contradict the index order if the labels are from same processor
5) A load response with timestamp t either contains an Initial label with no Stores being assigned a timestamp in between 0 and t, or it's a store label, with no other store being assigned a timestamp in between the store's timestamp and t.
*)

Module Type StoreAtomicity (d: DataTypes) (it: InputTypes d) (ai: Input d it).
  Import d it ai.
  Parameter respHasReq:
    forall {r}, exists q, labelR r = label q.

  Parameter respProc:
  forall {r q}, labelR r = label q -> procR r = proc q.

  Parameter uniqRespLabels:
  forall {r1 r2}, labelR r1 = labelR r2 ->
                  let (v1, _) := r1 in
                  let (v2, _) := r2 in
                  v1 = v2.

  Parameter uniqRespTimes:
  forall {r1 r2}, time r1 = time r2 ->
    forall {q1 q2}, labelR r1 = label q1 -> labelR r2 = label q2 ->
                    loc q1 = loc q2 -> desc q1 = St ->
                    labelR r1 = labelR r2 /\ procR r1 = procR r2 /\ time r1 = time r2.

  Parameter localOrdering:
  forall {r1 r2 q1 q2}, labelR r1 = label q1 -> labelR r2 = label q2 -> proc q1 = proc q2 ->
                        loc q1 = loc q2 -> index q1 < index q2 -> ~ time r2 > time r1.

  Parameter storeAtomicity:
  forall {r q}, labelR r = label q -> desc q = Ld ->
              match stl r with
                | Initial => forall {r' q'}, labelR r' = label q' ->
                                             0 <= time r' <= time r -> ~ (loc q = loc q' /\ desc q' = St)
                | Store st =>
                    exists qst rst ,
                      label qst = st /\ labelR rst = st /\ 
                      time rst < time r /\ loc q = loc qst /\ desc qst = St /\
                      forall {r' q'}, labelR r' = label q' ->
                                      time rst < time r' <= time r ->
                                      ~ (loc q = loc q' /\ desc q' = St)
              end.
End StoreAtomicity.

(* Some other property which can be proved by the above properties *)
Require Import Omega.
Module T (d: DataTypes) (it: InputTypes d) (ai: Input d it) (sa: StoreAtomicity d it ai).
  Import d it ai sa.
  Theorem initialBeginning:
  forall {r1 r2 q1 q2}, labelR r1 = label q1 -> labelR r2 = label q2 ->
                        loc q1 = loc q2 -> time r1 < time r2 -> desc q1 = Ld -> desc q2 = Ld ->
                        stl r2 = Initial -> stl r1 = Initial.
  Proof.
    intros r1 r2 q1 q2 l1 l2 addrEq t1LtT2 q1Ld q2Ld r2Init.
    pose proof storeAtomicity l2 q2Ld as q2Cond.
    rewrite r2Init in *.
    pose proof storeAtomicity l1 q1Ld as q1Cond.
    destruct (stl r1).
    auto.
    destruct q1Cond as [qst [rst [qMatch [rMatch [tLt [addr [des _]]]]]]].
    assert (0 <= time rst <= time r2) by omega.
    rewrite addrEq in *.
    rewrite <- qMatch in *.
    firstorder.
  Qed.
End T.
