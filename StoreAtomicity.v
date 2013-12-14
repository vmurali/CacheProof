Require Import DataTypes.

Module Type InputTypes (d: DataTypes).
  Import d.

  Parameter Req: Set.
  (*
   label q: Label of the request
   proc q: Processor the label got generated
   addr q: Address corresponding to label
   index q: The integer for ordering labels within a processor
   desc q: Ld or St
  *)
  Parameter proc: Req -> Cache.
  Parameter label: Req -> Label.
  Parameter loc: Req -> Addr.
  Parameter desc: Req -> Desc.
  Parameter index: Req -> Index.

  Parameter Resp: Set.
  (*
   origLabel: The label of the store request, or if load, the corresponding load request label in the response
   stl r: In case of a load, (Store label) for the response or Initial
   time r: Integer representing order at which response is generated for load, or the order of store
   procR r: Processor from which response is gotten
  *)
  Parameter procR: Resp -> Cache.
  Parameter origLabel: Resp -> Label.
  Parameter stl: Resp -> StLabel.
  Parameter time: Resp -> nat.
End InputTypes.

Module Type Input (d: DataTypes) (it: InputTypes d).
  Import d it.
  Axiom uniqReqLabels:
  forall {q1 q2},
    label q1 = label q2 -> q1 = q2.

  Axiom uniqIndicesPerProc:
  forall {q1 q2}, proc q1 = proc q2 -> index q1 = index q2 -> q1 = q2.
End Input.

(*
0) Responses come from same processor as request
1) Response labels are unique
2) Timestamps for store responses for an address is unique
3) Timestamps for two labels must not contradict the index order if the labels are from same processor
4) A load response with timestamp t either contains an Initial label with no Stores being assigned a timestamp in between 0 and t, or it's a store label, with no other store being assigned a timestamp in between the store's timestamp and t.
*)

Module Type StoreAtomicity (d: DataTypes) (it: InputTypes d) (ai: Input d it).
  Import d it ai.
  Parameter respProc:
  forall {r q}, origLabel r = label q -> procR r = proc q.

  Parameter uniqRespLabels:
  forall {r1 r2}, origLabel r1 = origLabel r2 -> r1 = r2.

  Parameter uniqRespTimes:
  forall {r1 r2}, time r1 = time r2 ->
    forall {q1 q2}, origLabel r1 = label q1 -> origLabel r2 = label q2 ->
                    loc q1 = loc q2 -> desc q1 = St -> q1 = q2.

  Parameter localOrdering:
  forall {r1 r2 q1 q2}, origLabel r1 = label q1 -> origLabel r2 = label q2 -> proc q1 = proc q2 ->
                        loc q1 = loc q2 -> index q1 < index q2 -> ~ time r2 > time r1.

  Parameter storeAtomicity:
  forall {r q}, origLabel r = label q -> desc q = Ld ->
              match stl r with
                | Initial => forall {r' q'}, origLabel r' = label q' ->
                                             0 <= time r' <= time r -> ~ (loc q = loc q' /\ desc q' = St)
                | Store st =>
                    exists qst rst ,
                      label qst = st /\ origLabel rst = st /\ 
                      time rst < time r /\ loc q = loc qst /\ desc qst = St /\
                      forall {r' q'}, origLabel r' = label q' ->
                                      time rst < time r' <= time r ->
                                      ~ (loc q = loc q' /\ desc q' = St)
              end.
End StoreAtomicity.

(* Some other property which can be proved by the above properties *)
Require Import Omega.
Module T (d: DataTypes) (it: InputTypes d) (ai: Input d it) (sa: StoreAtomicity d it ai).
  Import d it ai sa.
  Theorem initialBeginning:
  forall {r1 r2 q1 q2}, origLabel r1 = label q1 -> origLabel r2 = label q2 ->
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
