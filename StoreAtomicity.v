Require Import DataTypes.

Module Type L1InputTypes (d: DataTypes).
  Import d.
  Parameter Req: Set.
  Parameter procQ: Req -> Cache.
  Parameter labelQ: Req -> Label.
  Parameter loc: Req -> Addr.
  Parameter desc: Req -> Desc.
  Parameter index: Req -> Index.

  Parameter Resp: Set.
  Parameter procR: Resp -> Cache.
  Parameter labelR: Resp -> Label.
  Parameter stl: Resp -> StLabel.
  Parameter timeR: Resp -> Time.
End L1InputTypes.

Module Type L1BaseInputAxioms (d: DataTypes) (li: L1InputTypes d).
  Import d li.
  Axiom uniqReqLabels:
    forall {q1 q2}, labelQ q1 = labelQ q2 -> q1 = q2.

  Axiom uniqReqIndicesPerProc:
    forall {q1 q2}, procQ q1 = procQ q2 -> index q1 = index q2 -> q1 = q2.
End L1BaseInputAxioms.

Module Type StoreAtomicity (dt: DataTypes) (l1B: L1InputTypes dt).
  Import dt l1B.

  Parameter respHasReq:
    forall {r}, exists q, labelR r = labelQ q.

  Parameter respProc:
    forall {r q}, labelR r = labelQ q -> procR r = procQ q.

  Parameter uniqRespLabels:
    forall {r1 r2}, labelR r1 = labelR r2 ->
                    procR r1 = procR r2 /\ timeR r1 = timeR r2 /\
                    forall {q}, labelQ q = labelR r1 -> desc q = Ld ->
                                stl r1 = stl r2.

  Parameter uniqRespTimes:
    forall {r1 r2}, timeR r1 = timeR r2 ->
                    forall {q1 q2}, labelR r1 = labelQ q1 -> labelR r2 = labelQ q2 ->
                                    loc q1 = loc q2 -> desc q1 = St -> labelR r1 = labelR r2.


  Parameter localOrdering:
    forall {r1 r2 q1 q2}, labelR r1 = labelQ q1 -> labelR r2 = labelQ q2 -> procQ q1 = procQ q2 ->
                          loc q1 = loc q2 -> index q1 < index q2 -> ~ timeR r1 > timeR r2.

  Parameter storeAtomicity:
    forall {r q},
      labelR r = labelQ q -> desc q = Ld ->
      (stl r = Initial /\
       forall {r' q'},
         labelR r' = labelQ q' -> 0 <= timeR r' < timeR r
         -> ~ (loc q = loc q' /\ desc q' = St)) \/
      (exists m, stl r = Store m /\
                 exists rm qm, labelR rm = m /\ labelQ qm = m /\
                               timeR rm < timeR r /\ loc qm = loc q /\ desc qm = St /\
                               forall {r' q'},
                                 labelR r' = labelQ q' -> timeR rm < timeR r' < timeR r ->
                                 ~ (loc q = loc q' /\ desc q' = St)).
End StoreAtomicity.

