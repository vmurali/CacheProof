import Vector::*;
import FIFOF::*;
import Types::*;
import Cache::*;
import ConfigReg::*;
import FreeList::*;
import RegFile::*;

interface InternalCtrl#(numeric type mshrs, numeric type ways, numeric type sets, numeric type childs);
  method Action fromPM(FromParent x);
  method Action reqFromCM(ReqFromChild x);
  method Action respFromCM(RespFromChild x);
  method ActionValue#(ReqToParent) reqToPM;
  method ActionValue#(RespToParent) respToPM;
  method ActionValue#(ToChildren#(childs)) toCsM;
endinterface

typedef union tagged {
  Tuple2#(Index, Maybe#(Bit#(mshrSz))) Parent;
  Tuple4#(Child, Index, St, Maybe#(LineAddr)) Child;
} Mshr#(type mshrSz) deriving (Bits, Eq);

function St compat(St st);
  if(st == 2)
    return 0;
  else if(st == 1)
    return 1;
  else
    return 2;
endfunction

(* synthesize *)
module mkInternalCtrlInst(InternalCtrl#(64, 8, 1024, 16));
  let ctrl <- mkInternalCtrl(5, 5);
  return ctrl;
endmodule

module mkInternalCtrl#(Latency tagLat, Latency dataLat)
  (InternalCtrl#(mshrs, ways, sets, childs)) provisos(
    Log#(sets, setSz),
    Log#(ways, waySz),
    Add#(setSz, _x, AddrSz),
    Add#(setSz, tagSz, RemainSz),
    Add#(tagSz, _y, AddrSz),
    Add#(setSz, _z, 15),
    Add#(waySz, _w, 6),
    Log#(mshrs, mshrSz)
  );
  Cache#(mshrSz, tagSz, waySz, ways, sets, childs) cache <- mkCache;
  FreeList#(mshrs) mshrFl <- mkFreeList;
  RegFile#(Bit#(mshrSz), Mshr#(mshrSz)) mshr <- mkRegFileWCF(0, fromInteger(valueOf(mshrs)-1));

  FIFOF#(FromParent) fromP <- mkUGFIFOF;
  FIFOF#(ReqFromChild) reqFromC <- mkUGFIFOF;
  FIFOF#(RespFromChild) respFromC <- mkUGFIFOF;
  FIFOF#(ReqToParent) pReqF <- mkUGFIFOF1;
  FIFOF#(RespToParent) pRespF <- mkUGFIFOF1;
  FIFOF#(ToChildren#(childs)) toCsF <- mkUGFIFOF1;

  FIFOF#(ReqToParent) pReq <- mkUGFIFOF1;
  FIFOF#(RespToParent) pResp <- mkUGFIFOF1;
  FIFOF#(ToChildren#(childs)) toCs <- mkUGFIFOF1;

  Reg#(Counter) hit <- mkReg(0);
  Reg#(Counter) notPresentMiss <- mkReg(0);
  Reg#(Counter) childPermMiss <- mkReg(0);
  Reg#(Counter) parentPermMiss <- mkReg(0);

  Reg#(Latency) latPReq <- mkReg(0);
  Reg#(Latency) latPResp <- mkReg(0);
  Reg#(Latency) latToCs <- mkReg(0);

  function Bool whoHigher(St mustLower, currCState);
    return mustLower < currCState;
  endfunction

  function Bool childBitId(Child c, Integer i) = fromInteger(i) == c;

  function Bool free = pReq.notFull && pResp.notFull && toCs.notFull && latPReq == 0 && latPResp == 0 && latToCs == 0;

  rule pReqLat(latPReq > 1);
    latPReq <= latPReq - 1;
  endrule

  rule pRespLat(latPResp > 1);
    latPResp <= latPResp - 1;
  endrule

  rule toCsLat(latToCs > 1);
    latToCs <= latToCs - 1;
  endrule

  rule sPReq(latPReq == 1 && pReq.notEmpty && pReqF.notFull);
    pReq.deq;
    pReqF.enq(pReq.first);
    latPReq <= 0;
  endrule

  rule sPResp(latPResp == 1 && pResp.notEmpty && pRespF.notFull);
    pResp.deq;
    pRespF.enq(pResp.first);
    latPResp <= 0;
  endrule

  rule sToCs(latToCs == 1 && toCs.notEmpty && toCsF.notFull);
    toCs.deq;
    toCsF.enq(toCs.first);
    latToCs <= 0;
  endrule

begin // respFromC
match tagged RespFromChild{c: .c, trigger: .trigger, to: .to, dirty: .dirtyIn} = respFromC.first;
let index = case (trigger) matches
              tagged Voluntary .lineAddr: cache.getIndex(lineAddr);
              tagged Forced .index: index;
            endcase;
let newDirty = dirtyIn? True: cache.dirty(index);
let st = cache.getS(index);
let cstates = cache.getCs(index);
cstates[c] = to;
let waitCs = cache.getWaitCs(index);
let cHigher = map(whoHigher(waitCs), cstates);
let isCHigher = isValid(findElem(True, cHigher));
let mshrPtr = cache.getMshrPtr(index);

rule respFromC1(cache.init && mshrFl.init && free &&
                (!cache.isCReq(index) || isCHigher)
                && respFromC.notEmpty);
  respFromC.deq;
  if(!cache.isCReq(index) || isCHigher)
  begin
    if(dirtyIn)
      cache.setDirty(index);
    cache.setC(index, c, to);
  end
endrule

rule respFromC2(cache.init &&& mshrFl.init &&& free &&&
                (cache.isCReq(index) &&& !isCHigher) &&&
                mshr.sub(mshrPtr) matches tagged Child {.origC, .cIndex, .cTo, .addrToM} &&&
                addrToM matches tagged Valid .realAddr
                &&& respFromC.notEmpty && pReq.notFull);
  respFromC.deq;
  cache.unsetCReq(index);
  (* split *)
  if(newDirty && pResp.notFull)
  begin
    Bit#(setSz) set = truncate(index.set);
    Bit#(tagSz) tag = cache.getTag(index);
    Bit#(RemainSz) lineAddr = {tag, set};
    pResp.enq(RespToParent{trigger: Voluntary (lineAddr), to: 0, dirty: newDirty});
    latPResp <= newDirty? dataLat : 1;
  end
  cache.setTag(index, truncateLSB(realAddr));
  cache.setS(index, 0);
  cache.setCs(index, replicate(0));
  cache.setWaitS(index, cTo);
  cache.unsetDirty(index);
  mshr.upd(mshrPtr, Child (tuple4(origC, cIndex, cTo, Invalid)));
  pReq.enq(ReqToParent{index: index, lineAddr: realAddr, from: 0, to: cTo});
  latPReq <= 1;
endrule

rule respFromC3(cache.init &&& mshrFl.init &&& free &&&
                (cache.isCReq(index) &&& !isCHigher) &&&
                mshr.sub(mshrPtr) matches tagged Child {.origC, .cIndex, .cTo, .addrToM} &&&
                addrToM matches tagged Invalid &&&
                !cache.isPReq(index)
                && respFromC.notEmpty && toCs.notFull);
  respFromC.deq;
  cache.unsetCReq(index);
  if(dirtyIn)
    cache.setDirty(index);
  toCs.enq(ToChildren{children: genWith(childBitId(origC)), isReq: False,
                      index: cIndex, lineAddr: ?, from: cstates, to: cTo});
  latToCs <= 1;
  let newcstates = cstates;
  newcstates[origC] = cTo;
  cache.setCs(index, newcstates);
  cache.replaceUpd(index);
  mshrFl.free(mshrPtr);
endrule

rule respFromC4(cache.init &&& mshrFl.init &&& free &&&
                (cache.isCReq(index) &&& !isCHigher) &&&
                mshr.sub(mshrPtr) matches tagged Child {.origC, .cIndex, .cTo, .addrToM} &&&
                addrToM matches tagged Invalid &&&
                cache.isPReq(index)
                && respFromC.notEmpty);
  respFromC.deq;
  cache.unsetCReq(index);
  cache.setC(index, c, to);
  if(dirtyIn)
    cache.setDirty(index);
endrule

rule respFromC5(cache.init &&& mshrFl.init &&& free &&&
                (cache.isCReq(index) &&& !isCHigher) &&&
                mshr.sub(mshrPtr) matches tagged Parent {.pIndex, .oldMshrM}
                &&& respFromC.notEmpty && pResp.notFull);
  respFromC.deq;
  cache.unsetCReq(index);
  if(dirtyIn)
    cache.setDirty(index);
  if(oldMshrM matches tagged Valid .oldMshr)
    cache.setMshrPtr(index, oldMshr);
  cache.setC(index, c, to);
  cache.setS(index, waitCs);
  mshrFl.free(mshrPtr);
  pResp.enq(RespToParent{trigger: Forced (pIndex), to: waitCs, dirty: newDirty});
  latPResp <= newDirty? dataLat: 1;
  if(waitCs == 0)
    cache.replaceRem(index);
endrule
end

// (* mutually_excusive = "respFromC1, respFromC2, respFromC3, respFromC4, respFromC5" *)

begin //fromParentResp
match tagged FromParent{isReq: .isReq, index: .index, lineAddr: .lineAddr, from: .*, to: .to} = fromP.first;
let cstates = cache.getCs(index);
let mshrPtr = cache.getMshrPtr(index);

(* preempts = "(cache.initRule, pReqLat, pRespLat, toCsLat, sPReq, sPResp, sToCs, respFromC1, respFromC2, respFromC3, respFromC4, respFromC5), fromPResp1" *)
rule fromPResp1(cache.init && mshrFl.init && fromP.first.isReq == False && free &&
                cache.isCReq(index)
                && fromP.notEmpty);
  cache.setS(index, to);
  cache.unsetPReq(index);
  fromP.deq;
endrule

(* preempts = "(cache.initRule, pReqLat, pRespLat, toCsLat, sPReq, sPResp, sToCs, respFromC1, respFromC2, respFromC3, respFromC4, respFromC5), fromPResp2" *)
rule fromPResp2(cache.init && mshrFl.init && fromP.first.isReq == False && free &&
                !cache.isCReq(index)
                && fromP.notEmpty && toCs.notFull);
  fromP.deq;
  cache.setS(index, to);
  cache.unsetPReq(index);
  match {.origC, .cIndex, .cTo, .*} = mshr.sub(mshrPtr).Child;
  toCs.enq(ToChildren{children: genWith(childBitId(origC)), isReq: False,
                      index: cIndex, lineAddr: ?, from: cstates, to: cTo});
  latToCs <= cstates[origC] == 0? dataLat: 1;
  cache.replaceUpd(index);
  cache.setC(cIndex, origC, cTo);
  mshrFl.free(mshrPtr);
endrule
end

//(* mutually_exclusive = "fromPResp1, fromPResp2" *)

begin
match tagged ReqFromChild{c: .c, index: .cIndex, lineAddr: .lineAddr, from: .from, to: .to} = reqFromC.first;
let present = cache.isPresent(lineAddr);
let index = cache.getIndex(lineAddr);
let st = cache.getS(index);
let cstates = cache.getCs(index);
let cHigher = map(whoHigher(compat(to)), cstates);
cHigher[c] = False;
let isCHigher = isValid(findElem(True, cHigher));

(* preempts = "(cache.initRule, pReqLat, pRespLat, toCsLat, sPReq, sPResp, sToCs, respFromC1, respFromC2, respFromC3, respFromC4, respFromC5, fromPResp1, fromPResp2), reqFromC1" *)
rule reqFromC1(cache.init && mshrFl.init && free && !cache.isPReq(index) && !cache.isCReq(index) &&
               present &&
               cstates[c] == from &&
               st >= to && !isCHigher
               && reqFromC.notEmpty && toCs.notFull);
  reqFromC.deq;
  cache.setC(index, c, to);
  toCs.enq(ToChildren{children: genWith(childBitId(c)), isReq: False,
                      index: cIndex, lineAddr: ?, from: cstates, to: to});
  latToCs <= cstates[c] == 0? dataLat: tagLat;
  cache.replaceUpd(index);
  hit <= hit + 1;
endrule

(* preempts = "(cache.initRule, pReqLat, pRespLat, toCsLat, sPReq, sPResp, sToCs, respFromC1, respFromC2, respFromC3, respFromC4, respFromC5, fromPResp1, fromPResp2), reqFromC2" *)
rule reqFromC2(cache.init && mshrFl.init && free && !cache.isPReq(index) && !cache.isCReq(index) &&
               present &&
               cstates[c] == from &&
               !(st >= to && !isCHigher)
               && reqFromC.notEmpty);
  reqFromC.deq;
  let mshrPtr <- mshrFl.alloc;
  mshr.upd(mshrPtr, Child (tuple4(c, cIndex, to, Invalid)));
  cache.setMshrPtr(index, mshrPtr);
  (* split *)
  if(st < to && pReq.notFull)
  begin
    cache.setWaitS(index, to);
    pReq.enq(ReqToParent{index: index, lineAddr: lineAddr, from: cstates[c], to: to});
    latPReq <= tagLat;
    parentPermMiss <= parentPermMiss + 1;
  end
  if(isCHigher && toCs.notFull)
  begin
    cache.setWaitCs(index, compat(to));
    toCs.enq(ToChildren{children: cHigher, isReq: True, index: index,
                        lineAddr: lineAddr, from: ?, to: compat(to)});
    latToCs <= tagLat;
    childPermMiss <= childPermMiss + 1;
  end
endrule

let replaceIndex = cache.getReplace(lineAddr);
let replaceS = cache.getS(replaceIndex);
let replaceCStates = cache.getCs(replaceIndex);
let replaceCHigher = map(whoHigher(0), replaceCStates);
let isReplaceCHigher = isValid(findElem(True, replaceCHigher));
Bit#(setSz) replaceSet = truncate(index.set);
Bit#(tagSz) replaceTag = cache.getTag(index);
Bit#(RemainSz) replaceLineAddr = {replaceTag, replaceSet};

(* preempts = "(cache.initRule, pReqLat, pRespLat, toCsLat, sPReq, sPResp, sToCs, respFromC1, respFromC2, respFromC3, respFromC4, respFromC5, fromPResp1, fromPResp2), reqFromC3" *)
rule reqFromC3(cache.init && mshrFl.init && free && !cache.isPReq(index) && !cache.isCReq(index) &&
               !present &&
               from == 0 && cache.existsReplace(lineAddr) &&
               !isReplaceCHigher
               && reqFromC.notEmpty && pReq.notFull);
  (* split *)
  reqFromC.deq;
  let mshrPtr <- mshrFl.alloc;
  cache.setMshrPtr(replaceIndex, mshrPtr);
  notPresentMiss <= notPresentMiss + 1;
  if(replaceS > 0 && pResp.notFull)
  begin
    pResp.enq(RespToParent{trigger: Voluntary (replaceLineAddr), to: 0, dirty: cache.dirty(replaceIndex)});
    latPResp <= cache.dirty(replaceIndex)? dataLat : tagLat;
  end
  cache.setTag(replaceIndex, truncateLSB(lineAddr));
  cache.setS(replaceIndex, 0);
  cache.setCs(replaceIndex, replicate(0));
  cache.unsetDirty(replaceIndex);
  mshr.upd(mshrPtr, Child (tuple4(c, cIndex, to, Invalid)));
  cache.setWaitS(replaceIndex, to);
  pReq.enq(ReqToParent{index: replaceIndex, lineAddr: lineAddr, from: 0, to: to});
  latPReq <= tagLat;
endrule

(* preempts = "(cache.initRule, pReqLat, pRespLat, toCsLat, sPReq, sPResp, sToCs, respFromC1, respFromC2, respFromC3, respFromC4, respFromC5, fromPResp1, fromPResp2), reqFromC4" *)
(* mutually_exclusive = "reqFromC1, reqFromC2, reqFromC3, reqFromC4" *) 
rule reqFromC4(cache.init && mshrFl.init && free && !cache.isPReq(index) && !cache.isCReq(index) &&
               !present &&
               from == 0 && cache.existsReplace(lineAddr) &&
               isReplaceCHigher
               && reqFromC.notEmpty && toCs.notFull);
  reqFromC.deq;
  let mshrPtr <- mshrFl.alloc;
  cache.setMshrPtr(replaceIndex, mshrPtr);
  notPresentMiss <= notPresentMiss + 1;
  mshr.upd(mshrPtr, Child (tuple4(c, cIndex, to, Valid (lineAddr))));
  toCs.enq(ToChildren{children: replaceCHigher, isReq: True, index: replaceIndex, lineAddr: replaceLineAddr, from: replaceCStates, to: 0});
  latToCs <= tagLat;
  cache.setWaitCs(replaceIndex, 0);
endrule
end

begin // fromParentReq
match tagged FromParent{isReq: .isReq, index: .pIndex, lineAddr: .lineAddr, from: .from, to: .to} = fromP.first;
let present = cache.isPresent(lineAddr);
let index = cache.getIndex(lineAddr);
let st = cache.getS(index);
let cstates = cache.getCs(index);
let cHigher = map(whoHigher(to), cstates);
let isCHigher = isValid(findElem(True, cHigher));

(* preempts = "(cache.initRule, pReqLat, pRespLat, toCsLat, sPReq, sPResp, sToCs, respFromC1, respFromC2, respFromC3, respFromC4, respFromC5, fromPResp1, fromPResp2, reqFromC1, reqFromC2, reqFromC3, reqFromC4), fromPReq1" *)
rule fromPReq1(cache.init && mshrFl.init && fromP.first.isReq && free && !cache.isCReq(index) &&
               (!present || st <= to));
  fromP.deq;
endrule

(* preempts = "(cache.initRule, pReqLat, pRespLat, toCsLat, sPReq, sPResp, sToCs, respFromC1, respFromC2, respFromC3, respFromC4, respFromC5, fromPResp1, fromPResp2, reqFromC1, reqFromC2, reqFromC3, reqFromC4), fromPReq2" *)
rule fromPReq2(cache.init && mshrFl.init && fromP.first.isReq && free && !cache.isCReq(index) &&
               present && st > to &&
               isCHigher
               && fromP.notEmpty && toCs.notFull);
  fromP.deq;
  let mshrPtr <- mshrFl.alloc;
  let oldMshr = cache.isPReq(index)? Valid (cache.getMshrPtr(index)): Invalid;
  mshr.upd(mshrPtr, Parent (tuple2(pIndex, oldMshr)));
  toCs.enq(ToChildren{children: cHigher, isReq: True, index: index,
                      lineAddr: lineAddr, from:?, to: to});
  latToCs <= tagLat;
  cache.setWaitCs(index, to);
endrule

(* preempts = "(cache.initRule, pReqLat, pRespLat, toCsLat, sPReq, sPResp, sToCs, respFromC1, respFromC2, respFromC3, respFromC4, respFromC5, fromPResp1, fromPResp2, reqFromC1, reqFromC2, reqFromC3, reqFromC4), fromPReq3" *)
(* mutually_exclusive = "fromPReq1, fromPReq2, fromPReq3" *)
rule fromPReq3(cache.init && mshrFl.init && fromP.first.isReq && free && !cache.isCReq(index) &&
               present && st > to &&
               !isCHigher
               && fromP.notEmpty && pResp.notFull);
  fromP.deq;
  cache.setS(index, to);
  pResp.enq(RespToParent{trigger: Forced (pIndex), to: to, dirty: cache.dirty(index)});
  latPResp <= cache.dirty(index)? dataLat : tagLat;
  if(to == 0)
    cache.replaceRem(index);
endrule
end

  method fromPM if(fromP.notFull) = fromP.enq;
  method reqFromCM if(reqFromC.notFull) = reqFromC.enq;
  method respFromCM if(respFromC.notFull) = respFromC.enq;

  method ActionValue#(ReqToParent) reqToPM if(pReqF.notEmpty);
    pReqF.deq;
    return pReqF.first;
  endmethod

  method ActionValue#(RespToParent) respToPM if(pRespF.notEmpty);
    pRespF.deq;
    return pRespF.first;
  endmethod

  method ActionValue#(ToChildren#(childs)) toCsM if(toCsF.notEmpty);
    toCsF.deq;
    return toCsF.first;
  endmethod
endmodule
