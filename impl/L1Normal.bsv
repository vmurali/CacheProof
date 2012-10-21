import Vector::*;
import FIFOF::*;
import Types::*;
import Cache::*;
import ConfigReg::*;
import FreeList::*;
import RegFile::*;

interface L1Normal#(numeric type ways, numeric type sets);
  method Action fromPM(FromParent x);
  method Action reqFromCoreM(ReqFromCore x);
//  method Action respToCoreM;
  method ActionValue#(ReqToParent) reqToPM;
  method ActionValue#(RespToParent) respToPM;
endinterface

(* synthesize *)
module mkL1NormalInst(L1Normal#(8, 64));
  let ctrl <- mkL1Normal;
  return ctrl;
endmodule

module mkL1Normal
  (L1Normal#(ways, sets)) provisos(
    Log#(sets, setSz),
    Log#(ways, waySz),
    Add#(setSz, tagSz, RemainSz),
    Add#(setSz, _z, 15),
    Add#(waySz, _w, 6)
  );
  Cache#(0, tagSz, waySz, ways, sets, 0) cache <- mkCache;

  FIFOF#(FromParent) fromP <- mkFIFOF;
  FIFOF#(ReqFromCore) reqFromCore <- mkFIFOF;
//  FIFOF#(void) respToCore <- mkFIFOF;
  FIFOF#(ReqToParent) pReq <- mkFIFOF;
  FIFOF#(RespToParent) pResp <- mkFIFOF;

  Reg#(Counter) hit <- mkReg(0);
  Reg#(Counter) notPresentMiss <- mkReg(0);
  Reg#(Counter) parentPermMiss <- mkReg(0);

rule fromPResp(cache.init && fromP.first.isReq == False);
  match tagged FromParent{isReq: .isReq, index: .index, lineAddr: .lineAddr, from: .*, to: .to} = fromP.first;
  reqFromCore.deq;
  fromP.deq;
  cache.setS(index, to);
  cache.unsetPReq(index);
  cache.replaceUpd(index);
//  respToCore.enq(?);
endrule

begin
match tagged ReqFromCore{lineAddr: .lineAddr, to: .to} = reqFromCore.first;
let present = cache.isPresent(lineAddr);
let index = cache.getIndex(lineAddr);
let st = cache.getS(index);

(* preempts = "fromPResp, reqFromCore1" *)
rule reqFromCore1(cache.init && !cache.isPReq(index) &&
                  present &&
                  st >= to);
  hit <= hit + 1;
  reqFromCore.deq;
  cache.replaceUpd(index);
//  respToCore.enq(?);
endrule

(* preempts = "fromPResp, reqFromCore2" *)
rule reqFromCore2(cache.init && !cache.isPReq(index) &&
                  present &&
                  st < to);
  parentPermMiss <= parentPermMiss + 1;
  pReq.enq(ReqToParent{index: index, lineAddr: lineAddr, from: st, to: to});
  cache.setWaitS(index, to);
endrule

(* preempts = "fromPResp, reqFromCore3" *)
(* mutually_exclusive = "reqFromCore1, reqFromCore2, reqFromCore3" *)
rule reqFromCore3(cache.init && !cache.isPReq(index) &&
                  !present &&
                  cache.existsReplace(lineAddr));
  (* split *)
  notPresentMiss <= notPresentMiss + 1;
  let replaceIndex = cache.getReplace(lineAddr);
  Bit#(setSz) replaceSet = truncate(lineAddr);
  let replaceTag = cache.getTag(replaceIndex);
  let replaceLineAddr = {replaceTag, replaceSet};
  let replaceSt = cache.getS(replaceIndex);
  if(replaceSt > 0)
    pResp.enq(RespToParent{trigger: Voluntary (replaceLineAddr), to: 0, dirty: cache.dirty(replaceIndex)});
  cache.setTag(replaceIndex, truncateLSB(lineAddr));
  cache.setS(replaceIndex, 0);
  cache.setWaitS(replaceIndex, to);
  pReq.enq(ReqToParent{index: replaceIndex, lineAddr: lineAddr, from: 0, to: to});
endrule
end

begin
match tagged FromParent{isReq: .isReq, index: .pIndex, lineAddr: .lineAddr, from: .from, to: .to} = fromP.first;
let present = cache.isPresent(lineAddr);
let index = cache.getIndex(lineAddr);
let st = cache.getS(index);

(* preempts = "(fromPResp, reqFromCore1, reqFromCore2, reqFromCore3), fromPReq1" *)
rule fromPReq1(cache.init && fromP.first.isReq == True &&
               (!present || st <= to));
  fromP.deq;
endrule

(* preempts = "(fromPResp, reqFromCore1, reqFromCore2, reqFromCore3), fromPReq2" *)
(* mutually_exclusive = "fromPReq1, fromPReq2" *)
rule fromPReq2(cache.init && fromP.first.isReq == True &&
               (present && st > to));
  fromP.deq;
  pResp.enq(RespToParent{trigger: Forced (pIndex), to: to, dirty: cache.dirty(index)});
  cache.setS(index, to);
  if(to == 0)
    cache.replaceRem(index);
endrule
end

  method fromPM = fromP.enq;
  method reqFromCoreM = reqFromCore.enq;

  method ActionValue#(ReqToParent) reqToPM;
    pReq.deq;
    return pReq.first;
  endmethod

  method ActionValue#(RespToParent) respToPM;
    pResp.deq;
    return pResp.first;
  endmethod

//  method Action respToCoreM;
//    respToCore.deq;
//  endmethod
endmodule
