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

function Bool transfer(St from, St to);
  return (from == 0);
endfunction

(* synthesize *)
module mkInternalCtrlInst(InternalCtrl#(64, 8, 1024, 16));
  let ctrl <- mkInternalCtrl;
  return ctrl;
endmodule

module mkInternalCtrl
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

  FIFOF#(FromParent) fromP <- mkFIFOF;
  FIFOF#(ReqFromChild) reqFromC <- mkFIFOF;
  FIFOF#(RespFromChild) respFromC <- mkFIFOF;
  FIFOF#(ReqToParent) pReq <- mkFIFOF;
  FIFOF#(RespToParent) pResp <- mkFIFOF;
  FIFOF#(ToChildren#(childs)) toCs <- mkFIFOF;

  Reg#(Counter) hit <- mkReg(0);
  Reg#(Counter) notPresentMiss <- mkReg(0);
  Reg#(Counter) childPermMiss <- mkReg(0);
  Reg#(Counter) parentPermMiss <- mkReg(0);

  function Bool whoHigher(St mustLower, currCState);
    return mustLower < currCState;
  endfunction

  function Bool childBitId(Child c, Integer i) = fromInteger(i) == c;

rule respFromCRl(cache.init && mshrFl.init);
match tagged RespFromChild{c: .c, trigger: .trigger, to: .to, dirty: .dirtyIn} = respFromC.first;
begin
  respFromC.deq;
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
  if(!cache.isCReq(index) || isCHigher)
  begin
    if(dirtyIn)
      cache.setDirty(index);
    cache.setC(index, c, to);
  end
  else
  begin
    cache.unsetCReq(index);
    case (mshr.sub(mshrPtr)) matches
      tagged Child {.origC, .cIndex, .cTo, .addrToM} :
      begin
        if(addrToM matches tagged Valid .realAddr)
        begin
          if(newDirty)
          begin
            Bit#(setSz) set = truncate(index.set);
            Bit#(tagSz) tag = cache.getTag(index);
            Bit#(RemainSz) lineAddr = {tag, set};
            pResp.enq(RespToParent{trigger: Voluntary (lineAddr), to: 0, dirty: newDirty});
          end
          cache.setTag(index, truncateLSB(realAddr));
          cache.setS(index, 0);
          cache.setCs(index, replicate(0));
          cache.setWaitS(index, cTo);
          cache.unsetDirty(index);
          mshr.upd(mshrPtr, Child (tuple4(origC, cIndex, cTo, Invalid)));
          pReq.enq(ReqToParent{index: index, lineAddr: realAddr, from: 0, to: cTo});
        end
        else if(!cache.isPReq(index))
        begin
          if(dirtyIn)
            cache.setDirty(index);
          toCs.enq(ToChildren{children: genWith(childBitId(origC)), isReq: False,
                              index: cIndex, lineAddr: ?, from: cstates, to: cTo});
          cstates[origC] = cTo;
          cache.setCs(index, cstates);
          cache.replaceUpd(index);
          mshrFl.free(mshrPtr);
        end
        else
        begin
          cache.setC(index, c, to);
          if(dirtyIn)
            cache.setDirty(index);
        end
      end
      tagged Parent {.pIndex, .oldMshrM}:
      begin
        if(dirtyIn)
          cache.setDirty(index);
        if(oldMshrM matches tagged Valid .oldMshr)
          cache.setMshrPtr(index, oldMshr);
        cache.setC(index, c, to);
        cache.setS(index, waitCs);
        mshrFl.free(mshrPtr);
        pResp.enq(RespToParent{trigger: Forced (pIndex), to: waitCs, dirty: newDirty});
        if(waitCs == 0)
          cache.replaceRem(index);
      end
    endcase
  end
end
endrule

(* preempts = "respFromCRl, fromPResp" *)
rule fromPResp(cache.init && mshrFl.init && fromP.first.isReq == False);
match tagged FromParent{isReq: .isReq, index: .index, lineAddr: .lineAddr, from: .*, to: .to} = fromP.first;
begin
  fromP.deq;
  cache.setS(index, to);
  cache.unsetPReq(index);
  let cstates = cache.getCs(index);
  let mshrPtr = cache.getMshrPtr(index);
  if(!cache.isCReq(index))
  begin
    case (mshr.sub(mshrPtr)) matches
      tagged Child {.origC, .cIndex, .cTo, .*} :
      begin
        toCs.enq(ToChildren{children: genWith(childBitId(origC)), isReq: False,
                            index: cIndex, lineAddr: ?, from: cstates, to: cTo});
        cache.replaceUpd(index);
        cache.setC(cIndex, origC, cTo);
        mshrFl.free(mshrPtr);
      end
    endcase
  end
end
endrule

(* preempts = "(respFromCRl, fromPResp), reqFromCRl" *)
rule reqFromCRl(cache.init && mshrFl.init);
match tagged ReqFromChild{c: .c, index: .cIndex, lineAddr: .lineAddr, from: .from, to: .to} = reqFromC.first;
begin
  let present = cache.isPresent(lineAddr);
  let index = cache.getIndex(lineAddr);
  let st = cache.getS(index);
  let cstates = cache.getCs(index);
  let cHigher = map(whoHigher(compat(to)), cstates);
  cHigher[c] = False;
  let isCHigher = isValid(findElem(True, cHigher));

  if(!cache.isPReq(index) && !cache.isCReq(index))
  begin
    if(present && cstates[c] == from)
    begin
      reqFromC.deq;
      if(st >= to && !isCHigher)
      begin
        cache.setC(index, c, to);
        toCs.enq(ToChildren{children: genWith(childBitId(c)), isReq: False,
                            index: cIndex, lineAddr: ?, from: cstates, to: to});
        cache.replaceUpd(index);
        hit <= hit + 1;
      end
      else
      begin
        let mshrPtr <- mshrFl.alloc;
        mshr.upd(mshrPtr, Child (tuple4(c, cIndex, to, Invalid)));
        cache.setMshrPtr(index, mshrPtr);
        if(st < to)
        begin
          cache.setWaitS(index, to);
          pReq.enq(ReqToParent{index: index, lineAddr: lineAddr, from: cstates[c], to: to});
          parentPermMiss <= parentPermMiss + 1;
        end
        if(isCHigher)
        begin
          cache.setWaitCs(index, compat(to));
          toCs.enq(ToChildren{children: cHigher, isReq: True, index: index,
                              lineAddr: lineAddr, from: ?, to: compat(to)});
          childPermMiss <= childPermMiss + 1;
        end
      end
    end
    else if(from == 0 && cache.existsReplace(lineAddr))
    begin
      reqFromC.deq;
      let replaceIndex = cache.getReplace(lineAddr);
      let replaceS = cache.getS(replaceIndex);
      let replaceCStates = cache.getCs(replaceIndex);
      let replaceCHigher = map(whoHigher(0), replaceCStates);
      let isReplaceCHigher = isValid(findElem(True, replaceCHigher));
      Bit#(setSz) replaceSet = truncate(index.set);
      Bit#(tagSz) replaceTag = cache.getTag(index);
      Bit#(RemainSz) replaceLineAddr = {replaceTag, replaceSet};
      let mshrPtr <- mshrFl.alloc;
      cache.setMshrPtr(replaceIndex, mshrPtr);
      if(!isReplaceCHigher)
      begin
        if(replaceS > 0)
          pResp.enq(RespToParent{trigger: Voluntary (replaceLineAddr), to: 0, dirty: cache.dirty(replaceIndex)});
        cache.setTag(replaceIndex, truncateLSB(lineAddr));
        cache.setS(replaceIndex, 0);
        cache.setCs(replaceIndex, replicate(0));
        cache.unsetDirty(replaceIndex);
        mshr.upd(mshrPtr, Child (tuple4(c, cIndex, to, Invalid)));
        cache.setWaitS(replaceIndex, to);
        pReq.enq(ReqToParent{index: replaceIndex, lineAddr: lineAddr, from: 0, to: to});
      end
      else
      begin
        mshr.upd(mshrPtr, Child (tuple4(c, cIndex, to, Valid (lineAddr))));
        toCs.enq(ToChildren{children: replaceCHigher, isReq: True, index: replaceIndex, lineAddr: replaceLineAddr, from: replaceCStates, to: 0});
        cache.setWaitCs(replaceIndex, 0);
      end
      notPresentMiss <= notPresentMiss + 1;
    end
  end
end
endrule

(* preempts = "(respFromCRl, fromPResp, reqFromCRl), fromPReq"*)
rule fromPReq(cache.init && mshrFl.init && fromP.first.isReq);
match tagged FromParent{isReq: .isReq, index: .pIndex, lineAddr: .lineAddr, from: .from, to: .to} = fromP.first;
begin
  let present = cache.isPresent(lineAddr);
  let index = cache.getIndex(lineAddr);
  let st = cache.getS(index);
  let cstates = cache.getCs(index);
  let cHigher = map(whoHigher(to), cstates);
  let isCHigher = isValid(findElem(True, cHigher));
  if(!cache.isCReq(index))
  begin
    fromP.deq;
    if(present && st > to)
    begin
      if(!isCHigher)
      begin
        cache.setS(index, to);
        pResp.enq(RespToParent{trigger: Forced (pIndex), to: to, dirty: cache.dirty(index)});
        if(to == 0)
          cache.replaceRem(index);
      end
      else
      begin
        let mshrPtr <- mshrFl.alloc;
        let oldMshr = cache.isPReq(index)? Valid (cache.getMshrPtr(index)): Invalid;
        mshr.upd(mshrPtr, Parent (tuple2(pIndex, oldMshr)));
        toCs.enq(ToChildren{children: cHigher, isReq: True, index: index,
                            lineAddr: lineAddr, from:?, to: to});
        cache.setWaitCs(index, to);
      end
    end
  end
end
endrule

  method fromPM = fromP.enq;
  method reqFromCM = reqFromC.enq;
  method respFromCM = respFromC.enq;

  method ActionValue#(ReqToParent) reqToPM;
    pReq.deq;
    return pReq.first;
  endmethod

  method ActionValue#(RespToParent) respToPM;
    pResp.deq;
    return pResp.first;
  endmethod

  method ActionValue#(ToChildren#(childs)) toCsM;
    toCs.deq;
    return toCs.first;
  endmethod
endmodule
