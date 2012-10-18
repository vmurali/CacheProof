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
  let ctrl <- mkInternalCtrl(10, 20, 20);
  return ctrl;
endmodule

typedef enum {Nothing, ReqToP, RespToP, ToCs} Who deriving (Bits, Eq);

module mkInternalCtrl#(Latency tagLat, Latency dataReadLat, Latency dataWriteLat)
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

  function Bool whoHigher(St mustLower, currCState);
    return currCState > mustLower;
  endfunction

  function Bool childBitId(Child c, Integer i) = fromInteger(i) == c;

rule all(cache.init && mshrFl.init);
if(respFromC.first matches tagged RespFromChild{
     c: .c, trigger: .trigger, to: .to, dirty: .dirtyIn})
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
          mshr.upd(mshrPtr, Child (tuple4(origC, cIndex, cTo, Invalid)));
          pReq.enq(ReqToParent{index: index, lineAddr: realAddr, from: 0, to: cTo});
        end
        else if(!cache.isPReq(index))
        begin
          if(dirtyIn)
            cache.setDirty(index);
          toCs.enq(ToChildren{children: genWith(childBitId(origC)), isReq: False,
                              index: cIndex, lineAddr: ?, from: cstates, to: cTo});
          cache.replaceUpd(index);
          cstates[c] = to;
          cstates[origC] = cTo;
          cache.setCs(index, cstates);
          mshrFl.free(mshrPtr);
        end
        else
        begin
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
else if(fromP.first matches tagged FromParent{
        isReq: .isReq, index: .index, lineAddr: .lineAddr, from: .from, to: .to} &&& isReq == False)
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
else if(reqFromC.first matches tagged ReqFromChild{c: .c, index: .cIndex, lineAddr: .lineAddr, from: .from, to: .to})
begin
  let present = cache.isPresent(lineAddr);
  let index = cache.getIndex(lineAddr);
  let st = cache.getS(index);
  let cstates = cache.getCs(index);
  let cHigher = map(whoHigher(compat(to)), cstates);
  cHigher[c] = False;
  let isCHigher = isValid(findElem(True, cHigher));

  if(!cache.isPReq(index) && !cache.isCReq(index) &&
        (present && cstates[c] == from || from == 0 && cache.existsReplace(lineAddr)))
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
        end
        if(isCHigher)
        begin
          cache.setWaitCs(index, compat(to));
          toCs.enq(ToChildren{children: cHigher, isReq: True, index: index,
                              lineAddr: lineAddr, from: ?, to: compat(to)});
        end
      end
    end
    else if(from == 0 && cache.existsReplace(lineAddr))
    begin
      let replaceIndex = cache.getReplace(lineAddr);
      cache.setTag(replaceIndex, truncateLSB(lineAddr));
      cache.setS(replaceIndex, 0);
      cache.setCs(replaceIndex, replicate(0));
      let mshrPtr <- mshrFl.alloc;
      mshr.upd(mshrPtr, Child (tuple4(c, cIndex, to, Valid (lineAddr))));
      cache.setMshrPtr(replaceIndex, mshrPtr);
      cache.setWaitS(replaceIndex, to);
      pReq.enq(ReqToParent{index: replaceIndex, lineAddr: lineAddr, from: 0, to: to});
      reqFromC.deq;
    end
  end
end
else if(fromP.first matches tagged FromParent{
        isReq: .isReq, index: .pIndex, lineAddr: .lineAddr, from: .from, to: .to} &&& isReq == True)
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
        fromP.deq;
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
      end
    end
  end
  if(!present || !cache.isCReq(index))
  begin
    if(st > to)
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
        cache.setWaitCs(index, to);
        toCs.enq(ToChildren{children: cHigher, isReq: True, index: index, lineAddr: lineAddr, from: cstates, to: to});
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
