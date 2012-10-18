import Types::*;
import Vector::*;
import ConfigReg::*;
import Library::*;
import RegFile::*;

interface Cache#(numeric type mshrSz, numeric type tagSz, numeric type waySz, numeric type ways, numeric type sets, numeric type childs);
  method Bool init;
  method Bool isPresent(LineAddr lineAddr);
  method Index getIndex(LineAddr lineAddr);

  method St getS(Index index);
  method Action setS(Index index, St to);

  method Vector#(childs, St) getCs(Index index);
  method Action setC(Index index, Child id, St to);
  method Action setCs(Index index, Vector#(childs, St) tos);

  method Bool isCReq(Index index);
  method St getWaitCs(Index index);
  method Action setWaitCs(Index index, St to);
  method Action unsetCReq(Index index);

  method Bool isPReq(Index index);
  method Action setWaitS(Index index, St to);
  method Action unsetPReq(Index index);

  method Bool dirty(Index index);
  method Action setDirty(Index index);

  method Bit#(tagSz) getTag(Index index);
  method Action setTag(Index index, Bit#(tagSz) inTag);

  method Bool existsReplace(LineAddr lineAddr);
  method Action replaceUpd(Index index);
  method Action replaceRem(Index index);
  method Index getReplace(LineAddr lineAddr);

  method Bit#(mshrSz) getMshrPtr(Index index);
  method Action setMshrPtr(Index index, Bit#(mshrSz) mshrPtr);
endinterface

module mkCache
  (Cache#(mshrSz, tagSz, waySz, ways, sets, childs)) provisos(
    Log#(sets, setSz),
    Log#(ways, waySz),
    Add#(setSz, _x, AddrSz),
    Add#(setSz, tagSz, RemainSz),
    Add#(tagSz, _y, AddrSz),
    Add#(setSz, _z, 15),
    Add#(waySz, _w, 6)
  );

  Vector#(ways, RegFile#(Bit#(setSz), St)) st <- replicateM(mkRegFileWCF(0, fromInteger(valueOf(sets)-1)));
  Vector#(ways, RegFile#(Bit#(setSz), Vector#(childs, St))) cstates <- replicateM(mkRegFileWCF(0, fromInteger(valueOf(sets)-1)));
  Vector#(ways, RegFile#(Bit#(setSz), Bool)) pReq <- replicateM(mkRegFileWCF(0, fromInteger(valueOf(sets)-1)));
  Vector#(ways, RegFile#(Bit#(setSz), St)) waitSt <- replicateM(mkRegFileWCF(0, fromInteger(valueOf(sets)-1)));
  Vector#(ways, RegFile#(Bit#(setSz), Bool)) cReq <- replicateM(mkRegFileWCF(0, fromInteger(valueOf(sets)-1)));
  Vector#(ways, RegFile#(Bit#(setSz), St)) waitCStates <- replicateM(mkRegFileWCF(0, fromInteger(valueOf(sets)-1)));

  Vector#(ways, RegFile#(Bit#(setSz), Bool)) dirtyReg <- replicateM(mkRegFileWCF(0, fromInteger(valueOf(sets)-1)));
  Vector#(ways, RegFile#(Bit#(setSz), Bit#(tagSz))) tag <- replicateM(mkRegFileWCF(0, fromInteger(valueOf(sets)-1)));
  Vector#(ways, RegFile#(Bit#(setSz), Bit#(waySz))) lruBits <- replicateM(mkRegFileWCF(0, fromInteger(valueOf(sets)-1)));
  Vector#(ways, RegFile#(Bit#(setSz), Bit#(mshrSz))) mshrPtr <- replicateM(mkRegFileWCF(0, fromInteger(valueOf(sets)-1)));

  Reg#(Bool) inited <- mkReg(False);
  Reg#(Bit#(setSz)) initer <- mkReg(0);

  rule initRule(!inited);
    initer <= initer + 1;
    if(initer == maxBound)
      inited <= True;
    for(Integer i = 0; i < valueOf(ways); i = i + 1)
    begin
      dirtyReg[i].upd(initer, False);
      pReq[i].upd(initer, False);
      cReq[i].upd(initer, False);
      st[i].upd(initer, 0);
      cstates[i].upd(initer, replicate(0));
      lruBits[i].upd(initer, fromInteger(i));
    end
  endrule

  function dataT getRegFile(Vector#(ways, RegFile#(Bit#(setSz), dataT)) rf, Bit#(setSz) set, Integer i) = rf[i].sub(set);

  method Bool init = inited; 

  method Bool isPresent(LineAddr lineAddr);
    Bit#(tagSz) inTag = truncateLSB(lineAddr);
    Bit#(setSz) set = truncate(lineAddr);
    Vector#(ways, Bit#(tagSz)) tags = genWith(getRegFile(tag, set));
    return isValid(findElem(inTag, tags));
  endmethod

  method Index getIndex(LineAddr lineAddr);
    Bit#(tagSz) inTag = truncateLSB(lineAddr);
    Bit#(setSz) set = truncate(lineAddr);
    Vector#(ways, Bit#(tagSz)) tags = genWith(getRegFile(tag, set));
    return Index{set: zeroExtend(set), way: zeroExtend(pack(validValue(findElem(inTag, tags))))};
  endmethod

  method St getS(Index index);
    return st[index.way].sub(truncate(index.set));
  endmethod

  method Action setS(Index index, St to);
    st[index.way].upd(truncate(index.set), to);
  endmethod

  method Vector#(childs, St) getCs(Index index);
    return cstates[index.way].sub(truncate(index.set));
  endmethod

  method Action setC(Index index, Child id, St to);
    let cstatesL = cstates[index.way].sub(truncate(index.set));
    cstatesL[id] = to;
    cstates[index.way].upd(truncate(index.set), cstatesL);
  endmethod

  method Action setCs(Index index, Vector#(childs, St) tos);
    cstates[index.way].upd(truncate(index.set), tos);
  endmethod

  method Bool isCReq(Index index);
    return cReq[index.way].sub(truncate(index.set));
  endmethod

  method St getWaitCs(Index index) = waitCStates[index.way].sub(truncate(index.set));

  method Action setWaitCs(Index index, St to);
    cReq[index.way].upd(truncate(index.set), True);
    waitCStates[index.way].upd(truncate(index.set), to);
  endmethod

  method Action unsetCReq(Index index);
    cReq[index.way].upd(truncate(index.set), False);
  endmethod

  method Bool isPReq(Index index);
    return pReq[index.way].sub(truncate(index.set));
  endmethod

  method Action setWaitS(Index index, St to);
    pReq[index.way].upd(truncate(index.set), True);
    waitSt[index.way].upd(truncate(index.set), to);
  endmethod

  method Action unsetPReq(Index index);
    pReq[index.way].upd(truncate(index.set), False);
  endmethod

  method Bool dirty(Index index);
    return dirtyReg[index.way].sub(truncate(index.set));
  endmethod

  method Bit#(tagSz) getTag(Index index) = tag[index.way].sub(truncate(index.set));

  method Action setTag(Index index, Bit#(tagSz) inTag);
    tag[index.way].upd(truncate(index.set), inTag);
  endmethod

  method Action setDirty(Index index);
    dirtyReg[index.way].upd(truncate(index.set), True);
  endmethod

  method Bool existsReplace(LineAddr lineAddr);
    Bit#(setSz) set = truncate(lineAddr);
    function Bool bothFalse(Bool x, Bool y) = !x && !y;
    function Bool anyTrue(Bool x, Bool y) = x || y;
    Vector#(ways, Bool) cReqVec = genWith(getRegFile(cReq, set));
    Vector#(ways, Bool) pReqVec = genWith(getRegFile(pReq, set));
    return isValid(findElem(True, zipWith(bothFalse, cReqVec, pReqVec)));
  endmethod

  method Action replaceUpd(Index index);
    Bit#(waySz) old = lruBits[index.way].sub(truncate(index.set));
    for(Integer i = 0; i < valueOf(ways); i = i + 1)
    begin
      Bit#(waySz) bits = lruBits[i].sub(truncate(index.set));
      if(bits < old)
        lruBits[i].upd(truncate(index.set), bits + 1);
    end
  endmethod

  method Action replaceRem(Index index);
    Bit#(waySz) old = lruBits[index.way].sub(truncate(index.set));
    for(Integer i = 0; i < valueOf(ways); i = i + 1)
    begin
      Bit#(waySz) bits = lruBits[i].sub(truncate(index.set));
      if(bits > old)
        lruBits[i].upd(truncate(index.set), bits - 1);
      else if(bits == old)
        lruBits[i].upd(truncate(index.set), fromInteger(valueOf(ways)-1));
    end
  endmethod

  method Index getReplace(LineAddr lineAddr);
    Bit#(setSz) set = truncate(lineAddr);
    function isLast(Bit#(waySz) lru) = lru == fromInteger(valueOf(ways) - 1);
    Vector#(ways, Bit#(waySz)) lrus = genWith(getRegFile(lruBits, set));
    return Index{set: zeroExtend(set), way: zeroExtend(validValue(find(isLast, lrus)))};
  endmethod

  method Bit#(mshrSz) getMshrPtr(Index index) = mshrPtr[index.way].sub(truncate(index.set));

  method Action setMshrPtr(Index index, Bit#(mshrSz) mshrIndex);
    mshrPtr[index.way].upd(truncate(index.set), mshrIndex);
  endmethod
endmodule
