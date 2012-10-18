import Types::*;
import FIFOF::*;
import ConfigReg::*;

interface Memory;
  method Action respFromCache(RespToParent x);
  method Action reqFromCache(ReqToParent x);
  method ActionValue#(FromParent) respToCache;
endinterface

(* synthesize *)
module mkMemoryInst(Memory);
  let mem <- mkMemory(150);
  return mem;
endmodule

module mkMemory#(Latency lat)(Memory);
  FIFOF#(ReqToParent) reqFromC <- mkFIFOF;
  FIFOF#(FromParent) respToC <- mkFIFOF;
  FIFOF#(void) respFromC <- mkFIFOF;

  Reg#(Latency) latency <- mkConfigReg(0);
  Reg#(FromParent) to <- mkConfigRegU;

  rule deqReq(latency == 0);
    latency <= lat;
    reqFromC.deq;
    to <= FromParent {isReq: False, index: reqFromC.first.index, lineAddr: ?,
                      from: 0, to: 2};
  endrule

  rule countLat(latency > 1);
    latency <= latency - 1;
  endrule

  rule enqResp(latency == 1);
    respToC.enq(to);
    latency <= 0;
  endrule

  (* preempts = "deqReq, deqResp" *)
  rule deqResp(latency == 0);
    respFromC.deq;
  endrule

  method Action respFromCache(RespToParent x) = respFromC.enq(?);

  method reqFromCache = reqFromC.enq;

  method ActionValue#(FromParent) respToCache;
    respToC.deq;
    return respToC.first;
  endmethod
endmodule
