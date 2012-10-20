import CFeeder::*;
import FIFOF::*;
import Types::*;

interface Feeder;
  method ActionValue#(ReqFromCore) feed;
  method Action init(Bit#(32) tId);
endinterface

(* synthesize *)
module mkDataFeeder(Feeder);
  FIFOF#(ReqFromCore) f <- mkFIFOF;
  Reg#(Bool) inited <- mkReg(False);
  Reg#(Bit#(32)) tId <- mkRegU;
  Reg#(Bit#(32)) count <- mkReg(0);

  rule downCount(inited && count != 0);
    count <= count - 1;
  endrule

  rule feedRl(inited && count == 0);
    let to <- getDataSt(tId);
    if(to == 0)
    begin
      let count_ <- getCount(tId);
      count <= count_;
    end
    else
    begin
      let addr <- getFeed(True, tId);
      LineAddr lineAddr = truncateLSB(addr);
      f.enq(ReqFromCore{to: to, lineAddr: lineAddr});
    end
  endrule

  method Action init(Bit#(32) x) if(!inited);
    initialize(True, x);
    tId <= x;
    inited <= True;
  endmethod

  method ActionValue#(ReqFromCore) feed;
    f.deq;
    return f.first;
  endmethod
endmodule

(* synthesize *)
module mkInstFeeder(Feeder);
  FIFOF#(ReqFromCore) f <- mkFIFOF;
  Reg#(Bool) inited <- mkReg(False);
  Reg#(Bit#(32)) tId <- mkRegU;

  rule feedRl(inited);
    let addr <- getFeed(False, tId);
    LineAddr lineAddr = truncateLSB(addr);
    f.enq(ReqFromCore{to: 1, lineAddr: lineAddr});
  endrule

  method Action init(Bit#(32) x) if(!inited);
    initialize(False, x);
    tId <= x;
    inited <= True;
  endmethod

  method ActionValue#(ReqFromCore) feed;
    f.deq;
    return f.first;
  endmethod
endmodule
