import Library::*;
import FIFOF::*;

interface FreeList#(numeric type t);
  method Bool init;
  method Bool isAvail;
  method ActionValue#(Bitt#(t)) alloc;
  method Action free(Bitt#(t) x);
endinterface

module mkFreeList(FreeList#(t));
  FIFOF#(Bitt#(t)) f <- mkSizedFIFOF(valueOf(t));

  Reg#(Bitt#(t)) initVal <- mkReg(0);
  Reg#(Bool) inited <- mkReg(False);

  rule initRl(!inited);
    initVal <= initVal + 1;
    f.enq(initVal);
    if(initVal == maxBound)
      inited <= True;
  endrule

  method Bool init = inited;

  method Bool isAvail = f.notEmpty;

  method ActionValue#(Bitt#(t)) alloc;
    f.deq;
    return f.first;
  endmethod

  method Action free(Bitt#(t) x);
    f.enq(x);
  endmethod
endmodule
