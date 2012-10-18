import Vector::*;
import InternalCtrl::*;
import ConfigReg::*;
import Types::*;

(* synthesize *)
module mkTestInst();
  let ctrl <- mkInternalCtrlInst;

  Reg#(Latency) step <- mkConfigReg(0);

  Reg#(Index) idx <- mkConfigRegU;

  function next;
  action
    step <= step + 1;
  endaction
  endfunction

  rule cReq(step == 0);
    ctrl.reqFromCM(ReqFromChild{c:1, lineAddr: 0, index: ?, from: 0, to: 2});
    $display("sent req from child");
    next;
  endrule

/*
  rule pReq(step == 1);
    ctrl.fromPM(FromParent{isReq: True, index: ?, lineAddr: 0, from: ?, to: 0});
    $display("sent req from parent");
    next;
  endrule
*/

  rule waiter(step < 16);
    next;
  endrule

  rule getCReq(step == 16);
    let toCs <- ctrl.toCsM;
    $display("got req to downgrade children");
    $display("children: %b, isReq: %d, index: %b, lineAddr: %d, from: %b, to: %d",
              toCs.children, toCs.isReq, toCs.index, toCs.lineAddr, toCs.from, toCs.to);
    idx <= toCs.index;
    next;
  endrule

  rule c2Resp(step == 17);
    ctrl.respFromCM(RespFromChild{c: 3, trigger: Forced (idx), to: 0, dirty: False});
    $display("send downgrade resp 3");
    next;
  endrule

  rule c3Resp(step == 18);
    ctrl.respFromCM(RespFromChild{c: 2, trigger: Forced (idx), to: 0, dirty: False});
    $display("send downgrade resp 2");
    next;
  endrule

  rule getPResp;
    let resp <- ctrl.respToPM;
    $display("%d resp to parent: set: %d way: %d %d %b", $time, resp.trigger.Forced.set, resp.trigger.Forced.way, resp.to, resp.dirty);
  endrule

  rule getPReq;
    let req <- ctrl.reqToPM;
    $display("req to parent: from: %d to: %d", req.from, req.to);
    ctrl.fromPM(FromParent{isReq: False, index: req.index, lineAddr: 0, from: req.from, to: req.to});
  endrule

  rule getCResp;
    let resp <- ctrl.toCsM;
    $display("%d children: %b, isReq: %d set: %d, way: %d, lineAddr: %x from: %b, to: %d", $time,
              resp.children, resp.isReq, resp.index.set, resp.index.way, resp.lineAddr, resp.from, resp.to);
  endrule
endmodule
