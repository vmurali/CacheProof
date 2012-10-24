#pragma once

#include "Fifo.h"
#include "CacheTypes.h"

typedef class memory {
private:
  Latency latency;
  Latency latWait;
  Fifo respFromP;

  Fifo* reqToP,* respFromPF;

  void sendCResp(Index& cIndex) {
    FromP* resp = new FromP(false, cIndex, 0, 0, 2);
    latWait = latency;
    printf("memory send resp %d %d\n", cIndex.set, cIndex.way);
    respFromP.enq(resp);
  }

  bool handleCReq() {
    if(reqToP->empty())
      return false;
    ReqToP* msg = (ReqToP*) reqToP->first();
    sendCResp(msg->index);
    reqToP->deq();
    delete msg;
    return true;
  }

public:
  memory(Fifo* _reqToP, Fifo* _respFromP, Latency _latWait):
         latWait(0), latency(_latWait),
         respFromP(1), reqToP(_reqToP), respFromPF(_respFromP) {}
  ~memory() {}

  void cycle() {
    if(latWait != 0) {
      if(latWait > 1)
        latWait--;
      else if(latWait == 1 && !respFromP.empty() && !respFromPF->full()) {
        respFromPF->enq(respFromP.first());
        respFromP.deq();
        latWait = 0;
      }
      return;
    }
    handleCReq();

    respFromP.cycle();
  }
} Memory;
