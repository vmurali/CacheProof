#pragma once

#include "Fifo.h"
#include "CacheTypes.h"

typedef class memory {
private:
  Latency latRespFromP;
  Latency latRespToP;
  Latency latency;

  Fifo* reqToP,* respFromPF,* respToP;

  Fifo respFromP;

  void sendCResp(Index& cIndex, LineAddr lineAddr) {
    FromP* resp = new FromP(false, cIndex, lineAddr, 0, 2);
    latRespFromP = latency;
    respFromP.enq(resp);
  }

  bool handleCReq() {
    if(reqToP->empty())
      return false;
    ReqToP* msg = (ReqToP*) reqToP->first();
    sendCResp(msg->index, msg->lineAddr);
    reqToP->deq();
    delete msg;
    return true;
  }

public:
  memory(Fifo* _reqToP, Fifo* _respFromP, Fifo* _respToP, Latency _latency):
         latRespFromP(0), latRespToP(0), latency(_latency),
         respFromP(1), reqToP(_reqToP), respFromPF(_respFromP), respToP(_respToP) {}
  ~memory() {}

  void cycle() {
    if(latRespFromP != 0 || latRespToP != 0) {
      if(latRespFromP > 1) {
        latRespFromP--;
      } else if(latRespFromP == 1 && !respFromP.empty() && !respFromPF->full()) {
        respFromPF->enq(respFromP.first());
        respFromP.deq();
        latRespFromP = 0;
      }
      if(latRespToP > 0) {
        latRespToP--;
      }
      return;
    }
    if(!respToP->empty()) {
      latRespToP = latency;
      RespToP* msg = (RespToP*) respToP->first();
      respToP->deq();
      delete msg;
    } else {
      handleCReq();
    }
  }

  void transfer() {
    respFromP.cycle();
  }
} Memory;
