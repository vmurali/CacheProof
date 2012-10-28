#pragma once

#include "Fifo.h"
#include "CacheTypes.h"
#include "Debug.h"

typedef class memory {
private:
  Latency latRespFromP;
  Latency latRespToP;
  Latency latency;

  Fifo* reqToP,* respFromPF,* respToP;

  Fifo respFromP;

  void sendRespToC(Index& cIndex, LineAddr lineAddr) {
    FromP* resp = new FromP(Resp, cIndex, lineAddr, 0, 3, 0, 0);
    latRespFromP = latency;
    respFromP.enq(resp);
    printMemorySendResp(lineAddr, cIndex);
  }

  bool handleReqFromC() {
    if(reqToP->empty())
      return false;
    ReqToP* msg = (ReqToP*) reqToP->first();
    sendRespToC(msg->index, msg->lineAddr);
    reqToP->deq();
    printHandleReqFromC(0, msg->lineAddr, msg->to, true);
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
      handleReqFromC();
    }
  }

  void transfer() {
    respFromP.cycle();
  }
} Memory;
