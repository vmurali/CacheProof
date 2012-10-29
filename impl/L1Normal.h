#pragma once

#include "Cache.h"
#include "Fifo.h"
#include "CacheTypes.h"
#include "Debug.h"

typedef class l1Normal {
private:
  U8 setSz;
  Cache cache;
  Fifo fromP, reqFromCore, reqToP, respToP;

  bool processing;
  Who priority;

  void sendRespToP(Index& index, St to, Trigger trigger, Index& pIndex, LineAddr lineAddr) {
    printSendRespToP(lineAddr, trigger, index, to);
    cache.st[index.set][index.way] = to;
    RespToP* resp = new RespToP(trigger, pIndex, lineAddr, to, cache.dirty[index.set][index.way], false, 0);
    respToP.enq(resp);
    if(cache.dirty[index.set][index.way])
      respToPDataC++;
    else
      respToPC++;
    if(to == 0)
      cache.replaceRem(index);
  }

  void sendReqToP(Index& index, LineAddr lineAddr, St to) {
    printSendReqToP(lineAddr, index, to);
    processing = true;
    cache.pReq[index.set][index.way] = true;
    cache.waitS[index.set][index.way] = to;
    reqToPC++;
    ReqToP* req = new ReqToP(index, lineAddr, cache.st[index.set][index.way], to);
    reqToP.enq(req);
  }

  void resetLine(Index& index, LineAddr lineAddr) {
    cache.pReq[index.set][index.way] = false;
    cache.cReq[index.set][index.way] = false;
    cache.tag[index.set][index.way] = lineAddr >> setSz;
    cache.st[index.set][index.way] = 0;
    cache.dirty[index.set][index.way] = false;
  }

  bool handleRespFromP() {
    if(fromP.empty())
      return false;
    FromP* msg = (FromP*) fromP.first();
    if(msg->type != Resp)
       return false;
    printHandleRespFromP(msg->lineAddr, msg->index, msg->to);
    Index index = msg->index;
    cache.st[index.set][index.way] = msg->to;
    cache.pReq[index.set][index.way] = false;
    fromP.deq();
    delete msg;
    cache.replaceUpd(index);
    ReqFromCore* m = (ReqFromCore*) reqFromCore.first();
    reqFromCore.deq();
    processing = false;
    delete m;
    return true;
  }

  bool handleReqFromCore() {
    if(processing)
      return false;
    if(reqFromCore.empty()) {
      return false;
    }
    ReqFromCore* msg = (ReqFromCore*) reqFromCore.first();
    printHandleReqFromCore(msg->lineAddr, msg->to);
    LineAddr addr = msg->lineAddr;
    msg->lineAddr = addr >> 6;
    bool present = cache.isPresent(msg->lineAddr);
    if(!present) {
      if(!cache.existsReplace(msg->lineAddr)) {
        return true;
      }
      Index replaceIndex = cache.getReplace(msg->lineAddr);
      LineAddr replaceLineAddr = (cache.tag[replaceIndex.set][replaceIndex.way] << setSz)
                            | replaceIndex.set;
      if(reqToP.full()) {
        return true;
      }
      if(cache.st[replaceIndex.set][replaceIndex.way] > 0) {
        if(respToP.full()){
          return true;
        }
        sendRespToP(replaceIndex, (St)0, Voluntary, replaceIndex, replaceLineAddr);
      }
      sendReqToP(replaceIndex, msg->lineAddr, msg->to);
      resetLine(replaceIndex, msg->lineAddr);
      notPresentMiss++;
      return true;
    } else {
      Index index = cache.getIndex(msg->lineAddr);
      if(cache.pReq[index.set][index.way]) {
        return true;
      }
      if(cache.st[index.set][index.way] >= msg->to) {
        reqFromCore.deq();
        cache.replaceUpd(index);
        hit++;
        if(msg->to == 3)
           cache.dirty[index.set][index.way] = true;
        delete msg;
        return true;
      }
      if(reqToP.full()) {
        return true;
      }
      sendReqToP(index, msg->lineAddr, msg->to);
      if(cache.st[index.set][index.way] == 0)
        inclusiveMiss++;
      else
        noPermMiss++;
      return true;
    }
  }

  bool handleReqFromP() {
    if(fromP.empty())
      return false;
    FromP* msg = (FromP*) fromP.first();
    if(msg->type != Req)
       return false;
    bool present = cache.isPresent(msg->lineAddr);
    printHandleReqFromP(msg->lineAddr, msg->to, present);
    if(!present) {
      fromP.deq();
      return true;
    }
    Index index = cache.getIndex(msg->lineAddr);
    if(cache.st[index.set][index.way] > msg->to) {
      if(respToP.full())
        return true;
      sendRespToP(index, msg->to, Forced, msg->index, msg->lineAddr);
    }
    fromP.deq();
    delete msg;
    return true;
  }

public:

  Counter hit;
  Counter notPresentMiss;
  Counter noPermMiss;
  Counter inclusiveMiss;
  Counter reqToPC, respToPC, respToPDataC;

  l1Normal(Way ways, U8 _setSz):
          setSz(_setSz), cache(ways, setSz, 0),
          fromP(2), reqFromCore(2),
          reqToP(2), respToP(2),
          priority(C), processing(false),
          hit(0), notPresentMiss(0), noPermMiss(0), inclusiveMiss(0),
          reqToPC(0), respToPC(0), respToPDataC(0) {}

  ~l1Normal() {}

  void cycle() {
    LineAddr addr = (cache.tag[5][0] << setSz)|5;
    if(handleRespFromP()) {}
    else if(priority == P) {
      if(handleReqFromP()) {
        priority = C;
      }
      else handleReqFromCore();
    }
    else {
      if(handleReqFromCore()) {
        priority = P;
      }
      else handleReqFromP();
    }
  }

  void transfer() {
    fromP.cycle();
    reqFromCore.cycle();
    reqToP.cycle();
    respToP.cycle();
  }

  Fifo* getFromP() { return &fromP; }
  Fifo* getReqFromCore() { return &reqFromCore; }
  Fifo* getReqToP() { return &reqToP; }
  Fifo* getRespToP() { return &respToP; }
} L1Normal;
