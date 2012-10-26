#pragma once

#include "Cache.h"
#include "Fifo.h"
#include "CacheTypes.h"

typedef class l1Normal {
private:
  U8 setSz;
  Cache cache;
  Fifo fromP, reqFromCore, reqToP, respToP;

  bool processing;
  Who priority;

  void sendPResp(Index& index, St to, Trigger trigger, Index& pIndex, LineAddr lineAddr) {
    cache.st[index.set][index.way] = to;
    RespToP* resp = new RespToP(trigger, pIndex, lineAddr, to, cache.dirty[index.set][index.way]);
    respToP.enq(resp);
    if(to == 0)
      cache.replaceRem(index);
  }

  void sendPReq(Index& index, LineAddr lineAddr, St to) {
    processing = true;
    cache.pReq[index.set][index.way] = true;
    cache.waitS[index.set][index.way] = to;
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

  bool handlePResp() {
    if(fromP.empty())
      return false;
    FromP* msg = (FromP*) fromP.first();
    if(msg->isReq)
       return false;
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

  bool handleCReq() {
    if(processing)
      return false;
    if(reqFromCore.empty()) {
      return false;
    }
    ReqFromCore* msg = (ReqFromCore*) reqFromCore.first();
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
        if(respToP.full()) {
          return true;
        }
        sendPResp(replaceIndex, (St)0, Voluntary, replaceIndex, replaceLineAddr);
      }
      sendPReq(replaceIndex, msg->lineAddr, msg->to);
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
        delete msg;
        return true;
      }
      if(reqToP.full()) {
        return true;
      }
      sendPReq(index, msg->lineAddr, msg->to);
      if(cache.st[index.set][index.way] == 0)
        inclusiveMiss++;
      else
        noPermMiss++;
      return true;
    }
  }

  bool handlePReq() {
    if(fromP.empty())
      return false;
    FromP* msg = (FromP*) fromP.first();
    if(!msg->isReq)
       return false;
    bool present = cache.isPresent(msg->lineAddr);
    if(!present) {
      fromP.deq();
      return true;
    }
    Index index = cache.getIndex(msg->lineAddr);
    if(cache.st[index.set][index.way] > msg->to) {
      if(respToP.full())
        return true;
      sendPResp(index, msg->to, Forced, msg->index, msg->lineAddr);
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

  l1Normal(Way ways, U8 _setSz):
          setSz(_setSz), cache(ways, setSz, 0),
          fromP(2), reqFromCore(2),
          reqToP(2), respToP(2),
          priority(C), processing(false),
          hit(0), notPresentMiss(0), noPermMiss(0), inclusiveMiss(0) {}

  ~l1Normal() {}

  void cycle() {
    LineAddr addr = (cache.tag[5][0] << setSz)|5;
    if(handlePResp()) {}
    else if(priority == P) {
      if(handlePReq()) {
        priority = C;
      }
      else handleCReq();
    }
    else {
      if(handleCReq()) {
        priority = P;
      }
      else handlePReq();
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
