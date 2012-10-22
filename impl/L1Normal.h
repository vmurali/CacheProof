#pragma once

#include "Cache.h"
#include "Fifo.h"
#include "CacheTypes.h"

typedef class l1Normal {
private:
  Fifo* fromP,* reqFromCore,* pReq,* pResp;
  Cache* cache;

  Who priority;

  U8 setSz;

  void sendPResp(Index& index, St to, Trigger trigger, Index& pIndex, LineAddr lineAddr) {
    cache->st[index.set][index.way] = to;
    RespToP* resp = new RespToP(trigger, pIndex, lineAddr, to, cache->dirty[index.set][index.way]);
    pResp->enq(resp);
    if(to == 0)
      cache->replaceRem(index);
  }

  void sendPReq(Index& index, LineAddr lineAddr, St to) {
    cache->pReq[index.set][index.way] = true;
    cache->waitS[index.set][index.way] = to;
    ReqToP* req = new ReqToP(index, lineAddr, cache->st[index.set][index.way], to);
    pReq->enq(req);
  }

  void resetLine(Index& index, LineAddr lineAddr) {
    cache->pReq[index.set][index.way] = false;
    cache->cReq[index.set][index.way] = false;
    cache->tag[index.set][index.way] = lineAddr >> setSz;
    cache->st[index.set][index.way] = 0;
    cache->dirty[index.set][index.way] = false;
  }

  bool handlePResp() {
    if(fromP->empty())
      return false;
    FromP* msg = (FromP*) fromP->first();
    if(msg->isReq)
       return false;
    Index index = msg->index;
    cache->st[index.set][index.way] = msg->to;
    cache->pReq[index.set][index.way] = false;
    fromP->deq();
    delete msg;
    reqFromCore->deq();
    cache->replaceUpd(index);
    ReqFromCore* m = (ReqFromCore*) reqFromCore->first();
    delete m;
    return true;
  }

  bool handleCReq() {
    if(reqFromCore->empty())
      return false;
    ReqFromCore* msg = (ReqFromCore*) reqFromCore->first();
    bool present = cache->isPresent(msg->lineAddr);
    if(!present) {
      if(!cache->existsReplace(msg->lineAddr)) {
        return true;
      }
      notPresentMiss++;
      Index replaceIndex = cache->getReplace(msg->lineAddr);
      LineAddr replaceLineAddr = (cache->tag[replaceIndex.set][replaceIndex.way] << setSz)
                            | replaceIndex.set;
      if(cache->st[replaceIndex.set][replaceIndex.way] > 0) {
        sendPResp(replaceIndex, (St)0, Voluntary, replaceIndex, replaceLineAddr);
      }
      resetLine(replaceIndex, msg->lineAddr);
      sendPReq(replaceIndex, msg->lineAddr, msg->to);
      return true;
    } else {
      Index index = cache->getIndex(msg->lineAddr);
      if(cache->pReq[index.set][index.way]) {
        return true;
      }
      if(cache->st[index.set][index.way] >= msg->to) {
        reqFromCore->deq();
        cache->replaceUpd(index);
        hit++;
        delete msg;
        return true;
      }
      noPermMiss++;
      sendPReq(index, msg->lineAddr, msg->to);
      return true;
    }
  }

  bool handlePReq() {
    if(fromP->empty())
      return false;
    FromP* msg = (FromP*) fromP->first();
    if(!msg->isReq)
       return false;
    bool present = cache->isPresent(msg->lineAddr);
    if(!present) {
      fromP->deq();
      return true;
    } else {
      Index index = cache->getIndex(msg->lineAddr);
      if(cache->st[index.set][index.way] > msg->to) {
        sendPResp(index, msg->to, Forced, msg->index, 0);
      }
      fromP->deq();
      delete msg;
      return true;
    }
  }

public:
  l1Normal(Fifo* _fromP, Fifo* _reqFromCore,
           Fifo* _reqToP, Fifo* _respToP,
           Way ways, U8 _setSz) {
    setSz = _setSz;

    cache = new Cache(ways, setSz, 0);

    fromP = _fromP; reqFromCore = _reqFromCore;
    pReq = _reqToP; pResp = _respToP;

    hit = 0;
    notPresentMiss = 0;
    noPermMiss = 0;

    priority = C;
  }
  ~l1Normal() {
    delete cache;
  }

  void cycle() {
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

  Counter hit;
  Counter notPresentMiss;
  Counter noPermMiss;

} InternalCtrl;
