#pragma once

#include "Cache.h"
#include "Fifo.h"
#include "FreeList.h"
#include "CacheTypes.h"

typedef class toCs {
public:
  Child childs;
  bool* children;
  bool isReq;
  Index index;
  LineAddr lineAddr;
  St* from;
  St to;

  toCs(Child _childs, bool* _children, bool _isReq, Index _index,
       LineAddr _lineAddr, St* _from, St _to) {
    childs = _childs; children = _children; isReq = _isReq;
    index = _index; lineAddr = _lineAddr; from = _from; to = _to;
  }
  toCs(Child _childs, Child c, bool _isReq, Index _index,
       LineAddr _lineAddr, St _from, St _to) {
    childs = _childs;
    children = new bool[childs];
    for(Child i = 0; i < childs; i++)
      children[i] = false;
    children[c] = true;
    isReq = _isReq;
    index = _index;
    lineAddr = _lineAddr;
    from = new St[childs];
    from[c] = _from;
    to = _to;
  }
  ~toCs() {
    delete children;
    delete from;
  }
} ToCs;

typedef class reqFromC {
public:
  Child c;
  Index index;
  LineAddr lineAddr;
  St from;
  St to;

  reqFromC(Child _c, Index _index, LineAddr _lineAddr, St _from, St _to) {
    c = _c; index = _index; lineAddr = _lineAddr; from = _from; to = _to;
  }
  ~reqFromC() {}
} ReqFromC;

typedef class respFromC {
public:
  Child c;
  Trigger trigger;
  Index index;
  LineAddr lineAddr;
  St to;
  bool dirty;

  respFromC(Child _c, Trigger _trigger, Index _index, LineAddr _lineAddr, St _to, bool _dirty) {
    c = _c; trigger = _trigger; index = _index; lineAddr = _lineAddr; to = _to; dirty = _dirty;
  }

  ~respFromC() {}
} RespFromC;

typedef enum {P, C} Who;

typedef class mshr {
public:
  Who who;
  Child c;
  Index index;
  St to;
  bool isReplacing;
  LineAddr lineAddr;

  mshr() {}
  mshr(Who _who, Child _c, Index _index, St _to, bool _isReplacing, LineAddr _lineAddr) {
    who = _who; c = _c; index = _index; to = _to; isReplacing = _isReplacing;
    lineAddr = _lineAddr;
  }
  ~mshr() {}
} Mshr;

typedef U32 Latency;

typedef class internalCtrl {
private:
  Fifo* fromP,* reqFromC,* respFromC,* pReqF,* pRespF,* toCsF;
  Child childs;
  Cache* cache;
  FreeList* mshrFl;
  Mshr* mshr;
  Latency tagLat;
  Latency dataLat;

  Fifo* pReq,* pResp,* toCs;
  Latency latPReq, latPResp, latToCs, latWait;

  Who priority;

  U8 setSz;

  St compat(St to) {
    if(to == 2)
      return 0;
    if(to == 1)
      return 1;
    if(to == 0)
      return 2;
  }

  bool isCHigher(Index index, St to) {
    bool _isCHigher = false;
    for(Child i = 0; i < childs; i++)
      if(cache->cstates[index.set][index.way][i] > to)
        _isCHigher = true;
    return _isCHigher;
  }

  void sendPResp(Index& index, St to, Trigger trigger, Index& pIndex, LineAddr lineAddr, Latency lat) {
    cache->st[index.set][index.way] = to;
    RespToP* resp = new RespToP(trigger, pIndex, lineAddr, to, cache->dirty[index.set][index.way]);
    pResp->enq(resp);
    latPResp = cache->dirty[index.set][index.way]? dataLat : lat;
    if(to == 0)
      cache->replaceRem(index);
  }

  void sendCResp(Index& index, St to, Child c, Index& cIndex, Latency lat) {
    ToCs* resp = new ToCs(childs, c, false, cIndex, 0, cache->cstates[index.set][index.way][c], to);
    latToCs = cache->cstates[index.set][index.way][c] == 0? dataLat: lat;
    cache->cstates[index.set][index.way][c] = to;
    toCs->enq(resp);
    cache->replaceUpd(index);
  }

  void sendCsReq(Index& index, LineAddr lineAddr, St to) {
    cache->cReq[index.set][index.way] = true;
    cache->waitCs[index.set][index.way] = to;
    bool* highChildren = new bool[childs];
    for(Child i = 0; i < childs; i++)
       highChildren[i] = cache->cstates[index.set][index.way][i] > to;
    ToCs* req = new ToCs(childs, highChildren, true, index, lineAddr, NULL, to);
    toCs->enq(req);
    latToCs = tagLat;
  }

  void sendPReq(Index& index, LineAddr lineAddr, St to) {
    cache->pReq[index.set][index.way] = true;
    cache->waitS[index.set][index.way] = to;
    ReqToP* req = new ReqToP(index, lineAddr, cache->st[index.set][index.way], to);
    pReq->enq(req);
    latPReq = tagLat;
  }

  void allocMshr(Index& index, Mshr entry) {
    MshrPtr mshrPtr = mshrFl->alloc();
    cache->mshrPtr[index.set][index.way] = mshrPtr;
    mshr[mshrPtr] = entry;
  }

  void resetLine(Index& index, LineAddr lineAddr) {
    cache->pReq[index.set][index.way] = false;
    cache->cReq[index.set][index.way] = false;
    cache->tag[index.set][index.way] = lineAddr >> setSz;
    cache->st[index.set][index.way] = 0;
    for(Child i = 0; i < childs; i++)
      cache->cstates[index.set][index.way][i] = 0;
    cache->dirty[index.set][index.way] = false;
  }

  bool handleCResp() {
    if(respFromC->empty())
      return false;
    RespFromC* msg = (RespFromC*) respFromC->first();
    Index index = msg->trigger == Forced? msg->index: cache->getIndex(msg->lineAddr);
    cache->cstates[index.set][index.way][msg->c] = msg->to;
    if(cache->cReq[index.set][index.way]) {
      MshrPtr mshrPtr = cache->mshrPtr[index.set][index.way];
      Mshr m = mshr[mshrPtr];
      St to = m.who == P? m.to: compat(m.to);
      if(!isCHigher(index, to)) {
        cache->cReq[index.set][index.way] = false;
        if(m.who == P)
          sendPResp(index, m.to, Forced, m.index, 0, msg->trigger == Forced? 1: tagLat);
        else if(!cache->pReq[index.set][index.way])
          sendCResp(index, m.to, m.c, m.index, msg->trigger == Forced? 1: tagLat);
      }
    }
    respFromC->deq();
    delete msg;
    return true;
  }

  bool handlePResp() {
    if(fromP->empty())
      return false;
    FromP* msg = (FromP*) fromP->first();
    if(msg->isReq)
       return false;
    Index index = msg->index;
    MshrPtr mshrPtr = cache->mshrPtr[index.set][index.way];
    cache->st[index.set][index.way] = msg->to;
    cache->pReq[index.set][index.way] = false;
    if(!cache->cReq[index.set][index.way]) {
      Mshr m = mshr[mshrPtr];
      sendCResp(index, m.to, m.c, m.index, 1);
      mshrFl->free(mshrPtr);
    }
    fromP->deq();
    delete msg;
    return true;
  }

  bool handleCReq() {
    if(reqFromC->empty())
      return false;
    ReqFromC* msg = (ReqFromC*) reqFromC->first();
    bool present = cache->isPresent(msg->lineAddr);
    if(!present) {
      if(!mshrFl->isAvail() || !cache->existsReplace(msg->lineAddr)) {
        latWait = tagLat;
        return true;
      }
      notPresentMiss++;
      Index replaceIndex = cache->getReplace(msg->lineAddr);
      LineAddr replaceLineAddr = (cache->tag[replaceIndex.set][replaceIndex.way] << setSz)
                            | replaceIndex.set;
      if(!isCHigher(replaceIndex, 0)) {
        if(cache->st[replaceIndex.set][replaceIndex.way] > 0) {
          sendPResp(replaceIndex, (St)0, Voluntary, replaceIndex, replaceLineAddr, tagLat);
        }
        resetLine(replaceIndex, msg->lineAddr);
        allocMshr(replaceIndex, Mshr(C, msg->c, msg->index, msg->to, false, (LineAddr)0));
        sendPReq(replaceIndex, msg->lineAddr, msg->to);
        reqFromC->deq();
        delete msg;
        return true;
      } else {
        allocMshr(replaceIndex, Mshr(C, msg->c, msg->index, msg->to, true, msg->lineAddr));
        sendCsReq(replaceIndex, replaceLineAddr, 0);
        reqFromC->deq();
        delete msg;
        return true;
      }
    } else {
      Index index = cache->getIndex(msg->lineAddr);
      if(cache->cReq[index.set][index.way] || cache->pReq[index.set][index.way]) {
        latWait = tagLat;
        return true;
      }
      if(cache->st[index.set][index.way] >= msg->to && !isCHigher(index, compat(msg->to))) {
        sendCResp(index, msg->to, msg->c, msg->index, tagLat);
        reqFromC->deq();
        delete msg;
        return true;
      }
      if(!mshrFl->isAvail()) {
        latWait = tagLat;
        return true;
      }
      noPermMiss++;
      allocMshr(index, Mshr(C, msg->c, msg->index, msg->to, false, (LineAddr)0));
      if(cache->st[index.set][index.way] < msg->to) {
        sendPReq(index, msg->lineAddr, msg->to);
      }
      if(isCHigher(index, compat(msg->to))) {
        sendCsReq(index, msg->lineAddr, compat(msg->to));
      }
      reqFromC->deq();
      delete msg;
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
      latWait = tagLat;
      return true;
    } else {
      Index index = cache->getIndex(msg->lineAddr);
      if(cache->cReq[index.set][index.way]) {
        latWait = tagLat;
        return true;
      }
      if(!isCHigher(index, msg->to)) {
        if(cache->st[index.set][index.way] > msg->to) {
          sendPResp(index, msg->to, Forced, msg->index, 0, tagLat);
        }
        fromP->deq();
        delete msg;
        return true;
      }
      if(!mshrFl->isAvail()) {
        latWait = tagLat;
        return true;
      }
      allocMshr(index, Mshr(P, 0, msg->index, msg->to, false, (LineAddr)0));
      sendCsReq(index, msg->lineAddr, msg->to);
      fromP->deq();
      delete msg;
      return true;
    }
  }

public:
  internalCtrl(Fifo* _fromP, Fifo* _reqFromC, Fifo* _respFromC,
               Fifo* _reqToP, Fifo* _respToP, Fifo* _toCs,
               MshrPtr mshrs, Way ways, U8 _setSz, Child _childs,
               Latency _tagLat, Latency _dataLat) {
    setSz = _setSz;

    childs = _childs;
    cache = new Cache(ways, setSz, childs);
    mshrFl = new FreeList(mshrs);
    mshr = new Mshr[mshrs];

    tagLat = _tagLat;
    dataLat = _dataLat;

    fromP = _fromP; reqFromC = _reqFromC; respFromC = _respFromC;
    pReqF = _reqToP; pRespF = _respToP; toCsF = _toCs;

    pReq = new Fifo(1);
    pResp = new Fifo(1);
    toCs = new Fifo(1);

    latPReq = 0;
    latPResp = 0;
    latToCs = 0;
    latWait = 0;

    hit = 0;
    notPresentMiss = 0;
    noPermMiss = 0;

    priority = C;
  }
  ~internalCtrl() {
    delete cache;
    delete mshrFl;
    delete mshr;
    delete pReq;
    delete pResp;
    delete toCs;
  }

  void cycle() {
    if(latPReq != 0 || latPResp != 0 || latToCs != 0 || latWait != 0) {
      if(latPReq > 1)
        latPReq--;
      else if(!pReq->empty() && !pReqF->full()) {
        pReqF->enq(pReq->first());
        pReq->deq();
        latPReq = 0;
      }
      if(latPResp > 1)
        latPResp--;
      if(latToCs > 1)
        latToCs--;
      if(latWait != 0)
        latWait--;

      if(latPResp == 1 && !pResp->empty() && !pRespF->full()) {
        pRespF->enq(pResp->first());
        pResp->deq();
        latPResp = 0;
      }
      if(latToCs == 1 && !toCs->empty() && !toCsF->full()) {
        toCsF->enq(toCs->first());
        toCs->deq();
        latToCs = 0;
      }
      return;
    }
    if(handleCResp()) {}
    else if(handlePResp()) {}
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
