#pragma once

#include "Cache.h"
#include "Fifo.h"
#include "FreeList.h"

typedef U64 Counter;

typedef struct {
  bool isReq;
  Index index;
  LineAddr lineAddr;
  St from;
  St to;
} FromP;

typedef enum {P, C} Who;

typedef struct {
  Who who;
  Child c;
  Index index;
  St to;
  bool isReplacing;
  LineAddr lineAddr;
} Mshr;

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

typedef struct {
  Child c;
  Index index;
  LineAddr lineAddr;
  St from;
  St to;
} ReqFromC;

typedef struct {
  Index index;
  LineAddr lineAddr;
  St from;
  St to;
} ReqToP;

typedef enum {Forced, Voluntary} Trigger;

typedef struct {
  Child c;
  Trigger trigger;
  Index index;
  LineAddr lineAddr;
  St to;
  bool dirty;
} RespFromC;

typedef struct {
  Trigger trigger;
  Index index;
  LineAddr lineAddr;
  St to;
  bool dirty;
} RespToP;

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

  Counter hit;
  Counter notPresentMiss;
  Counter noPermMiss;

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

  bool handleCResp() {
    if(respFromC->empty())
      return false;
    RespFromC* msg = (RespFromC*) respFromC->first();
    respFromC->deq();
    Index index = msg->trigger == Forced? msg->index: cache->getIndex(msg->lineAddr);
    cache->cstates[index.set][index.way][msg->c] = msg->to;
    if(cache->cReq[index.set][index.way]) {
      MshrPtr mshrPtr = cache->mshrPtr[index.set][index.way];
      Mshr m = mshr[mshrPtr];
      St to = m.who == P? m.to: compat(m.to);
      if(!isCHigher(index, to)) {
        cache->cReq[index.set][index.way] = false;
        if(m.who == P) {
          RespToP* resp = new RespToP();
          resp->trigger = Forced; resp->index = m.index; resp->lineAddr = 0;
          resp->to = m.to; resp->dirty = cache->dirty[index.set][index.way];
          pResp->enq((void*)resp);
          latPResp = msg->trigger == Forced? 1 : tagLat;
        }
        else if(!cache->pReq[index.set][index.way]) {
          St from = cache->cstates[index.set][index.way][m.c];
          ToCs* resp = new ToCs(childs, m.c, false, m.index, 0, from, m.to);
          toCs->enq((void*)resp);
          latToCs = msg->trigger == Forced? 1 : tagLat;
          cache->replaceUpd(index);
        }
      }
    }
    delete msg;
    return true;
  }

  bool handlePResp() {
    if(fromP->empty())
      return false;
    FromP* msg = (FromP*) fromP->first();
    if(msg->isReq)
       return false;
    fromP->deq();
    Index index = msg->index;
    MshrPtr mshrPtr = cache->mshrPtr[index.set][index.way];
    cache->st[index.set][index.way] = msg->to;
    cache->pReq[index.set][index.way] = false;
    if(!cache->cReq[index.set][index.way]) {
      Mshr m = mshr[mshrPtr];
      mshrFl->free(mshrPtr);
      St from = cache->cstates[index.set][index.way][m.c];
      ToCs* resp = new ToCs(childs, m.c, false, m.index, 0, from, m.to);
      toCs->enq((void*)resp);
      latToCs = from == 0? dataLat: 1;
    }
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
      }
      MshrPtr mshrPtr = mshrFl->alloc();
      Index replaceIndex = cache->getReplace(msg->lineAddr);
      cache->mshrPtr[replaceIndex.set][replaceIndex.way] = mshrPtr;
      reqFromC->deq();
      if(!isCHigher(replaceIndex, 0)) {
        if(cache->st[replaceIndex.set][replaceIndex.way] > 0) {
          RespToP* vol = new RespToP;
          LineAddr lineAddr = (cache->tag[replaceIndex.set][replaceIndex.way] << setSz)
                                | replaceIndex.set;
          vol->trigger = Voluntary; vol->lineAddr = lineAddr; vol->to = 0;
          vol->dirty = cache->dirty[replaceIndex.set][replaceIndex.way];
          cache->replaceRem(replaceIndex);
          pResp->enq((void*) vol);
          latPResp = vol->dirty? dataLat: tagLat;
        }
        cache->tag[replaceIndex.set][replaceIndex.way] = (msg->lineAddr) >> setSz;
        cache->st[replaceIndex.set][replaceIndex.way] = 0;
        for(Child i = 0; i < childs; i++)
          cache->cstates[replaceIndex.set][replaceIndex.way][i] = 0;
        cache->dirty[replaceIndex.set][replaceIndex.way] = false;
        mshr[mshrPtr].who = C; mshr[mshrPtr].c = msg->c; mshr[mshrPtr].index = msg->index;
        mshr[mshrPtr].to = msg->to; mshr[mshrPtr].isReplacing = false;
        ReqToP* req = new ReqToP;
        req->index = replaceIndex; req->lineAddr = msg->lineAddr; req->from = 0; req->to = msg->to;
        pReq->enq((void*)req);
        latPReq = tagLat;
      } else {
        mshr[mshrPtr].who = C; mshr[mshrPtr].c = msg->c; mshr[mshrPtr].index = msg->index;
        mshr[mshrPtr].to = msg->to; mshr[mshrPtr].isReplacing = true; mshr[mshrPtr].lineAddr = msg->lineAddr;
        bool* highChildren = new bool[childs];
        for(Child i = 0; i < childs; i++)
           highChildren[i] = cache->cstates[replaceIndex.set][replaceIndex.way][i] > 0;
        ToCs* req = new ToCs(childs, highChildren, true, replaceIndex, 0, NULL, 0);
        toCs->enq((void*)req);
        latToCs = tagLat;
      }
    } else {
      Index index = cache->getIndex(msg->lineAddr);
      if(cache->cReq[index.set][index.way] || cache->pReq[index.set][index.way]) {
        latWait = tagLat;
      }
      if(cache->st[index.set][index.way] >= msg->to && !isCHigher(index, compat(msg->to))) {
        St oldSt = cache->cstates[index.set][index.way][msg->c];
        ToCs* resp = new ToCs(childs, msg->c, false, msg->index, msg->lineAddr, oldSt, msg->to);
        toCs->enq((void*)resp);
        latToCs = oldSt == 0? dataLat: tagLat;
      }
      if(!mshrFl->isAvail()) {
        latWait = tagLat;
      }
      MshrPtr mshrPtr = mshrFl->alloc();
      mshr[mshrPtr].who = C; mshr[mshrPtr].c = msg->c; mshr[mshrPtr].index = msg->index;
      mshr[mshrPtr].to = msg->to; mshr[mshrPtr].isReplacing = false;
      if(cache->st[index.set][index.way] < msg->to) {
        cache->pReq[index.set][index.way] = true;
        cache->waitS[index.set][index.way] = msg->to;
        ReqToP* req = new ReqToP;
        req->index = index; req->lineAddr = msg->lineAddr;
        req->from = cache->st[index.set][index.way]; req->to = msg->to;
        pReq->enq((void*)req);
        latPReq = tagLat;
      }
      if(isCHigher(index, compat(msg->to))) {
        cache->cReq[index.set][index.way] = true;
        cache->waitCs[index.set][index.way] = compat(msg->to);
        bool* highChildren = new bool[childs];
        for(Child i = 0; i < childs; i++)
           highChildren[i] = cache->cstates[index.set][index.way][i] > compat(msg->to);
        ToCs* req = new ToCs(childs, highChildren, true, index, 0, NULL, compat(msg->to));
        toCs->enq((void*)req);
        latToCs = tagLat;
      }
    }
    delete msg;
    return true;
  }

  bool handlePReq() {
    if(fromP->empty())
      return false;
    FromP* msg = (FromP*) fromP->first();
    if(!msg->isReq)
       return false;
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
  }
} InternalCtrl;
