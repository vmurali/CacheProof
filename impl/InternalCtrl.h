#pragma once

#include "Cache.h"
#include "Fifo.h"
#include "FreeList.h"
#include "CacheTypes.h"

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

typedef class internalCtrl {
private:
  U8 setSz;
  Child childs;
  Cache cache;
  FreeList mshrFl;
  Latency tagLat;
  Latency dataLat;
  Latency latPReq, latPResp, latToCs, latWait;
  Who priority;

  Fifo fromP, reqToPF, respToPF;
  Fifo reqFromC, respFromC, toCsF;

  Fifo reqToP, respToP, toCs;

  Mshr* mshr;

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
      if(cache.cstates[index.set][index.way][i] > to)
        _isCHigher = true;
    return _isCHigher;
  }

  void sendRespToP(Index& index, St to, Trigger trigger, Index& pIndex, LineAddr lineAddr, Latency lat) {
    cache.st[index.set][index.way] = to;
    RespToP* resp = new RespToP(trigger, pIndex, lineAddr, to, cache.dirty[index.set][index.way]);
    respToP.enq(resp);
    latPResp = cache.dirty[index.set][index.way]? dataLat : lat;
    if(to == 0)
      cache.replaceRem(index);
  }

  void sendRespToC(Index& index, St to, Child c, Index& cIndex, Latency lat) {
    ToCs* resp = new ToCs(childs, c, false, cIndex, 0, cache.cstates[index.set][index.way][c], to);
    latToCs = cache.cstates[index.set][index.way][c] == 0? dataLat: lat;
    cache.cstates[index.set][index.way][c] = to;
    toCs.enq(resp);
    cache.replaceUpd(index);
  }

  void sendReqToCs(Index& index, LineAddr lineAddr, St to) {
    cache.cReq[index.set][index.way] = true;
    cache.waitCs[index.set][index.way] = to;
    bool* highChildren = new bool[childs];
    for(Child i = 0; i < childs; i++)
       highChildren[i] = cache.cstates[index.set][index.way][i] > to;
    ToCs* req = new ToCs(childs, highChildren, true, index, lineAddr, NULL, to);
    toCs.enq(req);
    latToCs = tagLat;
  }

  void sendReqToP(Index& index, LineAddr lineAddr, St to) {
    cache.pReq[index.set][index.way] = true;
    cache.waitS[index.set][index.way] = to;
    ReqToP* req = new ReqToP(index, lineAddr, cache.st[index.set][index.way], to);
    reqToP.enq(req);
    latPReq = tagLat;
  }

  void allocMshr(Index& index, Mshr entry) {
    MshrPtr mshrPtr = mshrFl.alloc();
    cache.mshrPtr[index.set][index.way] = mshrPtr;
    mshr[mshrPtr] = entry;
  }

  void resetLine(Index& index, LineAddr lineAddr) {
    cache.pReq[index.set][index.way] = false;
    cache.cReq[index.set][index.way] = false;
    cache.tag[index.set][index.way] = lineAddr >> setSz;
    cache.st[index.set][index.way] = 0;
    for(Child i = 0; i < childs; i++)
      cache.cstates[index.set][index.way][i] = 0;
    cache.dirty[index.set][index.way] = false;
  }

  bool handleRespFromC() {
    if(respFromC.empty())
      return false;
    RespFromC* msg = (RespFromC*) respFromC.first();
    Index index = msg->trigger == Forced? msg->index: cache.getIndex(msg->lineAddr);
    cache.cstates[index.set][index.way][msg->c] = msg->to;
    if(cache.cReq[index.set][index.way]) {
      MshrPtr mshrPtr = cache.mshrPtr[index.set][index.way];
      Mshr m = mshr[mshrPtr];
      St to = m.who == P? m.to: compat(m.to);
      if(!isCHigher(index, to)) {
        cache.cReq[index.set][index.way] = false;
        if(m.who == P)
          sendRespToP(index, m.to, Forced, m.index, 0, msg->trigger == Forced? 1: tagLat);
        else if(!cache.pReq[index.set][index.way])
          sendRespToC(index, m.to, m.c, m.index, msg->trigger == Forced? 1: tagLat);
      }
    }
    respFromC.deq();
    delete msg;
    return true;
  }

  bool handleRespFromP() {
    if(fromP.empty())
      return false;
    FromP* msg = (FromP*) fromP.first();
    if(msg->isReq)
       return false;
    Index index = msg->index;
    MshrPtr mshrPtr = cache.mshrPtr[index.set][index.way];
    cache.st[index.set][index.way] = msg->to;
    cache.pReq[index.set][index.way] = false;
    if(!cache.cReq[index.set][index.way]) {
      Mshr m = mshr[mshrPtr];
      sendRespToC(index, m.to, m.c, m.index, 1);
      mshrFl.free(mshrPtr);
    }
    fromP.deq();
    delete msg;
    return true;
  }

  bool handleReqFromC() {
    if(reqFromC.empty())
      return false;
    ReqFromC* msg = (ReqFromC*) reqFromC.first();
    bool present = cache.isPresent(msg->lineAddr);
    if(!present) {
      if(!mshrFl.isAvail() || !cache.existsReplace(msg->lineAddr)) {
        latWait = tagLat;
        return true;
      }
      notPresentMiss++;
      Index replaceIndex = cache.getReplace(msg->lineAddr);
      LineAddr replaceLineAddr = (cache.tag[replaceIndex.set][replaceIndex.way] << setSz)
                            | replaceIndex.set;
      if(!isCHigher(replaceIndex, 0)) {
        if(cache.st[replaceIndex.set][replaceIndex.way] > 0) {
          sendRespToP(replaceIndex, (St)0, Voluntary, replaceIndex, replaceLineAddr, tagLat);
        }
        resetLine(replaceIndex, msg->lineAddr);
        allocMshr(replaceIndex, Mshr(C, msg->c, msg->index, msg->to, false, (LineAddr)0));
        sendReqToP(replaceIndex, msg->lineAddr, msg->to);
        reqFromC.deq();
        delete msg;
        return true;
      } else {
        allocMshr(replaceIndex, Mshr(C, msg->c, msg->index, msg->to, true, msg->lineAddr));
        sendReqToCs(replaceIndex, replaceLineAddr, 0);
        reqFromC.deq();
        delete msg;
        return true;
      }
    } else {
      Index index = cache.getIndex(msg->lineAddr);
      if(cache.cReq[index.set][index.way] || cache.pReq[index.set][index.way]) {
        latWait = tagLat;
        return true;
      }
      if(cache.st[index.set][index.way] >= msg->to && !isCHigher(index, compat(msg->to))) {
        sendRespToC(index, msg->to, msg->c, msg->index, tagLat);
        reqFromC.deq();
        delete msg;
        return true;
      }
      if(!mshrFl.isAvail()) {
        latWait = tagLat;
        return true;
      }
      noPermMiss++;
      allocMshr(index, Mshr(C, msg->c, msg->index, msg->to, false, (LineAddr)0));
      if(cache.st[index.set][index.way] < msg->to) {
        sendReqToP(index, msg->lineAddr, msg->to);
      }
      if(isCHigher(index, compat(msg->to))) {
        sendReqToCs(index, msg->lineAddr, compat(msg->to));
      }
      reqFromC.deq();
      delete msg;
      return true;
    }
  }

  bool handleReqFromP() {
    if(fromP.empty())
      return false;
    FromP* msg = (FromP*) fromP.first();
    if(!msg->isReq)
       return false;
    bool present = cache.isPresent(msg->lineAddr);
    if(!present) {
      latWait = tagLat;
      fromP.deq();
      delete msg;
      return true;
    } else {
      Index index = cache.getIndex(msg->lineAddr);
      if(cache.cReq[index.set][index.way]) {
        latWait = tagLat;
        return true;
      }
      if(!isCHigher(index, msg->to)) {
        if(cache.st[index.set][index.way] > msg->to) {
          sendRespToP(index, msg->to, Forced, msg->index, 0, tagLat);
        }
        fromP.deq();
        delete msg;
        return true;
      }
      if(!mshrFl.isAvail()) {
        latWait = tagLat;
        return true;
      }
      allocMshr(index, Mshr(P, 0, msg->index, msg->to, false, (LineAddr)0));
      sendReqToCs(index, msg->lineAddr, msg->to);
      fromP.deq();
      delete msg;
      return true;
    }
  }

public:
  Counter hit, notPresentMiss, noPermMiss;
  
  internalCtrl(MshrPtr mshrs, Way ways, U8 _setSz, Child _childs,
               Latency _tagLat, Latency _dataLat) :
          setSz(_setSz), childs(_childs), cache(ways, setSz, childs), mshrFl(mshrs),
          tagLat(_tagLat), dataLat(_dataLat), latPReq(0), latPResp(0), latToCs(0),
          latWait(0), priority(C),
          fromP(2), reqFromC(2), respFromC(2),
          reqToPF(1), respToPF(1), toCsF(1),
          reqToP(1), respToP(1), toCs(1),
          hit(0), notPresentMiss(0), noPermMiss(0)
  {
    mshr = new Mshr[mshrs];
  }
  ~internalCtrl() {
    delete[] mshr;
  }

  void cycle() {
    if(latPReq != 0 || latPResp != 0 || latToCs != 0 || latWait != 0) {
      if(latPReq > 1)
        latPReq--;
      else if(latPReq == 1 && !reqToP.empty() && !reqToPF.full()) {
        reqToPF.enq(reqToP.first());
        reqToP.deq();
        latPReq = 0;
      }
      if(latPResp > 1)
        latPResp--;
      else if(latPResp == 1 && !respToP.empty() && !respToPF.full()) {
        respToPF.enq(respToP.first());
        respToP.deq();
        latPResp = 0;
      }
      if(latToCs > 1)
        latToCs--;
      else if(latToCs == 1 && !toCs.empty() && !toCsF.full()) {
        toCsF.enq(toCs.first());
        toCs.deq();
        latToCs = 0;
      }
      if(latWait != 0)
        latWait--;
    } else {
      if(handleRespFromC()) {}
      else if(handleRespFromP()) {}
      else if(priority == P) {
        if(handleReqFromP()) {
          priority = C;
        }
        else handleReqFromC();
      }
      else {
        if(handleReqFromC()) {
          priority = P;
        }
        else handleReqFromP();
      }
    }

    fromP.cycle();
    reqFromC.cycle();
    respFromC.cycle();
    reqToPF.cycle();
    respToPF.cycle();
    toCsF.cycle();

    reqToP.cycle();
    respToP.cycle();
    toCs.cycle();
  }

  Fifo* getFromP() { return &fromP; }
  Fifo* getReqFromC() { return &reqFromC; }
  Fifo* getRespFromC() { return &respFromC; }
  Fifo* getReqToP() { return &respToPF; }
  Fifo* getRespToP() { return &respToPF; }
  Fifo* getToCs() { return &toCsF; }

} InternalCtrl;
