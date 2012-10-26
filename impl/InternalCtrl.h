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
  bool isPrev;
  MshrPtr prevMshr;

  mshr() {}
  mshr(Who _who, Child _c, Index _index, St _to,
       bool _isReplacing, LineAddr _lineAddr, bool _isPrev, MshrPtr _prevMshr) :
       who(_who), c(_c), index(_index), to(_to), isReplacing(_isReplacing),
       lineAddr(_lineAddr), isPrev(_isPrev), prevMshr(_prevMshr) {}
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

  bool isCompat(Child c, Index index, St to) {
    bool comp = true;
    for(Child i = 0; i < childs; i++)
      if(i != c && cache.cstates[index.set][index.way][i] > compat(to))
        comp = false;
    return comp;
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

  void sendRespToC(Index& index, St to, Child c, Index& cIndex, LineAddr lineAddr, Latency lat) {
    ToCs* resp = new ToCs(childs, c, false, cIndex, lineAddr, cache.cstates[index.set][index.way][c], to);
    latToCs = cache.cstates[index.set][index.way][c] == 0? dataLat: lat;
    cache.cstates[index.set][index.way][c] = to;
    toCs.enq(resp);
    cache.replaceUpd(index);
  }

  void sendReqToCs(Index& index, LineAddr lineAddr, St to, bool skip, Child skipChild) {
    cache.cReq[index.set][index.way] = true;
    cache.waitCs[index.set][index.way] = to;
    bool* highChildren = new bool[childs];
    for(Child i = 0; i < childs; i++)
       highChildren[i] = (!skip || i != skipChild) && cache.cstates[index.set][index.way][i] > to;
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
    assert(cache.isPresent(msg->lineAddr));
    cache.cstates[index.set][index.way][msg->c] = msg->to;
    cache.dirty[index.set][index.way] = msg->dirty;
    if(cache.cReq[index.set][index.way]) {
      MshrPtr mshrPtr = cache.mshrPtr[index.set][index.way];
      Mshr m = mshr[mshrPtr];
      if(m.who == P) {
        if(!isCHigher(index, m.to)) {
          cache.cReq[index.set][index.way] = false;
          sendRespToP(index, m.to, Forced, m.index, msg->lineAddr, msg->trigger == Forced? 1: tagLat);
          if(m.isPrev)
            cache.mshrPtr[index.set][index.way] = m.prevMshr;
          mshrFl.free(mshrPtr);
        }
      } else if(m.isReplacing) {
        if(!isCHigher(index, 0)) {
          cache.cReq[index.set][index.way] = false;
          sendRespToP(index, (St)0, Voluntary, index, msg->lineAddr, msg->trigger == Forced? (Latency)1: tagLat);
          resetLine(index, m.lineAddr);
          sendReqToP(index, m.lineAddr, m.to);
          m.isReplacing = false;
          mshr[mshrPtr] = m;
        }
      } else {
        if(isCompat(m.c, index, m.to)) {
          cache.cReq[index.set][index.way] = false;
          if(!cache.pReq[index.set][index.way]) {
            sendRespToC(index, m.to, m.c, m.index, m.lineAddr, msg->trigger == Forced? 1: tagLat);
            mshrFl.free(mshrPtr);
          }
        }
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
      sendRespToC(index, m.to, m.c, m.index, msg->lineAddr, 1);
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
        allocMshr(replaceIndex, Mshr(C, msg->c, msg->index, msg->to, false, msg->lineAddr, false, (MshrPtr)0));
        sendReqToP(replaceIndex, msg->lineAddr, msg->to);
        reqFromC.deq();
        delete msg;
        return true;
      } else {
        allocMshr(replaceIndex, Mshr(C, msg->c, msg->index, msg->to, true, msg->lineAddr, false, (MshrPtr)0));
        sendReqToCs(replaceIndex, replaceLineAddr, 0, false, 0);
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
      if(cache.st[index.set][index.way] >= msg->to && isCompat(msg->c, index, msg->to)) {
        sendRespToC(index, msg->to, msg->c, msg->index, msg->lineAddr, tagLat);
        hit++;
        reqFromC.deq();
        delete msg;
        return true;
      }
      if(!mshrFl.isAvail()) {
        latWait = tagLat;
        return true;
      }
      if(cache.st[index.set][index.way] == 0)
        inclusiveMiss++;
      else
        noPermMiss++;
      allocMshr(index, Mshr(C, msg->c, msg->index, msg->to, false, (LineAddr)0, false, (MshrPtr)0));
      if(cache.st[index.set][index.way] < msg->to) {
        sendReqToP(index, msg->lineAddr, msg->to);
      }
      if(!isCompat(msg->c, index, msg->to)) {
        sendReqToCs(index, msg->lineAddr, compat(msg->to), true, msg->c);
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
          sendRespToP(index, msg->to, Forced, msg->index, msg->lineAddr, tagLat);
        }
        fromP.deq();
        delete msg;
        return true;
      }
      if(!mshrFl.isAvail()) {
        latWait = tagLat;
        return true;
      }
      allocMshr(index, Mshr(P, 0, msg->index, msg->to, false, msg->lineAddr, cache.pReq[index.set][index.way], cache.mshrPtr[index.set][index.way]));
      sendReqToCs(index, msg->lineAddr, msg->to, false, 0);
      fromP.deq();
      delete msg;
      return true;
    }
  }

public:
  Counter hit, notPresentMiss, noPermMiss, inclusiveMiss;
  
  internalCtrl(MshrPtr mshrs, Way ways, U8 _setSz, Child _childs,
               Latency _tagLat, Latency _dataLat) :
          setSz(_setSz), childs(_childs), cache(ways, setSz, childs), mshrFl(mshrs),
          tagLat(_tagLat), dataLat(_dataLat), latPReq(0), latPResp(0), latToCs(0),
          latWait(0), priority(C),
          fromP(2), reqFromC(2), respFromC(2),
          reqToPF(2), respToPF(2), toCsF(2),
          reqToP(1), respToP(1), toCs(1),
          hit(0), notPresentMiss(0), noPermMiss(0), inclusiveMiss(0)
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
  }

  void transfer() {
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
  Fifo* getReqToP() { return &reqToPF; }
  Fifo* getRespToP() { return &respToPF; }
  Fifo* getToCs() { return &toCsF; }

} InternalCtrl;
