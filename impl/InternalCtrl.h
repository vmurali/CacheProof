#pragma once

#include "Cache.h"
#include "Fifo.h"
#include "FreeList.h"

typedef struct {
  bool isReq;
  Index index;
  LineAddr lineAddr;
  St from;
  St to;
} FromP;

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
  Fifo* fromP,* reqFromC,* respFromC,* reqToP,* respToP,* toCs;
  Child childs;
  Cache* cache;
  FreeList* mshrFl;
  MshrPtr* mshr;
  Latency tagLat;
  Latency dataLat;

public:
  internalCtrl(Fifo* _fromP, Fifo* _reqFromC, Fifo* _respFromC,
               Fifo* _reqToP, Fifo* _respToP, Fifo* _toCs,
               MshrPtr mshrs, Way ways, U8 setSz, Child _childs,
               Latency _tagLat, Latency _dataLat) {
    childs = _childs;
    cache = new Cache(ways, setSz, childs);
    mshrFl = new FreeList(mshrs);
    mshr = new MshrPtr[mshrs];

    tagLat = _tagLat;
    dataLat = _dataLat;

    fromP = _fromP; reqFromC = _reqFromC; respFromC = _respFromC;
    reqToP = _reqToP; respToP = _respToP; toCs = _toCs;
  }
  ~internalCtrl() {
    delete cache;
    delete mshrFl;
    delete mshr;
  }

  void cycle() {

  }
} InternalCtrl;
