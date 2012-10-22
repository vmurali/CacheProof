#pragma once

#include "Types.h"

typedef U64 Counter;

typedef U8 St;
typedef U64 LineAddr;
typedef U64 Tag;
typedef U32 Set;
typedef U8 Way;
typedef U32 Child;
typedef U8 MshrPtr;

typedef struct {
  Set set;
  Way way;
} Index;

typedef class fromP {
public:
  bool isReq;
  Index index;
  LineAddr lineAddr;
  St from;
  St to;

  fromP(bool _isReq, Index _index, LineAddr _lineAddr, St _from, St _to) {
    isReq = _isReq; index = _index; lineAddr = _lineAddr; from = _from; to = _to;
  }
  ~fromP() {}
} FromP;

typedef class reqToP {
public:
  Index index;
  LineAddr lineAddr;
  St from;
  St to;

  reqToP(Index _index, LineAddr _lineAddr, St _from, St _to) {
    index = _index; lineAddr = _lineAddr; from = _from; to = _to;
  }
  ~reqToP() {}
} ReqToP;

typedef enum {Forced, Voluntary} Trigger;

typedef class respToP {
public:
  Trigger trigger;
  Index index;
  LineAddr lineAddr;
  St to;
  bool dirty;

  respToP(Trigger _trigger, Index _index, LineAddr _lineAddr, St _to, bool _dirty) {
    trigger = _trigger; index = _index; lineAddr = _lineAddr; to = _to; dirty = _dirty;
  }

  ~respToP() {}
} RespToP;

typedef U32 Latency;

typedef enum {P, C} Who;

typedef U32 ThreadId;

typedef class reqFromCore {
public:
  St to;
  LineAddr lineAddr;

  reqFromCore(St _to, LineAddr _lineAddr) {
    to = _to; lineAddr = _lineAddr;
  }
  ~reqFromCore() {}
} ReqFromCore;

