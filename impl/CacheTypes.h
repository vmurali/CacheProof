#pragma once

typedef U64 Counter;

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

