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

