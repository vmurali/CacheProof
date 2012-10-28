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

typedef enum {Req, Resp, FwdReq, FwdResp, PAck} FromPType;

typedef class fromP {
public:
  FromPType type;
  Index index;
  LineAddr lineAddr;
  St from;
  St to;

  Child fwdC;
  St fwdTo;

  fromP(FromPType _type, Index _index, LineAddr _lineAddr, St _from, St _to,
        Child _fwdC, St _fwdTo): type(_type), index(_index), lineAddr(_lineAddr),
        from(_from), to(_to), fwdC(_fwdC), fwdTo(_fwdTo) {}
  ~fromP() {}
} FromP;

typedef class reqToP {
public:
  Index index;
  LineAddr lineAddr;
  St from;
  St to;

  reqToP(Index _index, LineAddr _lineAddr, St _from, St _to):
         index(_index), lineAddr(_lineAddr), from(_from), to(_to) {}
  ~reqToP() {}
} ReqToP;

typedef enum {Forced, Voluntary, CAck} Trigger;

typedef class respToP {
public:
  Trigger trigger;
  Index index;
  LineAddr lineAddr;
  St to;
  bool dirty;
  bool fwd;
  Child c;

  respToP(Trigger _trigger, Index _index, LineAddr _lineAddr, St _to, bool _dirty, bool _fwd, Child _c):
          trigger(_trigger), index(_index), lineAddr(_lineAddr), to(_to), dirty(_dirty), fwd(_fwd), c(_c) {}
  ~respToP() {}
} RespToP;

typedef class toCs {
public:
  Child childs;
  bool* children;
  FromPType type;
  Index index;
  LineAddr lineAddr;
  St* from;
  St to;
  Child fwdC;
  St fwdTo;

  toCs(Child _childs, bool* _children, FromPType _type, Index _index,
       LineAddr _lineAddr, St* _from, St _to, Child _fwdC, St _fwdTo):
       childs(_childs), children(_children), type(_type), index(_index),
       lineAddr(_lineAddr), from(_from), to(_to), fwdC(_fwdC), fwdTo(_fwdTo) {}
  toCs(Child _childs, Child c, FromPType _type, Index _index,
       LineAddr _lineAddr, St _from, St _to, Child _fwdC, St _fwdTo):
       childs(_childs), type(_type), index(_index), lineAddr(_lineAddr),
       to(_to), fwdC(_fwdC), fwdTo(_fwdTo) {
    children = new bool[childs];
    for(Child i = 0; i < childs; i++)
      children[i] = false;
    children[c] = true;
    from = new St[childs];
    from[c] = _from;
  }
  ~toCs() {
    delete[] children;
    delete[] from;
  }
} ToCs;

typedef class reqFromC {
public:
  Child c;
  Index index;
  LineAddr lineAddr;
  St from;
  St to;

  reqFromC(Child _c, Index _index, LineAddr _lineAddr, St _from, St _to):
           c(_c), index(_index), lineAddr(_lineAddr), from(_from), to(_to) {}
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

  respFromC(Child _c, Trigger _trigger, Index _index, LineAddr _lineAddr, St _to, bool _dirty):
            c(_c), trigger(_trigger), index(_index), lineAddr(_lineAddr), to(_to), dirty(_dirty) {}

  ~respFromC() {}
} RespFromC;

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

FromP* toCs2fromP(ToCs* toCs, Child c) {
  St from = toCs->from == NULL? 0: toCs->from[c];
  FromP* ret = new FromP(toCs->type, toCs->index, toCs->lineAddr, from, toCs->to, toCs->fwdC, toCs->fwdTo);
  return ret;
}

ReqFromC* reqToP2reqFromC(ReqToP* reqToP, Child c) {
  ReqFromC* ret = new ReqFromC(c, reqToP->index, reqToP->lineAddr, reqToP->from, reqToP->to);
  return ret;
}

RespFromC* respToP2respFromC(RespToP* respToP, Child c) {
  RespFromC* ret = new RespFromC(respToP->fwd? respToP->c: c, respToP->trigger,
                                 respToP->index, respToP->lineAddr, respToP->to, respToP->dirty);
  return ret;
}
