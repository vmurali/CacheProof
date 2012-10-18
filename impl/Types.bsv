import Vector::*;
typedef 6 LineSz;
typedef 64 AddrSz;
typedef TSub#(AddrSz, LineSz) RemainSz;
typedef Bit#(RemainSz) LineAddr;
typedef Bit#(AddrSz) Addr;
typedef Bit#(10) Child;
typedef Bit#(11) ChildCount;

typedef Bit#(64) Counter;

typedef Bit#(15) IndexSets;
typedef Bit#(6) IndexWays;
typedef struct {
  IndexSets set;
  IndexWays way;
} Index deriving (Bits, Eq);

typedef Bit#(2) St;

typedef struct {
  Bool isReq;
  Index index;
  LineAddr lineAddr;
  St from;
  St to;
} FromParent deriving (Bits, Eq);

typedef struct {
  Vector#(childs, Bool) children;
  Bool isReq;
  Index index;
  LineAddr lineAddr;
  Vector#(childs, St) from;
  St to;
} ToChildren#(type childs) deriving (Bits, Eq);

typedef struct {
  Child c;
  Index index;
  LineAddr lineAddr;
  St from;
  St to;
} ReqFromChild deriving (Bits, Eq);

typedef struct {
  Index index;
  LineAddr lineAddr;
  St from;
  St to;
} ReqToParent deriving (Bits, Eq);

typedef union tagged {
  Index Forced;
  LineAddr Voluntary;
} Trigger deriving (Bits, Eq);

typedef struct {
  Child c;
  Trigger trigger;
  St to;
  Bool dirty;
} RespFromChild deriving (Bits, Eq);

typedef struct {
  Trigger trigger;
  St to;
  Bool dirty;
} RespToParent deriving (Bits, Eq);

typedef struct {
  St to;
  LineAddr lineAddr;
} ReqFromCore deriving (Bits, Eq);

typedef Bit#(20) Latency;
