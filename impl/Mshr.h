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

