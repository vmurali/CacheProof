#pragma once

#include <cassert>

#ifdef Debug
#define printSendRespToP(lineAddr, trigger, index, to)\
  printf("%p SendRespToP: %llx %c %d.%d %d->%d\n",\
         this, lineAddr, trigger == Forced? 'F': 'V', index.set, index.way, cache.st[index.set][index.way], to)

#define printSendRespToC(c, lineAddr, index, to)\
  printf("%p SendRespToC: %d %llx %d.%d %d->%d\n",\
         this, c, lineAddr, index.set, index.way, cache.cstates[index.set][index.way][c], to)

#define printSendReqToCs(cs, lineAddr, index, to){\
  printf("%p SendReqToCs: ", this);\
  for(Child i = 0; i < childs; i++) {\
    printf("%d %d ", cs[i], cache.cstates[index.set][index.way][i]);\
  }\
  printf("%llx %d.%d ->%d\n", lineAddr, index.set, index.way, to);\
}

#define printSendReqToP(lineAddr, index, to)\
  printf("%p SendReqToP: %llx %d.%d %d->%d\n",\
         this, lineAddr, index.set, index.way, cache.st[index.set][index.way], to)

#define printMemorySendResp(lineAddr, cIndex)\
  printf("%p MemorySendResp: %llx %d.%x\n",\
         this, lineAddr, cIndex.set, cIndex.way);

#define printHandleRespFromC(c, lineAddr, trigger, index, to)\
  printf("%p HandleRespFromC: %d %llx %c %d.%d %d\n",\
         this, c, lineAddr, trigger == Forced? 'F': 'V', index.set, index.way, to)

#define printHandleRespFromP(lineAddr, index, to)\
  printf("%p HandleRespFromP: %llx %d.%d %d\n",\
         this, lineAddr, index.set, index.way, to)

#define printHandleReqFromC(c, lineAddr, to, present)\
  printf("%p HandleReqFromC: %d %llx %d %d\n",\
         this, c, lineAddr, to, present)

#define printHandleReqFromP(lineAddr, to, present)\
  printf("%p HandleReqFromP: %llx %d %d\n",\
         this, lineAddr, to, present)

#define printHandleReqFromCore(lineAddr, to)\
  printf("%p HandleReqFromCore: %llx %d\n",\
         this, lineAddr, to)

#define printCycle printf("\nCYCLE %lld\n", cycCount)

#define Assert(c) assert(c)

#else
#define printSendRespToP(lineAddr, trigger, index, to)
#define printSendRespToC(c, lineAddr, index, to)
#define printSendReqToP(lineAddr, index, to)
#define printSendReqToCs(cs, lineAddr, index, to)
#define printMemorySendResp(lineAddr, cIndex)
#define printHandleRespFromC(c, lineAddr, trigger, index, to)
#define printHandleRespFromP(lineAddr, index, to)
#define printHandleReqFromC(c, lineAddr, to, present)
#define printHandleReqFromP(lineAddr, to, present)
#define printHandleReqFromCore(lineAddr, to)
#define printCycle
#define Assert(c)
#endif
