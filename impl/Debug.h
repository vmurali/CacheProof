#pragma once

#ifdef DEBUG
#define printSendRespToP(lineAddr, trigger, index, to)\
  printf("%p SendRespToP: %llx %c %d.%d %d->%d\n",\
         this, lineAddr, trigger == Forced? 'F': 'V', index.set, index.way, cache.st[index.set][index.way], to);

#define printSendRespToC(c, lineAddr, index, to)\
  printf("%p SendRespToC: %d %llx %d.%d %d->%d\n",\
         this, c, lineAddr, index.set, index.way, cache.cstates[index.set][index.way][c], to);

#define printSendReqToCs(cs, lineAddr, index, to){\
  printf("%p SendReqToCs: ", this);\
  for(Child i = 0; i < childs; i++) {\
    printf("%d %d ", cs[i], cache.cstates[index.set][index.way][i]);\
  }\
  printf("%llx %d.%d ->%d\n", lineAddr, index.set, index.way, to);\
}

#define printSendReqToP(lineAddr, index, to)\
  printf("%p SendReqToP: %llx %d.%d %d->%d\n",\
         this, lineAddr, index.set, index.way, cache.st[index.set][index.way], to);

#define printHandleRespFromC(c, lineAddr, trigger, index, to)\
  printf("%p  HandleRespFromC: %d %llx %c %d.%d %d\n",\
         this, c, lineAddr, trigger == Forced? 'F': 'V', index.set, index.way, to);

#define printHandleRespFromP(lineAddr, index, to)\
  printf("%p  HandleRespFromP: %llx %d.%d %d\n",\
         this, lineAddr, index.set, index.way, to);

#define printHandleReqFromC(c, lineAddr, to)\
  printf("%p  HandleReqFromC: %d %llx %d\n",\
         this, c, lineAddr, to);

#define printHandleReqFromP(lineAddr, to)\
  printf("%p  HandleReqFromP: %llx %d\n",\
         this, lineAddr, to);

#define printHandleReqFromCore(lineAddr, to)\
  printf("%p  HandleReqFromCore: %llx %d\n",\
         this, lineAddr, to);

#define printCycle printf("\nCYCLE %lld\n", cycCount);

#else
#define printSendRespToP(lineAddr, trigger, index, to)
#define printSendRespToC(c, lineAddr, index, to)
#define printSendReqToP(lineAddr, index, to)
#define printSendReqToCs(cs, lineAddr, index, to)
#define printHandleRespFromC(c, lineAddr, trigger, index, to)
#define printHandleRespFromP(lineAddr, index, to)
#define printHandleReqFromC(c, lineAddr, to)
#define printHandleReqFromP(lineAddr, to)
#define printHandleReqFromCore(lineAddr, to)
#define printCycle
#endif
