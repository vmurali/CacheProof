#pragma once

#include "Fifo.h"
#include "L1Normal.h"
#include "InternalCtrl.h"
#include "Memory.h"
#include "InstFeeder.h"
#include "DataFeeder.h"
#include "Connect.h"

typedef class systemNormal {
private:
  ThreadId cores;
  U8 levels;
  Child* childs;
  ThreadId* numCtrls;
  InstFeeder** iFeeds;
  DataFeeder** dFeeds;
  L1Normal** l1s;
  InternalCtrl*** ctrls;
  Connect*** connects;
  Memory* mem;
public:
  systemNormal(ThreadId _cores, U8 _levels, Child* _childs,
               MshrPtr* mshrs, Way* ways, U8* setSzs,
               Latency* tagLats, Latency* dataLats, Latency memLat):
               cores(_cores), levels(_levels), childs(_childs) {
    l1s = new L1Normal*[2*cores];
    for(ThreadId i = 0; i < 2*cores; i++)
      l1s[i] = new L1Normal(ways[0], setSzs[0]);
    iFeeds = new InstFeeder*[cores];
    dFeeds = new DataFeeder*[cores];
    for(ThreadId i = 0; i < cores; i++) {
      iFeeds[i] = new InstFeeder(i, l1s[2*i]->getReqFromCore());
      dFeeds[i] = new DataFeeder(i, l1s[2*i+1]->getReqFromCore());
    }
    numCtrls = new ThreadId[levels];
    ctrls = new InternalCtrl**[levels];
    connects = new Connect**[levels];

    for(U8 i = 0; i < levels; i++) {
      numCtrls[i] = (i == 0? 2*cores : numCtrls[i-1])/childs[i];
      ctrls[i] = new InternalCtrl*[numCtrls[i]];
      connects[i] = new Connect*[numCtrls[i]];
      for(ThreadId j = 0; j < numCtrls[i]; j++) {
        ctrls[i][j] = new InternalCtrl(mshrs[i], ways[i], setSzs[i], childs[i],
                                       tagLats[i], dataLats[i]);
        Fifo* pToCs = ctrls[i][j]->getToCs();
        Fifo* pReqFromC = ctrls[i][j]->getReqFromC();
        Fifo* pRespFromC = ctrls[i][j]->getRespFromC();
        Fifo** csFromP = new Fifo*[childs[i]];
        Fifo** csReqToP = new Fifo*[childs[i]];
        Fifo** csRespToP = new Fifo*[childs[i]];
        for(Child k = 0; k < childs[i]; k++) {
          csFromP[k] = i == 0? l1s[j*childs[i] + k]->getFromP() : ctrls[i-1][j*childs[i] + k]->getFromP();
          csReqToP[k] = i == 0? l1s[j*childs[i] + k]->getFromP() : ctrls[i-1][j*childs[i] + k]->getReqToP();
          csRespToP[k] = i == 0? l1s[j*childs[i] + k]->getFromP() : ctrls[i-1][j*childs[i] + k]->getRespToP();
        }
        connects[i][j] = new Connect(childs[i], csFromP, csReqToP, csRespToP,
                                     pToCs, pReqFromC, pRespFromC);
      }
    }
    Fifo* csReqToP = ctrls[levels-1][0]->getReqToP();
    Fifo* csRespToP = ctrls[levels-1][0]->getRespToP();
    mem = new Memory(csReqToP, csRespToP, memLat);
  }
  ~systemNormal() {
    for(ThreadId i = 0; i < 2*cores; i++)
      delete l1s[i];
    delete[] l1s;
    for(ThreadId i = 0; i < cores; i++) {
      delete iFeeds;
      delete dFeeds;
    }
    delete[] iFeeds;
    delete[] dFeeds;
    for(U8 i = 0; i < levels; i++) {
      for(ThreadId j = 0; j < numCtrls[i]; j++) {
        delete ctrls[i][j];
        delete connects[i][j];
      }
      delete ctrls[i];
      delete connects[i];
    }
    delete[] ctrls;
    delete[] connects;
    delete numCtrls;
    delete mem;
  }
} SystemNormal;
