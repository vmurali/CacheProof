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
               Latency* tagLats, Latency* dataLats):
               cores(_cores), levels(_levels), childs(_childs) {
    l1s = new L1Normal*[2*cores];
    for(ThreadId i = 0; i < 2*cores; i++) {
      l1s[i] = new L1Normal(ways[0], setSzs[0]);
    }
    iFeeds = new InstFeeder*[cores];
    dFeeds = new DataFeeder*[cores];
    for(ThreadId i = 0; i < cores; i++) {
      iFeeds[i] = new InstFeeder(i, l1s[2*i]->getReqFromCore());
      dFeeds[i] = new DataFeeder(i, l1s[2*i+1]->getReqFromCore());
    }
    ThreadId* numCtrls = new ThreadId[levels];
    numCtrls[0] = 2*cores/childs[0];
    /*
    for(U8 i = 1; i < levels-1; i++) {
      numCtrls[i] = numCtrls[i-1]/childs[i];
      ctrls[i] = new InternalCtrl[numCtrls[i]];
      for(ThreadId j = 0; j < numCtrls[i]; j++) {
        ctrls[i][j] = new InternalCtrl(mshrs[i], ways[i], setSzs[i], childs[i],
                                       tagLats[i], dataLats[i]);
        Fifo* pToCs = ctrls[i][j].getToCs();
        Fifo* pReqFromC = ctrls[i][j].getReqFromC();
        Fifo* pRespFromC = ctrls[i][j].getRespFromC();
        Fifo** csFromP = new Fifo*[childs[i]];
        Fifo** csReqToP = new Fifo*[childs[i]];
        Fifo** csRespToP = new Fifo*[childs[i]];
        for(Child k = 0; k < childs[i]; k++) {
          csFromP[k] = ctrls[i-1][j*childs[i] + k].getFromP();
          csReqToP[k] = ctrls[i-1][j*childs[i] + k].getReqToP();
          csRespToP[k] = ctrls[i-1][j*childs[i] + k].getRespToP();
        }
        connects[i] = new Connect[numCtrls[i]];
        connects[i]
      }
    }
    */
  }
} SystemNormal;
