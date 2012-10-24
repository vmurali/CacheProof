#pragma once

#include "CacheTypes.h"
#include "Fifo.h"

typedef class connect {
private:
  Child childs;
  Fifo** csFromP,** csReqToP,** csRespToP;
  Fifo* pToCs,* pReqFromC,* pRespFromC;

  Child nextCReq, nextCResp;

public:
  connect(Child _childs,
          Fifo** _csFromP, Fifo** _csReqToP, Fifo** _csRespToP,
          Fifo* _pToCs, Fifo* _pReqFromC, Fifo* _pRespFromC):
          childs(_childs),
          csFromP(_csFromP), csReqToP(_csReqToP), csRespToP(_csRespToP),
          pToCs(_pToCs), pReqFromC(_pReqFromC), pRespFromC(_pRespFromC),
          nextCReq(0), nextCResp(0) {}
  ~connect() {
    delete[] csFromP;
    delete[] csReqToP;
    delete[] csRespToP;
  }

  void cycle() {
    if(!pReqFromC->full()) {
      for(Child i = 0; i < childs; i++) {
        Child c = (nextCReq + i)%childs;
        ReqToP* msg = (ReqToP*)csReqToP[c]->first();
        if(!csReqToP[c]->empty()) {
          printf("connect called %p %p %p\n", msg, pReqFromC, csReqToP[c]);
          nextCReq = c;
          pReqFromC->enq(reqToP2reqFromC(msg, c));
          csReqToP[c]->deq();
          delete msg;
          break;
        }
      }
    }
    if(!pRespFromC->full()) {
      for(Child i = 0; i < childs; i++) {
        Child c = (nextCResp + i)%childs;
        RespToP* msg = (RespToP*)csRespToP[c]->first();
        if(!csRespToP[c]->empty()) {
          nextCResp = c;
          pRespFromC->enq(respToP2respFromC(msg, c));
          csRespToP[c]->deq();
          delete msg;
          break;
        }
      }
    }

    if(!pToCs->empty()) {
      ToCs* msg = (ToCs*)pToCs->first();
      for(Child c = 0; c < childs; c++) {
        if(msg->children[c] && !csFromP[c]->full()) {
          msg->children[c] = false;
          csFromP[c]->enq(toCs2fromP(msg, c));
        }
      }
      bool notDone = false;
      for(Child c = 0; c < childs; c++) {
        if(msg->children[c]) {
          notDone = true;
          break;
        }
      }
      if(!notDone) {
        pToCs->deq();
        delete msg;
      }
    }
  }
} Connect;
