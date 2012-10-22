#pragma once

#include "Fifo.h"
#include "CacheTypes.h"
#include <unistd.h>
#include <fcntl.h>
#include <cstdio>

typedef class feeder {
private:
  U32 count;
  U32 dFd, iFd;
  ThreadId tId;
  Fifo* iReq,* dReq;
  bool iDone, dDone;

  bool feed(Fifo* req, St to, U32 fd) {
    if(req->full())
      return false;
    LineAddr addr;
    ssize_t bytes = read(fd, &addr, 8);
    if(bytes == 0) {
      close(fd);
      return true;
    }
    ReqFromCore* sendReq = new ReqFromCore(to, addr>>6);
    req->enq(sendReq);
    return false;
  }

  St getTo() {
    U8 to = 0;
    ssize_t bytes = read(dFd, &to, 1);
    return to;
  }

public:
  bool done;
  feeder(ThreadId _tId, Fifo* _iReq, Fifo* _dReq) {
    tId = _tId;
    char dBuf[10], iBuf[10];
    sprintf(dBuf, "d%d.tra", tId);
    sprintf(iBuf, "i%d.tra", tId);
    dFd = open(dBuf, O_RDONLY);
    iFd = open(iBuf, O_RDONLY);
    iReq = _iReq; dReq = _dReq;
    iDone = false; dDone = false;
    done = false;
  }
  ~feeder() {
    close(dFd);
    close(iFd);
  }

  void cycle() {
    if(!iDone) {
      iDone = feed(iReq, 1, iFd);
    }
    if(!dDone) {
      dDone = feed(dReq, getTo(), dFd);
    }
    done = iDone && dDone;
  }
} Feeder;
