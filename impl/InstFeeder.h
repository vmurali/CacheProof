#pragma once

#include "Fifo.h"
#include "CacheTypes.h"
#include <unistd.h>
#include <fcntl.h>

typedef class instFeeder {
private:
  U32 count;
  U32 fd;
  ThreadId tId;
  Fifo * req;

  bool feed() {
    LineAddr addr;
    ssize_t bytes = read(fd, &addr, 8);
    if(bytes == 0) {
      close(fd);
      return true;
    }
    ReqFromCore* sendReq = new ReqFromCore(1, addr);
    printf("Inst sent %llx\n", addr);
    req->enq(sendReq);
    return false;
  }

public:
  bool done;
  instFeeder(ThreadId _tId, Fifo* _req) {
    tId = _tId;
    char buf[10];
    sprintf(buf, "i%d.tra", tId);
    fd = open(buf, O_RDONLY);
    req = _req;
    done = false;
  }
  ~instFeeder() {
    close(fd);
  }

  void cycle() {
    if(req->full())
      return;
    if(!done) {
      done = feed();
    }
  }
} InstFeeder;
