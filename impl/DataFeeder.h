#pragma once

#include "Fifo.h"
#include "CacheTypes.h"
#include <unistd.h>
#include <fcntl.h>
#include <cstdio>

typedef class dataFeeder {
private:
  ThreadId tId;
  U32 count;
  U32 fd;
  Fifo * req;

  void feed(St to) {
    LineAddr addr;
    ssize_t bytes = read(fd, &addr, 8);
    if(bytes == 0) {
      close(fd);
      return;
    }
    ReqFromCore* sendReq = new ReqFromCore(to, addr);
    req->enq(sendReq);
  }

public:
  bool done;
  dataFeeder(ThreadId _tId, Fifo* _req) : tId(_tId), count(0) {
    tId = _tId;
    char buf[10];
    sprintf(buf, "d%d.tra", tId);
    fd = open(buf, O_RDONLY);
    req = _req;
    done = false;
  }
  ~dataFeeder() {
    close(fd);
  }

  void cycle() {
    if(!done) {
      if(count != 0) {
        count --;
        return;
      }
      if(req->full())
        return;
      St to = 0;
      ssize_t bytes;
      bytes = read(fd, &to, 1);
      if(bytes == 0) {
        done = true;
        return;
      }
      if(to == 0) {
        bytes = read(fd, &count, 4);
        if(count != 0)
          count--;
        return;
      }
      feed(to);
    }
  }
} DataFeeder;
