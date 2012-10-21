#pragma once

#include "Types.h"
#include <queue>

using namespace std;

typedef class fifo {
private:
  queue<void*>* q;
  U8 size;
  U8 numElems;
public:
  fifo(U8 s) {
    q = new queue<void*>;
    size = s;
    numElems = 0;
  }
  ~fifo() {
    delete q;
  }
  bool full() {
    return numElems == size;
  }
  bool empty() {
    return numElems == 0;
  }
  void enq(void* x) {
    q->push(x);
  }
  void deq() {
    q->pop();
  }
  void* first() {
    return q->front();
  }
} Fifo;
