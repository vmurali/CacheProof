#pragma once

#include "Types.h"
#include <queue>

using namespace std;

typedef class fifo {
private:
  queue<void*>* q;
  U8 size;
  U8 numElems;
  bool enqEn;
  bool deqEn;
public:
  fifo(U8 s) {
    q = new queue<void*>;
    size = s; numElems = 0; enqEn = false; deqEn = false;
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
    enqEn = true;
  }
  void deq() {
    q->pop();
    deqEn = true;
  }
  void* first() {
    return q->front();
  }

  void cycle() {
    if(enqEn)
      numElems++;
    if(deqEn)
      numElems--;
  }
} Fifo;
