#pragma once

#include "Types.h"
#include "Debug.h"
#include <queue>

using namespace std;

typedef class fifo {
private:
  queue<void*> q;
  U8 size;
  U8 numElems;
  bool enqEn;
  bool deqEn;
public:
  fifo(U8 s) : q(), size(s), numElems(0), enqEn(false), deqEn(false){}
  ~fifo() {}

  bool full() {
    return numElems == size;
  }
  bool empty() {
    return numElems == 0;
  }
  void enq(void* x) {
    Assert (numElems < size);
    q.push(x);
    enqEn = true;
  }
  void deq() {
    Assert (numElems > 0);
    q.pop();
    deqEn = true;
  }
  void* first() {
    return q.front();
  }

  void cycle() {
    if(enqEn)
      numElems++;
    if(deqEn)
      numElems--;
    enqEn = false;
    deqEn = false;
  }
} Fifo;
