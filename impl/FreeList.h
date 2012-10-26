#pragma once

#include "Types.h"
#include <queue>

using namespace std;

typedef class freeList {
private:
  queue<U8>* q;
public:
  U8 numElems;
  freeList(U8 s): numElems(s) {
    q = new queue<U8>;
    for(U8 i = 0; i < s; i++)
      q->push(i);
  }
  ~freeList() {
    delete q;
  }
  bool isAvail() {
    return !q->empty();
  }
  U8 alloc() {
    numElems--;
    U8 idx = q->front();
    q->pop();
    return idx;
  }
  void free(U8 x) {
    numElems++;
    q->push(x);
  }
} FreeList;
