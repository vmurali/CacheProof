#pragma once

#include "Types.h"
#include <queue>

using namespace std;

typedef class freeList {
private:
  queue<U8>* q;
public:
  freeList(U8 s) {
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
    U8 idx = q->front();
    q->pop();
    return idx;
  }
  void free(U8 x) {
    q->push(x);
  }
} FreeList;
