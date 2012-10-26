#pragma once

#include "Types.h"
#include <queue>

#include <cstdio>

using namespace std;

typedef class freeList {
private:
  queue<U8> q;
  U8 numElems;
public:
  freeList(U8 s): q(), numElems(s) {
    for(U8 i = 0; i < s; i++)
      q.push(i);
  }
  ~freeList() {printf("%p free list getting deleted\n", this);}
  bool isAvail() {
    return !q.empty();
  }
  U8 alloc() {
    numElems--;
    U8 idx = q.front();
    q.pop();
    return idx;
  }
  void free(U8 x) {
    numElems++;
    q.push(x);
  }
} FreeList;
