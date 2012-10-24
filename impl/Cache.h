#pragma once

#include "CacheTypes.h"

#include <cstdio>

typedef class cache {
private:
  Way** lruBits;
  Way ways;
  U8 setSz;
  Child childs;
  Set sets;

public:
  St** st;
  St*** cstates;
  bool** pReq;
  St** waitS;
  bool** cReq;
  St** waitCs;
  bool** dirty;
  Tag** tag;
  MshrPtr** mshrPtr;

  cache(Way _ways, Set _setSz, Child _childs):
        ways(ways), setSz(_setSz), childs(_childs), sets(1<<setSz) { 

    st = new St*[sets];
    cstates = new St**[sets];
    pReq = new bool*[sets];
    waitS = new St*[sets];
    cReq = new bool*[sets];
    waitCs = new St*[sets];
    dirty = new bool*[sets];
    tag = new Tag*[sets];
    mshrPtr = new MshrPtr*[sets];
    lruBits = new Way*[sets];

    for(Set i = 0; i < sets; i++) {
      st[i] = new St[ways];
      cstates[i] = new St*[ways];
      pReq[i] = new bool[ways];
      waitS[i] = new St[ways];
      cReq[i] = new bool[ways];
      waitCs[i] = new St[ways];
      dirty[i] = new bool[ways];
      tag[i] = new Tag[ways];
      mshrPtr[i] = new MshrPtr[ways];
      lruBits[i] = new Way[ways];

      for(Way j = 0; j < ways; j++) {
        st[i][j] = 0;
        pReq[i][j] = false;
        cReq[i][j] = false;
        cstates[i][j] = new St[childs];
        lruBits[i][j] = j;

        for(Child k = 0; k < childs; k++) {
          cstates[i][j][k] = 0;
        }
      }
    }
  }
  ~cache() {
    for(Set i = 0; i < sets; i++) {
      for(Way j = 0; j < ways; j++)
        delete[] cstates[i][j];

      delete[] st[i];
      delete[] cstates[i];
      delete[] pReq[i];
      delete[] waitS[i];
      delete[] cReq[i];
      delete[] waitCs[i];
      delete[] dirty[i];
      delete[] tag[i];
    }
    delete[] st;
    delete[] cstates;
    delete[] pReq;
    delete[] waitS;
    delete[] cReq;
    delete[] waitCs;
    delete[] dirty;
    delete[] tag;
  }
  bool isPresent(LineAddr lineAddr) {
    Set set = lineAddr & (sets-1);
    Tag _tag = lineAddr >> setSz;
    for(Way i = 0; i < ways; i++)
      if(tag[set][i] == _tag)
        return true;
    return false;
  }
  Index getIndex(LineAddr lineAddr) {
    printf("addr: %llx\n", lineAddr);
    Set set = lineAddr & (sets-1);
    printf("set: %d\n", set);
    Tag _tag = lineAddr >> setSz;
    printf("tag: %llx %d\n", _tag, setSz);
    Index index;
    index.set = set;
    for(Way i = 0; i < ways; i++)
      if(tag[set][i] == _tag)
        index.way = i;
    printf("way: %d\n", index.way);
    return index;
  }

  bool existsReplace(LineAddr lineAddr) {
    Set set = lineAddr & (sets - 1);
    for(Way i = 0; i < ways; i++)
      if(!pReq[set][i] && !cReq[set][i])
        return true;
    return false;
  }
  void replaceUpd(Index index) {
    Way old = lruBits[index.set][index.way];
    lruBits[index.set][index.way] = 0;
    for(Way i = 0; i < ways; i++) {
      Way bits = lruBits[index.set][i];
      if(bits < old)
        lruBits[index.set][i] = bits+1;
    }
  }
  void replaceRem(Index index) {
    Way old = lruBits[index.set][index.way];
    lruBits[index.set][index.way] = ways-1;
    for(Way i = 0; i < ways; i++) {
      Way bits = lruBits[index.set][i];
      if(bits > old)
        lruBits[index.set][i] = bits-1;
    }
  }
  Index getReplace(LineAddr lineAddr) {
    Set set = lineAddr & (sets - 1);
    bool found = false;
    Way highestLruBits = 0;
    Index index;
    index.set = set;
    for(Way i = 0; i < ways; i++) {
      if(!pReq[set][i] && !cReq[set][i]) {
        if(!found || lruBits[set][i] > highestLruBits) {
          index.way = i;
          highestLruBits = lruBits[set][i];
        }
        found = true;
      }
    }
    return index;
  }
} Cache;
