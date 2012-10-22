#pragma once

#include "Types.h"

typedef U8 St;
typedef U64 LineAddr;
typedef U64 Tag;
typedef U32 Set;
typedef U8 Way;
typedef U32 Child;
typedef U8 MshrPtr;

typedef struct {
  Set set;
  Way way;
} Index;

typedef class cache {
private:
  Way** lruBits;
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

  Set sets;
  Way ways;
  Child childs;
  U8 setSz;

  cache(Way _ways, Set _setSz, Child _childs) {
    sets = 1<<_setSz;
    childs = _childs;
    ways = _ways;

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

    for(U32 i = 0; i < sets; i++) {
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
        cstates[i][j] = new Way[childs];
        lruBits[i][j] = j;

        for(U32 k = 0; k < childs; k++) {
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
    Set set = lineAddr & (sets-1);
    Tag _tag = lineAddr >> setSz;
    Index index;
    index.set = set;
    for(Way i = 0; i < ways; i++)
      if(tag[set][i] == _tag)
        index.way = i;
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
    Index index;
    index.set = set;
    for(Way i = 0; i < ways; i++) {
      if(!pReq[set][i] && !cReq[set][i]) {
        found = true;
        if(!found)
          index.way = i;
        else if(index.way < i)
          index.way = i;
      }
    }
    return index;
  }
} Cache;
