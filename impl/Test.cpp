#include "SystemNormal.h"

#include <cstdio>

using namespace std;

ThreadId cores = 1;
U8 levels = 1;
Child childs[] = {2};
MshrPtr mshrs[] = {1};
Way ways[] = {2, 2};
U8 setSzs[] = {0, 0};
Latency tagLats[] = {5};
Latency dataLats[] = {10};
Latency memLat = 150;

int main() {
  SystemNormal sys(cores, levels, childs, mshrs, ways, setSzs, tagLats, dataLats, memLat);
  sys.run();
  sys.display();
}
