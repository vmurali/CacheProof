#include "SystemNormal.h"

using namespace std;

ThreadId cores = 8;
U8 levels = 1;
Child childs[] = {16};
MshrPtr mshrs[] = {16};
Way ways[] = {8, 8};
U8 setSzs[] = {6, 8};
Latency tagLats[] = {4};
Latency dataLats[] = {10};
Latency memLat = 50;

int main() {

  SystemNormal sys(cores, levels, childs, mshrs, ways, setSzs, tagLats, dataLats, memLat);
  sys.run();
  sys.display();
}
