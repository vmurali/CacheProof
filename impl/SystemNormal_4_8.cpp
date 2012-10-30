#include "SystemNormal.h"

using namespace std;

ThreadId cores = 4;
U8 levels = 1;
Child childs[] = {8};
MshrPtr mshrs[] = {8};
Way ways[] = {8, 16};
U8 setSzs[] = {6, 8};
Latency tagLats[] = {4};
Latency dataLats[] = {10};
Latency memLat = 50;

int main() {

  SystemNormal sys(cores, levels, childs, mshrs, ways, setSzs, tagLats, dataLats, memLat);
  sys.run();
  sys.display();
}
