#include "SystemNormal.h"

using namespace std;

ThreadId cores = 2;
U8 levels = 2;
Child childs[] = {2, 2};
MshrPtr mshrs[] = {32, 64};
Way ways[] = {8, 16, 16};
U8 setSzs[] = {6, 8, 10};
Latency tagLats[] = {5, 10};
Latency dataLats[] = {5, 10};
Latency memLat = 40;

int main() {

  SystemNormal sys(cores, levels, childs, mshrs, ways, setSzs, tagLats, dataLats, memLat);
  sys.run();
  sys.display();
}
