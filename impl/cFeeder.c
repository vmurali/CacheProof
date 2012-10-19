#include<unistd.h>
#include<fcntl.h>
#include<stdio.h>

int iFds[1024];
int dFds[1024];

void initialize(unsigned char isData, unsigned int tId) {
  int fd = 0;
  char buf[10];
  if(isData) {
    sprintf(buf, "d%d.tra", tId);
    dFds[tId] = open(buf, O_RDONLY);
    printf("opened %s %d\n", buf, dFds[tId]);
  }
  else {
    sprintf(buf, "i%d.tra", tId);
    iFds[tId] = open(buf, O_RDONLY);
    printf("opened %s %d\n", buf, iFds[tId]);
  }
}

char getDataSt(unsigned int tId) {
  char st;
  read(dFds[tId], &st, 1);
  return st;
}

unsigned long long getFeed(char isData, unsigned int tId) {
  unsigned long long addr;
  int fd = isData == 0? iFds[tId] : dFds[tId];
  read(fd, &addr, 8);
  return addr;
}
