#include "system.h"

#include <stdlib.h>
#include <stdio.h>
#include <time.h>

int get_new_work(void) {
  srand(time(0));
  int r = rand() % 10;
  return r;
}

int do_work(char id, char data) {
  printf("Working on %d with data %d..", id, data);
  srand(time(0));
  int r = rand() % 500; // in millisec
  struct timespec req;
  req.tv_sec = 0;
  req.tv_nsec = r * 1000000;

  nanosleep(&req, NULL);
  printf("done\n");

  return (data - 1);
}
