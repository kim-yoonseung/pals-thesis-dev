#include "test_interface.h"
#include "system.h"

#include <stdlib.h>

extern void job_0(uint64_t tm, inbox_t *);
extern void job_1(uint64_t tm, inbox_t *);
extern void job_2(uint64_t tm, inbox_t *);
extern void job_3(uint64_t tm, inbox_t *);
extern void job_4(uint64_t tm, inbox_t *);
extern void job_5(uint64_t tm, inbox_t *);
extern void job_6(uint64_t tm, inbox_t *);
extern void job_7(uint64_t tm, inbox_t *);
extern void job_8(uint64_t tm, inbox_t *);

extern void init_0(void);
extern void init_1(void);
extern void init_2(void);
extern void init_3(void);
extern void init_4(void);
extern void init_5(void);
extern void init_6(void);
extern void init_7(void);
extern void init_8(void);

const int NUM_TASKS = 9;
const int NUM_MCASTS = 1;
const int MSG_SIZE = 2;
const uint64_t PALS_PERIOD = 1000000000;

const char MCAST_MEMBER[1][_MAX_NUM_TASKS] =
  {
    { 1, 1, 1, 1, 1, 1, 1, 1, 1 },
  };


int get_new_work() {
  int r = extcall_event_int("get_new_work", 0, NULL);
  return r;
}

int do_work(char wid, char data) {
  int args[2];
  args[0] = wid;
  args[1] = data;

  int r = extcall_event_int("do_work", 2, args);
  return r;
}

void call_job(uint64_t tm, int tid) {
  switch(tid) {
  case 0:
    job_0(tm, &inbox);
    break;
  case 1:
    job_1(tm, &inbox);
    break;
  case 2:
    job_2(tm, &inbox);
    break;
  case 3:
    job_3(tm, &inbox);
    break;
  case 4:
    job_4(tm, &inbox);
    break;
  case 5:
    job_5(tm, &inbox);
    break;
  case 6:
    job_6(tm, &inbox);
    break;
  case 7:
    job_7(tm, &inbox);
    break;
  case 8:
    job_8(tm, &inbox);
    break;
  }
}

void init_job(int tid) {
  switch(tid) {
  case 0:
    init_0();
    break;
  case 1:
    init_1();
    break;
  case 2:
    init_2();
    break;
  case 3:
    init_3();
    break;
  case 4:
    init_4();
    break;
  case 5:
    init_5();
    break;
  case 6:
    init_6();
    break;
  case 7:
    init_7();
    break;
  case 8:
    init_8();
    break;
  }
}
