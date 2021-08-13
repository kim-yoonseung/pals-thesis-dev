#include "test_interface.h"
#include "system.h"

#include <stdlib.h>

extern void job_0(uint64_t tm, inbox_t *);
extern void job_1(uint64_t tm, inbox_t *);
extern void job_2(uint64_t tm, inbox_t *);
extern void job_3(uint64_t tm, inbox_t *);
extern void job_4(uint64_t tm, inbox_t *);
extern void job_5(uint64_t tm, inbox_t *);

extern void init_0(void);
extern void init_1(void);
extern void init_2(void);
extern void init_3(void);
extern void init_4(void);
extern void init_5(void);

const int NUM_TASKS = 6;
const int NUM_MCASTS = 1;
const int MSG_SIZE = 8;
const uint64_t PALS_PERIOD = 100000000;

const char MCAST_MEMBER[1][_MAX_NUM_TASKS] =
  {
    { 0, 1, 1, 0, 0, 0 },
  };

int get_user_input() {
  int r = extcall_event_int("get_user_input", 0, NULL);
  return r;
}

void write_log(int log_val) {
  int args[1];
  args[0] = log_val;

  extcall_event_void("write_log", 1, args);
  return;
}

int check_demand() {
  int r = extcall_event_int("check_demand", 0, NULL);
  return r;
}

void use_resource() {
  extcall_event_void("use_resource", 0, NULL);
  return;
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
  }
}
