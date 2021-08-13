#include "app.h"

#include "system.h"
#include "main.h"

#include <stdlib.h>

#define UNINIT 0
#define OWNER 1
#define NOT_OWNER 2

#define OWNER_TIMEOUT 5
#define ID_MCAST 6

#define MSG_SIZE 8

#ifndef _TASK_ID
#define _TASK_ID 3
#endif

TEST_STATIC const char TASK_ID = _TASK_ID;

TEST_STATIC char acq_msg[MSG_SIZE] = {1};
TEST_STATIC char rel_msg[MSG_SIZE] = {2};

typedef struct _dev_state {
  char is_owner;
  char demand;
} dev_state;

TEST_STATIC dev_state state;

#ifdef FOR_TESTING
void INIT_FNAME(_TASK_ID)() {
  state.is_owner = 0;
  state.demand = 0;
}
#endif

TEST_STATIC void sync_dev_state(inbox_t *inbox, dev_state *dst) {
  msg_entry_t *e1 = &inbox->entry[1], *e2 = &inbox->entry[2];

  if (e1->received || e2->received)
    dst->is_owner = OWNER;
}

TEST_STATIC char get_new_demand() {
  int d = check_demand();

  if (OWNER_TIMEOUT < d)
    return OWNER_TIMEOUT;
  else if (d < 0)
    return 0;
  else
    return d;
}

TEST_STATIC int update_demand(dev_state *dst) {
  // TODO
  if (dst->demand == 0) {
    // got new demand => SendAcq
    char d = get_new_demand();
    if (0 < d) {
      dst->demand = d;
      return 1;
    }
  }
  return 0;
}

TEST_STATIC void run_device(dev_state *dstate) {
  char dmd = dstate->demand;
  if (0 < dmd) {
    use_resource();
    --dmd;
    dstate->demand = dmd;
  }
}

TEST_STATIC void job_device(char tid, dev_state *dstate,
		uint64_t pbt, inbox_t *inbox) {
  int ret;

  if (dstate->is_owner == UNINIT) {
    dstate->is_owner = NOT_OWNER;
    pals_send(ID_MCAST, rel_msg);
    write_log(0);
    return;
  }

  sync_dev_state(inbox, dstate);
  ret = update_demand(dstate);

  if (dstate->is_owner == OWNER) {
    run_device(dstate);

    if (dstate->demand == 0) {
      dstate->is_owner = NOT_OWNER;
      pals_send(ID_MCAST, rel_msg);
    }
  } else if (0 < ret) {
      pals_send(ID_MCAST, acq_msg);
  }

  write_log(0);
}

void JOB_FNAME(_TASK_ID)(uint64_t pbt, inbox_t *inbox) {
  job_device(TASK_ID, &state, pbt, inbox);
}
