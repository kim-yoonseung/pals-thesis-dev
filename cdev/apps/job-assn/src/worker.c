#include "app.h"

#include "system.h"
#include "main.h"

#define IDLE 0
#define BIDDING 1
#define WORKING 2

#define NUM_WORKERS 8
#define ID_MCAST 9

#define MSG_SIZE 2

#ifndef _TASK_ID
#define _TASK_ID 1
#endif

TEST_STATIC const char TASK_ID = _TASK_ID;

static char bid_msg[MSG_SIZE] = {1, 0};

// worker state
typedef struct _worker_state {
  char status;
  char work_id;
  char data;
} worker_state;

static worker_state state;


#ifdef FOR_TESTING
void INIT_FNAME(_TASK_ID)() {
  state.status = 0;
  state.work_id = 0;
  state.data = 0;
}
#endif

static void check_bidding(inbox_t *inb) {

  int bid_fail = 0;

  if (state.status == BIDDING) {
    for (int i = TASK_ID + 1; i <= NUM_WORKERS; ++i) {
      msg_entry_t *ent = &inb->entry[i];

      if (ent->received) {
	bid_fail = 1;
	break;
      }
    }

    if (bid_fail == 0) {
      state.status = WORKING;
    } else {
      state.status = IDLE;
    }
  }
}

static void check_new_work(inbox_t *inb) {
  msg_entry_t *ent = &inb->entry[0];

  if (ent->received) {
    state.status = BIDDING;
    state.work_id = ent->content[0];
    state.data = ent->content[1];

    pals_send(ID_MCAST, bid_msg);
  }
}

static void continue_work() {
  char ret = (char)do_work(state.work_id, state.data);
  state.data = ret;

  if (ret == 0) {
    state.status = IDLE;
    state.work_id = 0;
  }
}

// Wrapper function invoking actual job
void JOB_FNAME(_TASK_ID)(uint64_t pbt, inbox_t *inbox) {
  check_bidding(inbox);

  if (state.status == IDLE) {
    check_new_work(inbox);
  } else {
    continue_work();
  }
}
