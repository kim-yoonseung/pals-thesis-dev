#include "app.h"

#include "system.h"
#include "main.h"

#include <stdio.h>

#define IDLE 0
#define NEW_WORK 1
#define PENDING 2

#define NUM_WORKERS 8
#define ID_MCAST 9

#define MSG_SIZE 2

#ifndef _TASK_ID
#define _TASK_ID 0
#endif

TEST_STATIC const char TASK_ID = _TASK_ID;

static char req_msg[MSG_SIZE] = {0, 0};

// master state
typedef struct _master_state {
  char status;
  char next_work_id;
  char data;
} master_state;

static master_state state;


#ifdef FOR_TESTING
void INIT_FNAME(_TASK_ID)() {
  state.status = IDLE;
  state.next_work_id = 0;
  state.data = 0;
}
#endif


static void sync_workers(inbox_t *inbox) {
  if (state.status == PENDING) {
    for (int i = 1; i < NUM_WORKERS + 1; ++i) {
      msg_entry_t *ent = &inbox->entry[i];
      if (ent->received) {
	state.status = IDLE;
	break;
      }
    }
  }
}

static void update_master() {
  if (state.status == PENDING) {
    return;
  } else if (state.status == NEW_WORK) {
    state.status = PENDING;
  } else {
    // IDLE
    char work_init_data = (char)get_new_work();

    if (0 < work_init_data) {
      state.status = NEW_WORK;
      ++state.next_work_id;
      state.data = work_init_data;
    }
  }
}

static void send_request() {
  if (state.status == NEW_WORK) {
    req_msg[0] = state.next_work_id;
    req_msg[1] = state.data;
    pals_send(ID_MCAST, req_msg);
  }
}

// Wrapper function invoking actual job
void JOB_FNAME(_TASK_ID)(uint64_t pbt, inbox_t *inbox) {
  sync_workers(inbox);
  update_master();
  send_request();
}
