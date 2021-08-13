#include "app.h"

#include "system.h"
#include "main.h"

#include <stdint.h>
#include <string.h>

#define MSG_SIZE 8
#define ID_MCAST 6

#ifndef _TASK_ID
#define _TASK_ID 0
#endif

TEST_STATIC const char TASK_ID = 0;

TEST_STATIC char toggle_msg[MSG_SIZE] = {1};


#ifdef FOR_TESTING
void INIT_FNAME(_TASK_ID)() {}
#endif


TEST_STATIC void job_console(char tid, int *unit,
			     uint64_t pbt, inbox_t *inbox) {
  int r = get_user_input();

  if (r != 0)
    pals_send(ID_MCAST, toggle_msg);

  write_log(0);
}

void JOB_FNAME(_TASK_ID)(uint64_t pbt, inbox_t *inbox) {
  job_console(TASK_ID, NULL, pbt, inbox);
}
