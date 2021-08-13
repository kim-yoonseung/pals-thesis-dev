#include "app.h"

#include "system.h"
#include "main.h"

#define ACTIVE 1
#define STANDBY 2
#define QSIZE 4

#define OWNER_TIMEOUT 5

#define NUM_DEVICES 3
#define ID_DEV1 3
#define ID_DEV2 4
#define ID_DEV3 5
#define ID_MCAST 6

#define MSG_SIZE 8

#ifndef _TASK_ID
#define _TASK_ID 1
#endif

TEST_STATIC const char TASK_ID = _TASK_ID;

TEST_STATIC char grant_msg[MSG_SIZE] = {1};

// controller_state
typedef struct _ctrl_state {
  // [mode|tout|qb|qe|q1|q2|q3|q4]
  char arr[MSG_SIZE];
} ctrl_state;

TEST_STATIC ctrl_state state;


#ifdef FOR_TESTING
void INIT_FNAME(_TASK_ID)() {
  for (int i = 0; i < MSG_SIZE; ++i)
    state.arr[i] = 0;
}
#endif


TEST_STATIC int qrange_sanitize(int i) {
  if (0 <= i && i < QSIZE) return i;
  else return 0;
}

TEST_STATIC int adv_qidx(int i) {
  return qrange_sanitize(++i);
}

/* // idx in [lb, ub) */
/* int check_range(char idx, char lb, char ub) { */
/*   int r = (lb <= idx) && (idx < ub); */
/*   return r; */
/* } */

TEST_STATIC int check_dev_id(char tid) {
  int r = (tid == ID_DEV1) ||
    (tid == ID_DEV2) || (tid == ID_DEV3);
  return r;
}

TEST_STATIC void copy_state_from_hb(char st[MSG_SIZE],
			char hb[MSG_SIZE]) {
  for (int i = 1; i < 8; ++i)
    st[i] = hb[i];
}

TEST_STATIC void sync_istate(char tid, char st[MSG_SIZE], inbox_t *inbox) {
  char other_tid = 3 - tid;
  msg_entry_t *con = &inbox->entry[0];
  msg_entry_t *hb = &inbox->entry[other_tid];
  int i;

  // dec_mode
  char cur_mode = st[0];

  if (cur_mode == 0) {
    if (0 < hb->received) {
      copy_state_from_hb(st, hb->content);
      st[0] = STANDBY;
    } else {
      st[0] = tid;
    }
  } else if (cur_mode == ACTIVE) {
    if (0 < hb->received && 0 < con->received)
      st[0] = STANDBY;
  } else { // STANDBY
    if (0 < hb->received) {
      // no effects in normal situations
      copy_state_from_hb(st, hb->content);
      if (0 < con->received) st[0] = ACTIVE;
    } else {
      st[0] = ACTIVE;
      // If not sure about sending Grant
      if (st[1] == OWNER_TIMEOUT)
	st[1] = 0;
    }
  }
}


TEST_STATIC void try_add_queue(char st[MSG_SIZE], char id_dev) {
  char qb = st[2], qe = st[3];
  char *q = &st[4];

  char csr = qrange_sanitize(qb);
  for (int i = 0; i < NUM_DEVICES; ++i) {
    if (csr == qe) {
      q[csr] = id_dev;
      st[3] = adv_qidx(csr);
      break;
    }

    char tid = q[csr];
    if (tid == id_dev) break;
    csr = adv_qidx(csr);
  }
}

TEST_STATIC void try_release(char st[MSG_SIZE], char id_dev) {
  char tout = st[1], qb = st[2], qe = st[3];
  char *q = &st[4];

  if (qb != qe && q[qrange_sanitize(qb)] == id_dev)
    if (0 < tout && tout < OWNER_TIMEOUT)
      st[1] = 1;
}

TEST_STATIC void apply_devmsg(char st[MSG_SIZE], char id_dev,
		  msg_entry_t *me) {
  if (0 < me->received) {
    char b = me->content[0];
    if (b == 1) {
      // Sent Acquire
      try_add_queue(st, id_dev);
    } else {
      // (b == 2)
      // Sent Release
      try_release(st, id_dev);
    }
  }
}

TEST_STATIC void reduce_timeout(char st[MSG_SIZE]) {
  char tout = st[1], qb = st[2];

  if (tout == 1) {
    st[1] = 0;
    st[2] = adv_qidx(qb);
  } else if (1 < tout) {
    st[1] = tout - 1;
  }
}

TEST_STATIC void update_queue(char st[MSG_SIZE], inbox_t *inbox) {
  msg_entry_t *devmsg;
  for (int i = 0; i < NUM_DEVICES; ++i) {
    char id_dev = 3 + i;
    devmsg = &inbox->entry[id_dev];
    apply_devmsg(st, id_dev, devmsg);
  }
  reduce_timeout(st);
}

TEST_STATIC void update_istate(char tid, char st[MSG_SIZE], inbox_t *inbox) {
  sync_istate(tid, st, inbox);
  update_queue(st, inbox);
}

TEST_STATIC char update_owner(char st[MSG_SIZE]) {
  char md = st[0];
  /* char *qst = st->qstate; */
  char tout = st[1], qb = st[2], qe = st[3];
  char *q = &st[4];
  char hd = q[qrange_sanitize(qb)];

  // Only Active controller does the job
  /* if (md != 1) return -1; */

  // pick new owner (if head doesn't have ownership yet)
  if (tout == 0 && qb != qe) {
    st[1] = OWNER_TIMEOUT;

    if (md != 1) return -1;
    else return hd;
  } else {
    return -1;
  }
}

TEST_STATIC void send_hb(char st[MSG_SIZE], char tid) {
  char other_tid = 3 - tid;
  pals_send(other_tid, st);
}

TEST_STATIC void job_controller(char tid, ctrl_state *cst,
		    uint64_t pbt, inbox_t *inbox) {
  char tid_owner;
  char *st = (char*)cst->arr;

  update_istate(tid, st, inbox);
  tid_owner = update_owner(st);
  if (check_dev_id(tid_owner))
    pals_send(tid_owner, grant_msg);

  send_hb(st, tid);
}

// Wrapper function invoking actual job
void JOB_FNAME(_TASK_ID)(uint64_t pbt, inbox_t *inbox) {
  job_controller(TASK_ID, &state, pbt, inbox);
}
