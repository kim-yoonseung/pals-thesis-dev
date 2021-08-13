/* #include "app.h" */

/* #include "system.h" */
/* #include "main.h" */

#include <time.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

// From app.h
#ifndef _MSG_SIZE_K
#define _MSG_SIZE_K 1
#endif

#ifndef _MAX_NUM_TASKS
#define _MAX_NUM_TASKS 16
#endif

#ifndef _MAX_NUM_MCASTS
#define _MAX_NUM_MCASTS 8
#endif

/* #define _MSG_SIZE_K 2 */
#define _MAX_MSG_SIZE (8 * _MSG_SIZE_K + 7)


// From applications
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

#define UNINIT 0
#define OWNER 1
#define NOT_OWNER 2


/* TESTER */

#define PERIOD_LENGTH 10

#define MAX_NUM_PERIODS 1000
#define NUM_TASKS 6

char cur_task_id = 0;
uint64_t cur_period = 0;

typedef struct msg_entry_t {
  char received;
  char content[_MAX_MSG_SIZE];
} msg_entry_t;

typedef struct inbox_t {
  msg_entry_t entry[_MAX_NUM_TASKS];
} inbox_t;

int cur_inbox_idx = 0;
inbox_t inbox[2][NUM_TASKS];


// TODO: initialize as -1s
char fail_history[MAX_NUM_PERIODS][NUM_TASKS];
int uinp_history[MAX_NUM_PERIODS][NUM_TASKS];
char compl_history[MAX_NUM_PERIODS][NUM_TASKS];
int demand_history[MAX_NUM_PERIODS][NUM_TASKS];
char ures_history[MAX_NUM_PERIODS][NUM_TASKS];

const int FAIL_RATIO_INV = 30;
const int UINP_RATIO_INV = 10;
const int MAX_DEMAND = 8;

int get_user_input() {
  int r;
  if (0 < fail_history[cur_period][cur_task_id])
    return 0;

  r = rand() % FAIL_RATIO_INV;
  if (r == 0) {
    fail_history[cur_period][cur_task_id] = 1;
    return 0;
  }

  r = rand() % UINP_RATIO_INV;
  if (r == 0) {
    uinp_history[cur_period][cur_task_id] = 1;
    return 1;
  } else {
    uinp_history[cur_period][cur_task_id] = 0;
    return 0;
  }
}

void mark_complete(uint64_t sytm) {
  int r;
  if (0 < fail_history[cur_period][cur_task_id])
    return;

  r = rand() % FAIL_RATIO_INV;
  if (r == 0) {
    fail_history[cur_period][cur_task_id] = 1;
    return;
  }

  compl_history[cur_period][cur_task_id] = 1;
}

int check_demand() {
  int r;
  if (0 < fail_history[cur_period][cur_task_id])
    return 0;

  r = rand() % FAIL_RATIO_INV;
  if (r == 0) {
    fail_history[cur_period][cur_task_id] = 1;
    return 0;
  }

  r = rand() % MAX_DEMAND;
  demand_history[cur_period][cur_task_id] = r;
  return r;
}

void use_resource() {
  int r;
  if (0 < fail_history[cur_period][cur_task_id])
    return;

  r = rand() % FAIL_RATIO_INV;
  if (r == 0) {
    fail_history[cur_period][cur_task_id] = 1;
    return;
  }

  ures_history[cur_period][cur_task_id] = 1;
}

void pals_send(char id_dest, char *msg) {
  // TODO
  if (id_dest == ID_MCAST) {
    msg_entry_t *ent1 = &inbox[1 - cur_inbox_idx][1].entry[cur_task_id],
      *ent2 = &inbox[1 - cur_inbox_idx][2].entry[cur_task_id];

    ent1->received = 1;
    memcpy(ent1->content, msg, MSG_SIZE);
    ent2->received = 1;
    memcpy(ent2->content, msg, MSG_SIZE);
  } else {
    msg_entry_t *ent = &inbox[1 - cur_inbox_idx][id_dest].entry[cur_task_id];
    ent->received = 1;
    memcpy(ent->content, msg, MSG_SIZE);
  }
}


/** 1. Console */
char toggle_msg[MSG_SIZE] = {1};

void job_console(char tid, int *unit,
		 uint64_t pbt, inbox_t *inbox) {
  int r = get_user_input();

  if (r != 0)
    pals_send(ID_MCAST, toggle_msg);

  mark_complete(pbt);
}

/* void job(uint64_t pbt, inbox_t *inbox) { */
/*   job_console(TASK_ID, NULL, pbt, inbox); */
/* } */


/** 2. Controller */
char grant_msg[MSG_SIZE] = {1};

// controller_state
typedef struct _ctrl_state {
  // [mode|tout|qb|qe|q1|q2|q3|q4]
  char arr[MSG_SIZE];
} ctrl_state;

int qrange_sanitize(int i) {
  if (0 <= i && i < QSIZE) return i;
  else return 0;
}

int adv_qidx(int i) {
  return qrange_sanitize(++i);
}

int check_dev_id(char tid) {
  int r = (tid == ID_DEV1) ||
    (tid == ID_DEV2) || (tid == ID_DEV3);
  return r;
}

void copy_state_from_hb(char st[MSG_SIZE],
			char hb[MSG_SIZE]) {
  for (int i = 1; i < 8; ++i)
    st[i] = hb[i];
}

void sync_istate(char tid, char st[MSG_SIZE], inbox_t *inbox) {
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


void try_add_queue(char st[MSG_SIZE], char id_dev) {
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

void try_release(char st[MSG_SIZE], char id_dev) {
  char tout = st[1], qb = st[2], qe = st[3];
  char *q = &st[4];

  if (qb != qe && q[qrange_sanitize(qb)] == id_dev) {
    if (0 < tout && tout < OWNER_TIMEOUT)
      st[1] = 1;
  }
}

void apply_devmsg(char st[MSG_SIZE], char id_dev,
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

void reduce_timeout(char st[MSG_SIZE]) {
  char tout = st[1], qb = st[2];

  if (tout == 1) {
    st[1] = 0;
    st[2] = adv_qidx(qb);
  } else if (1 < tout) {
    st[1] = tout - 1;
  }
}

void update_queue(char st[MSG_SIZE], inbox_t *inbox) {
  msg_entry_t *devmsg;
  for (int i = 0; i < NUM_DEVICES; ++i) {
    char id_dev = 3 + i;
    devmsg = &inbox->entry[id_dev];
    apply_devmsg(st, id_dev, devmsg);
  }
  reduce_timeout(st);
}

void update_istate(char tid, char st[MSG_SIZE], inbox_t *inbox) {
  sync_istate(tid, st, inbox);
  update_queue(st, inbox);
}

char update_owner(char st[MSG_SIZE]) {
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
    return hd;
  }

  return -1;
}

void send_hb(char st[MSG_SIZE], char tid) {
  char other_tid = 3 - tid;
  pals_send(other_tid, st);
}

void job_controller(char tid, ctrl_state *cst,
		    uint64_t pbt, inbox_t *inbox) {
  char tid_owner;
  char *st = (char*)cst->arr;

  update_istate(tid, st, inbox);
  tid_owner = update_owner(st);
  if (check_dev_id(tid_owner))
    pals_send(tid_owner, grant_msg);

  send_hb(st, tid);
  mark_complete(pbt);
}

/* // Wrapper function invoking actual job */
/* void job(uint64_t pbt, inbox_t *inbox) { */
/*   job_controller(TASK_ID, &state, pbt, inbox); */
/* } */

/** 3. Device */
char acq_msg[MSG_SIZE] = {1};
char rel_msg[MSG_SIZE] = {2};

typedef struct _dev_state {
  char is_owner;
  char demand;
} dev_state;

/* dev_state state; */

void sync_dev_state(inbox_t *inbox, dev_state *dst) {
  msg_entry_t *e1 = &inbox->entry[1], *e2 = &inbox->entry[2];

  if (e1->received || e2->received)
    dst->is_owner = OWNER;
}

char get_new_demand() {
  int d = check_demand();

  if (OWNER_TIMEOUT < d)
    return OWNER_TIMEOUT;
  else if (d < 0)
    return 0;
  else
    return d;
}

int update_demand(dev_state *dst) {
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

void run_device(dev_state *dstate) {
  char dmd = dstate->demand;
  if (0 < dmd) {
    use_resource();
    --dmd;
    dstate->demand = dmd;
  }
}

void job_device(char tid, dev_state *dstate,
		uint64_t pbt, inbox_t *inbox) {
  int ret;

  if (dstate->is_owner == UNINIT) {
    dstate->is_owner = NOT_OWNER;
    pals_send(ID_MCAST, rel_msg);
    mark_complete(pbt);
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

  mark_complete(pbt);
}

/* void job(uint64_t pbt, inbox_t *inbox) { */
/*   job_device(TASK_ID, &state, pbt, inbox); */
/* } */

/* TESTER(2) */

int is_turned_off[NUM_TASKS];
ctrl_state cstate[2];
dev_state dstate[3];


void init_inboxes(inbox_t *inbs) {
  for (int i = 0; i < NUM_TASKS; ++i)
    for (int j = 0; j < NUM_TASKS; ++j)
      inbs[i].entry[j].received = 0;;
}

void init_data() {
  int i, j;

  for (i = 0; i < MAX_NUM_PERIODS; ++i)
    for (j = 0; j < NUM_TASKS; ++j) {
      fail_history[i][j] = -1;
      uinp_history[i][j] = -1;
      compl_history[i][j] = -1;
      demand_history[i][j] = -1;
      ures_history[i][j] = -1;
    }

  cur_task_id = 0;
  cur_period = 0;
  cur_inbox_idx = 0;

  init_inboxes(inbox[0]);
  init_inboxes(inbox[1]);

  for (i = 0; i < NUM_TASKS; ++i)
    is_turned_off[i] = 1;
}

const int TURN_ON_RATIO_INV = 3;

void run_console(uint64_t sytm) {
  int r;
  int *unit = 0;
  cur_task_id = 0;

  if (0 < is_turned_off[0]) {
    r = rand() % TURN_ON_RATIO_INV;
    if (r == 0) {
      is_turned_off[0] = 0;
      // initialize state
    }
  } else {

    job_console(0, unit, sytm, &inbox[cur_inbox_idx][0]);

    if (0 < fail_history[cur_period][0]) {
      is_turned_off[0] = 1;
    } else {
      r = rand() % FAIL_RATIO_INV;
      if (r == 0) {
	fail_history[cur_period][0] = 1;
	is_turned_off[0] = 1;
      }
    }
  }
}

void run_ctrl(uint64_t sytm, int idx) {
  int r;
  int tid = idx + 1;
  cur_task_id = tid;

  if (0 < is_turned_off[tid]) {
    r = rand() % TURN_ON_RATIO_INV;
    if (r == 0) {
      is_turned_off[tid] = 0;
      // initialize state
      for (int j = 0; j < MSG_SIZE; ++j)
	cstate[idx].arr[j] = 0;
    }
  } else {

    job_controller(tid, &cstate[idx],
		   sytm, &inbox[cur_inbox_idx][tid]);

    if (0 < fail_history[cur_period][tid]) {
      is_turned_off[tid] = 1;
    } else {
      r = rand() % FAIL_RATIO_INV;
      if (r == 0) {
	fail_history[cur_period][tid] = 1;
	is_turned_off[tid] = 1;
      }
    }
  }
}

void run_dev(uint64_t sytm, int idx) {
  int r;
  int tid = idx + 3;
  cur_task_id = tid;

  if (0 < is_turned_off[tid]) {
    r = rand() % TURN_ON_RATIO_INV;
    if (r == 0) {
      is_turned_off[tid] = 0;
      // initialize state
      for (int j = 0; j < MSG_SIZE; ++j) {
	dstate[idx].is_owner = 0;
	dstate[idx].demand = 0;
      }
    }
  } else {

    job_device(tid, &dstate[idx],
	       sytm, &inbox[cur_inbox_idx][tid]);

    if (0 < fail_history[cur_period][tid]) {
      is_turned_off[tid] = 1;
    } else {
      r = rand() % FAIL_RATIO_INV;
      if (r == 0) {
	fail_history[cur_period][tid] = 1;
	is_turned_off[tid] = 1;
      }
    }
  }
}

void print_inbox(inbox_t *inb) {
  for (int i = 0; i < NUM_TASKS; ++i) {
    if (0 < inb->entry[i].received) {
      printf("[ ");
      for (int j = 0; j < MSG_SIZE; ++j)
	printf("%d ", inb->entry[i].content[j]);
      printf("] ");
    } else {
      printf("[] ");
    }
  }
  printf("\n");
}

int lv_max_glob = 0;

void run_test(int num_periods) {
  init_data();

  uint64_t sytm = PERIOD_LENGTH * 10;

  for (int pidx = 0; pidx < num_periods; ++pidx) {
    cur_period = pidx;

    /* printf("[LOG] pidx= %d, sytm= %lu \n", pidx, sytm); */
    /* printf("[LOG] task_id: 0\n"); */
    /* print_inbox(&inbox[cur_inbox_idx][0]); */
    /* printf("[LOG] task_id: 1\n"); */
    /* print_inbox(&inbox[cur_inbox_idx][1]); */
    /* printf("[LOG] task_id: 2\n"); */
    /* print_inbox(&inbox[cur_inbox_idx][2]); */
    /* printf("[LOG] task_id: 3\n"); */
    /* print_inbox(&inbox[cur_inbox_idx][3]); */
    /* printf("[LOG] task_id: 4\n"); */
    /* print_inbox(&inbox[cur_inbox_idx][4]); */
    /* printf("[LOG] task_id: 5\n"); */
    /* print_inbox(&inbox[cur_inbox_idx][5]); */

    run_console(sytm);
    run_ctrl(sytm, 0);
    run_ctrl(sytm, 1);

    run_dev(sytm, 0);

    run_dev(sytm, 1);

    run_dev(sytm, 2);

    init_inboxes(inbox[cur_inbox_idx]);
    cur_inbox_idx = 1 - cur_inbox_idx;
    sytm += PERIOD_LENGTH;
  }

  // print

  /* for (int pidx = 0; pidx < num_periods; ++pidx) { */
  /*   printf("period_index: %d\n", pidx); */
  /*   for (int tid = 0; tid < NUM_TASKS; ++tid) { */
  /*     printf("  [TASK %d] ", tid); */

  /*     char inp = uinp_history[pidx][tid], */
  /* 	compl = compl_history[pidx][tid], */
  /* 	dmd = demand_history[pidx][tid], */
  /* 	ures = ures_history[pidx][tid], */
  /* 	fail = fail_history[pidx][tid]; */

  /*     if (0 <= inp) printf("I(%d) ", inp); */
  /*     if (0 <= dmd) printf("D(%d) ", dmd); */
  /*     if (0 <= ures) printf("U "); */
  /*     if (0 <= compl) printf("C "); */
  /*     if (0 <= fail) printf("X"); */

  /*     printf("\n"); */
  /*   } */
  /* } */

  // property checks

  int started = 0;
  int prev_compl1 = 0, prev_compl2 = 0;

  int lv_prds_left[3];
  int rem_demand[3];

  int vio = 0;
  int lv_max = 0;
  int max_wait = 2 + 2 * (OWNER_TIMEOUT + 1) + OWNER_TIMEOUT;

  for (int i = 0; i < 3; ++i) {
    rem_demand[i] = 0;
    lv_prds_left[i] = 0;
  }

  for (int i = 0; i < num_periods - max_wait; ++i) {
    int cur_compl1 = compl_history[i][1];
    int cur_compl2 = compl_history[i][2];

    // safety check
    int ucnt = 0;
    for (int j = 0; j < NUM_TASKS; ++j)
      if (0 < ures_history[i][j]) ++ucnt;

    if (1 < ucnt) {
      printf("safety violated at pidx: %d\n", i);
      vio = 1;
      break;
    }

    if (0 < started) {
      if ((0 < prev_compl1 && 0 < cur_compl1) ||
	  (0 < prev_compl2 && 0 < cur_compl2)) {
	// ok
      } else {
	// system service end
	/* printf("service ended at %d\n", i); */
	break;
      }
    }

    if (0 < cur_compl1 || 0 < cur_compl2) {
      if (started == 0) {
	/* printf("service started at %d\n", i); */
	started = 1;
      }
    }

    for (int j = 0; j < 3; ++j) {
      int tid_dev = j + 3;
      /* printf("DEV (i:%d, tid:%d, rem_dmd:%d, left:%d)\n", */
      /* 	     i, tid_dev, */
      /* 	     rem_demand[j], */
      /* 	     lv_prds_left[j]); */

      if (0 < demand_history[i][tid_dev]) {
	if (started == 0) {
	  /* printf("demand before start"); */
	  vio = 4;
	  break;
	}
	if (0 < rem_demand[j]) {
	  printf("double demand error\n");
	  vio = 3;
	  break;
	}

	rem_demand[j] =
	  (OWNER_TIMEOUT < demand_history[i][tid_dev])?
	  OWNER_TIMEOUT : demand_history[i][tid_dev];
	lv_prds_left[j] = max_wait;
      }

      if (0 < rem_demand[j]) {
	if (0 < fail_history[i][tid_dev]) {
	  // dev failed
	  rem_demand[j] = 0;
	  lv_prds_left[j] = 0;
	  continue;
	}

	if (lv_prds_left[j] == 0) {
	  printf("Liveness violated at prd:%d tid:%d\n", i, tid_dev);
	  vio = 2;
	} else {
	  --lv_prds_left[j];
	  if (0 < ures_history[i][tid_dev]) {
	    --rem_demand[j];
	    if (rem_demand[j] == 0)
	      if (lv_max < lv_prds_left[j]) {
		/* printf("[[%d]]\n", lv_prds_left[j]); */
		lv_max = lv_prds_left[j];
	      }
	  }
	}
      }

    }

    if (0 < vio) break;

    prev_compl1 = cur_compl1;
    prev_compl2 = cur_compl2;
  }

  if (lv_max_glob < lv_max) lv_max_glob = lv_max;

  if (0 < vio && vio < 4) {
    printf("ASSUMPTION VIOLATED %d\n", vio);
  }
}

void main(int argc, char **argv) {
  int num_periods = 30;
  int num_repets = 1;

  if (1 < argc) {
    num_periods = atoi(argv[1]);
  }
  if (2 < argc) {
    num_repets = atoi(argv[2]);
  }

  time_t seed = time(NULL);
  /* time_t seed = 1622457814; */
  srand(seed);

  printf("number of periods, repetitions: (%d, %d) with seed %ld\n",
	 num_periods, num_repets, seed);

  for (int i = 0; i < num_repets; ++i)
    run_test(num_periods);


  printf("max_wait: %d, lv_max_glob: %d\n",
	 2 + 2 * (OWNER_TIMEOUT + 1) + OWNER_TIMEOUT,
	 lv_max_glob);
}
