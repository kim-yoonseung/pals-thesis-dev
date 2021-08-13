#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define MAX_TOUT 5
#define NUM_HIST 10000

const int fail_ratio = 10;
const int max_demand = 8;
const int reboot_ratio = 3;

typedef struct Ctrl {
  int timeout;

  int qsz;
  int queue[4];
} Ctrl;

typedef struct Dev {
  int state; // fail = 0 / init = 1 / running = 2

  int is_owner;
  int demand;
} Dev;

Ctrl ctrl;
Dev devs[3];

int inbox_ctrl[3];
int outbox_ctrl[3];

int inbox_dev[3];
int outbox_dev[3];



int demand_history[NUM_HIST][3];
int use_history[NUM_HIST][3];
int fail_history[NUM_HIST][3];

int period;



int rand_fail() {
  int r = rand() % fail_ratio;
  if (r == 0) return 1;
  else return 0;
}

int rand_reboot() {
  int r = rand() % reboot_ratio;
  if (r == 0) return 1;
  else return 0;
}

int rand_demand(int tidx) {
  int r = rand() % max_demand;
  demand_history[period][tidx] = r;
  return r;
}


void try_add_queue(int tid) {
  int i = 0;
  for (i = 0; i < ctrl.qsz; ++i) {
    if (ctrl.queue[i] == tid) return;
  }
  ctrl.queue[i] = tid;
  ctrl.qsz = ctrl.qsz + 1;
}

void try_rel_queue(int tid) {
  if (0 < ctrl.qsz && ctrl.queue[0] == tid) {
    if (0 < ctrl.timeout && ctrl.timeout < MAX_TOUT)
      ctrl.timeout = 1;
    else
      return;
  }
}

void remove_hd() {
  if (0 < ctrl.qsz) {
    for (int i = 1; i < ctrl.qsz; ++i) {
      ctrl.queue[i-1] = ctrl.queue[i];
    }
    ctrl.qsz = ctrl.qsz - 1;
  }
}

void ctrl_update() {
  // update
  int i;
  for (i = 0; i < 3; ++i) {
    int tid = i + 1;
    int m = inbox_ctrl[i];

    if (m == 1) {
      try_add_queue(tid);
    } else if (m == 2) {
      try_rel_queue(tid);
    }
  }

  // reduce_timeout
  if (ctrl.timeout == 1) {
    ctrl.timeout = 0;
    remove_hd();
  } else if (1 < ctrl.timeout) {
    ctrl.timeout = ctrl.timeout - 1;
  }
}

void send_grant() {
  if (ctrl.timeout == 0 && 0 < ctrl.qsz) {
    if (rand_fail()) return;
    /* printf("sent grant to %d\n", ctrl.queue[0]); */
    outbox_ctrl[ctrl.queue[0] - 1] = 1;

    if (rand_fail()) return;
    ctrl.timeout = MAX_TOUT;
  }
}

void job_ctrl() {
  ctrl_update();
  send_grant();
}


/* dev */

int fail_dev(int tidx) {
  if (rand_fail()) {
    devs[tidx].state = 0;
    devs[tidx].is_owner = 0;
    devs[tidx].demand = 0;

    fail_history[period][tidx] = 1;
    return 1;
  }
  return 0;
}

void update_ownership(int tidx) {
  /* printf("inbox[%d]: %d\n", tidx, inbox_dev[tidx]); */
  if (inbox_dev[tidx] == 1) {
    devs[tidx].is_owner = 1;
  }
}

int update_demand(int tidx) {
  if (0 == devs[tidx].demand) {
    int d = rand_demand(tidx);
    if (MAX_TOUT < d) d = MAX_TOUT;

    devs[tidx].demand = d;

    return 1;
  }
  return 0;
}

void use_res(int tidx) {
  if ((devs[tidx].is_owner == 1) &&
      (0 < devs[tidx].demand)) {
    use_history[period][tidx] = 1;
    devs[tidx].demand = devs[tidx].demand - 1;
  }
}

void send_msg(int dupd, int tidx) {
  if ((devs[tidx].is_owner == 1) &&
      (devs[tidx].demand == 0)) {
    outbox_dev[tidx] = 2; // Release
    devs[tidx].is_owner = 0;
  } else if ((devs[tidx].is_owner == 0) &&
	     (0 < devs[tidx].demand) &&
	     (0 < dupd)) {
    outbox_dev[tidx] = 1; // Acquire
  }
}

void job_dev(int tidx, Dev *d) {
  int r;
  if (d->state == 0) {
    if (rand_reboot())
      d->state = 1;
  } else if (d->state == 1) {
    if (fail_dev(tidx)) return;
    outbox_dev[tidx] = 2; // Release

    if (fail_dev(tidx)) return;
    d->state = 2;
    d->is_owner = 0;
    d->demand = 0;
  } else {
    // running

    int dupd;
    update_ownership(tidx);
    if (fail_dev(tidx)) return;

    dupd = update_demand(tidx);
    if (fail_dev(tidx)) return;

    use_res(tidx);
    if (fail_dev(tidx)) return;

    send_msg(dupd, tidx);
    if (fail_dev(tidx)) return;
  }
}

void print_ctrl() {
  printf("timeout: %d, qsz: %d, [",
	 ctrl.timeout, ctrl.qsz);
  for (int i = 0; i < ctrl.qsz; ++i){
    printf("%d ", ctrl.queue[i]);
  }
  printf("] ");
}

void print_dev(Dev *d) {
  printf("state: %d, is_owner: %d, demand: %d\n",
	 d->state, d->is_owner, d->demand);
}


void run_ctrl_test() {
  printf("[ try_add_queue ]\n");

  ctrl.timeout = 5;
  ctrl.qsz = 2;
  ctrl.queue[0] = 3;
  ctrl.queue[1] = 1;

  printf("before add\n");
  print_ctrl();

  try_add_queue(2);

  printf("after add 2\n");
  print_ctrl();

  try_add_queue(3);

  printf("after add 3\n");
  print_ctrl();

  printf("[ try_rel_queue ]\n");

  try_rel_queue(1);
  printf("after rel 1\n");
  print_ctrl();

  try_rel_queue(3);
  printf("after rel 3\n");
  print_ctrl();

  remove_hd();

  printf("after remove_hd\n");
  print_ctrl();


  printf("[ ctrl_update 1 ]\n");

  ctrl.timeout = 3;
  ctrl.qsz = 2;
  ctrl.queue[0] = 3;
  ctrl.queue[1] = 1;

  inbox_ctrl[0] = 2;
  inbox_ctrl[1] = 1;
  inbox_ctrl[2] = 0;

  print_ctrl();
  ctrl_update();
  printf("after update 1 \n");
  print_ctrl();


  printf("[ ctrl_update 2 ]\n");

  ctrl.timeout = 1;
  ctrl.qsz = 2;
  ctrl.queue[0] = 3;
  ctrl.queue[1] = 1;

  inbox_ctrl[0] = 2;
  inbox_ctrl[1] = 1;
  inbox_ctrl[2] = 0;

  print_ctrl();
  ctrl_update();
  printf("after update 1 \n");
  print_ctrl();


  printf("[ ctrl_update 3 ]\n");

  ctrl.timeout = 3;
  ctrl.qsz = 2;
  ctrl.queue[0] = 3;
  ctrl.queue[1] = 1;

  inbox_ctrl[0] = 2;
  inbox_ctrl[1] = 1;
  inbox_ctrl[2] = 2;

  print_ctrl();
  ctrl_update();
  printf("after update 3 \n");
  print_ctrl();


  printf("[ send_grant ]\n");

  ctrl.timeout = 0;
  ctrl.qsz = 2;
  ctrl.queue[0] = 3;
  ctrl.queue[1] = 1;

  outbox_ctrl[0] = 0;
  outbox_ctrl[1] = 0;
  outbox_ctrl[2] = 0;

  printf("before send_grant\n");
  print_ctrl();
  send_grant();
  printf("after send_grant\n");
  print_ctrl();
  printf("outbox: [ %d %d %d ]\n",
	 outbox_ctrl[0], outbox_ctrl[1],
	 outbox_ctrl[2]);


  printf("[ send_grant ]\n");

  ctrl.timeout = 0;
  ctrl.qsz = 2;
  ctrl.queue[0] = 3;
  ctrl.queue[1] = 1;

  outbox_ctrl[0] = 0;
  outbox_ctrl[1] = 0;
  outbox_ctrl[2] = 0;

  printf("before send_grant\n");
  print_ctrl();
  send_grant();
  printf("after send_grant\n");
  print_ctrl();
  printf("outbox: [ %d %d %d ]\n",
	 outbox_ctrl[0], outbox_ctrl[1],
	 outbox_ctrl[2]);



  printf("[ send_grant ]\n");

  ctrl.timeout = 0;
  ctrl.qsz = 2;
  ctrl.queue[0] = 3;
  ctrl.queue[1] = 1;

  outbox_ctrl[0] = 0;
  outbox_ctrl[1] = 0;
  outbox_ctrl[2] = 0;

  printf("before send_grant\n");
  print_ctrl();
  send_grant();
  printf("after send_grant\n");
  print_ctrl();
  printf("outbox: [ %d %d %d ]\n",
	 outbox_ctrl[0], outbox_ctrl[1],
	 outbox_ctrl[2]);


  printf("[ send_grant ]\n");

  ctrl.timeout = 0;
  ctrl.qsz = 2;
  ctrl.queue[0] = 3;
  ctrl.queue[1] = 1;

  outbox_ctrl[0] = 0;
  outbox_ctrl[1] = 0;
  outbox_ctrl[2] = 0;

  printf("before send_grant\n");
  print_ctrl();
  send_grant();
  printf("after send_grant\n");
  print_ctrl();
  printf("outbox: [ %d %d %d ]\n",
	 outbox_ctrl[0], outbox_ctrl[1],
	 outbox_ctrl[2]);


  printf("[ send_grant ]\n");

  for (int j = 0; j < 20; ++j) {
    ctrl.timeout = 0;
    ctrl.qsz = 2;
    ctrl.queue[0] = 3;
    ctrl.queue[1] = 1;

    outbox_ctrl[0] = 0;
    outbox_ctrl[1] = 0;
    outbox_ctrl[2] = 0;

    printf("before send_grant\n");
    print_ctrl();
    send_grant();
    printf("after send_grant\n");
    print_ctrl();
    printf("outbox: [ %d %d %d ]\n",
	   outbox_ctrl[0], outbox_ctrl[1],
	   outbox_ctrl[2]);
    printf("==== \n");
  }
  printf("[ send_grant end ]\n");



}



void initialize() {
  ctrl.timeout = 0;
  ctrl.qsz = 0;

  devs[0].state = 0;
  devs[0].is_owner = 0;
  devs[0].demand = 0;

  devs[1].state = 0;
  devs[1].is_owner = 0;
  devs[1].demand = 0;

  devs[2].state = 0;
  devs[2].is_owner = 0;
  devs[2].demand = 0;

  for (int i = 0; i < 3; ++i) {
    inbox_ctrl[i] = 0;
    inbox_dev[i] = 0;
    outbox_ctrl[i] = 0;
    outbox_dev[i] = 0;
  }

  for (int i = 0; i < NUM_HIST; ++i) {
    for (int j = 0; j < 3; ++j) {
      demand_history[i][j] = 0;
      use_history[i][j] = 0;
      fail_history[i][j] = 0;
    }
  }

  period = 0;

}


int verify_safety() {
  int vflag = 0;
  for (int i = 0; i < NUM_HIST; ++i) {
    int sum = use_history[i][0] + use_history[i][1] +
      use_history[i][2];

    if (1 < sum) {
      printf("SAFETY VIOLATED at %d\n", i);
      vflag = 1;
    }
  }

  return vflag;
}

int verify_liveness(int *lv) {
  int pmax_cnt = 0;

  int vflag = 0;
  int MAX = 2 + 2 * (MAX_TOUT + 1) + MAX_TOUT;
  /* printf("MAX: %d\n", MAX); */

  for (int i = 0; i < NUM_HIST - MAX; ++i)
    for (int j = 0; j < 3; ++j)
      if (0 < demand_history[i][j]) {
	int d = demand_history[i][j];
	if (MAX_TOUT < d) d = MAX_TOUT;

	int ucnt = 0;
	for (int k = 0; k < MAX; ++k) {
	  if (fail_history[i + k][j]) {
	    ucnt = -1;
	    break;
	  }
	  ucnt += use_history[i + k][j];
	  if (d <= ucnt) {
	    if (pmax_cnt < k)
	      pmax_cnt = k;
	    break;
	  }
	}

	if (ucnt < 0) {
	  /* printf("Dev failed\n"); */
	} else if (d <= ucnt) {
	  /* printf("All uses found\n"); */
	} else {
	  vflag = 1;
	  printf("VIOLATION: demands: %d, uses found = %d\n", d, ucnt);
	  printf("%d %d\n", i, j);
	}
      }

  /* printf("maximum_periods: %d\n", pmax_cnt); */
  *lv = pmax_cnt;
  return vflag;
}

int verify_history() {
  int lv;

  int r1 = verify_safety();
  if (0 < r1) printf("safety violated\n");
  /* else printf("safety holds\n"); */

  int r2 = verify_liveness(&lv);
  if (0 < r2) printf("liveness violated\n");
  /* else printf("liveness holds\n"); */

  return lv;
}


int run_test() {

  initialize();

  srand(time(NULL));

  for (int i = 0; i < NUM_HIST; ++i) {
    period = i;
    job_ctrl();
    job_dev(0, &devs[0]);
    job_dev(1, &devs[1]);
    job_dev(2, &devs[2]);

    inbox_ctrl[0] = outbox_dev[0];
    inbox_ctrl[1] = outbox_dev[1];
    inbox_ctrl[2] = outbox_dev[2];

    inbox_dev[0] = outbox_ctrl[0];
    inbox_dev[1] = outbox_ctrl[1];
    inbox_dev[2] = outbox_ctrl[2];

    for (int j = 0; j < 3; j++) {
      outbox_ctrl[j] = 0;
      outbox_dev[j] = 0;
    }

    /* printf("period %d: ", i); */
    /* for (int j = 0; j < 3; ++j) { */
    /*   if (demand_history[i][j] != 0) */
    /* 	printf("D[%d] ", demand_history[i][j]); */
    /*   else */
    /* 	printf(".... "); */

    /*   if (use_history[i][j] != 0) */
    /* 	printf("U "); */
    /*   else */
    /* 	printf(". "); */
    /*   if (fail_history[i][j] != 0) */
    /* 	printf("X"); */
    /*   else */
    /* 	printf(". "); */

    /*   printf("\t|"); */

    /* } */
    /* print_ctrl(); */
    /* printf("\n"); */
  }

  verify_history();
}

void main(int argc, char **argv) {
  int k;
  if (argc < 2) k = 10;
  else k = atoi(argv[1]);

  printf("k= %d\n", k);

  int MAX = 2 + 2 * (MAX_TOUT + 1) + MAX_TOUT;
  printf("MAX: %d\n", MAX);

  int max_lv = 0;

  for (int i = 0; i < k; ++i) {
    int lv = run_test();
    if (max_lv < lv) max_lv = lv;
  }

  printf("MAX_LV: %d\n", max_lv);

}
