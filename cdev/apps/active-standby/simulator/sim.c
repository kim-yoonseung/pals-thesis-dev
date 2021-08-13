#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <stdint.h>

#define NUM_NODES 6
#define NUM_MCAST_GROUPS 1
#define MSG_SIZE 15

#define QSIZE 4
#define OWNER_TIMEOUT 3
#define NUM_DEVICES 3

#define MAX_ITER 40

typedef struct msg_entry_t {
  char received;
  char content[MSG_SIZE];
} msg_entry_t;

typedef struct inbox_t {
  msg_entry_t entry[NUM_NODES];
} inbox_t;

typedef struct msg_store_t {
  int cur_idx;
  inbox_t inbox[2][NUM_NODES];
} msg_store_t;

char TASK_ID;
int iter_glob;
msg_store_t msg_store;

char mcast_tid_map[NUM_NODES + NUM_MCAST_GROUPS][NUM_NODES + 1];

void init_mcast_tid_map() {
  for (int i = 0; i < NUM_NODES; ++i) {
    mcast_tid_map[i][0] = 1; mcast_tid_map[i][1] = i;
  }

  // mcast for controllers
  mcast_tid_map[6][0] = 2;
  mcast_tid_map[6][1] = 1; mcast_tid_map[6][2] = 2;
}


/*** Manipulating msg store */

/* void init_msg_entry(msg_entry_t *me) { */
/*   me->received = 0; */
/*   /\* for (int i = 0; i < MSG_SIZE; ++i) *\/ */
/*   /\*   me->content[i]; *\/ */
/* } */

void init_inboxes(inbox_t inb[NUM_NODES]) {
  for (int i = 0; i < NUM_NODES; ++i)
    for (int j = 0; j < NUM_NODES; ++j)
      inb[i].entry[j].received = 0;
      /* init_msg_entry(&inb[i].entry[j]); */
}

void init_msg_store() {
  msg_store.cur_idx = 0;
  init_inboxes(msg_store.inbox[0]);
  init_inboxes(msg_store.inbox[1]);
}

void switch_inboxes() {
  int cidx = msg_store.cur_idx;
  init_inboxes(msg_store.inbox[cidx]);
  msg_store.cur_idx = 1 - cidx;
}

inbox_t *get_cur_inbox(char tid) {
  return &msg_store.inbox[msg_store.cur_idx][tid];
}

inbox_t *get_nxt_inbox(char tid) {
  return &msg_store.inbox[1 - msg_store.cur_idx][tid];
}

msg_entry_t *get_dest_msg_entry(char tid_dest) {
  inbox_t *ninb = &msg_store.inbox[1 - msg_store.cur_idx][tid_dest];
  return &ninb->entry[TASK_ID];
}

void set_msg_entry(char tid, char msg[MSG_SIZE]) {
  msg_entry_t *me = get_dest_msg_entry(tid);

  if (0 < me->received) return;

  for (int i = 0; i < MSG_SIZE; ++i)
    me->content[i] = msg[i];
  me->received = 1;
}

/*** Handling failures */

// if alive, randomly fail the task
// return 1 for fail case
/* int random_fail() { */
/*   int fail_ratio = 3; */
/*   if (iter_glob < start_at[TASK_ID]) return 1; */

/*   int r = rand()%100; */
/*   if (r < fail_ratio) { */
/*     start_at[TASK_ID] = MAX_ITER; */
/*     return 1; */
/*   } */
/*   return 0; */
/* } */

/*** Sends and events */

int start_at[NUM_NODES];

// get_user_input/mark_complete/check_demand/use_resource
// -n: fail and start after (n+1)
// nonneg: succeed and return n if nat_num is to be returned
char oracle[MAX_ITER][NUM_NODES][4];

// oracle for pals_send
// -n: fail and start after (n+1)
// 0: succeed
char oracle_send[MAX_ITER][NUM_NODES][NUM_NODES+NUM_MCAST_GROUPS];

// [dead/alive][additional_info][ctrl_state..]
char node_hist[MAX_ITER][NUM_NODES][2 + MSG_SIZE];
/* char dev_hist[MAX_ITER][NUM_DEVICES][2]; */
/* char ctrl_hist[MAX_ITER][2][MSG_SIZE + 1]; */
/* char grant_hist[MAX_ITER]; */

int check_failed() {
  if (iter_glob < start_at[TASK_ID]) return 1;
  return 0;
}

void pals_send(char tid, char msg[MSG_SIZE]) {
  if (check_failed()) return;

  char ov = oracle_send[iter_glob][TASK_ID][tid];
  if (ov < 0) {
    printf("[[Failed before pals_send]]\n");
    start_at[TASK_ID] = iter_glob + ((-ov) + 1);
    return;
  }

  char *rcv_info = mcast_tid_map[tid];
  int num_rcv = rcv_info[0];

  // history
  if (TASK_ID == 1 || TASK_ID == 2) {
    if (3 <= tid) {
      // Sent grant msg
      node_hist[iter_glob][TASK_ID][1] = tid;
    }
  } else if (3 <= TASK_ID && TASK_ID < 3 + NUM_DEVICES) {
    if (msg[0] == 1) {
      // acq
      node_hist[iter_glob][TASK_ID][1] = 2;
    } else {
      // rel
      ++node_hist[iter_glob][TASK_ID][1];
    }
  }

  for (int i = 0; i < num_rcv; ++i)
    set_msg_entry(rcv_info[1 + i], msg);

}


int get_user_input() {
  if (check_failed()) return 0;

  char ov = oracle[iter_glob][TASK_ID][0];
  if (ov < 0) {
    printf("[[Failed before get_user_input]]\n");
    start_at[TASK_ID] = iter_glob + (-ov + 1);
    return 0;
  }

  if (0 < ov) {
    printf("[[Toggle!]]\n");
    node_hist[iter_glob][0][1] = 1;
    return 1;
  } else {
    return 0;
  }

  /* int toggle_ratio = 2; */
  /* int r = rand()%10; */

  /* if (r < toggle_ratio) { */
  /*   printf("[[Toggle!]]"); */
  /*   node_hist[iter_glob][0][1] = 1; */
  /*   return 1; */
  /* } */
  /* return 0; */
}

void mark_complete(uint64_t pbt) {
  if (check_failed()) return;

  char ov = oracle[iter_glob][TASK_ID][1];
  if (ov < 0) {
    printf("[[Failed before mark_complete]]\n");
    start_at[TASK_ID] = iter_glob + (-ov + 1);
    return;
  }

  printf("[[Annotation: controller %d COMPLETED %lu !]]", TASK_ID, pbt);
}

int check_demand() {
  if (check_failed()) return 0;

  char ov = oracle[iter_glob][TASK_ID][2];
  if (ov < 0) {
    printf("[[Failed before check_demand]]\n");
    start_at[TASK_ID] = iter_glob + (-ov + 1);
    return 0;
  }

  printf("[[demand: %d]]\n", ov);
  return ov;

  /* int demand_ratio = 7; */
  /* int r = rand()%10; */
  /* if (r < demand_ratio) { */
  /*   r = rand()%3; */
  /*   ++r; */
  /*   printf("[[demand: %d]]\n", r); */
  /*   return r; */
  /* } else { */
  /*   printf("[[no demands]]\n"); */
  /*   return 0; */
  /* } */
}

void use_resource() {
  if (check_failed()) return;

  char ov = oracle[iter_glob][TASK_ID][3];
  if (ov < 0) {
    printf("[[Failed before user_resource]]\n");
    start_at[TASK_ID] = iter_glob + (-ov + 1);
    return;
  }

  /* if (random_fail()) return; */

  node_hist[iter_glob][TASK_ID][1] = 3;
  printf("[[Using Resource by %d]]\n", TASK_ID);
}


/*** Job definitions */

/** Common */
const int ID_MCAST = 6;

/** Console */
char toggle_msg[MSG_SIZE] = {1,0,0,0,0,0,0,0};

void job0(uint64_t pbt, inbox_t *inbox) {
  int r = get_user_input();

  if (r == 1)
    pals_send(ID_MCAST, toggle_msg);
}

/** Controllers */

// (mode, rst, idx1, idx2, [..])
// mode = 0 / 1 / 2
// rst = OWNER_TIMEOUT + 1 / OWNER_TIMEOUT / n < OWNER_TIMEOUT
char *state;
char state1[MSG_SIZE] = {0,0,0,0,0,0,0,0};
char state2[MSG_SIZE] = {0,0,0,0,0,0,0,0};

char grant_msg[MSG_SIZE] = {1,0,0,0,0,0,0,0};

void init_ctrl_state(char *st) {
  for (int j = 0; j < MSG_SIZE; ++j) st[j] = 0;
}


void print_state(char state[MSG_SIZE]) {
  if (state[0] == 0) {
    printf("- mode: Uninitialized\n");
  }
  else if (state[0] == 1) {
    printf("- mode: Active\n");
  } else {
    printf("- mode: Standby\n");
  }

  printf("resc state: %d, (b,e) = (%d, %d) , [ ",
	 state[1], state[2], state[3]);

  for (int i = 4; i < 8; ++i)
    printf("%d ", state[i]);

  printf("]\n");
}

int adv_qidx(int i) {
  ++i;
  if (i == QSIZE) i = 0;
  return i;
}

void try_add_queue(char state[MSG_SIZE], char id_dev) {
  char qb = state[2], qe = state[3];
  char *queue = state + 4;
  char cursor = qb;
  while (cursor != qe) {
    if (queue[cursor] == id_dev) return;
    cursor = adv_qidx(cursor);
  }

  queue[qe] = id_dev;
  state[3] = adv_qidx(qe);
}

void try_release(char state[MSG_SIZE], char id_dev) {
  char rst = state[1], qb = state[2];
  char *queue = state + 4;

  // N.B. When rst == OWNER_TIMEOUT, Rel signal is sent before dev receives grant signal.
  if (queue[qb] == id_dev && 0 <= rst && rst < OWNER_TIMEOUT)
    state[1] = 0;
}

// TODO: copy all if passed check
void copy_state(char hbc[MSG_SIZE]) {
  state[1] = hbc[1];
  state[2] = 0; state[3] = 0;

  char csr = hbc[2], cend = hbc[3];
  char *queue = state + 4;
  if (csr < 0 || QSIZE <= csr || cend < 0 || QSIZE <= cend)
    return;

  while (csr != cend) {
    char tid_csr = hbc[4 + csr];
    if (tid_csr < 3 || 3 + NUM_DEVICES <= tid_csr)
      return;
    queue[csr] = tid_csr;
    csr = adv_qidx(csr);
  }

  state[2] = hbc[2]; state[3] = cend;
}

void dec_mode(char tid, char state[MSG_SIZE], inbox_t *inbox) {
  char other_tid = 3 - tid;
  msg_entry_t *con = &inbox->entry[0];
  msg_entry_t *hb = &inbox->entry[other_tid];
  int i;

  // dec_mode
  char cur_status = state[0];

  if (cur_status == 1) {
    // active
    if (0 < hb->received && 0 < con->received)
      state[0] = 2;
  } else {
    if (0 < hb->received) {
      // TODO: copy state
      copy_state(hb->content);

      if (cur_status == 2 && 0 < con->received)
	state[0] = 1;
      else state[0] = 2;
    } else {
      if (cur_status == 2) state[0] = 1;
      else {
	state[0] = tid;
	state[1] = -1;
      }
    }
  }
}

void apply_devmsg(char state[MSG_SIZE], char id_dev, msg_entry_t * me) {
  if (0 < me->received) {
    char b = me->content[0];
    if (b == 1) {
      // Sent Acquire
      try_add_queue(state, id_dev);
    } else if (b == 2) {
      // Sent Release
      try_release(state, id_dev);
    }
  }
}

void age_owner(char state[MSG_SIZE]) {
  char rst = state[1], qb = state[2];

  if (0 < rst) {
    state[1] = rst - 1;
  } else if (0 == rst) {
    state[1] = -1;
    state[2] = adv_qidx(qb);
  }
}

void update_queue(char state[MSG_SIZE], inbox_t *inbox) {
  msg_entry_t *devmsg;
  for (int i = 0; i < NUM_DEVICES; ++i) {
    char id_dev = 3 + i;
    devmsg = &inbox->entry[id_dev];
    apply_devmsg(state, id_dev, devmsg);
  }
  age_owner(state);
}

void update_istate(char tid, char state[MSG_SIZE], inbox_t *inbox) {
  dec_mode(tid, state, inbox);
  update_queue(state, inbox);
}

void update_owner(char state[MSG_SIZE]) {
  char md = state[0], rst = state[1], qb = state[2];
  char hd = state[4 + qb];

  if (md != 1) return;

  if (rst < 0 && 0 < hd) {
    state[1] = OWNER_TIMEOUT;
    pals_send(hd, grant_msg);
  }
}

void send_hb(char state[MSG_SIZE], char tid) {
  char other_tid = 3 - tid;
  pals_send(other_tid, state);
}

void job1(uint64_t pbt, inbox_t *inbox) {
  char tid = TASK_ID;

  update_istate(tid, state, inbox);
  update_owner(state);
  send_hb(state, tid);
  mark_complete(pbt);
}

void job2(uint64_t pbt, inbox_t *inbox) {
  char tid = TASK_ID;
  update_istate(tid, state, inbox);
  update_owner(state);
  send_hb(state, tid);
  mark_complete(pbt);
}


/** Devices */

char acq_msg[MSG_SIZE] = {1,0,0,0,0,0,0,0};
char rel_msg[MSG_SIZE] = {2,0,0,0,0,0,0,0};

typedef struct dev_state_t {
  char resc_status; // 0(uninit)/1(own)/2(req)/3(none)
  int count;
} dev_state_t;

dev_state_t *dstate;
dev_state_t dev_state[3];

void init_dev_state(dev_state_t *dst) {
  dst->resc_status = 0;
  dst->count = 0;
}

void print_dev_state(dev_state_t *dst) {
  printf("resource status: ");
  switch (dst->resc_status) {
  case 0:
    printf("Uninit");
    break;
  case 1:
    printf("Owned");
    break;
  case 2:
    printf("Sent Acquire");
    break;
  case 3:
    printf("None");
    break;
  }
  printf(" , count: %d\n", dst->count);
}


void update_demand(dev_state_t *state) {
  if (state->resc_status == 3) {
    int d = check_demand();
    if (OWNER_TIMEOUT < d)
      d = OWNER_TIMEOUT;
    state->count = d;
  }
}

void update_ownership(dev_state_t *state, inbox_t *inbox) {
  msg_entry_t *e1 = &inbox->entry[1], *e2 = &inbox->entry[2];

  if (state->resc_status == 0) return;

  if (e1->received || e2->received) {
    // own resource
    printf("log: Grant msg arrived\n");
    state->resc_status = 1;
  }
}

void run_device(dev_state_t *state) {
  if (state->resc_status == 1 && 0 < state->count) {
    use_resource();
    --state->count;
  }
}

void send_msg(dev_state_t *state) {
  if ((state->resc_status == 0) ||
      (state->resc_status == 1 && 0 == state->count)) {
    // release
    printf("log: sending release signal\n");
    pals_send(ID_MCAST, rel_msg);
    state->resc_status = 3;
  } else if (state->resc_status == 3 && 0 < state->count) {
    printf("log: sending acquire signal\n");
    pals_send(ID_MCAST, acq_msg);
    state->resc_status = 2;
  }
}

void job3(uint64_t pbt, inbox_t *inbox) {
  update_demand(dstate);
  update_ownership(dstate, inbox);

  run_device(dstate);
  send_msg(dstate);
}

/* void job3(uint64_t pbt, inbox_t *inbox) { */
/*   char msg[MSG_SIZE] = {}; */

/*   if (dstate->resc_status == 0) { */
/*     dstate->resc_status = 3; */
/*     dstate->count = 0; */
/*     pals_send(ID_MCAST, rel_msg); */
/*   } else { */
/*     update_demand_status(dstate); */
/*     check_grant_msg(dstate, inbox); */

/*     run_device(dstate); */
/*     send_msg(dstate); */
/*   } */
/* } */

void job4(uint64_t pbt, inbox_t *inbox) {
  update_demand(dstate);
  update_ownership(dstate, inbox);

  run_device(dstate);
  send_msg(dstate);
}

void job5(uint64_t pbt, inbox_t *inbox) {
  update_demand(dstate);
  update_ownership(dstate, inbox);

  run_device(dstate);
  send_msg(dstate);
}

/* end jobs */

void print_msg_entry(msg_entry_t *me) {
  if (0 == me->received) {
    printf("empty");
  } else {
    for (int i = 0; i < MSG_SIZE; ++i)
      printf("%d ", me->content[i]);
  }
}

void print_inbox(inbox_t *inbox) {
  for (int i = 0; i < NUM_NODES; ++i) {
    printf(" [%d]: ", i);
    print_msg_entry(&inbox->entry[i]);
  }
  printf("\n");
}

void run_job(uint64_t pbt) {
  char tid = TASK_ID;
  inbox_t *inbox = get_cur_inbox(tid);
  int r;

  if (iter_glob < start_at[tid]) {
    if (MAX_ITER <= start_at[tid]) {
      r = rand()%2;
      if (r < 1) start_at[tid] = iter_glob + 1;
    }
    // mark as dead node
    node_hist[iter_glob][tid][0] = 1;

    return;
  }

  printf("[[ Job %d Begin ]]\n", tid);
  print_inbox(inbox);

  switch (tid) {
  case 0:
    job0(pbt, inbox);
    break;
  case 1:
    state = state1;
    print_state(state);
    job1(pbt, inbox);
    print_state(state);
    break;
  case 2:
    state = state2;
    print_state(state);
    job2(pbt, inbox);
    print_state(state);
    break;
  case 3:
    dstate = &dev_state[0];
    print_dev_state(dstate);
    job3(pbt, inbox);
    print_dev_state(dstate);
    break;
  case 4:
    dstate = &dev_state[1];
    print_dev_state(dstate);
    job4(pbt, inbox);
    print_dev_state(dstate);
    break;
  case 5:
    dstate = &dev_state[2];
    print_dev_state(dstate);
    job5(pbt, inbox);
    print_dev_state(dstate);
    break;
  }

  if (iter_glob < start_at[tid]) {
    // failed during the period

    // init state
    if (tid == 1 || tid == 2) {
      init_ctrl_state(state);
    } else if (3 <= tid && tid < 3 + NUM_DEVICES) {
      // init state
      init_dev_state(dstate);
    }

    // mark as dead node
    node_hist[iter_glob][tid][0] = 1;
  }

  if (tid == 1 || tid == 2)
    for (int i = 0; i < MSG_SIZE; ++i)
      node_hist[iter_glob][tid][2 + i] = state[i];
}

/*** printing history */

void sprint_con_hist(char *buf, int iter) {
  buf[0] = ' '; buf[1] = ' ';
  if (0 < node_hist[iter][0][1])
    buf[0] = 'T';
  if (0 < node_hist[iter][0][0])
    buf[1] = 'X';
}

void sprint_ctrl_hist(char *buf, int iter, char tid) {
  buf[0] = ' '; buf[1] = ' ';
  if (0 < node_hist[iter][tid][1])
    buf[0] = '0' + node_hist[iter][tid][1];
  if (0 < node_hist[iter][tid][0])
    buf[1] = 'X';
}

void sprint_dev_hist(char *buf, int iter, char tid) {
  buf[0] = ' '; buf[1] = ' ';

  switch (node_hist[iter][tid][1]) {
  case 2:
    buf[0] = 'A';
    break;
  case 3:
    buf[0] = 'U';
    break;
  case 4:
    buf[0] = 'u';
    break;
  case 1:
    buf[0] = 'E';
    break;
  }

  if (0 < node_hist[iter][tid][0]) {
    buf[1] = 'X';
  }
}

void print_ctrl_state_hist(int iter, int k) {
  char *st = &node_hist[iter][k][2];
  printf(" <");
  if (st[0] == 1) {
    printf("A ");
  } else if (st[0] == 2) {
    printf("S ");
  } else {
    printf("U>");
    return;
  }

  printf("(%d) [", st[1]);

  int c = st[2], e = st[3];
  while (c != e) {
    printf(" %d", st[4 + c]);
    c = adv_qidx(c);
  }
  printf(" ] ");

  printf("> ");
}

/* void print_grant_hist(int iter) { */
/*   int g = grant_hist[iter]; */
/*   if (0 < g) */
/*     printf(" Grant: %d ", g); */
/* } */

int check_valid_hist_ctrl(char tid) {
  char otid = 3 - tid;

  for (int i = 1; i < MAX_ITER; ++i) {
    if (0 == node_hist[i - 1][tid][0] && 0 < node_hist[i][tid][0]) {
      // if this task failed at i
      if (0 < node_hist[i - 1][otid][0]) {
	return 0;
      } else if (0 < node_hist[i][otid][0]) {
	return 0;
      }
    }
  }

  return 1;
}

int check_valid_hist_devs() {
  // get first run of controller
  int fst = -1;
  for (int i = 0; i < MAX_ITER; ++i) {
    if (0 == node_hist[i][1][0] || 0 == node_hist[i][2][0]) {
      fst = i;
      break;
    }
  }

  if (fst < 0) return 0;

  for (int i = 0; i <= fst; ++i) {
    for (int j = 0; j < NUM_DEVICES; ++j) {
      if (0 == node_hist[i][3 + j][0])
	return 0;
    }
  }

  return 1;
}

int check_valid_hist() {
  if (check_valid_hist_ctrl(1) && check_valid_hist_ctrl(2) &&
      check_valid_hist_devs())
    return 1;

  return 0;
}

void init_history() {
  for (int i = 0; i < MAX_ITER; ++i)
    for (int j = 0; j < NUM_NODES; ++j)
      for (int k = 0; k < 2 + MSG_SIZE; ++k)
	node_hist[i][j][k] = 0;
}

void set_oracle() {
  // Set initial start time
  start_at[0] = 0; start_at[1] = 2; start_at[2] = 1;
  start_at[3] = 4; start_at[4] = 6; start_at[5] = 5;

  oracle[10][0][0] = 1; // toggle
  oracle[10][1][1] = -3; // annotate fail for 3+1 prds
  oracle[10][3][2] = 2; // demand: 2

  oracle[12][4][2] = 1; // demand: 1
  oracle[12][5][2] = 2; // demand: 2

  oracle[13][3][2] = 1; // demand: 1

  oracle[13][4][2] = -5; // demand fail for 5+1 prds
}

void set_rand_oracle() {
  start_at[0] = 0; start_at[1] = 2; start_at[2] = 1;
  start_at[3] = 4; start_at[4] = 6; start_at[5] = 5;
  int r, v;
  int fail_ratio = 15, fail_max = 5;
  int toggle_ratio = 20, demand_max = 5;

  // get_user_input
  for (int i = 0; i < MAX_ITER; ++i) {
    v = 0;
    r = rand()%100;
    if (r < fail_ratio) {
      v = - (rand()%fail_max);
    } else {
      r = rand()%100;
      if (r < toggle_ratio) v = 1;
    }
    oracle[i][0][0] = v;
  }

  for (int tid = 1; tid <= 2; ++tid)
    // mark_complete
    for (int i = 0; i < MAX_ITER; ++i) {
      v = 0;
      r = rand()%100;
      if (r < fail_ratio) {
	v = - (rand()%fail_max);
      }
      oracle[i][tid][1] = v;
    }

  for (int tid = 3; tid <= 3 + NUM_DEVICES; ++tid) {
    // check_demand
    for (int i = 0; i < MAX_ITER; ++i) {
      v = 0;
      r = rand()%100;
      if (r < fail_ratio) {
	v = - (rand()%fail_max);
      } else {
	v = rand()%demand_max;
      }
      oracle[i][tid][2] = v;
    }

    // use_resource
    for (int i = 0; i < MAX_ITER; ++i) {
      v = 0;
      r = rand()%100;
      if (r < fail_ratio) {
	v = - (rand()%fail_max);
      }
      oracle[i][tid][3] = v;
    }
  }
}

int main() {
  int i, j;

  time_t seed = time(0);
  printf("seed: %ld\n", seed);
  srand(seed);

  /* set_oracle(); */
  set_rand_oracle();

  init_mcast_tid_map();
  init_msg_store();

  int loop = 1;
  uint64_t prd = 10, pbt0 = 1000;

  while(loop) {
    // init states
    init_history();
    init_ctrl_state(state1);
    init_ctrl_state(state2);
    init_dev_state(&dev_state[0]);
    init_dev_state(&dev_state[1]);
    init_dev_state(&dev_state[2]);

    for (i = 0; i < MAX_ITER; ++i) {
      iter_glob = i;
      uint64_t pbt = pbt0 + i * prd;
      printf("------------ PERIOD %d Begin ------------\n", i);
      for (char j = 0; j < NUM_NODES; ++j) {
        /* decide_alive_status(i, j, init_time[j]); */
        TASK_ID = j;
        run_job(pbt);
      }
      switch_inboxes();
    }

    printf("History %d\n", loop);

    for (i = 0; i < MAX_ITER; ++i) {
      printf("%2d :", i);

      char buf[2];

      sprint_con_hist(buf, i);
      printf(" | %s", buf);

      sprint_ctrl_hist(buf, i, 1);
      printf(" | %s", buf);
      sprint_ctrl_hist(buf, i, 2);
      printf(" | %s", buf);

      sprint_dev_hist(buf, i, 3);
      printf(" | %s", buf);
      sprint_dev_hist(buf, i, 4);
      printf(" | %s", buf);
      sprint_dev_hist(buf, i, 5);
      printf(" | %s", buf);

      printf(" |     ");

      // print controller states
      print_ctrl_state_hist(i, 1);
      print_ctrl_state_hist(i, 2);
      printf("\n");

      /* for (j = 0; j < NUM_DEVICES; ++j) { */
      /*   char c1, c2 = ' '; */
      /*   switch (dev_hist[i][j][0]) { */
      /*   case 2: */
      /*   	c1 = 'A'; */
      /*   	break; */
      /*   case 3: */
      /*   	c1 = 'U'; */
      /*   	break; */
      /*   case 4: */
      /*   	c1 = 'R'; */
      /*   	break; */
      /*   case 1: */
      /*   	c1 = 'E'; */
      /*   	break; */
      /*   default: */
      /*   	c1 = ' '; */
      /*   } */

      /*   if (0 < dev_hist[i][j][1]) */
      /*   	c2 = 'X'; */

      /*   printf("| %c%c ", c1, c2); */
      /* } */
      /* printf("|     "); */

      /* print_ctrl_hist(i, 0); */
      /* print_ctrl_hist(i, 1); */
      /* print_grant_hist(i); */
      /* printf("\n"); */
    }

    if (check_valid_hist()) {
      loop = 0;
    } else {
      set_rand_oracle();
      ++loop;
    }
  }
}
