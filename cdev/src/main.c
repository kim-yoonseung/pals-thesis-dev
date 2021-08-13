#include "pals_infra.h"
#include "main.h"
#include "app.h"

#include <stdio.h>
#include <stdint.h>

// Total bytesize: [ 8 * _MSG_SIZE_K + 7 ]
typedef struct pals_msg_t {
  uint64_t period_base_time;
  char sender;
  char content[_MAX_MSG_SIZE];
} pals_msg_t;

typedef struct msg_store_t {
  int cur_idx;
  inbox_t inbox[2];
} msg_store_t;


pals_msg_t send_buf;
msg_store_t mstore;
char send_hist[_MAX_NUM_TASKS];
int txs, rxs;

inbox_t *get_cur_inbox() {
  return &mstore.inbox[mstore.cur_idx];
}

inbox_t *get_nxt_inbox() {
  return &mstore.inbox[1 - mstore.cur_idx];
}

void msg_copy(const char *src, char *dst) {
  for (int i = 0; i < MSG_SIZE; ++i)
    dst[i] = src[i];
}

int check_send_hist(char id_dest) {
  int i;

  if (id_dest < NUM_TASKS) {
    // unicast
    if (send_hist[id_dest] == 0) {
      send_hist[id_dest] = 1;
      return 1;
    } else
      return 0;
  } else if (id_dest < NUM_TASKS + NUM_MCASTS) {
    // multicast
    const char * group_mem =
      MCAST_MEMBER[id_dest - NUM_TASKS];
    for (i = 0; i < NUM_TASKS; ++i)
      if (0 < group_mem[i])
	if (0 < send_hist[i]) return 0;

    for (i = 0; i < NUM_TASKS; ++i)
      if (0 < group_mem[i]) send_hist[i] = 1;

    return 1;
  }
  return 0;
}

void reset_send_hist() {
  for (int i = 0; i < NUM_TASKS; ++i)
    send_hist[i] = 0;
}

// length(msg) = MSG_SIZE
void pals_send(char tid, char *msg) {
  if (check_send_hist(tid)) {
    const char *dest_ip = IP_ADDR[tid];

    msg_copy(msg, send_buf.content);
    pals_sendto(txs, dest_ip, PORT,
		(char*)&send_buf, MSG_SIZE + 9);
  }
}

uint64_t get_base_time(uint64_t p, uint64_t tm) {
  return tm - (tm % p);
}

void mcast_join(int rxs) {
  for (int i = 0; i < NUM_MCASTS; ++i) {
    const char * group_mem = MCAST_MEMBER[i];
    if (0 < group_mem[TASK_ID])
      pals_mcast_join(rxs, IP_ADDR[NUM_TASKS + i]);
  }
}

// length(c) = MSG_SIZE
void insert_msg(msg_entry_t *me, char sender_id,
		char *c) {
  if (0 <= sender_id && sender_id < NUM_TASKS) {
    me[sender_id].received = 1;
    msg_copy(c, me[sender_id].content);
  }
}

void fetch_msgs(int rxs, uint64_t cur_base_time) {
  uint64_t nxt_base_time = cur_base_time + PALS_PERIOD;
  msg_entry_t *cptr = get_cur_inbox()->entry,
    *nptr = get_nxt_inbox()->entry;
  pals_msg_t buf;
  int pld_size = MSG_SIZE + 9;

  for (int i = 0; i < NUM_TASKS * 4; ++i) {
    int sz = pals_recvfrom(rxs, (char*)&buf, pld_size);
    if (sz < 0) return;
    if (sz != pld_size) continue;
    if (buf.sender < 0) continue;

    if (buf.period_base_time == cur_base_time) {
      // in cptr
      insert_msg(cptr, buf.sender, buf.content);
    } else if (buf.period_base_time == nxt_base_time) {
      // in nptr
      insert_msg(nptr, buf.sender, buf.content);
    }
    // else ignore
  }
}

void init_inbox(inbox_t *inb) {
  for (int i = 0; i < NUM_TASKS; ++i)
    inb->entry[i].received = 0;
}

void switch_inbox() {
  int cidx = mstore.cur_idx;
  init_inbox(&mstore.inbox[cidx]);
  mstore.cur_idx = 1 - cidx;
}

void run_task(uint64_t cur_base_time) {
  uint64_t pprd = PALS_PERIOD,
    dlt = 2 * MAX_CSKEW + MAX_NWDELAY,
    maxt = UINT64_MAX - 10 * PALS_PERIOD;

  while (cur_base_time < maxt) {
    send_buf.period_base_time = cur_base_time + pprd;

    pals_wait_timer(cur_base_time);
    fetch_msgs(rxs, cur_base_time);

    job(cur_base_time, get_cur_inbox());

    cur_base_time += pprd;

    reset_send_hist();
    switch_inbox();
  }
}

int main() {
  uint64_t tm, nxt_base_time,
    pprd = PALS_PERIOD,
    dlt = 2 * MAX_CSKEW + MAX_NWDELAY,
    maxt = UINT64_MAX - 10 * PALS_PERIOD;
  int ret;

  send_buf.sender = TASK_ID;
  ret = pals_init_timer();
  if (ret < 0) return 0;

  tm = pals_current_time();
  if (tm == 0 || !(tm < maxt)) return 0;
  nxt_base_time = get_base_time(pprd, tm) + 2 * pprd;

  // Open sockets
  txs = pals_socket();
  rxs = pals_socket();
  if (txs < 0 || rxs < 0) return 0;

  // Begin receiving msgs after nxt_base_time
  pals_wait_timer(nxt_base_time);

  ret = pals_bind(rxs, PORT);
  if (ret < 0) return 0;

  mcast_join(rxs);

  nxt_base_time += 2 * pprd;
  run_task(nxt_base_time);

  return 0;
}
