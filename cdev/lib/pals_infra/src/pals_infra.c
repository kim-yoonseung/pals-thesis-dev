/* pals_infra */
/* TCB for verification of PALSware  */

#include "pals_infra.h"

#include <time.h>
#include <sys/timerfd.h>
#include <unistd.h>

#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <fcntl.h>
#include <endian.h>

#include <string.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

#define TIMER_GIGA_NS 1000000000L

// timer
int timer_id = -1;
uint64_t timelimit = 0;

uint64_t pals_current_time(void) {
  struct timespec tspec;
  int r = clock_gettime(CLOCK_REALTIME, &tspec);
  if (r < 0)
    return (uint64_t)0;
  else
    return ((uint64_t)tspec.tv_sec * TIMER_GIGA_NS + (uint64_t)tspec.tv_nsec);
}

int pals_init_timer(void) {
  timer_id = timerfd_create(CLOCK_REALTIME, 0);
  return (0 > timer_id ? (-1) : 0) ;
}

int pals_wait_timer(uint64_t time) {
  struct itimerspec setting_val;
  uint64_t spended_period;

  setting_val.it_value.tv_sec = time / TIMER_GIGA_NS;
  setting_val.it_value.tv_nsec = time % TIMER_GIGA_NS;

  setting_val.it_interval.tv_sec = 0L;
  setting_val.it_interval.tv_nsec = 0L;

  int r = timerfd_settime(timer_id, TFD_TIMER_ABSTIME, &setting_val, NULL);
  if (r < 0) return r;
  read(timer_id, &spended_period, sizeof(spended_period));
  return 0;
}

// sockets
int pals_socket(void) {
  int sock = socket(AF_INET, SOCK_DGRAM, 0);
  if (sock < 0) return -1;

  int opt_val = 1, opt_val_0 = 0;

  setsockopt(sock, IPPROTO_IP, IP_MULTICAST_TTL, (void *)&opt_val, sizeof(opt_val));
  setsockopt(sock, IPPROTO_IP, IP_MULTICAST_LOOP, (void *)&opt_val_0, sizeof(opt_val_0));
  setsockopt(sock, SOL_SOCKET, SO_REUSEADDR, &opt_val, sizeof(opt_val));

  int flag = fcntl(sock, F_GETFL, 0);
  fcntl(sock, F_SETFL, flag | O_NONBLOCK);

  return sock;
}

int pals_bind(int s, int port) {
  struct sockaddr_in saddr;
  bzero(&saddr, sizeof(struct sockaddr_in));

  saddr.sin_family = AF_INET;
  saddr.sin_addr.s_addr = INADDR_ANY;
  saddr.sin_port = htons(port);

  int ret = bind(s, (struct sockaddr *)&saddr, sizeof(saddr));

  return ret;
}

void pals_mcast_join(int s, const char *mcast_ip) {
  struct ip_mreq imreq;
  bzero(&imreq, sizeof(struct ip_mreq));

  imreq.imr_multiaddr.s_addr = inet_addr(mcast_ip);
  imreq.imr_interface.s_addr = htonl(INADDR_ANY);

  //join multicast group
  setsockopt(s, IPPROTO_IP, IP_ADD_MEMBERSHIP,
	     (void *)&imreq, sizeof(struct ip_mreq));
}

// network

int pals_sendto(int s, const char *dest_ip, int port,
		char *buf, int sz) {
  struct sockaddr_in saddr;
  bzero(&saddr, sizeof(struct sockaddr_in));

  saddr.sin_family = AF_INET;
  saddr.sin_addr.s_addr = inet_addr(dest_ip);
  saddr.sin_port = htons(port);

  return sendto(s, buf, sz, 0, (struct sockaddr *)&saddr, sizeof(saddr));

}

int pals_recvfrom(int s, char* buf, int sz) {
  struct sockaddr_in saddr; // not used
  socklen_t slen = sizeof(struct sockaddr_in);

  return recvfrom(s, buf, sz, 0, (struct sockaddr *)&saddr, &slen);
}
