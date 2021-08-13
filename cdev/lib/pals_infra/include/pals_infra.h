#include <stdint.h>

// timer
uint64_t pals_current_time(void);
int pals_init_timer(void);
int pals_wait_timer(uint64_t);

// sockets
int pals_socket(void);
int pals_bind(int s, int port);
void pals_mcast_join(int s, const char *mip);

// network
int pals_sendto(int s, const char *ip, int port, char* buf, int sz);
int pals_recvfrom(int s, char* buf, int sz);
