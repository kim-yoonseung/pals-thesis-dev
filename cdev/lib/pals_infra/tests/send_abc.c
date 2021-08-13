#include "pals_infra.h"

#include <string.h>
#include <stdio.h>
#include <stdint.h>

int main() {
  int port = 33333;
  int s = pals_socket();
  char ip_addr[20];

  printf("Enter destination IP ..\n");
  scanf("%s", ip_addr);
  printf("Gets %s\n", ip_addr);

  if (strlen(ip_addr) < 3) {
    printf("sending to localhost..\n");
    strcpy(ip_addr, "127.0.0.1");
  }

  pals_sendto(s, ip_addr, port, "abc", 3);

  printf("msg [abc] sent to (%s, %d) \n", ip_addr, port);
  return 0;
}
