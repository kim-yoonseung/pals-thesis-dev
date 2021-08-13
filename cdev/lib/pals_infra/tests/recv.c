#include "pals_infra.h"

#include <stdio.h>
#include <stdint.h>

int main() {
  int port = 33333;
  int s = pals_socket();
  char buf[20];

  pals_bind(s, port);

  printf("blocking.. enter any\n");
  scanf("%s", buf);

  int sz = pals_recvfrom(s, buf, 5);
  printf("received msgs of size %d\n", sz);
  if (0 <= sz) {
    buf[sz] = 0;
    printf("msg [%s] recv\n", buf);
  }

  return 0;
}
