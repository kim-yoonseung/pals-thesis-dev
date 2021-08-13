#include "pals_infra.h"

#include <stdio.h>
#include <stdint.h>

int main() {
  pals_init_timer();
  uint64_t tm = pals_current_time();

  pals_set_timelimit(tm + 1000000000);
  printf("btw advancing timelimit..\n");
  pals_set_timelimit(tm + 2000000000);

  pals_wait_timer(tm + 3000000000);

  printf("must be violated..\n");
  pals_set_timelimit(tm + 10000000000);

}
