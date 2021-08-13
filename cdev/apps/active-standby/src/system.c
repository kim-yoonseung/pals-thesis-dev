#include "system.h"

#include <stdlib.h>
#include <stdio.h>
#include <time.h>

// simulate user input
int get_user_input() {
  srand(time(0));
  char toggle_ratio = 10;
  char r = rand() % 100;
  int retval = 0;
  if (r < toggle_ratio) retval = 1;

  printf("[Event] get_user_input: %d\n", retval);
  return retval;
}

/* char get_input() { */
/*   // toggle at ratio of 1/10 */
/*   char r = rand()%10; */
/*   if (r == 0) return 1; */

/*   return 0; */
/* } */

/* void mark_complete(uint64_t pbt) { */
/*   printf("[Event] mark_complete(%lu)\n", pbt); */
/* } */

void write_log(int v) {
  printf("[Event] write_log(%d)\n", v);
}

int check_demand() {
  srand(time(0));
  char demand_ratio = 30, demand_max = 7;
  char r = rand() % 100;
  int retval = 0;
  if (r < demand_ratio) {
    r = rand() % demand_max;
    retval = 1 + r;
  }

  printf("[Event] check_demand: %d\n", retval);
  return retval;
}

void use_resource() {
  printf("[Event] use_resource\n");
}
