#define CAML_NAME_SPACE

#include "main.h"
#include <stdio.h>
#include <stdint.h>

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/callback.h>

/* #define MAX_NUM_TASKS 16 */
/* #define MAX_MSG_SIZE 15 */

// maximum arity of extcall events
#define MAX_NUM_ARGS 10

// in test_interface_impl.c
extern inbox_t inbox;
extern inbox_t outbox;

void extcall_event_void(char *fname, int num_args, int *args);
int extcall_event_int(char *fname, int num_args, int *args);

// in test_config.c
extern const int NUM_TASKS;
extern const int NUM_MCASTS;
extern const int MSG_SIZE;
extern const uint64_t PALS_PERIOD;
extern const char MCAST_MEMBER[][_MAX_NUM_TASKS];

void init_job(int);
void call_job(uint64_t, int);
