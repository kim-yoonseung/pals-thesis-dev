#define CAML_NAME_SPACE

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/callback.h>

int get_new_work_impl(void) {
  srand(time(0));
  int r = rand() % 10;
  return r;
}

int do_work_impl(char id, char data) {
  printf("Working on %d with data %d..", id, data);
  srand(time(0));
  int r = rand() % 500; // in millisec
  struct timespec req;
  req.tv_sec = 0;
  req.tv_nsec = r * 1000000;

  nanosleep(&req, NULL);
  printf("done\n");

  return (data - 1);
}

CAMLprim value call_event_impl(value fname, value args) {
  CAMLparam2 (fname, args);
  CAMLlocal1 (res);

  int ret_c;

  if (strcmp(String_val(fname), "get_new_work") == 0) {
    ret_c = get_new_work_impl();
  } else if (strcmp(String_val(fname), "do_work") == 0) {
    int id = Int_val(Field(args, 0));
    int data = Int_val( Field(Field(args,1), 0) );
    ret_c = do_work_impl(id, data);
  }

  res = Val_int(ret_c);
  CAMLreturn (res);
}
