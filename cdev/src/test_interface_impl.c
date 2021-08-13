#include "test_interface.h"
#include "main.h"

inbox_t inbox;
inbox_t outbox;

char tid_cur;
char is_on[_MAX_NUM_TASKS];

value callback_rand;
value callback_event;
value callback_send;

void init_boxes() {
  for (int i = 0; i < NUM_TASKS; ++i) {
    inbox.entry[i].received = 0;
    outbox.entry[i].received = 0;
  }
}

value make_event_args(int nargs, int *args) {
  CAMLparam0 ();
  CAMLlocal3 (res, hd, tl);

  if (nargs > 0) {
    hd = Val_int(args[0]);
    tl = make_event_args(nargs - 1, args + 1);
    res = caml_alloc(2, 0);
    Store_field(res, 0, hd);
    Store_field(res, 1, tl);
  } else {
    res = Val_int(0);
  }

  CAMLreturn (res);
}

int extcall_event_int(char *fname, int nargs, int *args) {
  CAMLparam0 ();
  CAMLlocal2 (args_event, res);

  value args_ml[4];

  int ret = 0;

  if (0 < is_on[tid_cur]) {
    --is_on[tid_cur];

    args_event = make_event_args(nargs, args);

    /* args_ml = caml_alloc(4, 0); */
    /* Store_field(args_ml, 0, Val_int(tid_cur)); */
    /* Store_field(args_ml, 1, Val_int(1)); */
    /* Store_field(args_ml, 2, caml_copy_string(fname)); */
    /* Store_field(args_ml, 3, args_event); */
    args_ml[0] = Val_int(tid_cur);
    args_ml[1] = Val_int(1);
    args_ml[2] = caml_copy_string(fname);
    args_ml[3] = args_event;

    res = caml_callbackN(callback_event, 4, args_ml);
    ret = Int_val(res);
  }

  CAMLreturn (ret);
}

void extcall_event_void(char *fname, int nargs, int *args) {
  CAMLparam0 ();
  CAMLlocal1 (args_event);

  value args_ml[4];

  if (0 < is_on[tid_cur]) {
    -- is_on[tid_cur];

    args_event = make_event_args(nargs, args);
    /* args_ml = caml_alloc(4, 0); */
    /* Store_field(args_ml, 0, Val_int(tid_cur)); */
    /* Store_field(args_ml, 1, Val_int(0)); */
    /* Store_field(args_ml, 2, caml_copy_string(fname)); */
    /* Store_field(args_ml, 3, args_event); */

    args_ml[0] = Val_int(tid_cur);
    args_ml[1] = Val_int(0);
    args_ml[2] = caml_copy_string(fname);
    args_ml[3] = args_event;

    caml_callbackN(callback_event, 4, args_ml);
    /* Val_int(tid_cur), Val_int(0), */
    /* caml_copy_string(fname), args_ml); */
  }

  CAMLreturn0;
}

// (int list) option -> store at msg_entry_t*
void msg_entry_ml2c(value ent, /* int idx */ msg_entry_t *eptr) {
  CAMLparam1 (ent);
  CAMLlocal2 (l, hd);

  if (Is_block(ent)) {
    eptr->received = 1;

    l = Field(ent, 0);
    for (int i = 0; i < MSG_SIZE; ++i) {
      hd = Field(l, 0);
      eptr->content[i] = Int_val(hd);
      l = Field(l, 1);
    }
  } else {
    eptr->received = 0;
  }

  CAMLreturn0;
}

// char* -> int list
value msg_c2ml(char *msg, int idx) {
  CAMLparam0 ();
  CAMLlocal2 (res, tl);

  if (idx >= MSG_SIZE) {
    res = Val_int(0);
  } else {
    tl = msg_c2ml(msg, idx + 1);
    res = caml_alloc(2, 0);
    Store_field(res, 0, Val_int(msg[idx]));
    Store_field(res, 1, tl);
  }

  CAMLreturn (res);
}

// msg_entry_t* -> (int list) option
value msg_entry_c2ml(/* int idx */ msg_entry_t *eptr) {
  CAMLparam0 ();
  CAMLlocal2 (ent, bs);

  /* msg_entry_t *eptr = &outbox.entry[idx]; */

  if (eptr->received) {
    bs = msg_c2ml(eptr->content, 0);
    ent = caml_alloc(1, 0);
    Store_field(ent, 0, bs);
  } else {
    ent = Val_int(0);
  }

  CAMLreturn (ent);
}

// outbox -> ((int list) option) list
value outbox_c2ml(int idx) {
  CAMLparam0 ();
  CAMLlocal3 (ent, hd, tl);

  if (idx >= NUM_TASKS) {
    ent = Val_int(0);
  } else {
    ent = caml_alloc(2, 0);

    hd = msg_entry_c2ml(&outbox.entry[idx]);
    /* copy_out_msg_entry(idx); */
    tl = outbox_c2ml(idx + 1);

    Store_field(ent, 0, hd);
    Store_field(ent, 1, tl);
  }

  CAMLreturn (ent);
}

// ((int list) option) list -> store inbox
void inbox_ml2c(value inb, msg_entry_t *ent) {
  CAMLparam1 (inb);
  CAMLlocal1 (hd);

  if (Is_block(inb)) {
    hd = Field(inb, 0);
    msg_entry_ml2c(hd, ent);
    inb = Field(inb, 1);
    inbox_ml2c(inb, ent + 1);
  }

  CAMLreturn0 ;
}

void pals_send(char tid_dest, char *msg) {
  CAMLparam0 ();
  CAMLlocal3 (outbox_cur, msg_ml, outbox_nxt);

  if (0 < is_on[tid_cur]) {
    -- is_on[tid_cur];
    // TODO
    outbox_cur = outbox_c2ml(0);
    msg_ml = msg_c2ml(msg, 0);

    /* args = caml_alloc(4, 0); */
    /* Store_field(args, 0, Val_int(tid_cur)); */
    /* Store_field(args, 1, outbox_cur); */
    /* Store_field(args, 2, Val_int(tid_dest)); */
    /* Store_field(args, 3, msg_ml); */

    outbox_nxt = caml_callback3(callback_send, outbox_cur,
				Val_int(tid_dest), msg_ml);
    /* Val_int(tid_cur), */
    /* outbox_cur, */
    /* Val_int(tid_dest), msg_ml); */
    inbox_ml2c(outbox_nxt, outbox.entry);
  }

  CAMLreturn0 ;
}


///

CAMLprim void register_callbacks(value cb_rand, value cb_event, value cb_send) {
  CAMLparam3 (cb_rand, cb_event, cb_send);

  caml_register_global_root(&callback_rand);
  callback_rand = cb_rand;
  caml_register_global_root(&callback_event);
  callback_event = cb_event;
  caml_register_global_root(&callback_send);
  callback_send = cb_send;

  CAMLreturn0;
}

CAMLprim void remove_callbacks() {
  CAMLparam0 ();

  caml_remove_global_root(&callback_rand);
  caml_remove_global_root(&callback_event);
  caml_remove_global_root(&callback_send);

  CAMLreturn0;
}


CAMLprim value run_job_interface(/* value nts, value msz, */
				 /* value cb_rand, value cb_evt, */
				 value tid, value tm, value inb) {
  CAMLparam3 (tid, tm, inb);
  CAMLlocal3 (res, rnd1, rnd2);

  init_boxes();
  // convert inbox
  inbox_ml2c(inb, inbox.entry);

  int tid_int = Int_val(tid);
  int rnd_val;
  tid_cur = tid_int;

  if (is_on[tid_int] == 0) {
    // 0: random_recovery
    rnd1 = caml_callback2(callback_rand, tid, 0);

    rnd_val = Int_val(rnd1);
    if (0 < rnd_val) {
      init_job(tid_int);
      is_on[tid_int] = 1;
    }
  } else {
    // 1: random_failure
    rnd1 = caml_callback2(callback_rand, tid, 1);

    rnd_val = Int_val(rnd1);
    if (0 == rnd_val) {
      // failure actually happened
      is_on[tid_int] = 0;
    } else {
      // 2: random_fuel
      rnd2 = caml_callback2(callback_rand, tid, 2);

      is_on[tid_int] = Int_val(rnd2);

      call_job((uint64_t)Int64_val(tm), tid_int);
    }
  }

  // convert outbox
  res = outbox_c2ml(0);

  CAMLreturn (res);
}

CAMLprim value get_num_tasks() {
  CAMLparam0 ();
  CAMLlocal1 (res);

  res = Val_int(NUM_TASKS);

  CAMLreturn (res);
}

CAMLprim value get_msg_size() {
  CAMLparam0 ();
  CAMLlocal1 (res);

  res = Val_int(MSG_SIZE);

  CAMLreturn (res);
}

CAMLprim value get_period() {
  CAMLparam0 ();
  CAMLlocal1 (res);

  res = Val_int(PALS_PERIOD);

  CAMLreturn (res);
}

CAMLprim value get_num_mcasts() {
  CAMLparam0 ();
  CAMLlocal1 (res);

  res = Val_int(NUM_MCASTS);

  CAMLreturn (res);
}

CAMLprim value check_mcast_member(value midx, value tid) {
  CAMLparam2 (midx, tid);
  CAMLlocal1 (res);

  int midx_c = Int_val(midx), tid_c = Int_val(tid);

  if (0 <= midx_c && midx_c < NUM_MCASTS) {
    if (0 <= tid_c && tid_c < NUM_TASKS) {
      res = Val_int(MCAST_MEMBER[midx_c][tid_c]);
    }
  }

  CAMLreturn (res);
}
