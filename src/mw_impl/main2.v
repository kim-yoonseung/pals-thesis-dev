From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Module Info.
  Definition version := "3.8".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "src/main.c".
  Definition normalized := false.
End Info.

Definition _IP_ADDR : ident := $"IP_ADDR".
Definition _MAX_CSKEW : ident := $"MAX_CSKEW".
Definition _MAX_NWDELAY : ident := $"MAX_NWDELAY".
Definition _MCAST_MEMBER : ident := $"MCAST_MEMBER".
Definition _MSG_SIZE : ident := $"MSG_SIZE".
Definition _NUM_MCASTS : ident := $"NUM_MCASTS".
Definition _NUM_TASKS : ident := $"NUM_TASKS".
Definition _PALS_PERIOD : ident := $"PALS_PERIOD".
Definition _PORT : ident := $"PORT".
Definition _TASK_ID : ident := $"TASK_ID".
Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _buf : ident := $"buf".
Definition _c : ident := $"c".
Definition _check_send_hist : ident := $"check_send_hist".
Definition _cidx : ident := $"cidx".
Definition _content : ident := $"content".
Definition _cptr : ident := $"cptr".
Definition _cur_base_time : ident := $"cur_base_time".
Definition _cur_idx : ident := $"cur_idx".
Definition _dest_ip : ident := $"dest_ip".
Definition _dlt : ident := $"dlt".
Definition _dst : ident := $"dst".
Definition _entry : ident := $"entry".
Definition _fetch_msgs : ident := $"fetch_msgs".
Definition _get_base_time : ident := $"get_base_time".
Definition _get_cur_inbox : ident := $"get_cur_inbox".
Definition _get_nxt_inbox : ident := $"get_nxt_inbox".
Definition _group_mem : ident := $"group_mem".
Definition _i : ident := $"i".
Definition _id_dest : ident := $"id_dest".
Definition _inb : ident := $"inb".
Definition _inbox : ident := $"inbox".
Definition _inbox_t : ident := $"inbox_t".
Definition _init_inbox : ident := $"init_inbox".
Definition _insert_msg : ident := $"insert_msg".
Definition _job : ident := $"job".
Definition _main : ident := $"main".
Definition _maxt : ident := $"maxt".
Definition _mcast_join : ident := $"mcast_join".
Definition _me : ident := $"me".
Definition _msg : ident := $"msg".
Definition _msg_copy : ident := $"msg_copy".
Definition _msg_entry_t : ident := $"msg_entry_t".
Definition _msg_store_t : ident := $"msg_store_t".
Definition _mstore : ident := $"mstore".
Definition _nptr : ident := $"nptr".
Definition _nxt_base_time : ident := $"nxt_base_time".
Definition _p : ident := $"p".
Definition _pals_bind : ident := $"pals_bind".
Definition _pals_current_time : ident := $"pals_current_time".
Definition _pals_init_timer : ident := $"pals_init_timer".
Definition _pals_mcast_join : ident := $"pals_mcast_join".
Definition _pals_msg_t : ident := $"pals_msg_t".
Definition _pals_recvfrom : ident := $"pals_recvfrom".
Definition _pals_send : ident := $"pals_send".
Definition _pals_sendto : ident := $"pals_sendto".
Definition _pals_socket : ident := $"pals_socket".
Definition _pals_wait_timer : ident := $"pals_wait_timer".
Definition _period_base_time : ident := $"period_base_time".
Definition _pld_size : ident := $"pld_size".
Definition _pprd : ident := $"pprd".
Definition _received : ident := $"received".
Definition _reset_send_hist : ident := $"reset_send_hist".
Definition _ret : ident := $"ret".
Definition _run_task : ident := $"run_task".
Definition _rxs : ident := $"rxs".
Definition _rxs__1 : ident := $"rxs__1".
Definition _send_buf : ident := $"send_buf".
Definition _send_hist : ident := $"send_hist".
Definition _sender : ident := $"sender".
Definition _sender_id : ident := $"sender_id".
Definition _src : ident := $"src".
Definition _switch_inbox : ident := $"switch_inbox".
Definition _sz : ident := $"sz".
Definition _tid : ident := $"tid".
Definition _tm : ident := $"tm".
Definition _txs : ident := $"txs".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.

Definition v_PALS_PERIOD := {|
  gvar_info := tulong;
  gvar_init := nil;
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_MAX_CSKEW := {|
  gvar_info := tulong;
  gvar_init := nil;
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_MAX_NWDELAY := {|
  gvar_info := tulong;
  gvar_init := nil;
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_MSG_SIZE := {|
  gvar_info := tint;
  gvar_init := nil;
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_NUM_TASKS := {|
  gvar_info := tint;
  gvar_init := nil;
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_NUM_MCASTS := {|
  gvar_info := tint;
  gvar_init := nil;
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_PORT := {|
  gvar_info := tint;
  gvar_init := nil;
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_IP_ADDR := {|
  gvar_info := (tarray (tarray tschar 16) 28);
  gvar_init := nil;
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_MCAST_MEMBER := {|
  gvar_info := (tarray (tarray tschar 13) 15);
  gvar_init := nil;
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_TASK_ID := {|
  gvar_info := tschar;
  gvar_init := nil;
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_send_buf := {|
  gvar_info := (Tstruct _pals_msg_t noattr);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_mstore := {|
  gvar_info := (Tstruct _msg_store_t noattr);
  gvar_init := (Init_space 628 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_send_hist := {|
  gvar_info := (tarray tschar 13);
  gvar_init := (Init_space 13 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_txs := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_rxs := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_get_cur_inbox := {|
  fn_return := (tptr (Tstruct _inbox_t noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oadd
                 (Efield (Evar _mstore (Tstruct _msg_store_t noattr)) _inbox
                   (tarray (Tstruct _inbox_t noattr) 2))
                 (Efield (Evar _mstore (Tstruct _msg_store_t noattr))
                   _cur_idx tint) (tptr (Tstruct _inbox_t noattr)))))
|}.

Definition f_get_nxt_inbox := {|
  fn_return := (tptr (Tstruct _inbox_t noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oadd
                 (Efield (Evar _mstore (Tstruct _msg_store_t noattr)) _inbox
                   (tarray (Tstruct _inbox_t noattr) 2))
                 (Ebinop Osub (Econst_int (Int.repr 1) tint)
                   (Efield (Evar _mstore (Tstruct _msg_store_t noattr))
                     _cur_idx tint) tint) (tptr (Tstruct _inbox_t noattr)))))
|}.

Definition f_msg_copy := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_src, (tptr tschar)) :: (_dst, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Evar _MSG_SIZE tint) tint)
        Sskip
        Sbreak)
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _dst (tptr tschar)) (Etempvar _i tint)
            (tptr tschar)) tschar)
        (Ederef
          (Ebinop Oadd (Etempvar _src (tptr tschar)) (Etempvar _i tint)
            (tptr tschar)) tschar)))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_check_send_hist := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_id_dest, tschar) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_group_mem, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _id_dest tschar) (Evar _NUM_TASKS tint)
                 tint)
    (Sifthenelse (Ebinop Oeq
                   (Ederef
                     (Ebinop Oadd (Evar _send_hist (tarray tschar 13))
                       (Etempvar _id_dest tschar) (tptr tschar)) tschar)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _send_hist (tarray tschar 13))
              (Etempvar _id_dest tschar) (tptr tschar)) tschar)
          (Econst_int (Int.repr 1) tint))
        (Sreturn (Some (Econst_int (Int.repr 1) tint))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Ebinop Olt (Etempvar _id_dest tschar)
                   (Ebinop Oadd (Evar _NUM_TASKS tint)
                     (Evar _NUM_MCASTS tint) tint) tint)
      (Ssequence
        (Sset _group_mem
          (Ederef
            (Ebinop Oadd (Evar _MCAST_MEMBER (tarray (tarray tschar 13) 15))
              (Ebinop Osub (Etempvar _id_dest tschar) (Evar _NUM_TASKS tint)
                tint) (tptr (tarray tschar 13))) (tarray tschar 13)))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Evar _NUM_TASKS tint) tint)
                  Sskip
                  Sbreak)
                (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tint)
                               (Ederef
                                 (Ebinop Oadd
                                   (Etempvar _group_mem (tptr tschar))
                                   (Etempvar _i tint) (tptr tschar)) tschar)
                               tint)
                  (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tint)
                                 (Ederef
                                   (Ebinop Oadd
                                     (Evar _send_hist (tarray tschar 13))
                                     (Etempvar _i tint) (tptr tschar))
                                   tschar) tint)
                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                    Sskip)
                  Sskip))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Evar _NUM_TASKS tint) tint)
                    Sskip
                    Sbreak)
                  (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tint)
                                 (Ederef
                                   (Ebinop Oadd
                                     (Etempvar _group_mem (tptr tschar))
                                     (Etempvar _i tint) (tptr tschar))
                                   tschar) tint)
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _send_hist (tarray tschar 13))
                          (Etempvar _i tint) (tptr tschar)) tschar)
                      (Econst_int (Int.repr 1) tint))
                    Sskip))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Sreturn (Some (Econst_int (Int.repr 1) tint))))))
      Sskip))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_reset_send_hist := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Evar _NUM_TASKS tint)
                     tint)
        Sskip
        Sbreak)
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _send_hist (tarray tschar 13))
            (Etempvar _i tint) (tptr tschar)) tschar)
        (Econst_int (Int.repr 0) tint)))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_pals_send := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_tid, tschar) :: (_msg, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_dest_ip, (tptr tschar)) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _check_send_hist (Tfunction (Tcons tschar Tnil) tint cc_default))
    ((Etempvar _tid tschar) :: nil))
  (Sifthenelse (Etempvar _t'1 tint)
    (Ssequence
      (Sset _dest_ip
        (Ederef
          (Ebinop Oadd (Evar _IP_ADDR (tarray (tarray tschar 16) 28))
            (Etempvar _tid tschar) (tptr (tarray tschar 16)))
          (tarray tschar 16)))
      (Ssequence
        (Scall None
          (Evar _msg_copy (Tfunction
                            (Tcons (tptr tschar) (Tcons (tptr tschar) Tnil))
                            tvoid cc_default))
          ((Etempvar _msg (tptr tschar)) ::
           (Efield (Evar _send_buf (Tstruct _pals_msg_t noattr)) _content
             (tarray tschar 23)) :: nil))
        (Scall None
          (Evar _pals_sendto (Tfunction
                               (Tcons tint
                                 (Tcons (tptr tschar)
                                   (Tcons tint
                                     (Tcons (tptr tschar) (Tcons tint Tnil)))))
                               tint cc_default))
          ((Evar _txs tint) :: (Etempvar _dest_ip (tptr tschar)) ::
           (Evar _PORT tint) ::
           (Ecast
             (Eaddrof (Evar _send_buf (Tstruct _pals_msg_t noattr))
               (tptr (Tstruct _pals_msg_t noattr))) (tptr tschar)) ::
           (Ebinop Oadd (Evar _MSG_SIZE tint) (Econst_int (Int.repr 9) tint)
             tint) :: nil))))
    Sskip))
|}.

Definition f_get_base_time := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_p, tulong) :: (_tm, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Osub (Etempvar _tm tulong)
                 (Ebinop Omod (Etempvar _tm tulong) (Etempvar _p tulong)
                   tulong) tulong)))
|}.

Definition f_mcast_join := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rxs__1, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_group_mem, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Evar _NUM_MCASTS tint)
                     tint)
        Sskip
        Sbreak)
      (Ssequence
        (Sset _group_mem
          (Ederef
            (Ebinop Oadd (Evar _MCAST_MEMBER (tarray (tarray tschar 13) 15))
              (Etempvar _i tint) (tptr (tarray tschar 13)))
            (tarray tschar 13)))
        (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tint)
                       (Ederef
                         (Ebinop Oadd (Etempvar _group_mem (tptr tschar))
                           (Evar _TASK_ID tschar) (tptr tschar)) tschar)
                       tint)
          (Scall None
            (Evar _pals_mcast_join (Tfunction
                                     (Tcons tint (Tcons (tptr tschar) Tnil))
                                     tvoid cc_default))
            ((Etempvar _rxs__1 tint) ::
             (Ederef
               (Ebinop Oadd (Evar _IP_ADDR (tarray (tarray tschar 16) 28))
                 (Ebinop Oadd (Evar _NUM_TASKS tint) (Etempvar _i tint) tint)
                 (tptr (tarray tschar 16))) (tarray tschar 16)) :: nil))
          Sskip)))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_insert_msg := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_me, (tptr (Tstruct _msg_entry_t noattr))) ::
                (_sender_id, tschar) :: (_c, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 0) tint)
                 (Etempvar _sender_id tschar) tint)
    (Sset _t'1
      (Ecast
        (Ebinop Olt (Etempvar _sender_id tschar) (Evar _NUM_TASKS tint) tint)
        tbool))
    (Sset _t'1 (Econst_int (Int.repr 0) tint)))
  (Sifthenelse (Etempvar _t'1 tint)
    (Ssequence
      (Sassign
        (Efield
          (Ederef
            (Ebinop Oadd (Etempvar _me (tptr (Tstruct _msg_entry_t noattr)))
              (Etempvar _sender_id tschar)
              (tptr (Tstruct _msg_entry_t noattr)))
            (Tstruct _msg_entry_t noattr)) _received tschar)
        (Econst_int (Int.repr 1) tint))
      (Scall None
        (Evar _msg_copy (Tfunction
                          (Tcons (tptr tschar) (Tcons (tptr tschar) Tnil))
                          tvoid cc_default))
        ((Etempvar _c (tptr tschar)) ::
         (Efield
           (Ederef
             (Ebinop Oadd (Etempvar _me (tptr (Tstruct _msg_entry_t noattr)))
               (Etempvar _sender_id tschar)
               (tptr (Tstruct _msg_entry_t noattr)))
             (Tstruct _msg_entry_t noattr)) _content (tarray tschar 23)) ::
         nil)))
    Sskip))
|}.

Definition f_fetch_msgs := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rxs__1, tint) :: (_cur_base_time, tulong) :: nil);
  fn_vars := ((_buf, (Tstruct _pals_msg_t noattr)) :: nil);
  fn_temps := ((_nxt_base_time, tulong) ::
               (_cptr, (tptr (Tstruct _msg_entry_t noattr))) ::
               (_nptr, (tptr (Tstruct _msg_entry_t noattr))) ::
               (_pld_size, tint) :: (_i, tint) :: (_sz, tint) ::
               (_t'3, tint) :: (_t'2, (tptr (Tstruct _inbox_t noattr))) ::
               (_t'1, (tptr (Tstruct _inbox_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _nxt_base_time
    (Ebinop Oadd (Etempvar _cur_base_time tulong) (Evar _PALS_PERIOD tulong)
      tulong))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _get_cur_inbox (Tfunction Tnil (tptr (Tstruct _inbox_t noattr))
                               cc_default)) nil)
      (Sset _cptr
        (Efield
          (Ederef (Etempvar _t'1 (tptr (Tstruct _inbox_t noattr)))
            (Tstruct _inbox_t noattr)) _entry
          (tarray (Tstruct _msg_entry_t noattr) 13))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _get_nxt_inbox (Tfunction Tnil
                                 (tptr (Tstruct _inbox_t noattr)) cc_default))
          nil)
        (Sset _nptr
          (Efield
            (Ederef (Etempvar _t'2 (tptr (Tstruct _inbox_t noattr)))
              (Tstruct _inbox_t noattr)) _entry
            (tarray (Tstruct _msg_entry_t noattr) 13))))
      (Ssequence
        (Sset _pld_size
          (Ebinop Oadd (Evar _MSG_SIZE tint) (Econst_int (Int.repr 9) tint)
            tint))
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Ebinop Omul (Evar _NUM_TASKS tint)
                               (Econst_int (Int.repr 4) tint) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar _pals_recvfrom (Tfunction
                                           (Tcons tint
                                             (Tcons (tptr tschar)
                                               (Tcons tint Tnil))) tint
                                           cc_default))
                    ((Etempvar _rxs__1 tint) ::
                     (Ecast
                       (Eaddrof (Evar _buf (Tstruct _pals_msg_t noattr))
                         (tptr (Tstruct _pals_msg_t noattr))) (tptr tschar)) ::
                     (Etempvar _pld_size tint) :: nil))
                  (Sset _sz (Etempvar _t'3 tint)))
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _sz tint)
                                 (Econst_int (Int.repr 0) tint) tint)
                    (Sreturn None)
                    Sskip)
                  (Ssequence
                    (Sifthenelse (Ebinop One (Etempvar _sz tint)
                                   (Etempvar _pld_size tint) tint)
                      Scontinue
                      Sskip)
                    (Ssequence
                      (Sifthenelse (Ebinop Olt
                                     (Efield
                                       (Evar _buf (Tstruct _pals_msg_t noattr))
                                       _sender tschar)
                                     (Econst_int (Int.repr 0) tint) tint)
                        Scontinue
                        Sskip)
                      (Sifthenelse (Ebinop Oeq
                                     (Efield
                                       (Evar _buf (Tstruct _pals_msg_t noattr))
                                       _period_base_time tulong)
                                     (Etempvar _cur_base_time tulong) tint)
                        (Scall None
                          (Evar _insert_msg (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _msg_entry_t noattr))
                                                (Tcons tschar
                                                  (Tcons (tptr tschar) Tnil)))
                                              tvoid cc_default))
                          ((Etempvar _cptr (tptr (Tstruct _msg_entry_t noattr))) ::
                           (Efield (Evar _buf (Tstruct _pals_msg_t noattr))
                             _sender tschar) ::
                           (Efield (Evar _buf (Tstruct _pals_msg_t noattr))
                             _content (tarray tschar 23)) :: nil))
                        (Sifthenelse (Ebinop Oeq
                                       (Efield
                                         (Evar _buf (Tstruct _pals_msg_t noattr))
                                         _period_base_time tulong)
                                       (Etempvar _nxt_base_time tulong) tint)
                          (Scall None
                            (Evar _insert_msg (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _msg_entry_t noattr))
                                                  (Tcons tschar
                                                    (Tcons (tptr tschar)
                                                      Tnil))) tvoid
                                                cc_default))
                            ((Etempvar _nptr (tptr (Tstruct _msg_entry_t noattr))) ::
                             (Efield (Evar _buf (Tstruct _pals_msg_t noattr))
                               _sender tschar) ::
                             (Efield (Evar _buf (Tstruct _pals_msg_t noattr))
                               _content (tarray tschar 23)) :: nil))
                          Sskip)))))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))))))
|}.

Definition f_init_inbox := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_inb, (tptr (Tstruct _inbox_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Evar _NUM_TASKS tint)
                     tint)
        Sskip
        Sbreak)
      (Sassign
        (Efield
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _inb (tptr (Tstruct _inbox_t noattr)))
                  (Tstruct _inbox_t noattr)) _entry
                (tarray (Tstruct _msg_entry_t noattr) 13)) (Etempvar _i tint)
              (tptr (Tstruct _msg_entry_t noattr)))
            (Tstruct _msg_entry_t noattr)) _received tschar)
        (Econst_int (Int.repr 0) tint)))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_switch_inbox := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_cidx, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _cidx
    (Efield (Evar _mstore (Tstruct _msg_store_t noattr)) _cur_idx tint))
  (Ssequence
    (Scall None
      (Evar _init_inbox (Tfunction
                          (Tcons (tptr (Tstruct _inbox_t noattr)) Tnil) tvoid
                          cc_default))
      ((Ebinop Oadd
         (Efield (Evar _mstore (Tstruct _msg_store_t noattr)) _inbox
           (tarray (Tstruct _inbox_t noattr) 2)) (Etempvar _cidx tint)
         (tptr (Tstruct _inbox_t noattr))) :: nil))
    (Sassign
      (Efield (Evar _mstore (Tstruct _msg_store_t noattr)) _cur_idx tint)
      (Ebinop Osub (Econst_int (Int.repr 1) tint) (Etempvar _cidx tint) tint))))
|}.

Definition f_run_task := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cur_base_time, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_pprd, tulong) :: (_dlt, tulong) :: (_maxt, tulong) ::
               (_t'1, (tptr (Tstruct _inbox_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _pprd (Evar _PALS_PERIOD tulong))
  (Ssequence
    (Sset _dlt
      (Ebinop Oadd
        (Ebinop Omul (Econst_int (Int.repr 2) tint) (Evar _MAX_CSKEW tulong)
          tulong) (Evar _MAX_NWDELAY tulong) tulong))
    (Ssequence
      (Sset _maxt
        (Ebinop Osub (Econst_long (Int64.repr (-1)) tulong)
          (Ebinop Omul (Econst_int (Int.repr 10) tint)
            (Evar _PALS_PERIOD tulong) tulong) tulong))
      (Swhile
        (Ebinop Olt (Etempvar _cur_base_time tulong) (Etempvar _maxt tulong)
          tint)
        (Ssequence
          (Sassign
            (Efield (Evar _send_buf (Tstruct _pals_msg_t noattr))
              _period_base_time tulong)
            (Ebinop Oadd (Etempvar _cur_base_time tulong)
              (Etempvar _pprd tulong) tulong))
          (Ssequence
            (Scall None
              (Evar _pals_wait_timer (Tfunction (Tcons tulong Tnil) tint
                                       cc_default))
              ((Etempvar _cur_base_time tulong) :: nil))
            (Ssequence
              (Scall None
                (Evar _fetch_msgs (Tfunction (Tcons tint (Tcons tulong Tnil))
                                    tvoid cc_default))
                ((Evar _rxs tint) :: (Etempvar _cur_base_time tulong) :: nil))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'1)
                    (Evar _get_cur_inbox (Tfunction Tnil
                                           (tptr (Tstruct _inbox_t noattr))
                                           cc_default)) nil)
                  (Scall None
                    (Evar _job (Tfunction
                                 (Tcons tulong
                                   (Tcons (tptr (Tstruct _inbox_t noattr))
                                     Tnil)) tvoid cc_default))
                    ((Etempvar _cur_base_time tulong) ::
                     (Etempvar _t'1 (tptr (Tstruct _inbox_t noattr))) :: nil)))
                (Ssequence
                  (Sset _cur_base_time
                    (Ebinop Oadd (Etempvar _cur_base_time tulong)
                      (Etempvar _pprd tulong) tulong))
                  (Ssequence
                    (Scall None
                      (Evar _reset_send_hist (Tfunction Tnil tvoid
                                               cc_default)) nil)
                    (Scall None
                      (Evar _switch_inbox (Tfunction Tnil tvoid cc_default))
                      nil)))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_tm, tulong) :: (_nxt_base_time, tulong) ::
               (_pprd, tulong) :: (_dlt, tulong) :: (_maxt, tulong) ::
               (_ret, tint) :: (_t'8, tint) :: (_t'7, tint) ::
               (_t'6, tint) :: (_t'5, tint) :: (_t'4, tulong) ::
               (_t'3, tint) :: (_t'2, tulong) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _pprd (Evar _PALS_PERIOD tulong))
    (Ssequence
      (Sset _dlt
        (Ebinop Oadd
          (Ebinop Omul (Econst_int (Int.repr 2) tint)
            (Evar _MAX_CSKEW tulong) tulong) (Evar _MAX_NWDELAY tulong)
          tulong))
      (Ssequence
        (Sset _maxt
          (Ebinop Osub (Econst_long (Int64.repr (-1)) tulong)
            (Ebinop Omul (Econst_int (Int.repr 10) tint)
              (Evar _PALS_PERIOD tulong) tulong) tulong))
        (Ssequence
          (Sassign
            (Efield (Evar _send_buf (Tstruct _pals_msg_t noattr)) _sender
              tschar) (Evar _TASK_ID tschar))
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _pals_init_timer (Tfunction Tnil tint cc_default)) nil)
              (Sset _ret (Etempvar _t'1 tint)))
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _ret tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                Sskip)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'2)
                    (Evar _pals_current_time (Tfunction Tnil tulong
                                               cc_default)) nil)
                  (Sset _tm (Etempvar _t'2 tulong)))
                (Ssequence
                  (Ssequence
                    (Sifthenelse (Ebinop Oeq (Etempvar _tm tulong)
                                   (Econst_int (Int.repr 0) tint) tint)
                      (Sset _t'3 (Econst_int (Int.repr 1) tint))
                      (Sset _t'3
                        (Ecast
                          (Eunop Onotbool
                            (Ebinop Olt (Etempvar _tm tulong)
                              (Etempvar _maxt tulong) tint) tint) tbool)))
                    (Sifthenelse (Etempvar _t'3 tint)
                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                      Sskip))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar _get_base_time (Tfunction
                                               (Tcons tulong
                                                 (Tcons tulong Tnil)) tulong
                                               cc_default))
                        ((Etempvar _pprd tulong) :: (Etempvar _tm tulong) ::
                         nil))
                      (Sset _nxt_base_time
                        (Ebinop Oadd (Etempvar _t'4 tulong)
                          (Ebinop Omul (Econst_int (Int.repr 2) tint)
                            (Etempvar _pprd tulong) tulong) tulong)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'5)
                          (Evar _pals_socket (Tfunction Tnil tint cc_default))
                          nil)
                        (Sassign (Evar _txs tint) (Etempvar _t'5 tint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'6)
                            (Evar _pals_socket (Tfunction Tnil tint
                                                 cc_default)) nil)
                          (Sassign (Evar _rxs tint) (Etempvar _t'6 tint)))
                        (Ssequence
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Evar _txs tint)
                                           (Econst_int (Int.repr 0) tint)
                                           tint)
                              (Sset _t'7 (Econst_int (Int.repr 1) tint))
                              (Sset _t'7
                                (Ecast
                                  (Ebinop Olt (Evar _rxs tint)
                                    (Econst_int (Int.repr 0) tint) tint)
                                  tbool)))
                            (Sifthenelse (Etempvar _t'7 tint)
                              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                              Sskip))
                          (Ssequence
                            (Scall None
                              (Evar _pals_wait_timer (Tfunction
                                                       (Tcons tulong Tnil)
                                                       tint cc_default))
                              ((Etempvar _nxt_base_time tulong) :: nil))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'8)
                                  (Evar _pals_bind (Tfunction
                                                     (Tcons tint
                                                       (Tcons tint Tnil))
                                                     tint cc_default))
                                  ((Evar _rxs tint) :: (Evar _PORT tint) ::
                                   nil))
                                (Sset _ret (Etempvar _t'8 tint)))
                              (Ssequence
                                (Sifthenelse (Ebinop Olt (Etempvar _ret tint)
                                               (Econst_int (Int.repr 0) tint)
                                               tint)
                                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                  Sskip)
                                (Ssequence
                                  (Scall None
                                    (Evar _mcast_join (Tfunction
                                                        (Tcons tint Tnil)
                                                        tvoid cc_default))
                                    ((Evar _rxs tint) :: nil))
                                  (Ssequence
                                    (Sset _nxt_base_time
                                      (Ebinop Oadd
                                        (Etempvar _nxt_base_time tulong)
                                        (Ebinop Omul
                                          (Econst_int (Int.repr 2) tint)
                                          (Etempvar _pprd tulong) tulong)
                                        tulong))
                                    (Ssequence
                                      (Scall None
                                        (Evar _run_task (Tfunction
                                                          (Tcons tulong Tnil)
                                                          tvoid cc_default))
                                        ((Etempvar _nxt_base_time tulong) ::
                                         nil))
                                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _msg_entry_t Struct
   ((_received, tschar) :: (_content, (tarray tschar 23)) :: nil)
   noattr ::
 Composite _inbox_t Struct
   ((_entry, (tarray (Tstruct _msg_entry_t noattr) 13)) :: nil)
   noattr ::
 Composite _pals_msg_t Struct
   ((_period_base_time, tulong) :: (_sender, tschar) ::
    (_content, (tarray tschar 23)) :: nil)
   noattr ::
 Composite _msg_store_t Struct
   ((_cur_idx, tint) :: (_inbox, (tarray (Tstruct _inbox_t noattr) 2)) ::
    nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_pals_current_time,
   Gfun(External (EF_external "pals_current_time"
                   (mksignature nil AST.Tlong cc_default)) Tnil tulong
     cc_default)) ::
 (_pals_init_timer,
   Gfun(External (EF_external "pals_init_timer"
                   (mksignature nil AST.Tint cc_default)) Tnil tint
     cc_default)) ::
 (_pals_wait_timer,
   Gfun(External (EF_external "pals_wait_timer"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (_pals_socket,
   Gfun(External (EF_external "pals_socket"
                   (mksignature nil AST.Tint cc_default)) Tnil tint
     cc_default)) ::
 (_pals_bind,
   Gfun(External (EF_external "pals_bind"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons tint (Tcons tint Tnil)) tint
     cc_default)) ::
 (_pals_mcast_join,
   Gfun(External (EF_external "pals_mcast_join"
                   (mksignature (AST.Tint :: AST.Tlong :: nil) AST.Tvoid
                     cc_default)) (Tcons tint (Tcons (tptr tschar) Tnil))
     tvoid cc_default)) ::
 (_pals_sendto,
   Gfun(External (EF_external "pals_sendto"
                   (mksignature
                     (AST.Tint :: AST.Tlong :: AST.Tint :: AST.Tlong ::
                      AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint
       (Tcons (tptr tschar)
         (Tcons tint (Tcons (tptr tschar) (Tcons tint Tnil))))) tint
     cc_default)) ::
 (_pals_recvfrom,
   Gfun(External (EF_external "pals_recvfrom"
                   (mksignature (AST.Tint :: AST.Tlong :: AST.Tint :: nil)
                     AST.Tint cc_default))
     (Tcons tint (Tcons (tptr tschar) (Tcons tint Tnil))) tint cc_default)) ::
 (_PALS_PERIOD, Gvar v_PALS_PERIOD) :: (_MAX_CSKEW, Gvar v_MAX_CSKEW) ::
 (_MAX_NWDELAY, Gvar v_MAX_NWDELAY) :: (_MSG_SIZE, Gvar v_MSG_SIZE) ::
 (_NUM_TASKS, Gvar v_NUM_TASKS) :: (_NUM_MCASTS, Gvar v_NUM_MCASTS) ::
 (_PORT, Gvar v_PORT) :: (_IP_ADDR, Gvar v_IP_ADDR) ::
 (_MCAST_MEMBER, Gvar v_MCAST_MEMBER) :: (_TASK_ID, Gvar v_TASK_ID) ::
 (_job,
   Gfun(External (EF_external "job"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons tulong (Tcons (tptr (Tstruct _inbox_t noattr)) Tnil)) tvoid
     cc_default)) :: (_send_buf, Gvar v_send_buf) ::
 (_mstore, Gvar v_mstore) :: (_send_hist, Gvar v_send_hist) ::
 (_txs, Gvar v_txs) :: (_rxs, Gvar v_rxs) ::
 (_get_cur_inbox, Gfun(Internal f_get_cur_inbox)) ::
 (_get_nxt_inbox, Gfun(Internal f_get_nxt_inbox)) ::
 (_msg_copy, Gfun(Internal f_msg_copy)) ::
 (_check_send_hist, Gfun(Internal f_check_send_hist)) ::
 (_reset_send_hist, Gfun(Internal f_reset_send_hist)) ::
 (_pals_send, Gfun(Internal f_pals_send)) ::
 (_get_base_time, Gfun(Internal f_get_base_time)) ::
 (_mcast_join, Gfun(Internal f_mcast_join)) ::
 (_insert_msg, Gfun(Internal f_insert_msg)) ::
 (_fetch_msgs, Gfun(Internal f_fetch_msgs)) ::
 (_init_inbox, Gfun(Internal f_init_inbox)) ::
 (_switch_inbox, Gfun(Internal f_switch_inbox)) ::
 (_run_task, Gfun(Internal f_run_task)) :: (_main, Gfun(Internal f_main)) ::
 nil).

Definition public_idents : list ident :=
(_main :: _run_task :: _switch_inbox :: _init_inbox :: _fetch_msgs ::
 _insert_msg :: _mcast_join :: _get_base_time :: _pals_send ::
 _reset_send_hist :: _check_send_hist :: _msg_copy :: _get_nxt_inbox ::
 _get_cur_inbox :: _rxs :: _txs :: _send_hist :: _mstore :: _send_buf ::
 _job :: _TASK_ID :: _MCAST_MEMBER :: _IP_ADDR :: _PORT :: _NUM_MCASTS ::
 _NUM_TASKS :: _MSG_SIZE :: _MAX_NWDELAY :: _MAX_CSKEW :: _PALS_PERIOD ::
 _pals_recvfrom :: _pals_sendto :: _pals_mcast_join :: _pals_bind ::
 _pals_socket :: _pals_wait_timer :: _pals_init_timer ::
 _pals_current_time :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


