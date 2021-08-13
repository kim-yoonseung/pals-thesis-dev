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
  Definition source_file := "src/ctrl.c".
  Definition normalized := false.
End Info.

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
Definition __ctrl_state : ident := $"_ctrl_state".
Definition _adv_qidx : ident := $"adv_qidx".
Definition _apply_devmsg : ident := $"apply_devmsg".
Definition _arr : ident := $"arr".
Definition _b : ident := $"b".
Definition _check_dev_id : ident := $"check_dev_id".
Definition _con : ident := $"con".
Definition _content : ident := $"content".
Definition _copy_state_from_hb : ident := $"copy_state_from_hb".
Definition _csr : ident := $"csr".
Definition _cst : ident := $"cst".
Definition _cur_mode : ident := $"cur_mode".
Definition _devmsg : ident := $"devmsg".
Definition _entry : ident := $"entry".
Definition _grant_msg : ident := $"grant_msg".
Definition _hb : ident := $"hb".
Definition _hd : ident := $"hd".
Definition _i : ident := $"i".
Definition _id_dev : ident := $"id_dev".
Definition _inbox : ident := $"inbox".
Definition _inbox_t : ident := $"inbox_t".
Definition _job : ident := $"job".
Definition _job_controller : ident := $"job_controller".
Definition _main : ident := $"main".
Definition _md : ident := $"md".
Definition _me : ident := $"me".
Definition _msg_entry_t : ident := $"msg_entry_t".
Definition _other_tid : ident := $"other_tid".
Definition _pals_send : ident := $"pals_send".
Definition _pbt : ident := $"pbt".
Definition _q : ident := $"q".
Definition _qb : ident := $"qb".
Definition _qe : ident := $"qe".
Definition _qrange_sanitize : ident := $"qrange_sanitize".
Definition _r : ident := $"r".
Definition _received : ident := $"received".
Definition _reduce_timeout : ident := $"reduce_timeout".
Definition _send_hb : ident := $"send_hb".
Definition _st : ident := $"st".
Definition _state : ident := $"state".
Definition _sync_istate : ident := $"sync_istate".
Definition _tid : ident := $"tid".
Definition _tid_owner : ident := $"tid_owner".
Definition _tout : ident := $"tout".
Definition _try_add_queue : ident := $"try_add_queue".
Definition _try_release : ident := $"try_release".
Definition _update_istate : ident := $"update_istate".
Definition _update_owner : ident := $"update_owner".
Definition _update_queue : ident := $"update_queue".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.

Section PARAMETRIZATION.
Variable task_id: Z.

Definition v_TASK_ID := {|
  gvar_info := tschar;
  gvar_init := (Init_int8 (Int.repr task_id) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_grant_msg := {|
  gvar_info := (tarray tschar 8);
  gvar_init := (Init_int8 (Int.repr 1) :: Init_space 7 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_state := {|
  gvar_info := (Tstruct __ctrl_state noattr);
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_qrange_sanitize := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_i, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 0) tint) (Etempvar _i tint)
                 tint)
    (Sset _t'1
      (Ecast
        (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 4) tint) tint)
        tbool))
    (Sset _t'1 (Econst_int (Int.repr 0) tint)))
  (Sifthenelse (Etempvar _t'1 tint)
    (Sreturn (Some (Etempvar _i tint)))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_adv_qidx := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_i, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Ecast
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint) tint))
      (Sset _i (Etempvar _t'1 tint)))
    (Scall (Some _t'2)
      (Evar _qrange_sanitize (Tfunction (Tcons tint Tnil) tint cc_default))
      ((Etempvar _t'1 tint) :: nil)))
  (Sreturn (Some (Etempvar _t'2 tint))))
|}.

Definition f_check_dev_id := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_tid, tschar) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _tid tschar)
                     (Econst_int (Int.repr 3) tint) tint)
        (Sset _t'1 (Econst_int (Int.repr 1) tint))
        (Sset _t'1
          (Ecast
            (Ebinop Oeq (Etempvar _tid tschar) (Econst_int (Int.repr 4) tint)
              tint) tbool)))
      (Sifthenelse (Etempvar _t'1 tint)
        (Sset _t'2 (Econst_int (Int.repr 1) tint))
        (Sset _t'2
          (Ecast
            (Ebinop Oeq (Etempvar _tid tschar) (Econst_int (Int.repr 5) tint)
              tint) tbool))))
    (Sset _r (Etempvar _t'2 tint)))
  (Sreturn (Some (Etempvar _r tint))))
|}.

Definition f_copy_state_from_hb := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr tschar)) :: (_hb, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 1) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Econst_int (Int.repr 8) tint) tint)
        Sskip
        Sbreak)
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _st (tptr tschar)) (Etempvar _i tint)
            (tptr tschar)) tschar)
        (Ederef
          (Ebinop Oadd (Etempvar _hb (tptr tschar)) (Etempvar _i tint)
            (tptr tschar)) tschar)))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_sync_istate := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_tid, tschar) :: (_st, (tptr tschar)) ::
                (_inbox, (tptr (Tstruct _inbox_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_other_tid, tschar) ::
               (_con, (tptr (Tstruct _msg_entry_t noattr))) ::
               (_hb, (tptr (Tstruct _msg_entry_t noattr))) :: (_i, tint) ::
               (_cur_mode, tschar) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _other_tid
    (Ecast
      (Ebinop Osub (Econst_int (Int.repr 3) tint) (Etempvar _tid tschar)
        tint) tschar))
  (Ssequence
    (Sset _con
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _inbox (tptr (Tstruct _inbox_t noattr)))
            (Tstruct _inbox_t noattr)) _entry
          (tarray (Tstruct _msg_entry_t noattr) 16))
        (Econst_int (Int.repr 0) tint) (tptr (Tstruct _msg_entry_t noattr))))
    (Ssequence
      (Sset _hb
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _inbox (tptr (Tstruct _inbox_t noattr)))
              (Tstruct _inbox_t noattr)) _entry
            (tarray (Tstruct _msg_entry_t noattr) 16))
          (Etempvar _other_tid tschar) (tptr (Tstruct _msg_entry_t noattr))))
      (Ssequence
        (Sset _cur_mode
          (Ecast
            (Ederef
              (Ebinop Oadd (Etempvar _st (tptr tschar))
                (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar) tschar))
        (Sifthenelse (Ebinop Oeq (Etempvar _cur_mode tschar)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tint)
                         (Efield
                           (Ederef
                             (Etempvar _hb (tptr (Tstruct _msg_entry_t noattr)))
                             (Tstruct _msg_entry_t noattr)) _received tschar)
                         tint)
            (Ssequence
              (Scall None
                (Evar _copy_state_from_hb (Tfunction
                                            (Tcons (tptr tschar)
                                              (Tcons (tptr tschar) Tnil))
                                            tvoid cc_default))
                ((Etempvar _st (tptr tschar)) ::
                 (Efield
                   (Ederef
                     (Etempvar _hb (tptr (Tstruct _msg_entry_t noattr)))
                     (Tstruct _msg_entry_t noattr)) _content
                   (tarray tschar 15)) :: nil))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _st (tptr tschar))
                    (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar)
                (Econst_int (Int.repr 2) tint)))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _st (tptr tschar))
                  (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar)
              (Etempvar _tid tschar)))
          (Sifthenelse (Ebinop Oeq (Etempvar _cur_mode tschar)
                         (Econst_int (Int.repr 1) tint) tint)
            (Ssequence
              (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tint)
                             (Efield
                               (Ederef
                                 (Etempvar _hb (tptr (Tstruct _msg_entry_t noattr)))
                                 (Tstruct _msg_entry_t noattr)) _received
                               tschar) tint)
                (Sset _t'1
                  (Ecast
                    (Ebinop Olt (Econst_int (Int.repr 0) tint)
                      (Efield
                        (Ederef
                          (Etempvar _con (tptr (Tstruct _msg_entry_t noattr)))
                          (Tstruct _msg_entry_t noattr)) _received tschar)
                      tint) tbool))
                (Sset _t'1 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'1 tint)
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _st (tptr tschar))
                      (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar)
                  (Econst_int (Int.repr 2) tint))
                Sskip))
            (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tint)
                           (Efield
                             (Ederef
                               (Etempvar _hb (tptr (Tstruct _msg_entry_t noattr)))
                               (Tstruct _msg_entry_t noattr)) _received
                             tschar) tint)
              (Ssequence
                (Scall None
                  (Evar _copy_state_from_hb (Tfunction
                                              (Tcons (tptr tschar)
                                                (Tcons (tptr tschar) Tnil))
                                              tvoid cc_default))
                  ((Etempvar _st (tptr tschar)) ::
                   (Efield
                     (Ederef
                       (Etempvar _hb (tptr (Tstruct _msg_entry_t noattr)))
                       (Tstruct _msg_entry_t noattr)) _content
                     (tarray tschar 15)) :: nil))
                (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tint)
                               (Efield
                                 (Ederef
                                   (Etempvar _con (tptr (Tstruct _msg_entry_t noattr)))
                                   (Tstruct _msg_entry_t noattr)) _received
                                 tschar) tint)
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _st (tptr tschar))
                        (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar)
                    (Econst_int (Int.repr 1) tint))
                  Sskip))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _st (tptr tschar))
                      (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar)
                  (Econst_int (Int.repr 1) tint))
                (Sifthenelse (Ebinop Oeq
                               (Ederef
                                 (Ebinop Oadd (Etempvar _st (tptr tschar))
                                   (Econst_int (Int.repr 1) tint)
                                   (tptr tschar)) tschar)
                               (Econst_int (Int.repr 5) tint) tint)
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _st (tptr tschar))
                        (Econst_int (Int.repr 1) tint) (tptr tschar)) tschar)
                    (Econst_int (Int.repr 0) tint))
                  Sskip)))))))))
|}.

Definition f_try_add_queue := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr tschar)) :: (_id_dev, tschar) :: nil);
  fn_vars := nil;
  fn_temps := ((_qb, tschar) :: (_qe, tschar) :: (_q, (tptr tschar)) ::
               (_csr, tschar) :: (_i, tint) :: (_tid, tschar) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _qb
    (Ecast
      (Ederef
        (Ebinop Oadd (Etempvar _st (tptr tschar))
          (Econst_int (Int.repr 2) tint) (tptr tschar)) tschar) tschar))
  (Ssequence
    (Sset _qe
      (Ecast
        (Ederef
          (Ebinop Oadd (Etempvar _st (tptr tschar))
            (Econst_int (Int.repr 3) tint) (tptr tschar)) tschar) tschar))
    (Ssequence
      (Sset _q
        (Ebinop Oadd (Etempvar _st (tptr tschar))
          (Econst_int (Int.repr 4) tint) (tptr tschar)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _qrange_sanitize (Tfunction (Tcons tint Tnil) tint
                                     cc_default))
            ((Etempvar _qb tschar) :: nil))
          (Sset _csr (Ecast (Etempvar _t'1 tint) tschar)))
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 3) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sifthenelse (Ebinop Oeq (Etempvar _csr tschar)
                               (Etempvar _qe tschar) tint)
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _q (tptr tschar))
                          (Etempvar _csr tschar) (tptr tschar)) tschar)
                      (Etempvar _id_dev tschar))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'2)
                          (Evar _adv_qidx (Tfunction (Tcons tint Tnil) tint
                                            cc_default))
                          ((Etempvar _csr tschar) :: nil))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _st (tptr tschar))
                              (Econst_int (Int.repr 3) tint) (tptr tschar))
                            tschar) (Etempvar _t'2 tint)))
                      Sbreak))
                  Sskip)
                (Ssequence
                  (Sset _tid
                    (Ecast
                      (Ederef
                        (Ebinop Oadd (Etempvar _q (tptr tschar))
                          (Etempvar _csr tschar) (tptr tschar)) tschar)
                      tschar))
                  (Ssequence
                    (Sifthenelse (Ebinop Oeq (Etempvar _tid tschar)
                                   (Etempvar _id_dev tschar) tint)
                      Sbreak
                      Sskip)
                    (Ssequence
                      (Scall (Some _t'3)
                        (Evar _adv_qidx (Tfunction (Tcons tint Tnil) tint
                                          cc_default))
                        ((Etempvar _csr tschar) :: nil))
                      (Sset _csr (Ecast (Etempvar _t'3 tint) tschar)))))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))))))
|}.

Definition f_try_release := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr tschar)) :: (_id_dev, tschar) :: nil);
  fn_vars := nil;
  fn_temps := ((_tout, tschar) :: (_qb, tschar) :: (_qe, tschar) ::
               (_q, (tptr tschar)) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _tout
    (Ecast
      (Ederef
        (Ebinop Oadd (Etempvar _st (tptr tschar))
          (Econst_int (Int.repr 1) tint) (tptr tschar)) tschar) tschar))
  (Ssequence
    (Sset _qb
      (Ecast
        (Ederef
          (Ebinop Oadd (Etempvar _st (tptr tschar))
            (Econst_int (Int.repr 2) tint) (tptr tschar)) tschar) tschar))
    (Ssequence
      (Sset _qe
        (Ecast
          (Ederef
            (Ebinop Oadd (Etempvar _st (tptr tschar))
              (Econst_int (Int.repr 3) tint) (tptr tschar)) tschar) tschar))
      (Ssequence
        (Sset _q
          (Ebinop Oadd (Etempvar _st (tptr tschar))
            (Econst_int (Int.repr 4) tint) (tptr tschar)))
        (Ssequence
          (Sifthenelse (Ebinop One (Etempvar _qb tschar)
                         (Etempvar _qe tschar) tint)
            (Ssequence
              (Scall (Some _t'3)
                (Evar _qrange_sanitize (Tfunction (Tcons tint Tnil) tint
                                         cc_default))
                ((Etempvar _qb tschar) :: nil))
              (Sset _t'2
                (Ecast
                  (Ebinop Oeq
                    (Ederef
                      (Ebinop Oadd (Etempvar _q (tptr tschar))
                        (Etempvar _t'3 tint) (tptr tschar)) tschar)
                    (Etempvar _id_dev tschar) tint) tbool)))
            (Sset _t'2 (Econst_int (Int.repr 0) tint)))
          (Sifthenelse (Etempvar _t'2 tint)
            (Ssequence
              (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tint)
                             (Etempvar _tout tschar) tint)
                (Sset _t'1
                  (Ecast
                    (Ebinop Olt (Etempvar _tout tschar)
                      (Econst_int (Int.repr 5) tint) tint) tbool))
                (Sset _t'1 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'1 tint)
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _st (tptr tschar))
                      (Econst_int (Int.repr 1) tint) (tptr tschar)) tschar)
                  (Econst_int (Int.repr 1) tint))
                Sskip))
            Sskip))))))
|}.

Definition f_apply_devmsg := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr tschar)) :: (_id_dev, tschar) ::
                (_me, (tptr (Tstruct _msg_entry_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, tschar) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tint)
               (Efield
                 (Ederef (Etempvar _me (tptr (Tstruct _msg_entry_t noattr)))
                   (Tstruct _msg_entry_t noattr)) _received tschar) tint)
  (Ssequence
    (Sset _b
      (Ecast
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _me (tptr (Tstruct _msg_entry_t noattr)))
                (Tstruct _msg_entry_t noattr)) _content (tarray tschar 15))
            (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar) tschar))
    (Sifthenelse (Ebinop Oeq (Etempvar _b tschar)
                   (Econst_int (Int.repr 1) tint) tint)
      (Scall None
        (Evar _try_add_queue (Tfunction
                               (Tcons (tptr tschar) (Tcons tschar Tnil))
                               tvoid cc_default))
        ((Etempvar _st (tptr tschar)) :: (Etempvar _id_dev tschar) :: nil))
      (Scall None
        (Evar _try_release (Tfunction
                             (Tcons (tptr tschar) (Tcons tschar Tnil)) tvoid
                             cc_default))
        ((Etempvar _st (tptr tschar)) :: (Etempvar _id_dev tschar) :: nil))))
  Sskip)
|}.

Definition f_reduce_timeout := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_tout, tschar) :: (_qb, tschar) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _tout
    (Ecast
      (Ederef
        (Ebinop Oadd (Etempvar _st (tptr tschar))
          (Econst_int (Int.repr 1) tint) (tptr tschar)) tschar) tschar))
  (Ssequence
    (Sset _qb
      (Ecast
        (Ederef
          (Ebinop Oadd (Etempvar _st (tptr tschar))
            (Econst_int (Int.repr 2) tint) (tptr tschar)) tschar) tschar))
    (Sifthenelse (Ebinop Oeq (Etempvar _tout tschar)
                   (Econst_int (Int.repr 1) tint) tint)
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _st (tptr tschar))
              (Econst_int (Int.repr 1) tint) (tptr tschar)) tschar)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Scall (Some _t'1)
            (Evar _adv_qidx (Tfunction (Tcons tint Tnil) tint cc_default))
            ((Etempvar _qb tschar) :: nil))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _st (tptr tschar))
                (Econst_int (Int.repr 2) tint) (tptr tschar)) tschar)
            (Etempvar _t'1 tint))))
      (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 1) tint)
                     (Etempvar _tout tschar) tint)
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _st (tptr tschar))
              (Econst_int (Int.repr 1) tint) (tptr tschar)) tschar)
          (Ebinop Osub (Etempvar _tout tschar) (Econst_int (Int.repr 1) tint)
            tint))
        Sskip))))
|}.

Definition f_update_queue := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr tschar)) ::
                (_inbox, (tptr (Tstruct _inbox_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_devmsg, (tptr (Tstruct _msg_entry_t noattr))) ::
               (_i, tint) :: (_id_dev, tschar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 3) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _id_dev
            (Ecast
              (Ebinop Oadd (Econst_int (Int.repr 3) tint) (Etempvar _i tint)
                tint) tschar))
          (Ssequence
            (Sset _devmsg
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _inbox (tptr (Tstruct _inbox_t noattr)))
                    (Tstruct _inbox_t noattr)) _entry
                  (tarray (Tstruct _msg_entry_t noattr) 16))
                (Etempvar _id_dev tschar)
                (tptr (Tstruct _msg_entry_t noattr))))
            (Scall None
              (Evar _apply_devmsg (Tfunction
                                    (Tcons (tptr tschar)
                                      (Tcons tschar
                                        (Tcons
                                          (tptr (Tstruct _msg_entry_t noattr))
                                          Tnil))) tvoid cc_default))
              ((Etempvar _st (tptr tschar)) :: (Etempvar _id_dev tschar) ::
               (Etempvar _devmsg (tptr (Tstruct _msg_entry_t noattr))) ::
               nil)))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Scall None
    (Evar _reduce_timeout (Tfunction (Tcons (tptr tschar) Tnil) tvoid
                            cc_default))
    ((Etempvar _st (tptr tschar)) :: nil)))
|}.

Definition f_update_istate := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_tid, tschar) :: (_st, (tptr tschar)) ::
                (_inbox, (tptr (Tstruct _inbox_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _sync_istate (Tfunction
                         (Tcons tschar
                           (Tcons (tptr tschar)
                             (Tcons (tptr (Tstruct _inbox_t noattr)) Tnil)))
                         tvoid cc_default))
    ((Etempvar _tid tschar) :: (Etempvar _st (tptr tschar)) ::
     (Etempvar _inbox (tptr (Tstruct _inbox_t noattr))) :: nil))
  (Scall None
    (Evar _update_queue (Tfunction
                          (Tcons (tptr tschar)
                            (Tcons (tptr (Tstruct _inbox_t noattr)) Tnil))
                          tvoid cc_default))
    ((Etempvar _st (tptr tschar)) ::
     (Etempvar _inbox (tptr (Tstruct _inbox_t noattr))) :: nil)))
|}.

Definition f_update_owner := {|
  fn_return := tschar;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_md, tschar) :: (_tout, tschar) :: (_qb, tschar) ::
               (_qe, tschar) :: (_q, (tptr tschar)) :: (_hd, tschar) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _md
    (Ecast
      (Ederef
        (Ebinop Oadd (Etempvar _st (tptr tschar))
          (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar) tschar))
  (Ssequence
    (Sset _tout
      (Ecast
        (Ederef
          (Ebinop Oadd (Etempvar _st (tptr tschar))
            (Econst_int (Int.repr 1) tint) (tptr tschar)) tschar) tschar))
    (Ssequence
      (Sset _qb
        (Ecast
          (Ederef
            (Ebinop Oadd (Etempvar _st (tptr tschar))
              (Econst_int (Int.repr 2) tint) (tptr tschar)) tschar) tschar))
      (Ssequence
        (Sset _qe
          (Ecast
            (Ederef
              (Ebinop Oadd (Etempvar _st (tptr tschar))
                (Econst_int (Int.repr 3) tint) (tptr tschar)) tschar) tschar))
        (Ssequence
          (Sset _q
            (Ebinop Oadd (Etempvar _st (tptr tschar))
              (Econst_int (Int.repr 4) tint) (tptr tschar)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _qrange_sanitize (Tfunction (Tcons tint Tnil) tint
                                         cc_default))
                ((Etempvar _qb tschar) :: nil))
              (Sset _hd
                (Ecast
                  (Ederef
                    (Ebinop Oadd (Etempvar _q (tptr tschar))
                      (Etempvar _t'1 tint) (tptr tschar)) tschar) tschar)))
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _tout tschar)
                             (Econst_int (Int.repr 0) tint) tint)
                (Sset _t'2
                  (Ecast
                    (Ebinop One (Etempvar _qb tschar) (Etempvar _qe tschar)
                      tint) tbool))
                (Sset _t'2 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'2 tint)
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _st (tptr tschar))
                        (Econst_int (Int.repr 1) tint) (tptr tschar)) tschar)
                    (Econst_int (Int.repr 5) tint))
                  (Sifthenelse (Ebinop One (Etempvar _md tschar)
                                 (Econst_int (Int.repr 1) tint) tint)
                    (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                     tint)))
                    (Sreturn (Some (Etempvar _hd tschar)))))
                (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                 tint)))))))))))
|}.

Definition f_send_hb := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr tschar)) :: (_tid, tschar) :: nil);
  fn_vars := nil;
  fn_temps := ((_other_tid, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _other_tid
    (Ecast
      (Ebinop Osub (Econst_int (Int.repr 3) tint) (Etempvar _tid tschar)
        tint) tschar))
  (Scall None
    (Evar _pals_send (Tfunction (Tcons tschar (Tcons (tptr tschar) Tnil))
                       tvoid cc_default))
    ((Etempvar _other_tid tschar) :: (Etempvar _st (tptr tschar)) :: nil)))
|}.

Definition f_job_controller := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_tid, tschar) ::
                (_cst, (tptr (Tstruct __ctrl_state noattr))) ::
                (_pbt, tulong) ::
                (_inbox, (tptr (Tstruct _inbox_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_tid_owner, tschar) :: (_st, (tptr tschar)) ::
               (_t'2, tint) :: (_t'1, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _st
    (Ecast
      (Efield
        (Ederef (Etempvar _cst (tptr (Tstruct __ctrl_state noattr)))
          (Tstruct __ctrl_state noattr)) _arr (tarray tschar 8))
      (tptr tschar)))
  (Ssequence
    (Scall None
      (Evar _update_istate (Tfunction
                             (Tcons tschar
                               (Tcons (tptr tschar)
                                 (Tcons (tptr (Tstruct _inbox_t noattr))
                                   Tnil))) tvoid cc_default))
      ((Etempvar _tid tschar) :: (Etempvar _st (tptr tschar)) ::
       (Etempvar _inbox (tptr (Tstruct _inbox_t noattr))) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _update_owner (Tfunction (Tcons (tptr tschar) Tnil) tschar
                                cc_default))
          ((Etempvar _st (tptr tschar)) :: nil))
        (Sset _tid_owner (Ecast (Etempvar _t'1 tschar) tschar)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _check_dev_id (Tfunction (Tcons tschar Tnil) tint
                                  cc_default))
            ((Etempvar _tid_owner tschar) :: nil))
          (Sifthenelse (Etempvar _t'2 tint)
            (Scall None
              (Evar _pals_send (Tfunction
                                 (Tcons tschar (Tcons (tptr tschar) Tnil))
                                 tvoid cc_default))
              ((Etempvar _tid_owner tschar) ::
               (Evar _grant_msg (tarray tschar 8)) :: nil))
            Sskip))
        (Scall None
          (Evar _send_hb (Tfunction (Tcons (tptr tschar) (Tcons tschar Tnil))
                           tvoid cc_default))
          ((Etempvar _st (tptr tschar)) :: (Etempvar _tid tschar) :: nil))))))
|}.

Definition f_job := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pbt, tulong) ::
                (_inbox, (tptr (Tstruct _inbox_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _job_controller (Tfunction
                          (Tcons tschar
                            (Tcons (tptr (Tstruct __ctrl_state noattr))
                              (Tcons tulong
                                (Tcons (tptr (Tstruct _inbox_t noattr)) Tnil))))
                          tvoid cc_default))
  ((Evar _TASK_ID tschar) ::
   (Eaddrof (Evar _state (Tstruct __ctrl_state noattr))
     (tptr (Tstruct __ctrl_state noattr))) :: (Etempvar _pbt tulong) ::
   (Etempvar _inbox (tptr (Tstruct _inbox_t noattr))) :: nil))
|}.

Definition composites : list composite_definition :=
(Composite _msg_entry_t Struct
   ((_received, tschar) :: (_content, (tarray tschar 15)) :: nil)
   noattr ::
 Composite _inbox_t Struct
   ((_entry, (tarray (Tstruct _msg_entry_t noattr) 16)) :: nil)
   noattr ::
 Composite __ctrl_state Struct ((_arr, (tarray tschar 8)) :: nil) noattr ::
 nil).

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
 (_pals_send,
   Gfun(External (EF_external "pals_send"
                   (mksignature (AST.Tint :: AST.Tlong :: nil) AST.Tvoid
                     cc_default)) (Tcons tschar (Tcons (tptr tschar) Tnil))
     tvoid cc_default)) :: (_TASK_ID, Gvar v_TASK_ID) ::
 (_grant_msg, Gvar v_grant_msg) :: (_state, Gvar v_state) ::
 (_qrange_sanitize, Gfun(Internal f_qrange_sanitize)) ::
 (_adv_qidx, Gfun(Internal f_adv_qidx)) ::
 (_check_dev_id, Gfun(Internal f_check_dev_id)) ::
 (_copy_state_from_hb, Gfun(Internal f_copy_state_from_hb)) ::
 (_sync_istate, Gfun(Internal f_sync_istate)) ::
 (_try_add_queue, Gfun(Internal f_try_add_queue)) ::
 (_try_release, Gfun(Internal f_try_release)) ::
 (_apply_devmsg, Gfun(Internal f_apply_devmsg)) ::
 (_reduce_timeout, Gfun(Internal f_reduce_timeout)) ::
 (_update_queue, Gfun(Internal f_update_queue)) ::
 (_update_istate, Gfun(Internal f_update_istate)) ::
 (_update_owner, Gfun(Internal f_update_owner)) ::
 (_send_hb, Gfun(Internal f_send_hb)) ::
 (_job_controller, Gfun(Internal f_job_controller)) ::
 (_job, Gfun(Internal f_job)) :: nil).

Definition public_idents : list ident :=
(_job :: _job_controller :: _send_hb :: _update_owner :: _update_istate ::
 _update_queue :: _reduce_timeout :: _apply_devmsg :: _try_release ::
 _try_add_queue :: _sync_istate :: _copy_state_from_hb :: _check_dev_id ::
 _adv_qidx :: _qrange_sanitize :: _state :: _grant_msg :: _TASK_ID ::
 _pals_send :: ___builtin_debug :: ___builtin_write32_reversed ::
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

End PARAMETRIZATION.
