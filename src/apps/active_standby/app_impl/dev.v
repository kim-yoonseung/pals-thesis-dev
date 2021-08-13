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
  Definition source_file := "src/dev.c".
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
Definition __dev_state : ident := $"_dev_state".
Definition _acq_msg : ident := $"acq_msg".
Definition _check_demand : ident := $"check_demand".
Definition _content : ident := $"content".
Definition _d : ident := $"d".
Definition _demand : ident := $"demand".
Definition _dmd : ident := $"dmd".
Definition _dst : ident := $"dst".
Definition _dstate : ident := $"dstate".
Definition _e1 : ident := $"e1".
Definition _e2 : ident := $"e2".
Definition _entry : ident := $"entry".
Definition _get_new_demand : ident := $"get_new_demand".
Definition _inbox : ident := $"inbox".
Definition _inbox_t : ident := $"inbox_t".
Definition _is_owner : ident := $"is_owner".
Definition _job : ident := $"job".
Definition _job_device : ident := $"job_device".
Definition _main : ident := $"main".
Definition _msg_entry_t : ident := $"msg_entry_t".
Definition _pals_send : ident := $"pals_send".
Definition _pbt : ident := $"pbt".
Definition _received : ident := $"received".
Definition _rel_msg : ident := $"rel_msg".
Definition _ret : ident := $"ret".
Definition _run_device : ident := $"run_device".
Definition _state : ident := $"state".
Definition _sync_dev_state : ident := $"sync_dev_state".
Definition _tid : ident := $"tid".
Definition _update_demand : ident := $"update_demand".
Definition _use_resource : ident := $"use_resource".
Definition _write_log : ident := $"write_log".
Definition _t'1 : ident := 128%positive.

Section PARAMETRIZATION.

Variable task_id: Z.

Definition v_TASK_ID := {|
  gvar_info := tschar;
  gvar_init := (Init_int8 (Int.repr task_id) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_acq_msg := {|
  gvar_info := (tarray tschar 8);
  gvar_init := (Init_int8 (Int.repr 1) :: Init_space 7 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_rel_msg := {|
  gvar_info := (tarray tschar 8);
  gvar_init := (Init_int8 (Int.repr 2) :: Init_space 7 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_state := {|
  gvar_info := (Tstruct __dev_state noattr);
  gvar_init := (Init_space 2 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_sync_dev_state := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_inbox, (tptr (Tstruct _inbox_t noattr))) ::
                (_dst, (tptr (Tstruct __dev_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_e1, (tptr (Tstruct _msg_entry_t noattr))) ::
               (_e2, (tptr (Tstruct _msg_entry_t noattr))) :: (_t'1, tint) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _e1
    (Ebinop Oadd
      (Efield
        (Ederef (Etempvar _inbox (tptr (Tstruct _inbox_t noattr)))
          (Tstruct _inbox_t noattr)) _entry
        (tarray (Tstruct _msg_entry_t noattr) 16))
      (Econst_int (Int.repr 1) tint) (tptr (Tstruct _msg_entry_t noattr))))
  (Ssequence
    (Sset _e2
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _inbox (tptr (Tstruct _inbox_t noattr)))
            (Tstruct _inbox_t noattr)) _entry
          (tarray (Tstruct _msg_entry_t noattr) 16))
        (Econst_int (Int.repr 2) tint) (tptr (Tstruct _msg_entry_t noattr))))
    (Ssequence
      (Sifthenelse (Efield
                     (Ederef
                       (Etempvar _e1 (tptr (Tstruct _msg_entry_t noattr)))
                       (Tstruct _msg_entry_t noattr)) _received tschar)
        (Sset _t'1 (Econst_int (Int.repr 1) tint))
        (Sset _t'1
          (Ecast
            (Efield
              (Ederef (Etempvar _e2 (tptr (Tstruct _msg_entry_t noattr)))
                (Tstruct _msg_entry_t noattr)) _received tschar) tbool)))
      (Sifthenelse (Etempvar _t'1 tint)
        (Sassign
          (Efield
            (Ederef (Etempvar _dst (tptr (Tstruct __dev_state noattr)))
              (Tstruct __dev_state noattr)) _is_owner tschar)
          (Econst_int (Int.repr 1) tint))
        Sskip))))
|}.

Definition f_get_new_demand := {|
  fn_return := tschar;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_d, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _check_demand (Tfunction Tnil tint cc_default))
      nil)
    (Sset _d (Etempvar _t'1 tint)))
  (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 5) tint) (Etempvar _d tint)
                 tint)
    (Sreturn (Some (Econst_int (Int.repr 5) tint)))
    (Sifthenelse (Ebinop Olt (Etempvar _d tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      (Sreturn (Some (Etempvar _d tint))))))
|}.

Definition f_update_demand := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct __dev_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_d, tschar) :: (_t'1, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Efield
                   (Ederef
                     (Etempvar _dst (tptr (Tstruct __dev_state noattr)))
                     (Tstruct __dev_state noattr)) _demand tschar)
                 (Econst_int (Int.repr 0) tint) tint)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _get_new_demand (Tfunction Tnil tschar cc_default)) nil)
        (Sset _d (Ecast (Etempvar _t'1 tschar) tschar)))
      (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tint)
                     (Etempvar _d tschar) tint)
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _dst (tptr (Tstruct __dev_state noattr)))
                (Tstruct __dev_state noattr)) _demand tschar)
            (Etempvar _d tschar))
          (Sreturn (Some (Econst_int (Int.repr 1) tint))))
        Sskip))
    Sskip)
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_run_device := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dstate, (tptr (Tstruct __dev_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_dmd, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _dmd
    (Ecast
      (Efield
        (Ederef (Etempvar _dstate (tptr (Tstruct __dev_state noattr)))
          (Tstruct __dev_state noattr)) _demand tschar) tschar))
  (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tint)
                 (Etempvar _dmd tschar) tint)
    (Ssequence
      (Scall None (Evar _use_resource (Tfunction Tnil tvoid cc_default)) nil)
      (Ssequence
        (Sset _dmd
          (Ecast
            (Ebinop Osub (Etempvar _dmd tschar)
              (Econst_int (Int.repr 1) tint) tint) tschar))
        (Sassign
          (Efield
            (Ederef (Etempvar _dstate (tptr (Tstruct __dev_state noattr)))
              (Tstruct __dev_state noattr)) _demand tschar)
          (Etempvar _dmd tschar))))
    Sskip))
|}.

Definition f_job_device := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_tid, tschar) ::
                (_dstate, (tptr (Tstruct __dev_state noattr))) ::
                (_pbt, tulong) ::
                (_inbox, (tptr (Tstruct _inbox_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Efield
                   (Ederef
                     (Etempvar _dstate (tptr (Tstruct __dev_state noattr)))
                     (Tstruct __dev_state noattr)) _is_owner tschar)
                 (Econst_int (Int.repr 0) tint) tint)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _dstate (tptr (Tstruct __dev_state noattr)))
            (Tstruct __dev_state noattr)) _is_owner tschar)
        (Econst_int (Int.repr 2) tint))
      (Ssequence
        (Scall None
          (Evar _pals_send (Tfunction
                             (Tcons tschar (Tcons (tptr tschar) Tnil)) tvoid
                             cc_default))
          ((Econst_int (Int.repr 6) tint) ::
           (Evar _rel_msg (tarray tschar 8)) :: nil))
        (Ssequence
          (Scall None
            (Evar _write_log (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Econst_int (Int.repr 0) tint) :: nil))
          (Sreturn None))))
    Sskip)
  (Ssequence
    (Scall None
      (Evar _sync_dev_state (Tfunction
                              (Tcons (tptr (Tstruct _inbox_t noattr))
                                (Tcons (tptr (Tstruct __dev_state noattr))
                                  Tnil)) tvoid cc_default))
      ((Etempvar _inbox (tptr (Tstruct _inbox_t noattr))) ::
       (Etempvar _dstate (tptr (Tstruct __dev_state noattr))) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _update_demand (Tfunction
                                 (Tcons (tptr (Tstruct __dev_state noattr))
                                   Tnil) tint cc_default))
          ((Etempvar _dstate (tptr (Tstruct __dev_state noattr))) :: nil))
        (Sset _ret (Etempvar _t'1 tint)))
      (Ssequence
        (Sifthenelse (Ebinop Oeq
                       (Efield
                         (Ederef
                           (Etempvar _dstate (tptr (Tstruct __dev_state noattr)))
                           (Tstruct __dev_state noattr)) _is_owner tschar)
                       (Econst_int (Int.repr 1) tint) tint)
          (Ssequence
            (Scall None
              (Evar _run_device (Tfunction
                                  (Tcons (tptr (Tstruct __dev_state noattr))
                                    Tnil) tvoid cc_default))
              ((Etempvar _dstate (tptr (Tstruct __dev_state noattr))) :: nil))
            (Sifthenelse (Ebinop Oeq
                           (Efield
                             (Ederef
                               (Etempvar _dstate (tptr (Tstruct __dev_state noattr)))
                               (Tstruct __dev_state noattr)) _demand tschar)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _dstate (tptr (Tstruct __dev_state noattr)))
                      (Tstruct __dev_state noattr)) _is_owner tschar)
                  (Econst_int (Int.repr 2) tint))
                (Scall None
                  (Evar _pals_send (Tfunction
                                     (Tcons tschar
                                       (Tcons (tptr tschar) Tnil)) tvoid
                                     cc_default))
                  ((Econst_int (Int.repr 6) tint) ::
                   (Evar _rel_msg (tarray tschar 8)) :: nil)))
              Sskip))
          (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tint)
                         (Etempvar _ret tint) tint)
            (Scall None
              (Evar _pals_send (Tfunction
                                 (Tcons tschar (Tcons (tptr tschar) Tnil))
                                 tvoid cc_default))
              ((Econst_int (Int.repr 6) tint) ::
               (Evar _acq_msg (tarray tschar 8)) :: nil))
            Sskip))
        (Scall None
          (Evar _write_log (Tfunction (Tcons tint Tnil) tvoid cc_default))
          ((Econst_int (Int.repr 0) tint) :: nil))))))
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
  (Evar _job_device (Tfunction
                      (Tcons tschar
                        (Tcons (tptr (Tstruct __dev_state noattr))
                          (Tcons tulong
                            (Tcons (tptr (Tstruct _inbox_t noattr)) Tnil))))
                      tvoid cc_default))
  ((Evar _TASK_ID tschar) ::
   (Eaddrof (Evar _state (Tstruct __dev_state noattr))
     (tptr (Tstruct __dev_state noattr))) :: (Etempvar _pbt tulong) ::
   (Etempvar _inbox (tptr (Tstruct _inbox_t noattr))) :: nil))
|}.

Definition composites : list composite_definition :=
(Composite _msg_entry_t Struct
   ((_received, tschar) :: (_content, (tarray tschar 15)) :: nil)
   noattr ::
 Composite _inbox_t Struct
   ((_entry, (tarray (Tstruct _msg_entry_t noattr) 16)) :: nil)
   noattr ::
 Composite __dev_state Struct
   ((_is_owner, tschar) :: (_demand, tschar) :: nil)
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
 (_pals_send,
   Gfun(External (EF_external "pals_send"
                   (mksignature (AST.Tint :: AST.Tlong :: nil) AST.Tvoid
                     cc_default)) (Tcons tschar (Tcons (tptr tschar) Tnil))
     tvoid cc_default)) ::
 (_write_log,
   Gfun(External (EF_external "write_log"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_check_demand,
   Gfun(External (EF_external "check_demand"
                   (mksignature nil AST.Tint cc_default)) Tnil tint
     cc_default)) ::
 (_use_resource,
   Gfun(External (EF_external "use_resource"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) :: (_TASK_ID, Gvar v_TASK_ID) ::
 (_acq_msg, Gvar v_acq_msg) :: (_rel_msg, Gvar v_rel_msg) ::
 (_state, Gvar v_state) ::
 (_sync_dev_state, Gfun(Internal f_sync_dev_state)) ::
 (_get_new_demand, Gfun(Internal f_get_new_demand)) ::
 (_update_demand, Gfun(Internal f_update_demand)) ::
 (_run_device, Gfun(Internal f_run_device)) ::
 (_job_device, Gfun(Internal f_job_device)) ::
 (_job, Gfun(Internal f_job)) :: nil).

Definition public_idents : list ident :=
(_job :: _job_device :: _run_device :: _update_demand :: _get_new_demand ::
 _sync_dev_state :: _state :: _rel_msg :: _acq_msg :: _TASK_ID ::
 _use_resource :: _check_demand :: _write_log :: _pals_send ::
 ___builtin_debug :: ___builtin_write32_reversed ::
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
