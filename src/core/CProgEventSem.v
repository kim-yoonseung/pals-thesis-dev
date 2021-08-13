From ITree Require Import ITree.
From compcert Require Import AST Globalenvs Values Memory.
From compcert Require Clight.

Require Import sflib.
Require Import StdlibExt IntegersExt.

Require Import SysSem.
Require Import SyncSysModel.
Require Import IPModel DiscreteTimeModel IntByteModel.
Require Import NWSysModel.
Require Import OSModel OSNodes.
Require Import ProgSem.

Require Import ZArith String List Lia.

(* Import Params. *)

Set Nested Proofs Allowed.

(* Lemma Int_repr_eq_inv_signed *)
(*       z i *)
(*       (RANGE_Z: IntRange.sintz z) *)
(*       (REPR_EQ: Int.repr z = i) *)
(*   : z = Int.signed i. *)
(* Proof. *)
(*   subst i. r in RANGE_Z. *)
(*   rewrite Int.signed_repr. *)
(*   2: { apply RANGE_Z. } *)
(*   ss. *)
(* Qed. *)

Inductive extcallE: Type -> Type :=
| ExtcallEvent_Int (fname: string) (* (sig: signature) *) (args: list val)
  : extcallE int
| ExtcallEvent_Void (fname: string) (* (sig: signature) *) (args: list val)
  : extcallE unit
.

Notation obsE := (extcallE +' errE).
Notation progE := (osE +' obsE).
(* Notation nodeE := (nbE +' extcallE). *)


Lemma IntNat_of_nat_eq_inv_sint
      n m
      (RANGE_N: IntRange.sint n)
      (RANGE_M: IntRange.sint m)
      (INT_EQ: IntNat.of_nat n = IntNat.of_nat m)
  : n = m.
Proof.
  unfold IntNat.of_nat in INT_EQ.
  assert (Int.signed (Int.repr (Z.of_nat n)) =
          Int.signed (Int.repr (Z.of_nat m))).
  { congruence. }
  rewrite Int.signed_repr in * by range_stac.
  rewrite Int.signed_repr in * by range_stac.
  apply Nat2Z.inj. eauto.
Qed.

Lemma map_Byte_eq_inv
      bs1 bs2
      (MAP_EQ: map Byte bs1 = map Byte bs2)
  : bs1 = bs2.
Proof.
  depgen bs2.
  induction bs1; i;
    destruct bs2; ss.
  inv MAP_EQ.
  erewrite IHbs1; eauto.
Qed.

Lemma IntNat_of_nat64_eq_inv_uint
      n m
      (RANGE_N: IntRange.uint64 n)
      (RANGE_M: IntRange.uint64 m)
      (INT_EQ: IntNat.of_nat64 n = IntNat.of_nat64 m)
  : n = m.
Proof.
  unfold IntNat.of_nat64 in INT_EQ.
  cut (Int64.unsigned (Int64.repr (Z.of_nat n)) =
          Int64.unsigned (Int64.repr (Z.of_nat m))).
  { rewrite Int64.unsigned_repr by range_stac.
    rewrite Int64.unsigned_repr by range_stac.
    apply Nat2Z.inj.
  }
  rewrite INT_EQ. ss.
Qed.


(** ** External functions for progE *)

(* OS *)

Definition open_socket_ef: AST.external_function :=
  EF_external "pals_socket"
              (mksignature nil AST.Tint cc_default).
Definition bind_socket_ef: AST.external_function :=
  EF_external "pals_bind"
              (mksignature (AST.Tint :: AST.Tint :: nil)
                           AST.Tint cc_default).
Definition join_socket_ef: AST.external_function :=
  EF_external "pals_mcast_join"
              (mksignature (AST.Tint :: AST.Tlong :: nil)
                           AST.Tvoid cc_default).
(* Definition close_socket_ef: AST.external_function := *)
(*   EF_external "pals_close" *)
(*               (mksignature (AST.Tint :: nil) *)
(*                            AST.Tint cc_default). *)

Definition sendto_ef: AST.external_function :=
  EF_external "pals_sendto"
              (mksignature
                 (AST.Tint :: AST.Tlong :: AST.Tint :: AST.Tlong ::
                           AST.Tint :: nil) AST.Tint cc_default).
Definition recvfrom_ef: AST.external_function :=
  EF_external "pals_recvfrom"
              (mksignature (AST.Tint :: AST.Tlong :: AST.Tint :: nil)
                           AST.Tint cc_default).
Definition get_time_ef: AST.external_function :=
  EF_external "pals_current_time"
              (mksignature nil AST.Tlong cc_default).
Definition init_timer_ef: AST.external_function :=
  EF_external "pals_init_timer"
              (mksignature nil AST.Tint cc_default).
Definition wait_timer_ef: AST.external_function :=
  EF_external "pals_wait_timer"
              (mksignature (AST.Tlong :: nil)
                           AST.Tint cc_default).

Definition os_efs: list AST.external_function :=
  [open_socket_ef; bind_socket_ef; join_socket_ef;
  sendto_ef; recvfrom_ef;
  get_time_ef; init_timer_ef; wait_timer_ef ].
  (* get_user_input_ef; check_demand_ef; *)
  (* use_resource_ef; mark_complete_ef]. *)

(**)

Definition check_os_ef (ef: AST.external_function) : bool :=
  if find (fun ef' => Coqlib.proj_sumbool
                     (AST.external_function_eq ef ef')) os_efs
  then true else false.

(* Definition check_tlim_ef (ef: AST.external_function): bool := *)
(*   Coqlib.proj_sumbool (AST.external_function_eq ef). *)

Inductive ip_in_mem (ip: ip_t) (m: Mem.mem)
          (blk: block) (ofs: ptrofs): Prop :=
  IPInMem
    (mvs: list memval) (ip_bytes: list byte)
    (LOADBYTES: Mem.loadbytes m blk (Ptrofs.unsigned ofs)
                              (Zlength ip_bytes + 1) = Some mvs)
    (MEMDATA_BYTES: inj_bytes ip_bytes ++
                              [Memdata.Byte Byte.zero] = mvs)
    (CONVERT_FORMAT: IP.convert_brep ip_bytes = Some ip)
.



Lemma loadbytes_until_zero_length_not_lt
      z1 z2 bs1 bs2
      m b ofs
      (LB1: Mem.loadbytes m b ofs z1 =
            Some (inj_bytes bs1 ++ [Byte Byte.zero]))
      (LB2: Mem.loadbytes m b ofs z2 =
            Some (inj_bytes bs2 ++ [Byte Byte.zero]))
      (NZERO1: Forall (fun b => b <> Byte.zero) bs1)
      (NZERO2: Forall (fun b => b <> Byte.zero) bs2)
      (LT: (0 <= z1 < z2)%Z)
  : False.
Proof.
  assert (exists z', <<Z_POS': 0 < z'>> /\
                          <<Z'_DIFF: z1 + z' = z2>>)%Z.
  { exists (z2 - z1)%Z.
    splits; nia. }
  destruct LT as [Z1_NNEG LT12]. des.
  subst z2.
  apply Mem.loadbytes_split in LB2; cycle 1.
  { nia. }
  { nia. }

  destruct LB2 as (bytes1 & bytes2 & BYTES1 & BYTES2 & BS_EQ).
  rewrite LB1 in BYTES1.

  assert (INJ_BYTE_EX: forall b (IN1: In b bytes1),
             In b (inj_bytes bs2)).
  { assert (BYTES2_LEN_POS: 0 < length bytes2).
    { apply Mem.loadbytes_length in BYTES2.
      nia. }

    hexploit (des_snoc _ bytes2); eauto. i. des.
    subst bytes2.
    unfold snoc in BS_EQ.
    rewrite app_assoc in BS_EQ.

    hexploit snoc_eq_inv.
    { unfold snoc.
      apply BS_EQ. }
    intros (INJ_BS2_EQ & X_ZERO).
    rewrite INJ_BS2_EQ.
    apply in_or_app. left. eauto.
  }

  assert (BYTE_EX: forall b (IN1: In b bytes1),
             exists b', In b' bs2 /\ Byte b' = b).
  { intros mb MB_IN.
    hexploit INJ_BYTE_EX; eauto.
    intro IN_INJ.
    unfold inj_bytes in IN_INJ.
    rewrite in_map_iff in IN_INJ. des.
    esplits; eauto.
  }

  hexploit (BYTE_EX (Byte Byte.zero)).
  { clarify.
    apply in_or_app. right. ss. eauto. }
  i. des.

  rewrite Forall_forall in NZERO2.
  hexploit NZERO2; eauto.
  intro B. apply B. congruence.
Qed.


Lemma ip_in_mem_unique
      m blk ofs ip1 ip2
      (IP1: ip_in_mem ip1 m blk ofs)
      (IP2: ip_in_mem ip2 m blk ofs)
  : ip1 = ip2.
Proof.
  inv IP1.
  renames ip_bytes LOADBYTES CONVERT_FORMAT into
          ip_bs1 LOAD1 CONV1.
  inv IP2.
  renames ip_bytes LOADBYTES CONVERT_FORMAT into
          ip_bs2 LOAD2 CONV2.

  hexploit IP.valid_ip_brep_spec; try apply CONV1.
  intros (NZ1 & MAX1 & IP_RANGE1).
  hexploit IP.valid_ip_brep_spec; try apply CONV2.
  intros (NZ2 & MAX2 & IP_RANGE2).

  assert (LEN_EQ: Zlength ip_bs1 = Zlength ip_bs2).
  { destruct (Z_dec' (Zlength ip_bs1) (Zlength ip_bs2))
      as [[A | B] | C].
    - hexploit (loadbytes_until_zero_length_not_lt
                  (Zlength ip_bs1 + 1) (Zlength ip_bs2 + 1)); eauto.
      { splits.
        - rewrite Zlength_correct. nia.
        - nia. }
      ss.
    - hexploit (loadbytes_until_zero_length_not_lt
                  (Zlength ip_bs2 + 1) (Zlength ip_bs1 + 1)); eauto.
      { splits.
        - rewrite Zlength_correct. nia.
        - nia. }
      ss.
    - ss.
  }

  rewrite <- LEN_EQ in LOAD2.
  rewrite LOAD2 in LOAD1.

  assert (inj_bytes ip_bs1 = inj_bytes ip_bs2).
  { inv LOAD1.
    hexploit snoc_eq_inv; eauto. i. des. eauto. }

  cut (proj_bytes (inj_bytes ip_bs1) =
       proj_bytes (inj_bytes ip_bs2)).
  { do 2 rewrite proj_inj_bytes.
    i. congruence. }
  congruence.
Qed.


Inductive cprog_os_ec (senv: Senv.t) (ef: external_function)
  : list val -> Mem.mem -> forall {R}, osE R -> Prop :=
(* socket *)
| CProgOSEC_OpenSocket
    args m
    (EF: ef = open_socket_ef)
    (ARGS: args = [])
    (* (EC: ec = EventCall (subevent _ OSOpenSocket)) *)
  : cprog_os_ec senv ef args m OSOpenSocket

| CProgOSEC_BindSocket
    args m
    sid pn
    (EF: ef = bind_socket_ef)
    (RANGE_SID: IntRange.sint sid)
    (RANGE_PN: IntRange.sint pn)
    (ARGS: args = [Vint (IntNat.of_nat sid);
                  Vint (IntNat.of_nat pn)])
    (* (EC: ec = EventCall (subevent _ (OSBindSocket sid pn))) *)
  : cprog_os_ec senv ef args m (OSBindSocket sid pn)

| CProgOSEC_JoinSocket
    args m
    sid blk ofs ip_mcast
    (EF: ef = join_socket_ef)
    (RANGE_SID: IntRange.sint sid)
    (ARGS: args = [Vint (IntNat.of_nat sid);
                  Vptr blk ofs])
    (IP_IN_MEM: ip_in_mem ip_mcast m blk ofs)
    (* (EC: ec = EventCall (subevent _ )) *)
  : cprog_os_ec senv ef args m (OSJoinSocket sid ip_mcast)

| CProgOSEC_Sendto
    args m
    sid blk_buf ofs_buf sz_buf
    blk_ip ofs_ip
    bs ip_dest pn_dest
    (EF: ef = sendto_ef)
    (RANGE_SID: IntRange.sint sid)
    (RANGE_BUF_SIZE: IntRange.sint sz_buf)
    (RANGE_PN: IntRange.sint pn_dest)
    (ARGS: args = [Vint (IntNat.of_nat sid);
                  Vptr blk_ip ofs_ip;
                  Vint (IntNat.of_nat pn_dest);
                  Vptr blk_buf ofs_buf;
                  Vint (IntNat.of_nat sz_buf)])
    (BS_IN_MEM: Mem.loadbytes m blk_buf (Ptrofs.unsigned ofs_buf)
                              (Z.of_nat sz_buf) =
                Some (List.map Memdata.Byte bs))
    (IP_IN_MEM: ip_in_mem ip_dest m blk_ip ofs_ip)
    (* (EC: ec = EventCall (subevent _ (OSSendto sid bs ip_dest pn_dest))) *)
  : cprog_os_ec senv ef args m
                (OSSendto sid bs ip_dest pn_dest)

| CProgOSEC_Recvfrom
    args m
    sid blk_buf ofs_buf sz_buf
    (* (mvs: list memval) *)
    (EF: ef = recvfrom_ef)
    (RANGE_SID: IntRange.sint sid)
    (RANGE_BUF_SIZE: IntRange.sint sz_buf)
    (ARGS: args = [Vint (IntNat.of_nat sid);
                  Vptr blk_buf ofs_buf;
                  Vint (IntNat.of_nat sz_buf)])
    (WRITABLE_PERM: Mem.range_perm
                      m blk_buf (Ptrofs.unsigned ofs_buf)
                      (Ptrofs.unsigned ofs_buf + Z.of_nat sz_buf)
                      Cur Writable)
    (* (BS_IN_MEM: Mem.loadbytes m blk_buf (Ptrofs.unsigned ofs_buf) *)
    (*                           (Z.of_nat sz_buf) = *)
    (*             Some mvs) *)
    (* (EC: ec = EventCall (subevent _ (OSRecvfrom sid sz_buf))) *)
  : cprog_os_ec senv ef args m (OSRecvfrom sid sz_buf)

(* timer *)
| CProgOSEC_GetTime
    args m
    (EF: ef = get_time_ef)
    (ARGS: args = [])
    (* (EC: ec = EventCall (subevent _ OSGetTime)) *)
  : cprog_os_ec senv ef args m OSGetTime

| CProgOSEC_InitTimer
    args m
    (EF: ef = init_timer_ef)
    (ARGS: args = [])
    (* (EC: ec = EventCall (subevent _ OSInitTimer)) *)
  : cprog_os_ec senv ef args m OSInitTimer

| CProgOSEC_WaitTimer
    args m tm
    (EF: ef = wait_timer_ef)
    (RANGE_TM: IntRange.uint64 tm)
    (ARGS: args = [Vlong (IntNat.of_nat64 tm)])
    (* (EC: ec = EventCall (subevent _ (OSWaitTimer tm))) *)
  : cprog_os_ec senv ef args m (OSWaitTimer tm)
.

Inductive cprog_os_estep
          (senv: Senv.t)
  : forall {R}, osE R -> R ->
         list val -> Mem.mem -> val -> mem -> Prop :=
(* socket *)
| CProgOSEStep_OpenSocket
    (ret: Z) (args: list val) m retv
    (* (EVT: evt = Event (subevent _ OSOpenSocket) ret) *)
    (ARGS: args = [])
    (RANGE_RET: IntRange.sintz ret)
    (RET_VAL: retv = Vint (Int.repr ret))
  : cprog_os_estep senv OSOpenSocket
                   ret args m retv m

| CProgOSEStep_BindSocket
    (ret: Z) (args: list val) m retv
    sid pn
    (* (EVT: evt = Event (subevent _ (OSBindSocket sid pn)) ret) *)
    (RET_VAL: retv = Vint (Int.repr ret))
    (RANGE_RET: IntRange.sintz ret)
  : cprog_os_estep senv (OSBindSocket sid pn) ret
                   args m retv m

| CProgOSEStep_JoinSocket
    (ret: unit) (args: list val) m retv
    sid ip_mcast
    (* (EVT: evt = Event (subevent _ (OSJoinSocket sid ip_mcast)) ret) *)
    (RET_VAL: retv = Vundef)
  : cprog_os_estep senv (OSJoinSocket sid ip_mcast) ret
                   args m retv m

| CProgOSEStep_Sendto
    (ret: Z) (args: list val) m retv
    sid bs ip_d pn_d
    (* (EVT: evt = Event (subevent _ (OSSendto sid bs ip_d pn_d)) ret) *)
    (RET_VAL: retv = Vint (Int.repr ret))
    (RANGE_RET: IntRange.sintz ret)
  : cprog_os_estep senv (OSSendto sid bs ip_d pn_d) ret
                   args m retv m

| CProgOSEStep_Recvfrom
    (ret: (bytes?)) retz
    (args: list val) m retv m'
    sid sz_buf
    blk_buf ofs_buf
    (* (EVT: evt = Event (subevent _ (OSRecvfrom sid sz_buf)) ret) *)
    (ARGS: args = [Vint (IntNat.of_nat sid);
                  Vptr blk_buf ofs_buf;
                  Vint (IntNat.of_nat sz_buf)])
    (RETZ: (ret = None /\ m' = m /\ retz = Z_mone) \/
           (exists bs, ret = Some bs /\
                  Mem.storebytes
                    m blk_buf (Ptrofs.unsigned ofs_buf)
                    (List.map Memdata.Byte bs) = Some m' /\
                  retz = Zlength bs /\
                  length bs <= sz_buf /\
                  length bs <= Packet.maxlen))
    (RET_VAL: retv = Vint (Int.repr retz))
  : cprog_os_estep senv (OSRecvfrom sid sz_buf) ret
                   args m retv m'

(* timer *)
| CProgOSEStep_GetTime
    (ret: Z) (args: list val) m retv
    (* (EVT: evt = Event (subevent _ OSGetTime) ret) *)
    (RET_VAL: retv = Vlong (Int64.repr ret))
    (RANGE_RET: IntRange.uintz64 ret)
  : cprog_os_estep senv OSGetTime ret
                   args m retv m

| CProgOSEStep_InitTimer
    (ret: Z) (args: list val) m retv
    (* (EVT: evt = Event (subevent _ OSInitTimer) ret) *)
    (RET_VAL: retv = Vint (Int.repr ret))
    (RANGE_RET: IntRange.sintz ret)
  : cprog_os_estep senv OSInitTimer ret
                   args m retv m

| CProgOSEStep_WaitTimer
    (ret: Z) (args: list val) m retv tm
    (* (EVT: evt = Event (subevent _ (OSWaitTimer tm)) ret) *)
    (RET_VAL: retv = Vint (Int.repr ret))
    (RANGE_RET: IntRange.sintz ret)
  : cprog_os_estep senv (OSWaitTimer tm) ret
                    args m retv m

.


Section CPROG_SYS_EC.

  Definition retty_of_extcallE {R} (ec: extcallE R): rettype :=
    match ec with
    | ExtcallEvent_Int _ _ => Tint
    | ExtcallEvent_Void _ _ => Tvoid
    end.

  Inductive match_extcallE
    : forall {R}, external_function -> list val -> extcallE R -> Type :=
  | MatchExtcallE
      fname sig args
      (RET_INT: sig_res sig = Tint)
    : match_extcallE (EF_external fname sig) args
                     (ExtcallEvent_Int fname args)
  | MatchExtcallE_Void
      fname sig args
      (RET_VOID: sig_res sig = Tvoid)
    : match_extcallE (EF_external fname sig) args
                     (ExtcallEvent_Void fname args)
  .

  Section CPROG_EVENT_SEM.
    (* Context `{CProgSysEvent}. *)

    (* Match C program states with event calls *)
    Inductive cprog_ec
              (senv: Senv.t) (ef: external_function)
      : list val -> Mem.mem -> event_call (osE +' obsE) -> Prop :=
    | CProgEC_OS
        R (ose: osE R) ec
        args m
        (OS_EC: cprog_os_ec senv ef args m ose)
        (EVENT_CALL: ec = EventCall (subevent _ ose))
      : cprog_ec senv ef args m ec

    (* | CProgEC_TimeLimit *)
    (*     args m ec tm *)
    (*     (EF: ef = time_limit_ef) *)
    (*     (RANGE_TM: IntRange.uint64 tm) *)
    (*     (ARGS: args = [Vlong (IntNat.of_nat64 tm)]) *)
    (*     (EVENT_CALL: ec = EventCall (subevent _ (TimeLimitEvent tm))) *)
    (*   : cprog_ec senv ef args m ec *)

    | CProgEC_SystemEvent
        R args m ec (exte: extcallE R)
        (* (ret: R) *)
        (* fname sig *)
        (* (EXTFUN_EXTERNAL: ef = EF_external fname sig) *)
        (* (SYS_EC: cprog_sys_ec senv ef args m syse) *)
        (NOT_OS_CALL: forall R (ose: osE R), ~ cprog_os_ec senv ef args m ose)
        (* (NOT_SET_TLIM: ef <> time_limit_ef) *)
        (EVENT_CALL: ec = EventCall (subevent _ exte))
        (MATCH_EXTC: match_extcallE ef args exte)
      : cprog_ec senv ef args m ec
    .

    Inductive match_ext_retv: rettype -> forall {R}, R -> val -> Prop :=
    | MatchExtRetv_Int
        (n: int)
      : match_ext_retv Tint n (Vint n)
    | MatchExtRetv_Void
      : match_ext_retv Tvoid tt Vundef
    .

    (* system's cprog_match_after_event *)
    Inductive cprog_estep
              (senv: Senv.t)
              (evt: event (osE +' obsE)):
      list val -> Mem.mem -> val -> mem -> Prop :=
    (* socket *)
    | CProgEStep_OS
        R (ose: osE R) ret
        args m retv m'
        (OS_ESTEP: cprog_os_estep senv ose ret
                                  args m retv m')
        (EVENT: evt = Event (subevent _ ose) ret)
      : cprog_estep senv evt args m retv m'

    (* | CProgEStep_TimeLimit *)
    (*     (args: list val) m retv tm *)
    (*     (RET_VAL: retv = Vundef) *)
    (*     (EVENT: evt = Event (subevent _ (TimeLimitEvent tm)) tt) *)
    (*   : cprog_estep senv evt args m retv m *)

    | CProgEStep_SystemEvent
        R (exte: extcallE R) (ret: R) (retv: val)
        (args: list val) m
        (EVENT: evt = Event (subevent _ exte) ret)
        (MATCH_RETV: match_ext_retv (retty_of_extcallE exte) ret retv)
      : cprog_estep senv evt args m retv m
    .

    Program Instance cprog_event_instance
      : @cprog_event (osE +' obsE) :=
      {| cprog_event_call := cprog_ec ;
         cprog_event_step := cprog_estep ;
      |}.
    Next Obligation.
      inv AT_EVT1; inv AT_EVT2; ss.
      - inv OS_EC; inv OS_EC0; existT_elim1; ss.
        + list_eq_inv_tac.
          repeat f_equal.
          * apply IntNat_of_nat_eq_inv_sint; eauto.
            congruence.
          * apply IntNat_of_nat_eq_inv_sint; eauto.
            congruence.
        + list_eq_inv_tac.
          repeat f_equal.
          * apply IntNat_of_nat_eq_inv_sint; eauto.
            congruence.
          * inv ARGS1.
            eapply ip_in_mem_unique; eauto.
        + list_eq_inv_tac.
          repeat match goal with
                 | H: Vptr _ _ = Vptr _ _ |- _ => inv H
                 end.
          assert (sz_buf0 = sz_buf).
          { apply IntNat_of_nat_eq_inv_sint; eauto.
            congruence. }
          assert (sid0 = sid).
          { apply IntNat_of_nat_eq_inv_sint; eauto.
            congruence. }
          assert (pn_dest0 = pn_dest).
          { apply IntNat_of_nat_eq_inv_sint; eauto.
            congruence. }
          clarify.
          repeat f_equal.
          * apply map_Byte_eq_inv; eauto.
          * eapply ip_in_mem_unique; eauto.
        + list_eq_inv_tac.
          repeat match goal with
                 | H: Vptr _ _ = Vptr _ _ |- _ => inv H
                 end.
          assert (sz_buf0 = sz_buf).
          { apply IntNat_of_nat_eq_inv_sint; eauto.
            congruence. }
          assert (sid0 = sid).
          { apply IntNat_of_nat_eq_inv_sint; eauto.
            congruence. }
          clarify.
        + list_eq_inv_tac.
          repeat f_equal.
          eapply IntNat_of_nat64_eq_inv_uint; eauto.
          congruence.
      (* - inv OS_EC; ss. *)
      - exfalso.
        hexploit NOT_OS_CALL; eauto.
      (* - inv OS_EC; ss. *)
      (* - list_eq_inv_tac. *)
      (*   repeat f_equal. *)
      (*   eapply IntNat_of_nat64_eq_inv_uint; eauto. *)
      (*   congruence. *)
      - exfalso.
        hexploit NOT_OS_CALL; eauto.
      - inv MATCH_EXTC; inv MATCH_EXTC0; ss.
        + congruence.
        + congruence.
    Qed.

  End CPROG_EVENT_SEM.
End CPROG_SYS_EC.
