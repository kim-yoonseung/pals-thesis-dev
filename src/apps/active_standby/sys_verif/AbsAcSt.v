From Paco Require Import paco.
From ITree Require Import ITree.
Require Import sflib.

Require Import StdlibExt IntegersExt.
Require Import SysSem.
Require Import SyncSysModel.
Require Import RTSysEnv.
Require Import Executable.

Require Import CProgEventSem.

Require Import FMSim FMSim_Switch.
Require Import PALSSystem.
Require Import BehavUtils.
Require Import SystemAbstraction.

Require Import AcStSystem.

Require Import ZArith Streams List Lia.

Import ITreeNotations.

Local Opaque Z.of_nat Z.to_nat.

Set Nested Proofs Allowed.

(* Local Notation sysE := (extcallE +' errE). *)

Inductive abs_msg: Set :=
| Tgl
| Acq
| Rel
| Grant
| Heartbeat
.

Inductive amsgE: Type -> Type :=
| SendAbsMsg (msg: abs_msg): amsgE unit.

(* abstract system itree_step (possibly fails) *)
Inductive itree_astep {E S}
  : itree (E +' amsgE) S ->
    events E -> list abs_msg -> S? -> Prop :=
| ITreeAStep_Fail
    itr
  : itree_astep itr [] [] None
| ITreeAStep_Ret
    itr (s: S)
    (OBS_RET: observe itr = RetF s)
  : itree_astep itr [] [] (Some s)
| ITreeAStep_Tau
    itr itr' es ms (res: S?)
    (OBS_RET: observe itr = TauF itr')
    (ASTEP_REST: itree_astep itr' es ms res)
  : itree_astep itr es ms res
| ITreeAStep_Evt
    itr R (e: E R) k (ret: R)
    (es': events E) ms' (res: S?)
    (OBS_VIS: observe itr = VisF (inl1 e) k)
    (ASTEP_REST: itree_astep (k ret) es' ms' res)
  : itree_astep itr (Event e ret :: es') ms' res
| ITreeAStep_Msg
    itr msg k
    (es': events E) ms' (res: S?)
    (OBS_VIS: observe itr = VisF (inr1 (SendAbsMsg msg)) k)
    (ASTEP_REST: itree_astep (k tt) es' ms' res)
  : itree_astep itr es' (msg :: ms') res
.

Module AbsAcSt.

  Definition MAX_TIMEOUT: nat := 5.

  Inductive ctrl_state: Type :=
  | CtrlUninit
  | SentHB
  .

  Inductive dev_state: Type :=
  | DevUninit
  (* Send Rel and be Idle *)
  | SentRel
  | Idle
  (* Send Acq and be Waiting *)
  | SentAcq (demand: nat)
  | Waiting (demand: nat)
  (* Owner (including the case Grant just arrived) *)
  | Owner (demand_left: nat)
  .

  Inductive failed_side_t: Set :=
  | AllWorking
  | FstFailed (recover: bool)
  | SndFailed (recover: bool)
  .

  Inductive state: Type :=
  | PreState
  | Running
      (active_side: bool)
      (failed_side: failed_side_t)
      (queue: list Tid)
      (timeout: nat)

      (to_toggle: bool)
      (dev1: dev_state?)
      (dev2: dev_state?)
      (dev3: dev_state?)
  | OutOfService
  .

  Definition console_itree: itree (obsE +' amsgE) unit :=
    inp <- trigger GetUserInput ;;
    (if negb (Int.eq Int.zero inp) then
       trigger (SendAbsMsg Tgl)
     else Ret tt);;
    trigger (WriteLog 0).

  Definition ctrl_itree
             (is_active: bool)
    : itree (obsE +' amsgE) unit :=
    trigger (SendAbsMsg Grant) ;;
    trigger (SendAbsMsg Heartbeat) ;;
    trigger (WriteLog (if is_active then 1 else 2)).

  (* at the beginning of period *)
  Definition set_active_side
             (tgl: bool) (asd: bool)
             (hb_from1 hb_from2: bool)
    : bool * bool(* if changed by hb_check *) :=
    (* match oasd with *)
    (* | None => (true, false) *)
    (* | Some asd => *)
      let hb_actv := if asd then hb_from1 else hb_from2 in
      let hb_stby := if asd then hb_from2 else hb_from1 in
      if negb hb_actv then
        (negb asd, true)
      else
        if (tgl && hb_stby)%bool then
          (negb asd, false)
        else (asd, false)
               (* end. *)
  .

  (* Reset timeout if (1) hb not arrived from active side *)
  (* (2) and not sure about sending Grant *)
  Definition check_and_reset_timeout
             (achg_by_hbchk: bool)
             (tout: nat)
    : nat :=
    if achg_by_hbchk then
      if (tout =? MAX_TIMEOUT) then 0 else tout
    else tout.

  Definition apply_devmsg (tid_dev: Tid) (dst: dev_state?)
             (q: list Tid) (tout: nat)
    : list Tid * nat :=
    admit_t.

  Definition pick_new_owner (q: list Tid) (tout: nat)
    : list Tid * nat * Tid? :=
    admit_t.

  Definition update_queue
             (dst1: dev_state?)
             (dst2: dev_state?)
             (dst3: dev_state?)
             (q: list Tid) (tout: nat)
    : list Tid * nat * (Tid?) :=
    let (q1, tout1) := apply_devmsg tid_dev1 dst1 q tout in
    let (q2, tout2) := apply_devmsg tid_dev2 dst2 q1 tout1 in
    let (q3, tout3) := apply_devmsg tid_dev3 dst3 q2 tout2 in
    pick_new_owner q3 tout3.

  Definition active_side_sent_grant (asd': bool)
             (ms_c1 ms_c2: list abs_msg)
    : bool :=
    admit_t.

  Definition get_failed_side (es_c1 es_c2: events obsE)
    : failed_side_t? :=
    admit_t.

  Definition check_toggle (ms_con: list abs_msg): bool :=
    admit_t.

  Inductive step (sytm: Z)
    : state -> list (events obsE) -> state -> Prop :=
  | Step_AlreadyFailed
      (es_con es_c1 es_c2 es_d1 es_d2 es_d3: events obsE)
    : step sytm OutOfService
           [es_con; es_c1; es_c2; es_d1; es_d2; es_d3]
           OutOfService

  | Step_PrePre
      es_con ms_con (ou: unit?)
      (ASTEP_CON: itree_astep console_itree es_con ms_con ou)
    : step sytm PreState (es_con :: repeat [] 5) PreState
  | Step_PreFail
      (es_con es_d1 es_d2 es_d3: events obsE)
      (DEV_COMP_FIRST:
         es_d1 = [Event (inl1 (WriteLog 0)) tt] \/
         es_d2 = [Event (inl1 (WriteLog 0)) tt] \/
         es_d3 = [Event (inl1 (WriteLog 0)) tt])
    : step sytm PreState [es_con; []; []; es_d1; es_d2; es_d3]
           OutOfService
  | Step_StartRunning
      es_con ms_con ou
      es_c1 ms_c1 ocst1
      es_c2 ms_c2 ocst2
      odst1 odst2 odst3
      ttgl' fsd'
      (ASTEP_CON: itree_astep console_itree es_con ms_con ou)
      (ASTEP_CTRL1: itree_astep (ctrl_itree true)
                                es_c1 ms_c1 ocst1)
      (ASTEP_CTRL2: itree_astep (ctrl_itree false)
                                es_c2 ms_c2 ocst2)
      (TO_TOGGLE: ttgl' = check_toggle ms_con)
      (FAILED_SIDE: get_failed_side es_c1 es_c2 = Some fsd')
      (DST1: option_rel1 (fun dst => dst = Uninit) odst1)
      (DST2: option_rel1 (fun dst => dst = Uninit) odst2)
      (DST3: option_rel1 (fun dst => dst = Uninit) odst3)
    : step sytm PreState [es_con; es_c1; es_c2; []; []; []]
           (Running true fsd' [] O ttgl' odst1 odst2 odst3)

  | Step_RunningOK
      asd fsd q tout ttgl odst1 odst2 odst3
      asd' fsd' q' tout' ttgl' odst1' odst2' odst3'
      es_con es_c1 es_c2 es_d1 es_d2 es_d3
      chg_byhb

      (NEW_ACTIVE_SIDE:
         set_active_side ttgl asd (check_hb
         =
(asd', chg_byhb)
    : step sytm
           (Running asd fsd q tout ttgl odst1 odst2 odst3)
           [es_con; es_c1; es_c2; es_d1; es_d2; es_d3]
           (Running asd' fsd' q' tout' ttgl' odst1' odst2' odst3')

  | Step_RunningFails
      asd fsd q tout ttgl odst1 odst2 odst3
      es_con es_c1 es_c2 es_d1 es_d2 es_d3
      (* asd' fsd' q' tout' ttgl' odst1' odst2' odst3' *)
    : step sytm
           (Running asd fsd q tout ttgl odst1 odst2 odst3)
           [es_con; es_c1; es_c2; es_d1; es_d2; es_d3]
           OutOfService
  .

  (* active_side  *)


  AbsSys.t
