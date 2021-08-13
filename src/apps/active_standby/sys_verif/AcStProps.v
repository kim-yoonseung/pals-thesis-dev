From Paco Require Import paco.
From ITree Require Import ITree.
Require Import sflib.

Require Import StdlibExt IntegersExt.
Require Import SysSem.
Require Import SyncSysModel Executable.

Require Import MSteps FMSim FMSim_Switch.
Require Import PALSSystem.

Require Import RTSysEnv.
Require Import CProgEventSem.

Require Import BehavUtils SystemInvariant.

Require console ctrl dev.

Require Import AcStSystem.
Require Import SpecConsole SpecController SpecDevice.
Require Import CProgEventSem.

Require Import AcStRefinement.

Require Import ITreeTac.
Require Import ZArith Streams List Lia Bool.


(* Local Opaque Z.of_nat Z.to_nat. *)
(* Import ActiveStandby. *)

Set Nested Proofs Allowed.


Definition acst_sinv: system_invariant
                        (PALSSys.as_exec active_standby_system).
Admitted.

(* event in a period-trace *)
Definition event_in_ptrace (tid: Tid) (evt: event obsE)
           (ptr: list (events obsE)): Prop :=
  exists ptr_n,
    <<PTR_N: nth_error ptr tid = Some ptr_n>> /\
    <<EVT_IN_PTR_N: In evt ptr_n>>.

Definition event_in_trace (tid: Tid) (tm: Z) (evt: event obsE)
           (tr: list (list (Z * events obsE))): Prop :=
  exists tr_n es,
    <<TR_N: nth_error tr tid = Some tr_n>> /\
    <<ES_IN_TR_N: In (tm, es) tr_n>> /\
    <<EVT_IN_ES: In evt es>>.

Section SYS_INV.
  Let exec_sys: ExecutableSpec.t :=
    PALSSys.as_exec active_standby_system.
  Let prd: Z := ExecutableSpec.period exec_sys.
  Let nts: nat := length (ExecutableSpec.apps exec_sys).

  Definition went_wrong: abs_data _ acst_sinv -> Prop.
  Admitted.

  Definition start_control
    : abs_data _ acst_sinv -> Prop.
  Admitted.


  Inductive dchain
    : (abs_data _ acst_sinv) -> list (abs_data _ acst_sinv) -> Prop :=
  | DataChain_One
      d
      (WF_D: abs_data_wf _ _ d)
    : dchain d []
  | DataChain_Step
      d1 d2 ds
      (NEXT: abs_data_next _ acst_sinv d1 d2)
      (WF_D1: abs_data_wf _ _ d1)
      (REST_CHAIN: dchain d2 ds)
    : dchain d1 (d2 :: ds)
  .

  (* Lemma start_and_went_wrong_trace *)
  (*       tm0 d0 inbs0 lsts0 *)
  (*       tr d1 inbs1 lsts1 steps *)
  (*       (SYNC_TIME: (prd | tm0)%Z) *)
  (*       (SINV_STEPS: sinv_steps _ acst_sinv tm0 *)
  (*                               (d0, inbs0, lsts0) *)
  (*                               ((tr, d1, inbs1, lsts1) :: steps)) *)
  (*   : *)

End SYS_INV.


Section LIVENESS.
  Let exec_sys: ExecutableSpec.t :=
    PALSSys.as_exec active_standby_system.
  Let prd: Z := ExecutableSpec.period exec_sys.
  Let nts: nat := length (ExecutableSpec.apps exec_sys).

  Definition dev_wait
    : (abs_data _ acst_sinv) -> Tid ->
      nat(*demand*) -> nat(*wait_cnt*) -> Prop.
  Admitted.

  Definition dev_owner
    : (abs_data _ acst_sinv) -> Tid -> nat (*demand left*) -> Prop.
  Admitted.

  Definition dev_failed: abs_data _ acst_sinv -> Tid -> Prop.
  Admitted.

  Lemma dev_wait_advance
        (d d': abs_data _ acst_sinv)
        tid_dev dmd w
        (NEXT: abs_data_next _ _ d d')
        (WAIT_S_W: dev_wait d tid_dev dmd (S w))
        (WF_D: abs_data_wf _ acst_sinv d)
    : <<WENT_WRONG: went_wrong d'>> \/
      <<DEVICE_FAILED: dev_failed d' tid_dev>> \/
      <<DEV_WAIT_REDUCED: dev_wait d' tid_dev dmd w>>.
  Proof.
  Admitted.

  Lemma dev_wait_zero
        d tid_dev dmd
        (WAIT_ZERO: dev_wait d tid_dev dmd O)
        (WF_D: abs_data_wf _ acst_sinv d)
    : dev_owner d tid_dev dmd.
  Proof.
  Admitted.

  Lemma dev_wait_safe
        d tid_dev dmd w
        (WAIT: dev_wait d tid_dev dmd w)
        (WF_D: abs_data_wf _ acst_sinv d)
    : ~ went_wrong d.
  Proof.
  Admitted.

  Lemma dev_wait_not_failed
        d tid_dev dmd w
        (WAIT: dev_wait d tid_dev dmd w)
        (WF_D: abs_data_wf _ acst_sinv d)
    : ~ dev_failed d tid_dev.
  Proof.
  Admitted.

  Lemma dev_owner_advance
        d tid_dev dmd d'
        (OWNER: dev_owner d tid_dev (S dmd))
        (WF_D: abs_data_wf _ acst_sinv d)
        (NEXT: abs_data_next _ _ d d')
    : <<WENT_WRONG: went_wrong d'>> \/
      <<OWNER_REDUCED: dev_owner d tid_dev dmd>>.
  Proof.
  Admitted.

  Lemma dev_owner_safe
        d tid_dev dmd
        (WAIT: dev_owner d tid_dev dmd)
        (WF_D: abs_data_wf _ acst_sinv d)
    : ~ went_wrong d.
  Proof.
  Admitted.

  Inductive owner_dchain (tid_dev: Tid)
    : nat -> list (abs_data _ acst_sinv) -> Prop :=
  | OwnerDataChain_Base
      d0
      (OWNER_ZERO: dev_owner d0 tid_dev O)
      (WF_D0: abs_data_wf _ _ d0)
    : owner_dchain tid_dev O [d0]
  | OwnerDataChain_Cons
      dmd d ds
      (OWNER_N: dev_owner d tid_dev (S dmd))
      (WF_D0: abs_data_wf _ _ d)
      (OWNER_DATAS_REST: owner_dchain tid_dev dmd ds)
    : owner_dchain tid_dev (S dmd) (d :: ds)
  .

  (* Lemma demand_wait_start *)
  (*       d1 inbs1 lsts1 tm1 *)
  (*       tr lsts_out *)
  (*       tid_dev (dmd_raw: int) (dmd: nat) *)
  (*       d2 inbs2 lsts2 *)
  (*       (MATCH_LOCALS1: iForall2 *)
  (*                         (match_local _ acst_sinv tm1 d1) *)
  (*                         0 inbs1 lsts1) *)
  (*       (WF_D1: abs_data_wf _ _ d1) *)
  (*       (SAFE_D1: ~ went_wrong d1) *)
  (*       (LOCAL_STEPS: Forall4 (run_local exec_sys tm1) *)
  (*                             inbs1 lsts1 tr lsts_out) *)
  (*       (LOCAL_STATES': lsts2 = map fst lsts_out) *)
  (*       (INBS1: inbs2 = imap (fun tid _ => *)
  (*                               map (SNode.get_outbox_msg_by_dest *)
  (*                                      tid) (map snd lsts_out)) *)
  (*                            0 (repeat tt nts)) *)
  (*       (SAFE_TRACE: Forall safe_trace tr) *)
  (*       (DMD_POS: 0 < dmd) *)
  (*       (ACTUAL_DEMAND: dmd = Nat.min MAX_TIMEOUT (Z.to_nat (Int.signed dmd_raw))) *)
  (*       (EVT_IN_TR: event_in_trace tid_dev (Event (inl1 CheckDemand) dmd_raw) tr) *)
  (*       (MATCH_LOCALS2: iForall2 *)
  (*                         (match_local _ acst_sinv (tm1 + prd)%Z d2) *)
  (*                         0 inbs2 lsts2) *)
  (*       (WF_D2: abs_data_wf _ _ d2) *)
  (*   : exists wait_max, *)
  (*     <<WENT_WRONG: went_wrong d2>> \/ *)
  (*     <<WAIT_START: dev_wait d2 tid_dev wait_max dmd>> *)
  (* . *)
  (* Proof. *)
  (* Admitted. *)

  Lemma dchain_wait_to_owner
        d ds
        tid_dev (dmd: nat) w
        (DCHAIN: dchain d ds)
        (WAIT_START: dev_wait d tid_dev dmd w)
        (LEN_DS: dmd <= length ds)
    : exists ds_w d_wend ds',
      <<DCHAIN_DIV: d :: ds = ds_w ++ d_wend :: ds'>> /\
      <<LEN_DS_W: length ds_w <= w>> /\
      (<<WENT_WRONG: went_wrong d_wend>> \/
       <<DEV_FAILED: dev_failed d_wend tid_dev>> \/
       <<BECAME_OWNER: dev_owner d_wend tid_dev dmd>>).
  Proof.
  Admitted.

  Lemma dev_wait_dmd_le_max
        d tid_dev dmd w
        (WAIT: dev_wait d tid_dev dmd w)
    : dmd <= MAX_TIMEOUT.
  Proof.
  Admitted.

  Lemma owner_dchain_cases
        d tid_dev dmd
        (OWNER: dev_owner d tid_dev dmd)
    : forall ds
        (DS_LEN: dmd <= length ds)
        (DCHAIN: dchain d ds)
    ,
      Exists went_wrong ds \/
      Exists (flip dev_failed tid_dev) ds \/
      exists ds_use ds_rest,
        <<DS_DIV: d :: ds = ds_use ++ ds_rest>> /\
        <<USES: owner_dchain tid_dev dmd ds_use>>.
  Proof.
  Admitted.

  Lemma liveness_dchain_cases
        tid_dev
        d (dmd: nat) w
        (WAITING: dev_wait d tid_dev dmd w)
    : forall ds
        (DS_LEN: length ds = w + MAX_TIMEOUT)
        (DCHAIN: dchain d ds),
      ((* CTRL_FAILED *)
        Exists went_wrong ds) \/
      ((* DEV_FAILED *)
        Exists (flip dev_failed tid_dev) ds) \/
      ((* USE RESOURCE *)
        exists ds1 ds_use ds2,
          <<DS_DIV: d :: ds = ds1 ++ ds_use ++ ds2>> /\
          <<USES: owner_dchain tid_dev dmd ds_use>>)
  .
  Proof.
    i.
    hexploit dev_wait_dmd_le_max; eauto. intro DMD_LE_MAX.
    hexploit dchain_wait_to_owner; eauto.
    { nia. }
    i. des.
    { left.
      destruct ds_w.
      { simpl in DCHAIN_DIV. clarify.
        exfalso.
        hexploit dev_wait_safe; eauto.
        inv DCHAIN; done.
      }
      simpl in DCHAIN_DIV. clarify.
      apply Exists_exists.
      esplits.
      { apply in_or_app. right.
        simpl. left. eauto. }
      done.
    }
    { right. left.
      destruct ds_w.
      { simpl in DCHAIN_DIV. clarify.
        exfalso.
        hexploit dev_wait_not_failed; eauto.
        inv DCHAIN; done.
      }
      simpl in DCHAIN_DIV. clarify.
      apply Exists_exists.
      esplits.
      { apply in_or_app. right.
        simpl. left. eauto. }
      done.
    }

    assert (DCHAIN_WEND: dchain d_wend ds').
    { clear - DCHAIN_DIV DCHAIN.
      destruct ds_w as [|h t].
      { ss. clarify. }

      ss. clarify.
      depgen h.
      induction t as [| h' t' IH]; i; ss; clarify.
      { inv DCHAIN. ss. }
      inv DCHAIN.
      eauto.
    }

    hexploit owner_dchain_cases; eauto.
    { cut (length (d::ds) = length ds_w + S (length ds')).
      { s. nia. }
      rewrite DCHAIN_DIV.
      rewrite app_length. s. reflexivity.
    }
    assert (DS'_DS: forall x, In x ds' -> In x ds).
    { i. destruct ds_w; simpl in DCHAIN_DIV; clarify.
      apply in_or_app. right. right. eauto. }

    intros [WRONG | [DFAIL | OK]].
    - left.
      apply Exists_exists.
      apply Exists_exists in WRONG. des.
      esplits; eauto.
    - right. left.
      apply Exists_exists.
      apply Exists_exists in DFAIL. des.
      esplits; eauto.
    - des.
      right. right.
      esplits; eauto.
      rewrite DCHAIN_DIV.
      rewrite DS_DIV. eauto.
  Qed.


  Lemma dev_failed_trace_nil
        d tid_dev (tm: Z)
        inbs lsts tr lsts_out
        (DEV_FAILED: dev_failed d tid_dev)
        (SYNC_TIME: (prd | tm)%Z)
        (MATCH: iForall2 (match_local _ acst_sinv tm d)
                         O inbs lsts)
        (WF_D: abs_data_wf _ _ d)
        (* steps *)
        (LOCAL_STEPS: Forall4 (run_local exec_sys tm)
                              inbs lsts tr lsts_out)
    : forall e, ~ event_in_ptrace tid_dev e tr.
  Proof.
  Admitted.

  Lemma dev_owner_trace_use
        d tid_dev (tm: Z) (dmd: nat)
        inbs lsts tr lsts_out
        d' inbs' lsts'
        (OWNER: dev_owner d tid_dev (S dmd))
        (SYNC_TIME: (prd | tm)%Z)
        (MATCH: iForall2 (match_local _ acst_sinv tm d)
                         O inbs lsts)
        (WF_D: abs_data_wf _ _ d)
        (* steps *)
        (LOCAL_STEPS: Forall4 (run_local exec_sys tm)
                              inbs lsts tr lsts_out)
        (LOCAL_STATES': lsts' = map fst lsts_out)
        (INBS': inbs' = imap (fun tid _ =>
                                map (SNode.get_outbox_msg_by_dest
                                       tid) (map snd lsts_out))
                             0 (repeat tt nts))
        (MATCH1: iForall2 (match_local _ acst_sinv tm d')
                         O inbs' lsts')
        (WF_D': abs_data_wf _ _ d')
        (OWNER': dev_owner d' tid_dev dmd)
    : event_in_ptrace tid_dev (Event (inl1 UseResource) tt) tr.
  Proof.
  Admitted.

End LIVENESS.

Local Opaque Z.to_nat Z.of_nat.

Section LIVENESS_BEH.
  Let exec_sys :=
    (PALSSys.as_exec active_standby_system).
  Let prd := (ExecutableSpec.period exec_sys).
  Let nts := (length (ExecutableSpec.apps exec_sys)).

  Let PRD_POS: (0 < prd)%Z.
  Proof.
    change prd with (Z.of_nat period).
    change period with (Z.to_nat ActiveStandby.period).
    ss.
  Qed.

  Variable tm_init: Z.

  Let dsys: DSys.t := ExecutableSpec.as_dsys
                        exec_sys tm_init None.

  Let st_init := (0%Z, ExecutableSpec.sys_itree
                         exec_sys tm_init None).

  (* no events except console *)
  Definition trace_pre
             (tr: list (list (Z * events obsE))): Prop.
  Admitted.

  (* Definition start_ctrl_trace *)
  (*            (tr: list (list (Z * events obsE))): Prop. *)
  (* Admitted. *)

  Definition log_in_trace (tid: Tid) (tm:Z)
             (tr: list (list (Z * events obsE))): Prop :=
    exists (v: Z),
      event_in_trace tid tm (Event (inl1 (WriteLog v)) tt) tr.

  Inductive trace_ctrl_fsd
            (tm: Z)
            (tr: list (list (Z * events obsE)))
    : (bool?) -> Prop :=
    TraceCtrlFsd
      fsd
      (FST_FSD: fsd = Some true \/ log_in_trace tid_ctrl1 tm tr)
      (SND_FSD: fsd = Some false \/ log_in_trace tid_ctrl2 tm tr)
    : trace_ctrl_fsd tm tr fsd.
  (* | TraceCtrlFsd_Snd *)
  (*     (FST_OK: log_in_trace tid_ctrl1 tm tr) *)
  (*     (SND_FAILED: ~ log_in_trace tid_ctrl2 tm tr) *)
  (*   : trace_ctrl_fsd tm tr (Some false) *)
  (* | TraceCtrlFsd_None *)
  (*     (FST_OK: log_in_trace tid_ctrl1 tm tr) *)
  (*     (SND_OK: log_in_trace tid_ctrl2 tm tr) *)
  (*   : trace_ctrl_fsd tm tr None *)
  (* . *)

  Inductive fsd_le: bool? -> bool? -> Prop :=
  | FsdLe_Eq x
    : fsd_le x x
  | FsdLe_None x
    : fsd_le x None
  .

  Inductive fsd_next: bool? -> bool? -> Prop :=
  | FsdNext_None1 fsd
    : fsd_next None fsd
  | FsdNext_None2 fsd
    : fsd_next fsd None
  | FsdNext_eq sd
    : fsd_next (Some sd) (Some sd)
  .

  Lemma trace_ctrl_fsd_le
        tm tr fsd fsd'
        (FSD: trace_ctrl_fsd tm tr fsd)
        (LE: fsd_le fsd' fsd)
    : trace_ctrl_fsd tm tr fsd'.
  Proof.
    inv LE; ss.
    inv FSD.
    des; ss.
    econs; eauto.
  Qed.

  (* Inductive trace_ctrl_on *)
  (*   : Z * bool? -> Z * bool? (* exclusive *) -> *)
  (*     list (list (Z * events obsE)) -> Prop := *)
  (* | TraceCtrlOn_Base *)
  (*     tr tm fsd *)
  (*     (* (SYNC_TIME: (prd | tm)%Z) *) *)
  (*     (* (FAILED_SIDE: trace_ctrl_fsd tm tr fsd) *) *)
  (*   : trace_ctrl_on (tm, fsd) (tm, fsd) tr *)
  (* | TraceCtrlOn_Cons *)
  (*     tr tm fsd *)
  (*     fsd1 tm' fsd' *)
  (*     (SYNC_TIME: (prd | tm)%Z) *)
  (*     (FAILED_SIDE: trace_ctrl_fsd tm tr fsd) *)
  (*     (CTRL_ON_REST: trace_ctrl_on ((tm + prd)%Z, fsd1) *)
  (*                                  (tm', fsd') tr) *)
  (*     (FSD_LE: fsd_le fsd fsd1) *)
  (*   : trace_ctrl_on (tm, fsd) (tm', fsd') tr *)
  (* . *)

  Definition tid_c_of_side (sd: bool): Tid :=
    if sd then tid_ctrl1 else tid_ctrl2.

  Lemma trace_ctrl_fsd_Some
        tm tr fsd sd
        (FSD: trace_ctrl_fsd tm tr fsd)
        (FSD_SOME: fsd = Some sd)
    : log_in_trace (tid_c_of_side (negb sd)) tm tr.
  Proof.
    subst fsd.
    inv FSD. des; clarify.
    destruct sd; ss.
  Qed.

  Inductive trace_ctrl_on
             (tm_s tm_e: Z)
             (fsd_s fsd_e: bool?)
             (tr: list (list (Z * events obsE)))
    : Prop :=
    TraceCtrlOn
      (TM_S_SYNC: (prd | tm_s)%Z)
      (START_FST: trace_ctrl_fsd tm_s tr fsd_s)
      (CHAIN_EXISTS:
         forall tm1 sd
           (TM1_SYNC: (prd | tm1)%Z)
           (* (TM_NEXT: (tm2 = tm1 + prd)%Z) *)
           (TM1_LBND: (tm_s <= tm1 < tm_e)%Z)
           (* (TM2_UBND: (tm2 < tm_e)%Z) *)
           (OFF_AT_TM: ~ log_in_trace (tid_c_of_side sd) tm1 tr)
         ,
           <<ON_OTHER: log_in_trace (tid_c_of_side (negb sd)) tm1 tr>> /\
           ((* chain exists *)
             <<ON_OTHER_NEXT: log_in_trace (tid_c_of_side (negb sd)) (tm1 + prd)%Z tr>> \/
           (* last log *)
             <<LAST_TIME: (tm_e <= tm1 + prd)%Z>> /\
             <<LAST_FAILED_SIDE: fsd_e = Some sd>>))
  .

  Lemma divide_next_eq
        p a b
        (P_POS: (0 < p)%Z)
        (DIV1: (p | a)%Z)
        (DIV2: (p | b)%Z)
        (GT: (a < b <= a + prd)%Z)
    : (b = a + prd)%Z.
  Proof.
  Admitted.

  Lemma trace_ctrl_on_app
        tr tm_s tm_m tm_e
        fsd_s fsd_m fsd_m' fsd_e
        (ON1: trace_ctrl_on tm_s tm_m fsd_s fsd_m tr)
        (ON2: trace_ctrl_on tm_m tm_e fsd_m' fsd_e tr)
        (FSD_NEXT: fsd_next fsd_m fsd_m')
    : trace_ctrl_on tm_s tm_e fsd_s fsd_e tr.
  Proof.
    inv ON1.
    renames TM_S_SYNC START_FST CHAIN_EXISTS into
            TM_S_SYNC1 START_FST1 CHAIN_EXISTS1.
    inv ON2.

    econs; eauto. i.
    destruct (Z_lt_ge_dec tm1 tm_m) as [LT|GE].
    - hexploit CHAIN_EXISTS1; eauto.
      { nia. }
      i. des.
      { eauto. }

      assert (TM_M_EQ: (tm_m = tm1 + prd)%Z).
      { eapply divide_next_eq; eauto. }

      split; ss.
      left.
      subst fsd_m.

      inv FSD_NEXT.
      + inv START_FST. des; clarify.
        r. destruct sd; ss.
      + inv START_FST. des; clarify.
        destruct sd; ss.

    - hexploit CHAIN_EXISTS; eauto.
      nia.
  Qed.

  Definition device_task_id (tid: Tid): Prop :=
    tid = tid_dev1 \/ tid = tid_dev2 \/ tid = tid_dev3.

  Inductive trace_pos_demand
            (tid_dev: Tid) (tm: Z) (dmd: nat)
            (tr: list (list (Z * events obsE))): Prop :=
    TracePosDemand
      (dmd_i: int)
      (DEV_TASK_ID: device_task_id tid_dev)
      (RANGE_DEMAND: 0 < dmd <= MAX_TIMEOUT)
      (DMD_TO_NAT2: Z_to_nat2 (Int.signed dmd_i) = Some dmd)
      (DEMAND_EVT_IN_TRACE:
         event_in_trace tid_dev tm
                        (Event (inl1 CheckDemand) dmd_i) tr)
  .

  Lemma liveness_exec
        scnt_pre tr_pre st_pre
        tr_s st_s
        scnt1 tr1 st1
        tr_dmd st_w exec_w
        (STEPS_PRE: msteps dsys scnt_pre st_init tr_pre st_pre)
        (STEPS_CSTART: msteps dsys 1 st_pre tr_s st_s)
        (STEPS_ALIVE: msteps dsys scnt1 st_s tr1 st1)
        (STEPS_DEMAND: msteps dsys 1 st1 tr_dmd st_w)
        (PRE_TR: trace_pre tr_pre)
        (CSTART_TR: trace_ctrl_on tr1)
        (EXEC_ST: DSys.exec_state dsys st_w exec_w)
    : True.
