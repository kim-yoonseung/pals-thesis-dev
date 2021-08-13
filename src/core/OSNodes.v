From Paco Require Import paco.
From ITree Require Import ITree.
From compcert Require Import Values.

Require Import sflib.
Require Import StdlibExt.
Require Import IntegersExt.

Require Import Axioms.
Require Import SysSem.
Require Import IPModel DiscreteTimeModel.
Require Import NWSysModel.
Require Import RTSysEnv.
Require Import ProgSem.
Require Import OSModel.

Require Import Arith ZArith Lia.
Require Import String List.

Import ListNotations.

Generalizable Variables sysE.

(* Annotation events - to advance allowed timestamp *)
(* Inductive tlimE : Type -> Type := *)
(*   TimeLimitEvent (n: nat): tlimE unit. *)


Module OSNode.
  Section NODE.
    Context {obsE: Type -> Type}.
    Context `{SystemEnv}.
    Notation progE := (osE +' obsE).
    Let prog_t : Type := @Prog.t progE.

    Section STATE.
      Variables (node_ip: ip_t) (prog: prog_t) (tsg: nat -> tsp).
      Hypothesis (VALID_UCAST_IP: IP.local_ip node_ip).

      (* process = program state & associated os resource *)
      Inductive process: Type :=
      | Proc (os: OS.state) (pst: Prog.state prog)
      | UndefState
      .

      (* Power On/Off *)
      Inductive istate: Type :=
      | Off
      | On (ltm: nat) (latency: nat) (proc: process)
      .

      Inductive init_process: process -> Prop :=
      | InitProcess_OK
          ost pst
          (OS_INIT_STATE: ost = OS.init_state)
          (PROG_INIT_STATE: Prog.initial_state prog pst)
        : init_process (Proc ost pst)
      | InitProcess_UB
          (PROG_INIT_STATE: ~ exists pst, Prog.initial_state prog pst)
        : init_process UndefState
      .

      Definition corr_os_prog
                 (ost: OS.state) (pst:Prog.state prog): Prop :=
        OS.running_state ost = true ->
        exists R (os_evt:osE R),
               <<PROG_EVT: Prog.at_event
                             _ pst (EventCall (subevent _ os_evt))>> /\
               <<OS_CORRESPONDS:
                 Some (EventCall os_evt) =
                 OS.status2oscall (OS.cur_status ost)>>.

      Inductive process_wf: process -> Prop :=
      | ProcessWf_Proc
          ost pst
          (CORR_OS_PROG: corr_os_prog ost pst)
          (WF_OS: OS.wf ost)
        : process_wf (Proc ost pst)
      | ProcessWf_Undef
        : process_wf UndefState
      .

      Inductive istate_wf (gtm: DTime.t): istate -> Prop :=
      | IStateWf_TurnedOff
          (* rbd (REBOOT_DELAY: rbd <= min_process_restart_delay * *)
          (*                          DTime.units_per_ns) *)
        : istate_wf gtm Off
      | IStateWf_Live
          ltm lat proc
          (WF_PROCESS: process_wf proc)
          (VALID_CLOCK_SKEW: valid_clock_skew gtm ltm)
        : istate_wf gtm (On ltm lat proc)
      .

      Definition proc_accept_packets
                 (dpms: list Packet.msg_t)
                 (proc: process)
        : process :=
        match proc with
        | UndefState => UndefState
        | Proc ost pst =>
          let ost' := OS.accept_msgs dpms ost in
          Proc ost' pst
        end.

      Definition accept_packets
                 (dpms: list Packet.msg_t)
                 (ist: istate)
        : istate :=
        match ist with
        | Off => Off
        | On ltm lat proc =>
          let proc' := proc_accept_packets dpms proc in
          On ltm lat proc'
        end.

      Lemma accept_msgs_sts_eq
            distr ost ost'
            (ACC: OS.accept_msgs distr ost = ost')
        : OS.cur_status ost' = OS.cur_status ost.
      Proof.
        unfold OS.accept_msgs in ACC.
        destruct ost; ss. subst. ss.
      Qed.

      Lemma accept_msgs_running_eq
            distr ost ost'
            (ACC: OS.accept_msgs distr ost = ost')
        : OS.running_state ost' = OS.running_state ost.
      Proof.
        unfold OS.running_state.
        erewrite accept_msgs_sts_eq; eauto.
      Qed.

      Lemma accept_msgs_corr_os_prog
            os pst ms
            (CORR: corr_os_prog os pst)
        : corr_os_prog (OS.accept_msgs ms os) pst.
      Proof.
        rr. erewrite accept_msgs_sts_eq; eauto.
        erewrite accept_msgs_running_eq; eauto.
      Qed.

      Lemma os_step_corr_os_prog
            os pst
            ip ltm op os'
            (CORR: corr_os_prog os pst)
            (OS_STEP: OS.step ip ltm os op os')
        : corr_os_prog os' pst.
      Proof.
        rr. inv OS_STEP; ss.
      Qed.

      (* program effective step *)
      Inductive peff_step
        : OS.state * Prog.state prog -> events obsE -> process -> Prop :=
      | PEffStep_OSCall
          ost pst
          (os_ec: event_call osE) ost'
          (AT_EVT: Prog.at_event prog pst (embed os_ec))
          (OS_CALL: OS.call ost os_ec ost')
        : peff_step (ost, pst) [] (Proc ost' pst)

      | PEffStep_SysEvent
          ost pst
          R (sys_ec: obsE R)
          (retv: R) pst' evt
          (* (PRECOND: precond_E sys_ec) *)
          (AT_EVT: Prog.at_event
                     prog pst (embed (EventCall sys_ec)))
          (* (POSTCOND: postcond_E sys_ec retv) *)
          (AFT_EVT: Prog.after_event
                      prog pst (embed (Event sys_ec retv)) pst')
          (EVT: evt = Event sys_ec retv)
        : peff_step (ost, pst) [evt] (Proc ost pst')

      | PEffStep_Step
          ost pst pst'
          (STEP: Prog.step prog pst pst')
        : peff_step (ost, pst) [] (Proc ost pst')

      | PEffStep_Final
          ost pst
          (APP_STEP: Prog.final_state prog pst)
        : peff_step (ost, pst) [] (Proc ost pst)

      | PEffStep_Stuck
          ost pst
          (PROG_STUCK: Prog.stuckstate prog pst)
          (* (ERR_EVENT: err_e = subevent _ ErrorEvent) *)
        : peff_step (ost, pst) (* [Event err_e tt] *) [] UndefState
      .

      Inductive proc_step (ltm: nat)
        : process -> events obsE -> Packet.t ? -> process -> Prop :=
      | ProcStep_ProgStep
          ost pst pst_m es proc'
          (* (TLIM_OK: is_time_limit_over ltm tlim = false) *)
          (OS_IDLE: OS.running_state ost = false)
          (PROG_SILENT_STEPS: Prog.tau_steps prog pst pst_m)
          (PEFF_STEP: peff_step (ost, pst_m) es proc')
        : proc_step ltm (Proc ost pst) es None proc'

      | ProcStep_OSStep
          ost pst
          opkt ost'
          (OS_STEP: OS.step node_ip ltm ost opkt ost')
        : proc_step ltm (Proc ost pst) [] opkt (Proc ost' pst)

      | ProcStep_OSReturn
          ost pst
          os_evt ost' pst'
          (OS_RET: OS.ret ost os_evt ost')
          (AFT_EVT: Prog.after_event prog pst (embed os_evt) pst')
        : proc_step ltm (Proc ost pst) [] None (Proc ost' pst')

      | ProcStep_UndefState
          (* err_e *) es opkt
          (OPKT_WF: option_rel1 Packet.wf opkt)
          (* (ERR_EVENT: err_e = Event (subevent _ ErrorEvent) tt) *)
        : proc_step ltm UndefState (* [err_e] *) es opkt UndefState
      .


      Definition is_time_limit_over (ltm: nat) (tlim: option nat): bool :=
        match tlim with
        | None => false
        | Some tlim => (tlim <=? ltm)%nat
        end.

      Definition proc_is_time_limit_over (ltm: nat) (proc: process): bool :=
        match proc with
        | Proc ost _ => is_time_limit_over ltm ost.(OS.tlim)
        | _ => false
        end.

      Inductive estep (gtm: DTime.t)
        : istate -> tsp * events (nbE +' obsE) -> Packet.t ? -> istate -> Prop :=
      | Estep_Boot
          ltm_i lat_i lst_i
          (INIT_PROC: init_process lst_i)
          (VALID_CLOCK_SKEW: valid_clock_skew gtm ltm_i)
        : estep gtm Off (0%Z, []) None
                (On ltm_i lat_i lst_i)

      | Estep_Latency
          ltm lat proc ts
          (TLIM_OK: proc_is_time_limit_over ltm proc = false)
          (TIMESTAMP: ts = tsg ltm)
        : estep gtm (On ltm (S lat) proc) (ts, []) None
                (On ltm lat proc)

      | Estep_RunProcess
          ltm proc
          ts es_proc op lat' proc' es
          (TLIM_OK: proc_is_time_limit_over ltm proc = false)
          (PROC_STEP: proc_step ltm proc es_proc op proc')
          (TIMESTAMP: ts = tsg ltm)
          (EMBED_EVENT: es = embed es_proc)
        : estep gtm (On ltm O proc) (ts, es) op
                (On ltm lat' proc')

      | Estep_TimeLimitOver
          ltm lat proc
          (nbevt: event (nbE +' obsE)) ts
          (TLIM_OVER: proc_is_time_limit_over ltm proc = true)
          (TIMESTAMP: ts = tsg ltm)
          (EVENT: nbevt = embed (Event (NobehEvent) tt))
        : estep gtm (On ltm lat proc) (ts, [nbevt]) None
                (On ltm lat proc)

      | Estep_Off ist
        : estep gtm ist (0%Z, []) None Off
      .

      Inductive istate_adv_local_clock (gtm: DTime.t)
        : istate -> istate -> Prop :=
      | IStateAdvLClock_Off
        : istate_adv_local_clock gtm Off Off
      | IStateAdvLClock_On
          ltm lat proc ltm'
          (ADV_LCLOCK: adv_local_clock gtm ltm ltm')
        : istate_adv_local_clock
            gtm (On ltm lat proc) (On ltm' lat proc)
      .

      Inductive istep
                (gtm: DTime.t) (pms: list Packet.msg_t)
        : istate -> tsp * events (nbE +' obsE) -> Packet.t ? -> istate -> Prop :=
        IStep
          ist ist1
          tes opkt ist2 ist'
          (ACCEPT: accept_packets pms ist = ist1)
          (ESTEP: estep gtm ist1 tes opkt ist2)
          (IST_ADV_LCLOCK: istate_adv_local_clock
                             gtm ist2 ist')
        : istep gtm pms ist tes opkt ist'.

      (*     (ADV_LCLOCK: adv_local_clock gtm ltm ltm') *)
      Definition as_node: Node.t :=
        Node.mk node_ip istate
                (fun ist => ist = Off) istep.

    End STATE.

    (* Instance progE_conds: event_conds progE. *)
    (* Proof. *)
    (*   unfold progE. typeclasses eauto. *)
    (* Defined. *)

    Lemma wf_proc_step_prsv
          ip prog ltm
          proc es op proc'
          (IP_LOCAL: IP.local_ip ip)
          (WF_PROC: process_wf prog proc)
          (PROC_STEP: proc_step ip prog ltm proc es op proc')
      : <<WF_OPKT: option_rel1 Packet.wf op>> /\
        <<WF_PROC': process_wf prog proc'>>.
    Proof.
      inv PROC_STEP.
      - esplits; ss.
        inv WF_PROC.

        clear CORR_OS_PROG.
        inv PEFF_STEP; ss.
        + econs.
          2: { destruct os_ec.
               eapply OS.wf_call; eauto. }
          inv OS_CALL.
          econs; eauto.
        + econs; eauto.
          r. congruence.
        + econs; eauto.
          r. congruence.
        + econs; eauto.
          r. congruence.
        + econs; eauto.
      - (* OS_STEP *)
        inv WF_PROC.
        hexploit OS.wf_preserve; eauto.
        i. des.
        esplits; eauto.
        econs; eauto.
        eapply os_step_corr_os_prog; eauto.
      - (* OS_RET *)
        esplits; ss.
        inv WF_PROC.
        (* inv OS_RET. *)
        econs; ss.
        + inv OS_RET. ss.
        + destruct os_evt.
          eapply OS.wf_ret; eauto.
      - (* UB *)
        esplits; eauto.
      (* - (* NB *) *)
      (*   esplits; eauto. ss. *)
    Qed.

    Lemma wf_proc_accept
          prog pms proc
          (WF_PMS: Forall Packet.msg_wf pms)
          (WF: process_wf prog proc)
      : process_wf prog (proc_accept_packets prog pms proc).
    Proof.
      inv WF.
      - econs; ss.
        + eapply accept_msgs_corr_os_prog. ss.
        + eapply OS.wf_accept_msgs; try reflexivity; eauto.
      - econs; ss.
    Qed.

    Lemma wf_prsv
          ip prog tsg
          gtm pms
          ist tes op ist'
          (IP_LOCAL: IP.local_ip ip)
          (WF_ISTATE: istate_wf prog gtm ist)
          (ISTEP: istep ip prog tsg gtm pms
                        ist tes op ist')
          (WF_PMS: Forall Packet.msg_wf pms)
      : <<WF_OPKT: option_rel1 Packet.wf op>> /\
        <<WF_ISTATE': istate_wf prog (DTime.succ gtm) ist'>>.
    Proof.
      inv WF_ISTATE.
      - inv ISTEP.
        inv ESTEP; ss.
        + inv IST_ADV_LCLOCK.
          inv ADV_LCLOCK.
          esplits; ss.

          inv INIT_PROC; ss.
          * econs; ss.
            econs; ss.
            apply OS.wf_init.
          * econs; ss.
            econs.
        + esplits; ss.
          inv IST_ADV_LCLOCK.
          econs.
      - inv ISTEP. ss.
        inv ESTEP; ss.
        + inv IST_ADV_LCLOCK.
          inv ADV_LCLOCK.
          splits; ss.
          econs; ss.
          eapply wf_proc_accept; eauto.
        + inv IST_ADV_LCLOCK.
          inv ADV_LCLOCK.
          hexploit wf_proc_step_prsv;
            try apply PROC_STEP; eauto.
          { eapply wf_proc_accept; eauto. }
          i. des.
          esplits; eauto.
          econs; eauto.
        + inv IST_ADV_LCLOCK.
          inv ADV_LCLOCK.
          splits; ss.
          econs; eauto.
          eapply wf_proc_accept; eauto.
        + inv IST_ADV_LCLOCK.
          splits; ss.
          econs.
    Qed.

    Lemma wf_progress
          ip prog tsg
          gtm pms ist
          (IP_LOCAL: IP.local_ip ip)
          (WF_ISTATE: istate_wf prog gtm ist)
          (WF_PMS: Forall Packet.msg_wf pms)
      : exists tes op ist',
        istep ip prog tsg gtm pms
              ist tes op ist'.
    Proof.
      esplits.
      econs; eauto.
      - econs.
      - econs.
    Qed.

    Lemma safe_node
          ip prog tsg
          (IP_LOCAL: IP.local_ip ip)
      : Node.safe (as_node ip prog tsg).
    Proof.
      econs; ss.
      { esplits; eauto. }
      i. subst.

      assert (WF_ST: istate_wf prog tm (Off prog)).
      { i. econs. }

      revert WF_ST.
      generalize (Off prog).
      revert tm.
      pcofix CIH. i.

      pfold. econs.
      - i. ss.
        hexploit wf_progress; eauto.
      - i. ss.
        hexploit wf_prsv; eauto. i. des.
        splits; ss.
        right. apply CIH. eauto.
    Qed.

  End NODE.
End OSNode.
