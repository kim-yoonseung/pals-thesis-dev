From ITree Require Import ITree.
From compcert Require Coqlib.
From Paco Require Import paco.

Require Import sflib.
Require Import Axioms StdlibExt IntegersExt.

Require Import SysSem.
Require Import IPModel DiscreteTimeModel IntByteModel.
Require Import RTSysEnv.
Require Import NWSysModel SyncSysModel AbstAsyncSysModel.
Require Import MWITree.

Require Import List.
Require Import Arith ZArith Lia.
Require Import Relation_Operators.

Generalizable Variable sysE.

Local Opaque Int.max_signed Int64.max_unsigned.

(* SpecNode: connects (inner) sync_node and async network *)
Module AbstMW.

  Section NODE.
    (* Variable msgT: Set. *)
    Context `{sysE: Type -> Type}.
    Context `{SystemEnv}.
    Let msgT: Set := bytes.
    Let t := @SNode.t sysE msgT.

    Inductive stage_t: Set :=
    | Ready
    | Running (sh: list bool)
    .

    Inductive istate_t {node: t} : Type :=
    | Off (* (outb: list (ip_t(*dip*) * bytes * nat)) *)
    | Prep
        (* (rcv_open: bool) *)
        (to_join: list Tid)
        (join_time_limit: nat)
        (inbp: list Packet.msg_t)
        (ast: node.(SNode.app_state))
    | On
        (sytm: nat)
        (inbp: list Packet.msg_t)
        (inbm: list msgT?)
        (* (outb: list (ip_t(*dip*) * bytes * nat)) *)
        (stage: stage_t)
        (ast: node.(SNode.app_state))
    .

    Record state: Type :=
      State {
          task_id: Tid ;
          ip_addr: ip_t ;
          snode: t ;
          istate: @istate_t snode ;
        }.

    Inductive istate_wf (snode: t)
      : @istate_t snode -> Prop :=
    | IStateWf_Off
      : istate_wf snode Off
    | IStateWf_Prep
        mids fsytm inbp ast
        (VALID_MCAST_IDS: Forall valid_mcast_id mids)
      : istate_wf snode (Prep mids fsytm inbp ast)
    | IStateWf_OnReady
        sytm inbp inbm ast
      : istate_wf snode (On sytm inbp inbm Ready ast)
    | IStateWf_On
        sytm inbp inbm sh ast
        (RUNNING_SYTM_UB: sytm < MAX_TIME)
        (SEND_HIST_LENGTH: length sh = num_tasks)
      : istate_wf snode (On sytm inbp inbm (Running sh) ast)
    .

    (* TODO: define wf for each case *)
    Inductive state_wf (tid: Tid): state -> Prop :=
      StateWf
        ip snode ist
        (TASK_ID_IP: task_id_ip tid ip)
        (* (WF_SNODE: SNode.wf imcasts snode) *)
        (WF_IST: istate_wf snode ist)
      : state_wf tid (State tid ip snode ist).

    Definition init_inbox : list msgT? :=
      List.repeat None (length task_ips).

    Lemma init_inbox_length
      : length init_inbox = num_tasks.
    Proof.
      unfold init_inbox.
      rewrite repeat_length. ss.
    Qed.

    Lemma init_inbox_nth
          n
          (VALID_N: n < num_tasks)
      : nth_error init_inbox n = Some None.
    Proof.
      apply repeat_nth_error_Some. ss.
    Qed.

    Lemma filtermap_init_inbox
      : filtermap id init_inbox = [].
    Proof.
      unfold init_inbox.
      apply filtermap_nil.
      intros a IN.
      eapply repeat_spec in IN. ss.
    Qed.


    Definition update_msg (ims: list (msgT?))
               (sid: Tid) (msg: msgT)
      : list (msgT?) :=
      replace_nth ims sid (Some msg).

    Definition parse_pld (pld: bytes)
      : (nat * Tid * msgT)? :=
      if length pld <? pld_size
      then None else parse_msg (firstn pld_size pld).

    Definition fetch_one_msg (sytm: nat)
               (pm: Packet.msg_t)
               (inbs: list (msgT?) * list (msgT?))
      : list (msgT?) * list (msgT?) :=
      let sytm_nxt := sytm + period in
      (* if negb (Packet.dest_port pm =? port)%nat *)
      (* then inbs *)
      match parse_pld (Packet.payload pm) with
      | None => inbs
      | Some (dtm, tid_s, msg) =>
        let (inbc, inbn) := inbs in
        if (dtm =? sytm) then
          (update_msg inbc tid_s msg, inbn)
        else if (dtm =? sytm_nxt) then
               (inbc, update_msg inbn tid_s msg)
             else inbs
      end.

    Definition fetch_msgs (sytm: nat)
               (inbp: list Packet.msg_t)
               (inbc: list msgT?)
      : list msgT? * list msgT? * list Packet.msg_t :=
      let inbn := init_inbox in
      process_firstn
        (fetch_one_msg sytm)
        inbp (inbc, inbn) (length task_ips * 4).

    Definition srl_pm (sytm_d: nat) (tid_s: nat)
               (tid_d: Tid) (msg: msgT)
      : Packet.t :=
      (* if (tid_d <? num_tasks + num_mcasts) then *)
      let ip_s := tid2ip tid_s in
      let ip_d := tid2ip tid_d in
      let rmsg := resize_bytes msg_size msg in
      let pld := serialize_msg sytm_d tid_s rmsg in
      Packet.Msg (Packet.mkMsg ip_s ip_d port pld).
    (* else None. *)

    Lemma wf_srl_pm
          sytm tid tid_d msg
          (* (RANGE_TID: IntRange.sint8 tid) *)
          (* (RANGE_SYTM: IntRange.uint64 sytm) *)
      : Packet.wf (srl_pm sytm tid tid_d msg).
    Proof.
      unfold srl_pm.
      econs. econs. ss.
      hexploit serialize_msg_size_lt_maxlen.
      { reflexivity. }
      2: { intro LE. apply LE. }
      erewrite resize_bytes_length; eauto.
    Qed.

    Definition check_and_send
               (sytm: nat) (tid: Tid)
               (sh: list bool) (om: (Tid * msgT)?)
      : list bool * Packet.t? :=
      match om with
      | None => (sh, None)
      | Some (tid_d, msg) =>
        match check_send_hist sh tid_d with
        | None => (sh, None)
        | Some sh' =>
          (sh', Some (srl_pm (sytm + period) tid tid_d msg))
        end
      end.

    Inductive istep
              (tm: DTime.t)
              (tid: Tid) (ip: ip_t)
              (node: t)
      : @istate_t node -> tsp * events (nbE +' sysE) -> Packet.t ? ->
        @istate_t node -> Prop :=
    | IStep_Fail st
        (* outb outb' opkt *)
        (* (OUTPUT: age_outbox ip outb = (outb', opkt)) *)
      : istep tm tid ip node
              st (Z0, []) None Off

    | IStep_TurnOn
        cbt jtl (* fsytm *)
        ast_i mids_j
        (CBT_LB: period <= cbt)
        (CUR_BASE_TIME: cbt = get_skwd_base_time period tm)
        (* (SYNC_TIME: Nat.divide period fsytm) *)
        (JOIN_BEFORE_START: jtl = cbt + period - max_clock_skew - max_nw_delay)
        (* (FIRST_SYNC_TIME: fsytm = cbt + period + period) *)
        (RANGE_TM: DTime.of_ns (cbt - max_clock_skew) < tm
                   < DTime.of_ns jtl)
        (ABST_INIT_STATE: SNode.init_app_state _ ast_i)
        (MCAST_IPS_TO_JOIN: mids_j = get_mcast_of tid)
      : istep tm tid ip node
              Off (Z0, []) None
              (Prep mids_j jtl [] ast_i)

    | IStep_Prep_Internal
        jtl inbp ast mids_j
        (BEFORE_LIMIT: tm < DTime.of_ns jtl)
      : istep tm tid ip node
              (Prep mids_j jtl inbp ast) (Z0, []) None
              (Prep mids_j jtl inbp ast)
    | IStep_Prep_SendJoin
        mid_j mids_j' jtl inbp ast mcm
        (BEFORE_LIMIT: tm < DTime.of_ns jtl)
        (MCAST_MEMBER: mcm = (tid2ip mid_j, ip))
      : istep tm tid ip node
              (Prep (mid_j::mids_j') jtl inbp ast)
              (Z0, []) (Some (Packet.MCast mcm))
              (Prep mids_j' jtl inbp ast)
    | IStep_Prep_Complete
        jtl sytm inbp inbm ast
        (BEFORE_LIMIT: tm < DTime.of_ns jtl)
        (JOIN_BEFORE_START: sytm = jtl + max_clock_skew +
                                   max_nw_delay + period)
        (INIT_INBOX: inbm = init_inbox)
      : istep tm tid ip node
              (Prep [] jtl inbp ast) (Z0, []) None
              (On sytm inbp inbm Ready ast)

    | IStep_OnStay
        sytm inbp inbm stg ast
        (TIME_UB: tm < DTime.of_ns (sytm + period - max_clock_skew - max_nw_delay))
      : istep tm tid ip node
              (On sytm inbp inbm stg ast)
              (Z0, []) None
              (On sytm inbp inbm stg ast)

    | IStep_PeriodBegin
        sytm inbp inbm ast
        inbc inbn inbp' ast' sh_i
        (SYTM_BELOW_MAX_TIME: sytm < MAX_TIME)
        (SYNC_TIME: sytm = get_skwd_base_time period tm)
        (RANGE_TIME: DTime.of_ns (sytm - max_clock_skew) < tm < DTime.of_ns (sytm + period - max_clock_skew - max_nw_delay))
        (FETCH_MSGS: fetch_msgs sytm inbp inbm =
                     (inbc, inbn, inbp'))
        (PERIOD_BEGIN: node.(SNode.period_begin) (Z.of_nat sytm) inbc ast ast')
        (SEND_HIST: sh_i = List.repeat false num_tasks)
        (* (NEXT_SYNC_TIME: nsytm = sytm + period) *)
      : istep tm tid ip node
              (On sytm inbp inbm Ready ast)
              (Z0, []) None
              (On sytm inbp' inbn (Running sh_i) ast')

    | IStep_Running_Go
        inbp inbm sh ast ast1
        oe om sh' ast' opkt
        sytm (* nsytm *) es zsytm
        (TIME_UB:  tm < DTime.of_ns (sytm + period - max_clock_skew - max_nw_delay))
        (TAU_STEPS: AANode.sh_tau_steps sh node ast ast1)
        (ISTEP: SNode.istep node ast1 oe om ast')
        (CHECK_SEND: check_and_send sytm tid sh om = (sh', opkt))
        (EVTS: es = opt2list oe)
        (TIMESTAMP: zsytm = Z.of_nat sytm)
      : istep tm tid ip node
              (On sytm inbp inbm (Running sh) ast)
              (zsytm, es) opkt
              (On sytm inbp inbm (Running sh') ast')

    | IStep_Done
        sytm inbp inbm sh ast ast_f nsytm
        (TIME_UB: tm < DTime.of_ns (sytm + period - max_clock_skew - max_nw_delay))
        (NEXT_SYNC_TIME: nsytm = sytm + period)
        (TAU_STEPS: AANode.sh_tau_steps sh node ast ast_f)
        (* (TAU_STEPS: clos_refl_trans *)
        (*               _ (SNode.app_step node) ast ast_f) *)
        (PERIOD_END: node.(SNode.period_end) ast_f)
      : istep tm tid ip node
              (On sytm inbp inbm (Running sh) ast)
              (Z0, []) None
              (On nsytm inbp inbm Ready ast_f)
    .

    Definition filter_port dpms_f1: list Packet.msg_t :=
      filter (fun pm : Packet.msg_t =>
                Packet.dest_port pm =? port) dpms_f1.

    Definition accept_packets {node: t}
               (* (tm: DTime.t) *)
               (pms: list Packet.msg_t)
               (ist: @istate_t node)
      : istate_t :=
      let pms' := filter_port pms in
      (* filter (fun pm => Packet.dest_port pm =? port) pms in *)
      match ist with
      | Prep mids tm inbp ast =>
        Prep mids tm (inbp ++ pms') ast
      | On sytm inbp inbm stg ast =>
        On sytm (inbp ++ pms') inbm stg ast
      | Off => Off
      end.

    Inductive step (tm: DTime.t) (dpms: list Packet.msg_t)
      : state -> tsp * events (nbE +' sysE) -> Packet.t ? ->
        state -> Prop :=
      Step
        tid ip node ist ist1
        tes op ist'
        (ACCEPT_PACKETS: ist1 = accept_packets dpms ist)
        (ISTEP: istep tm tid ip node
                      ist1 tes op ist')
      : step tm dpms
             (State tid ip node ist) tes op
             (State tid ip node ist').

    Lemma wf_accept_prsv
          pms node ist
          (* (WF_PMS: Forall Packet.msg_wf pms) *)
          (WF_IST: istate_wf node ist)
      : istate_wf node (accept_packets pms ist).
    Proof.
      inv WF_IST; econs; ss.
    Qed.

    Lemma wf_istep_prsv
          tm tid ip node
          ist tes op ist'
          (TASK_ID_IP: task_id_ip tid ip)
          (ISTEP: istep tm tid ip node
                        ist tes op ist')
          (WF_IST: istate_wf node ist)
      : <<WF_OPKT: option_rel1 Packet.wf op>> /\
        <<WF_IST': istate_wf node ist'>>.
    Proof.
      inv WF_IST.
      - inv ISTEP; ss.
        + esplits; ss. econs.
        + esplits; ss. econs.
          apply Forall_forall.
          intros mid IN.
          hexploit get_mcast_of_spec; eauto. i. des.
          r. esplits; eauto.
          unfold num_mcasts.
          eapply nth_error_Some. congruence.
      - inv ISTEP; ss.
        + esplits; ss. econs.
        + esplits; ss. econs. ss.
        + inv VALID_MCAST_IDS.
          esplits; ss.
          * econs. econs; ss.
            { hexploit valid_mcast_id_ip; eauto. i.
              hexploit mcast_id_ip_comput; eauto. i. des.
              eauto. }
            { hexploit task_id_ip_comput; eauto. i. des.
              eauto. }
          * econs; eauto.
        + esplits; ss. econs.
      - inv ISTEP.
        + esplits; ss. econs.
        + esplits; ss. econs.
        + esplits; ss. econs; ss.
          rewrite repeat_length. ss.
      - inv ISTEP; ss.
        + esplits; ss. econs.
        + esplits; ss. econs; ss.
        + unfold check_and_send in CHECK_SEND.
          destruct om as [ [tid_d m] |].
          2: { clarify.
               esplits; ss.
               econs; eauto. }
          destruct (check_send_hist sh tid_d) eqn:SH.
          2: { clarify.
               esplits; ss.
               econs; eauto. }
          clarify.
          apply check_send_hist_Some in SH; eauto.
          esplits.
          { apply wf_srl_pm. }
          { econs; ss.
            des; ss.
          }
        + esplits; ss. econs.
    Qed.

    Lemma wf_prsv
          tm dpms st tes op st' tid
          (STEP: step tm dpms st tes op st')
          (WF_STATE: state_wf tid st)
      : state_wf tid st' /\
        option_rel1 Packet.wf op.
    Proof.
      inv WF_STATE.
      inv STEP; ss. existT_elim. subst.
      hexploit wf_istep_prsv; eauto.
      { eapply wf_accept_prsv; eauto. }
      i. des.
      split; ss.
    Qed.

    Lemma istep_progress
          tm tid ip node ist
      : exists tes op ist',
        istep tm tid ip node
              ist tes op ist'.
    Proof.
      esplits. econs 1.
    Qed.

    Lemma step_progress
          tm dpms st
      : exists tes op st',
        step tm dpms st tes op st'.
    Proof.
      destruct st as [tid ip nd oist].
      hexploit istep_progress; eauto. i. des.
      esplits. econs; eauto.
    Qed.

    Lemma wf_init_state tid ip snode
          (* (WF_SNODE: SNode.wf imcasts snode) *)
          (TASK_ID_IP: task_id_ip tid ip)
      : state_wf tid (State tid ip snode Off).
    Proof.
      econs; eauto. econs.
    Qed.

    Definition as_node (tid: Tid) (snode: t)
      : @Node.t sysE :=
      let ip := tid2ip tid in
      Node.mk ip state
              (fun st => st = State tid ip snode Off) step.

    Lemma safe_node
          tid (* ip *) snode
          (* (WF_SNODE: SNode.wf imcasts snode) *)
      (* (TASK_ID_IP: task_id_ip tid ip) *)
          (VALID_TASK_ID: valid_task_id tid)
      : Node.safe (as_node tid snode).
    Proof.
      econs; ss.
      { esplits; eauto. }
      i. subst.

      eapply valid_task_id_ip in VALID_TASK_ID.

      (* hexploit task_id_ip_comput; eauto. *)
      (* intros (TID2IP_EQ & IP_LOCAL). *)
      (* rewrite TID2IP_EQ. *)
      pose (ip := tid2ip tid).
      fold ip.

      hexploit (wf_init_state tid ip snode); eauto.

      match goal with
      | |- _ -> Node.safe_istate _ _ ?st =>
        generalize st
      end.
      revert tm.

      clear VALID_TASK_ID ip.
      pcofix CIH. i.

      pfold. econs.
      - i. ss.
        hexploit step_progress; eauto.
      - i. ss.
        hexploit wf_prsv; eauto.
        intro WF_ST'.
        i. des.
        splits; ss.
        right. apply CIH. eauto.
    Qed.

  End NODE.
End AbstMW.
