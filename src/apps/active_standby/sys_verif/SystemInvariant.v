From Paco Require Import paco.
From ITree Require Import ITree.
Require Import sflib.

Require Import StdlibExt IntegersExt.
Require Import SysSem.
Require Import SyncSysModel.
Require Import RTSysEnv.
Require Import Executable.

Require Import MSteps.
Require Import FMSim FMSim_Switch.
Require Import PALSSystem.
Require Import BehavUtils.
Require Import CProgEventSem.

Require Import ZArith Streams List Lia.

Local Opaque Z.of_nat Z.to_nat.

Set Nested Proofs Allowed.

(* Arguments Nat.min: simpl nomatch. *)
(* Arguments nth_error: simpl nomatch. *)

Import ExecutableSpec.
Import ITreeNotations.



Section SYSTEM_INVARIANT.

  (* Context {sysE: Type -> Type}. *)
  Context {msgT: Set}.
  Notation lst_t := (@loc_state obsE msgT).

  (* Variable asys: @AbsSys.t sysE. *)
  Variable sys: @ExecutableSpec.t obsE msgT.

  Let prd: Z := period sys.
  Let nts: nat := (length (apps sys)).
  Let mcs: list (list nat) := (mcasts sys).
  Let sntz: msgT -> msgT? := (sanitize_msg sys).


  Definition safe_trace (tr: events obsE): Prop :=
    Forall (fun evt => exists (evt_ec: event extcallE),
                evt = embed evt_ec) tr.

  Inductive run_itree {ast_t: Type}
            (outbox: list (msgT?))
            (itr: itree (obsE +' @abst_sendE msgT) ast_t)
    : events obsE -> ast_t? -> list (msgT?) -> Prop :=
  | RunITree_Fail
    : run_itree outbox itr [] None outbox
  | RunITree_Ret
      ast_f
      (OBS_RET: observe itr = RetF ast_f)
    : run_itree outbox itr [] (Some ast_f) outbox
  | RunITree_Tau
      itr' es oast outbox'
      (OBS_TAU: observe itr = TauF itr')
      (RUN_REST: run_itree outbox itr' es oast outbox')
    : run_itree outbox itr es oast outbox'
  | RunITree_Event
      R (e: obsE R) (k: R -> itree _ ast_t)
      (r: R) es' oast outbox'
      (OBS_EVT: observe itr = VisF (inl1 e) k)
      (RUN_REST: run_itree outbox (k r) es' oast outbox')
    : run_itree outbox itr (Event e r :: es') oast outbox'
  | RunITree_Send
      tid_d msg outbox1
      (k: unit -> itree _ ast_t)
      es oast outbox'
      (OBS_SEND: observe itr = VisF (inr1 (AbstSendEvent
                                             tid_d msg)) k)
      (UPDATE_OUTBOX: update_outbox
                        nts mcs sntz
                        outbox tid_d msg = outbox1)
      (RUN_REST: run_itree outbox1 (k tt) es oast outbox')
    : run_itree outbox itr es oast outbox'
  .

  Inductive run_local (sytm: Z)
            (inb: list (msgT?))
    : lst_t -> events obsE -> lst_t * list (msgT?) -> Prop :=
  | RunLocal_Off
      app oast
    : run_local sytm inb
                (LocState app oast) [] (LocState app None, [])

  | RunLocal_On
      app ast
      (INIT_AST: ast = AppMod.init_abst_state app)
    : run_local sytm inb
                (LocState app None) [] (LocState app (Some ast), [])

  | RunLocal_RunPeriod
      app ast
      itr es out oast'
      (PINIT_ITREE: itr = AppMod.job_itree app sytm inb ast)
      (RUN_ITREE: run_itree (repeat None (length (apps sys))) itr
                            es oast' out)
    : run_local sytm inb
                (LocState app (Some ast)) es (LocState app oast', out)
  .

  Definition state_of (tm_p tm: Z)
             (inbs: list (list msgT?)) (lsts: list lst_t)
    : Z * itree (tgd (obsE +' randE) +' tspE) unit :=
    (tm_p, interp_ainvk
             sys unit
             (synch_itree_loop nts prd None tm inbs)
             lsts ;;
           Ret tt).


  (* Record system_invariant: Type := *)
  (*   { abs_data: Type ; *)
  (*     abs_data_next: abs_data -> abs_data -> Prop; *)
  (*     abs_data_wf: abs_data -> Prop ; *)

  (*     match_local: Z(*tm*) -> abs_data -> *)
  (*                  nat(*tid*) -> list msgT? -> lst_t -> Prop; *)
  (*     match_local_after: Z -> abs_data -> *)
  (*                        nat -> lst_t * list msgT? -> Prop; *)

  (*     MATCH_LOCAL_AFTER_NEXT_INBOX: *)
  (*       forall (sytm: Z) d lsts_aft *)
  (*         (WF: abs_data_wf d) *)
  (*         (NUM_LSTS: length lsts_aft = nts) *)
  (*         (MATCH_AFTER: iForall (match_local_after sytm d) *)
  (*                               0 lsts_aft) *)
  (*       , *)
  (*         let lsts' := map fst lsts_aft in *)
  (*         let outs := map snd lsts_aft in *)
  (*         let inbs' := imap (fun tid _ => map (SNode.get_outbox_msg_by_dest tid) outs) *)
  (*                           0 (repeat tt nts) in *)
  (*         iForall2 (match_local (sytm + prd)%Z d) 0 inbs' lsts' ; *)

  (*     MATCH_INITIAL: *)
  (*       forall sytm *)
  (*         (SYNC_TIME: (prd | sytm)%Z), *)
  (*         exists d, *)
  (*           iForall2 (match_local sytm d) 0 *)
  (*                    (repeat (repeat None nts) nts) *)
  (*                    (map init_loc_state (apps sys)) ; *)

  (*     NEXT_WF_PRSV: *)
  (*       forall d d' *)
  (*         (WF: abs_data_wf d) *)
  (*         (NEXT: abs_data_next d d'), *)
  (*         abs_data_wf d' ; *)

  (*     INV_PRSV: *)
  (*       forall (sytm: Z) *)
  (*         (d: abs_data) *)
  (*         (inbs: list (list msgT?)) *)
  (*         (lsts: list lst_t) *)
  (*         (lsts_f: list (lst_t * list msgT?)) *)
  (*         (tr: list (events obsE)) *)
  (*         (WF: abs_data_wf d) *)
  (*         (NUM_LSTS: length lsts = nts) *)
  (*         (MATCH: iForall2 (match_local sytm d) 0 inbs lsts) *)
  (*         (STEP_IMPL: Forall4 (run_local sytm) *)
  (*                             inbs lsts tr lsts_f) *)
  (*       , *)
  (*         <<SAFE_TRACE: Forall safe_trace tr>> /\ *)
  (*       exists (d': abs_data), *)
  (*         <<D_NEXT: abs_data_next d d'>> /\ *)
  (*         <<MATCH_AFTER: iForall (match_local_after sytm d') *)
  (*                                0 lsts_f>> *)
  (*     ; *)
  (*   }. *)

  (* Definition match_glob (* {sinv: system_invariant} *) *)
  (*            (tm: Z) *)
  (*            (d: abs_data sinv) *)
  (*            (inbs: list (list msgT?)) *)
  (*            (lsts:list (@loc_state obsE msgT)) *)
  (*   : Prop := *)
  (*   iForall2 (match_local sinv tm d) 0 inbs lsts. *)

End SYSTEM_INVARIANT.



Section SYSTEM_INVARIANT_PROPS.
  (* Context {sysE: Type -> Type}. *)
  Context {msgT: Set}.

  Variable sys: @ExecutableSpec.t obsE msgT.
  Variable sinv: system_invariant sys.

  Variable tm_init: Z.
  Notation lst_t := (@loc_state obsE msgT).
  Let dsys: DSys.t := as_dsys sys tm_init None.

  Let prd: Z := period sys.
  Let nts: nat := (length (apps sys)).
  Let mcs: list (list nat) := (mcasts sys).
  Let sntz: msgT -> msgT? := (sanitize_msg sys).

  (* Hypothesis PERIOD_POS: (0 < prd)%Z. *)

  Inductive match_sinv
            (tm: Z)
            (d: abs_data _ sinv)
            (inbs: list (list msgT?))
            (lsts: list lst_t)
    : Z * itree (tgd (obsE +' randE) +' tspE) unit -> Prop :=
    MatchSInv
      tm_p st
      (SYNC_TIME: (prd | tm)%Z)
      (STATE: st = state_of sys tm_p tm inbs lsts)
      (MATCH: match_glob _ tm d inbs lsts)
      (WF_ABS_DATA: abs_data_wf _ sinv d)
    : match_sinv tm d inbs lsts st.

  Inductive sinv_steps
    : Z (* tm *) ->
      abs_data _ sinv * list (list msgT?) * list lst_t ->
      list (list (events obsE) * abs_data _ sinv *
            list (list msgT?) * list lst_t) -> Prop :=
  | SInvSteps_Nil
      tm d inbs lsts
      (SYNC_TIME: (prd | tm)%Z)
      (* (MATCH_LOCALS: iForall2 (match_local _ sinv tm d) *)
      (*                         0 inbs lsts) *)
    : sinv_steps tm (d, inbs, lsts) []
  | SInvSteps_Cons
      tm d inbs lsts
      tr lsts_out
      d1 inbs1 lsts1 rest
      (SYNC_TIME: (prd | tm)%Z)
      (* (MATCH_LOCALS: iForall2 (match_local _ sinv tm d) *)
      (*                         0 inbs lsts) *)
      (LOCAL_STEPS: Forall4 (run_local sys tm)
                            inbs lsts tr lsts_out)
      (LOCAL_STATES': lsts1 = map fst lsts_out)
      (INBS1: inbs1 = imap (fun tid _ =>
                              map (SNode.get_outbox_msg_by_dest
                                     tid) (map snd lsts_out))
                           0 (repeat tt nts))
      (SAFE_TRACE: Forall safe_trace tr)
      (SINV_STEPS_REST: sinv_steps (tm + prd)%Z
                                   (d1, inbs1, lsts1) rest)
    : sinv_steps tm (d, inbs, lsts) ((tr, d1, inbs1, lsts1)::rest)
  .

  Lemma exec_div_one_period
        (tm: Z) (d: abs_data _ sinv) inbs lsts
        st exec
        (MATCH: match_sinv tm d inbs lsts st)
        (EXEC_ST: DSys.exec_state dsys st exec)
    : exists scnt tr
        d' inbs' lsts'
        st' exec',
      <<EXEC_DIV: sapp_each_rel tr exec' exec>> /\
      <<MSTEPS_PRD: msteps dsys scnt st tr st'>> /\
      <<DATA_NXT: abs_data_next _ _ d d'>> /\
      <<MATCH': match_sinv (tm + prd)%Z d' inbs' lsts' st'>> /\
      <<EXEC_ST': DSys.exec_state dsys st' exec'>>.
  Proof.
  Admitted.

  Lemma exec_div_event
        (tm: Z) (d: abs_data _ sinv) inbs lsts
        st exec
        tid tm_evt (evt: event obsE)
        (MATCH: match_sinv tm d inbs lsts st)
        (EXEC_ST: DSys.exec_state dsys st exec)
        (EVT_IN_EXEC: event_in_exec tid tm_evt evt exec)
    : exists tr1 exec1
        scnt1 st1 d1 inbs1 lsts1
        tr_evt exec'
        d' inbs' lsts'
        st' exec',
      <<EXEC_DIV1: sapp_each_rel tr1 exec1 exec>> /\
      <<MSTEPS1: msteps dsys scnt1 st tr1 st1>> /\
      (* <<DATA_NXT: refl_trans_clos (abs_data_next _ _) d d1>> /\ *)
      <<MATCH1: match_sinv (tm + prd)%Z d1 inbs1 lsts1 st1>> /\

      <<EXEC_DIV_EVT: sapp_each_rel tr_evt exec' exec1>> /\
      <<MSTEPS_EVT: msteps dsys 1 st1 tr_evt st2>> /\
      <<DATA_NXT: abs_data_next _ _ d1 d2>> /\
      <<MATCH1: match_sinv (tm + prd)%Z d1 inbs1 lsts1 st1>> /\

      <<EXEC_ST': DSys.exec_state dsys st' exec'>>.
  Proof.
  Admitted.


  (* Lemma divide_exec_aux *)
  (*       tm inbs lsts d *)
  (*       st exec *)
  (*       (MATCH_STATE: match_state tm inbs lsts d st) *)
  (*       (EXEC_STATE: DSys.exec_state dsys st exec) *)
  (*   : exists scnt tr_act tr_abs *)
  (*       lsts_outb' *)
  (*       st' exec', *)
  (*     <<EXEC_DIV: sapp_each_rel tr_act exec' exec >> /\ *)
  (*     <<MSTEPS: msteps dsys scnt st tr_act st'>> /\ *)
  (*     <<FORALL4: iForall4 (run_local sys tm) *)
  (*                         O inbs lsts tr_abs lsts_outb'>> /\ *)
  (*     << flatten_te tr_act >> *)
  (*     <<>> *)
  (*     <<>> *)
  (*     <<>> *)
  (* . *)

  (* Lemma abs_sys_refinement *)
  (*       (tm_init fsytm: Z) *)
  (*       (TM_FST_SYNC: *)
  (*          fsytm = *)
  (*          let n_pre: Z := *)
  (*              (let m: Z := tm_init mod period in *)
  (*               if (m =? 0)%Z then 0 else (period - m))%Z *)
  (*          in *)
  (*          (tm_init + n_pre)%Z) *)
  (*   : DSys.behav_sys (ExecutableSpec.as_dsys sys tm_init None) *)
  (*     <1= DSys.behav_sys (AbsSys.as_dsys asys fsytm). *)
  (* Proof. *)
  (* Admitted. *)

End SYSTEM_INVARIANT_PROPS.







Import ITreeNotations.

Section EXECUTABLE_SYS_LEMMAS.
  Import ExecutableSpec.

  Variable E: Type -> Type.
  Variable M: Set.
  Variable sys: @ExecutableSpec.t E M.
  Variable tm_init: Z.
  Hypothesis PRD_NZERO: ExecutableSpec.period sys <> 0%Z.
  (* Variable sys': @DSys.t E. *)
  Let dsys := ExecutableSpec.as_dsys sys tm_init.
  Let period: Z := ExecutableSpec.period sys.
  Let nts: nat := (length (apps sys)).
  Let mcs: list (list nat) := (mcasts sys).
  Let sntz: M -> M? := (sanitize_msg sys).
  Notation lst_t := (@loc_state E M).

  (* Lemma sync_exec_time_order *)
  (*       (st: @SyncSys.state E M) exec *)
  (*       (SAFE: @DSys.safe_state _ dsys st) *)
  (*       (EXEC_STATE: DSys.exec_state dsys st exec) *)
  (*   : forall (n k: nat) exec_n t e, *)
  (*       nth_error exec n = Some exec_n -> *)
  (*       Str_nth k exec_n = (t, e) -> *)
  (*       t = SyncSys.time st + k. *)
  (* Proof. *)
  (*   intros n k exec_n t e EXEC_N STR_N. *)
  (*   depgen exec. depgen exec_n. depgen st. revert t. *)
  (*   induction k as [| k' IH]; i; ss. *)
  (*   { destruct exec_n as [exec1 exec_n']; ss. *)
  (*     unfold Str_nth in STR_N. ss. subst. *)
  (*     rewrite Nat.add_0_r. *)

  (*     punfold SAFE. inv SAFE. *)
  (*     punfold EXEC_STATE. inv EXEC_STATE. *)
  (*     { exfalso. eauto. } *)
  (*     clear PROGRESS. *)
  (*     ss. *)

  (*     unfold Cons_each_rel in BEH_CONS. *)
  (*     eapply Forall3_nth3 in BEH_CONS; eauto. des. *)
  (*     destruct e1 as [tsp1 evt1]. *)
  (*     renames NTH1 NTH2 into E1 EXEC'_N. *)
  (*     r in P_FA. clarify. *)

  (*     eapply FMSim_Switch.DSys_filter_nb_sysstep_inv *)
  (*       in FILTER_NOBEH. *)
  (*     eapply Forall2_nth2 in FILTER_NOBEH; eauto. *)

  (*     des. *)
  (*     renames NTH1 P_FA into ES_N FILTER_LOC. *)
  (*     destruct e1 as [t' evt1_r]. *)

  (*     apply filter_nb_localstep_inv in FILTER_LOC. ss. *)
  (*     des; subst. *)

  (*     inv STEP; ss. *)
  (*     - eapply nth_error_In in ES_N. *)
  (*       apply repeat_spec in ES_N. clarify. *)
  (*     - rewrite map_nth_error_iff in ES_N. des. clarify. *)
  (*   } *)

  (*   punfold SAFE. inv SAFE. *)
  (*   punfold EXEC_STATE. inv EXEC_STATE. *)
  (*   { exfalso. eauto. } *)
  (*   clear PROGRESS. ss. *)

  (*   r in BEH_CONS. *)
  (*   eapply Forall3_nth3 in BEH_CONS; eauto. i. des. *)
  (*   renames e1 e2 into tes1 exec'_n. *)
  (*   renames NTH1 NTH2 into TES1 EXEC'_N. *)
  (*   r in P_FA. subst. *)

  (*   replace (SyncSys.time st + S k') with *)
  (*       (SyncSys.time st' + k'). *)
  (*   2: { inv STEP; ss; nia. } *)
  (*   eapply IH. *)
  (*   { hexploit SAFE_NXT; eauto. *)
  (*     { congruence. } *)
  (*     clear. i. pclearbot. ss. } *)
  (*   { unfold Str_nth in *. ss. eauto. } *)
  (*   { r in EXEC_REST. des; ss. eauto. } *)
  (*   ss. *)
  (* Qed. *)

  Lemma exec_div_one_period
        (tm: Z) inbs lsts
        st exec
        (MATCH: match_sinv tm d inbs lsts st)
        (EXEC_ST: DSys.exec_state dsys st exec)
    : exists scnt tr
        d' inbs' lsts'
        st' exec',
      <<EXEC_DIV: sapp_each_rel tr exec' exec>> /\
      <<MSTEPS_PRD: msteps dsys scnt st tr st'>> /\
      <<DATA_NXT: abs_data_next _ _ d d'>> /\
      <<MATCH': match_sinv (tm + prd)%Z d' inbs' lsts' st'>> /\
      <<EXEC_ST': DSys.exec_state dsys st' exec'>>.
  Proof.
  Admitted.


  Lemma exec_state



  Lemma sync_exec_time_props
        (tm_lb: nat)
    : forall (st: @Executable. state E M)
        (exec: exec_t E)
        (SAFE: @DSys.safe_state _ dsys st)
        (EXEC_STATE: DSys.exec_state dsys st exec)
        (TIME: (tm_lb <= SyncSys.time st))
    ,
      Forall (Forall_stream (fun x: Z * events _ =>
                                 (* Z.of_nat ts_n = fst x /\ *)
                                 (Z.of_nat tm_lb <= fst x)%Z /\
                                 (snd x = [] \/
                                  Z.divide (Z.of_nat (SyncSys.period sys)) (fst x))))
             exec.
  Proof.
    i.
    apply Forall_forall. intros lexec LEXEC_IN.
    revert_until st. revert st.
    pcofix CIH. i.

    punfold SAFE. inv SAFE.
    punfold EXEC_STATE. inv EXEC_STATE.
    { exfalso. eauto. }
    r in EXEC_REST. des; ss.

    r in BEH_CONS.
    eapply In_nth_error in LEXEC_IN. des.
    eapply Forall3_nth3 in BEH_CONS; eauto.
    unfold Cons_rel in BEH_CONS.
    des.
    destruct e1 as [tsp1 es1].
    renames e2 NTH1 NTH2 into exec'_n ES1 EXEC'_N. subst.

    assert (<<TSP1_UBND: (Z.of_nat tm_lb <= tsp1)%Z>> /\
            <<TSP_DIVIDE: es1 = [] \/ Z.divide (Z.of_nat (SyncSys.period sys)) tsp1>>).
    { eapply DSys_filter_nb_sysstep_inv in FILTER_NOBEH.
      eapply Forall2_nth2 in FILTER_NOBEH; eauto.
      des.
      destruct e1 as [tsp1' es1_r].
      renames NTH1 P_FA into ES_N FILTER_NB_LOC.

      inv STEP.
      - apply nth_error_In in ES_N.
        apply repeat_spec in ES_N. clarify.
        unfold DSys.filter_nb_localstep in *.
        ss. clarify.
        splits.
        + nia.
        + left. ss.
      - unfold DSys.filter_nb_localstep in *. ss.
        destruct (deopt_list (map DSys.filter_nb1 es1_r))
          as [es_f|]; ss.
        clarify.

        apply map_nth_error_iff in ES_N. des. clarify.
        esplits; eauto.
        + nia.
        + right.
          apply Nat2Z_inj_divide. ss.
    }
    nbdes.

    pfold. econs.
    { eauto. }
    right.
    eapply CIH.
    { hexploit SAFE_NXT; eauto.
      { congruence. }
      clear. i. pclearbot. eauto. }
    { eauto. }
    { inv STEP.
      - ss. nia.
      - ss. nia. }

    eapply nth_error_In; eauto.
  Qed.


  Lemma event_in_exec_must_in_tr
        (exec exec': exec_t E) tr
        tid (t:Z) e st'
        (IN_EXEC: event_in_exec tid t e exec)
        (EXEC_DIV: sapp_each_rel tr exec' exec)
        (SAFE_STATE: DSys.safe_state st')
        (EXEC_STATE: DSys.exec_state dsys st' exec')
        (TIME_BEFORE: (t < Z.of_nat (SyncSys.time st'))%Z)
    : event_in_tr tid t e tr.
  Proof.
    inv IN_EXEC.
    eapply Forall3_nth3 in EXEC_DIV; eauto. des. subst.
    apply stream_In_app_or in EVTS_AT_T. des.
    { econs; eauto. }

    exfalso.
    eapply sync_exec_time_props in SAFE_STATE; eauto.
    eapply Forall_nth1 in SAFE_STATE; eauto.

    eapply Forall_stream_forall in SAFE_STATE; eauto.
    des; ss.
    - subst. ss.
    - nia.
  Qed.


  Lemma sync_event_in_exec_synchronous
    : forall (st: @SyncSys.state E M)
        (exec: exec_t E)
        tid t e
        (SAFE: @DSys.safe_state _ dsys st)
        (EXEC_STATE: DSys.exec_state dsys st exec)
        (IN_EXEC: event_in_exec tid t e exec)
    ,
      Z.divide (Z.of_nat period) t.
  Proof.
    i.
    inv IN_EXEC.
    hexploit sync_exec_time_props; eauto.
    intro AUX.
    eapply Forall_nth1 in AUX; eauto.
    eapply stream_In_app_ex in EVTS_AT_T. des. subst.
    eapply Forall_stream_app_div in AUX. des.
    punfold FA_STR. inv FA_STR. ss.
    des.
    - exfalso. subst. ss.
    - ss.
  Qed.


  Lemma sync_msteps_time
        scnt st tr st' tm
        (TIME: tm = SyncSys.time st)
        (MSTEPS: msteps dsys scnt st tr st')
    : <<TIME': SyncSys.time st' = tm + scnt>> /\
      <<TRACE_TIME: Forall (Forall (fun te => Z.of_nat tm <= fst te < Z.of_nat (tm + scnt))%Z) tr>>.
  Proof.
    depgen tm.
    induction MSTEPS; i; ss.
    { rewrite Nat.add_0_r. esplits; eauto.
      subst es.
      apply Forall_forall. intros x IN.
      apply repeat_spec in IN. subst x.
      econs. }

    hexploit IHMSTEPS; eauto. i. des.
    clear IHMSTEPS.

    inv STEP; ss.
    - esplits; eauto.
      + nia.
      + apply Forall_nth.
        intro k.
        destruct (nth_error tr k) eqn: TR_K; ss.
        * eapply Forall3_nth3 in CONS_EVENTS; eauto.
          des. subst.
          renames e1 e2 into es1_k tr2_k.
          renames NTH1 NTH2 into ES1_K TR2_K.
          econs.
          2: {
            eapply Forall_nth1 in TRACE_TIME; eauto.
            eapply Forall_impl; eauto.
            s. i. nia.
          }
          apply DSys_filter_nb_sysstep_inv in FILTER_NB.
          eapply Forall2_nth2 in FILTER_NB; eauto. des.
          eapply nth_error_In in NTH1.
          apply repeat_spec in NTH1. subst e1.
          unfold DSys.filter_nb_localstep in P_FA.
          ss. clarify. ss. nia.

    - esplits; eauto.
      + nia.
      + apply Forall_nth.
        intro k.
        destruct (nth_error tr k) eqn: TR_K; ss.
        * eapply Forall3_nth3 in CONS_EVENTS; eauto.
          des. subst.
          renames e1 e2 into es1_k tr2_k.
          renames NTH1 NTH2 into ES1_K TR2_K.
          econs.
          2: {
            eapply Forall_nth1 in TRACE_TIME; eauto.
            eapply Forall_impl; eauto.
            s. i. nia.
          }
          apply DSys_filter_nb_sysstep_inv in FILTER_NB.
          eapply Forall2_nth2 in FILTER_NB; eauto. des.

          eapply map_nth_error_iff in NTH1. des. clarify.
          apply DSys_filter_nb_localstep_inv in P_FA. des.
          ss. nia.
  Qed.

  Lemma sync_msteps_system_time_adv
        scnt st tr st' tm
        (TIME: tm = SyncSys.time st)
        (MSTEPS: msteps dsys scnt st tr st')
    : <<TIME': SyncSys.time st' = tm + scnt>>.
  Proof.
    hexploit sync_msteps_time; eauto. i. des. ss.
  Qed.


  Lemma sync_msteps_trace_time_range
        scnt st tr st'
        tid tr_n t es
        (MSTEP: msteps dsys scnt st tr st')
        (TR_N: nth_error tr tid = Some tr_n)
        (COMPL: In (t, es) tr_n)
    : (Z.of_nat (SyncSys.time st) <= t < Z.of_nat (SyncSys.time st'))%Z.
  Proof.
    hexploit sync_msteps_time; eauto. i. des.
    eapply Forall_nth1 in TRACE_TIME; eauto.
    eapply In_nth_error in COMPL. des.
    eapply Forall_nth1 in TRACE_TIME; eauto.
    ss. nia.
  Qed.


  Lemma sync_nonsync_msteps_det
        st tm nst tr st_f
        (SYS_TIME: SyncSys.time st = tm)
        (* (NONSYNC: ~ Nat.divide period tm) *)
        (NST: nst = nsteps_to_sync period (SyncSys.time st))
        (EMPTY_TRACE: tr = empty_trace
                             (Z.of_nat tm) (SyncSys.num_sites st) nst)
        (ST_F: st_f = SyncSys.State (tm + nst)
                                    (SyncSys.node_states st))
    : <<PROG: msteps dsys nst st tr st_f>> /\
      <<DET: forall tr' st_f'
               (MSTEPS': msteps dsys nst st tr' st_f'),
        tr' = tr /\ st_f' = st_f>>.
  Proof.
    depgen tm. depgen st. depgen tr.
    induction nst as [| nst']; i; ss.
    - subst.
      rewrite Nat.add_0_r.
      split.
      { destruct st. ss. econs; ss. }
      r. i. inv MSTEPS'. ss.
      split; ss.
      destruct st_f'; ss.

    - destruct st; ss. subst.

      assert (TM_NONSYNC: ~ Nat.divide period tm).
      { hexploit (nsteps_to_sync_spec period); eauto.
        intros (_ & NS).
        hexploit (NS O).
        { nia. }
        rewrite Nat.add_0_r. ss. }

      hexploit IHnst'; eauto.
      { instantiate (1:= SyncSys.State (S tm) node_states).
        ss.
        hexploit (nsteps_to_sync_adv
                    period tm (S nst')); eauto. }
      { ss. f_equal. nia. }
      i. des.

      split.
      + econs.
        * econs 1; eauto.
        * unfold DSys.filter_nb_sysstep.
          apply deopt_list_Some_iff.
          instantiate (1:= repeat (Z.of_nat tm, []) (length (node_states))).
          apply nth_eq_list_eq.
          i. unfold DSys.filter_nb_localstep.
          do 2 rewrite Coqlib.list_map_nth.

          destruct (lt_ge_dec n (length node_states)).
          2: {
            rewrite nth_error_None2.
            2: { rewrite repeat_length. ss. }
            rewrite nth_error_None2.
            2: { rewrite repeat_length. ss. }
            ss.
          }
          rewrite repeat_nth_error_Some by ss.
          rewrite repeat_nth_error_Some by ss.
          ss.
        * eauto.
        * ss. clear. r.
          unfold SyncSys.num_sites. ss.
          apply Forall3_nth. i.
          unfold empty_trace.

          destruct (lt_ge_dec n (length node_states)).
          2: {
            rewrite nth_error_None2.
            2: { rewrite repeat_length. ss. }
            rewrite nth_error_None2.
            2: { rewrite repeat_length. ss. }
            rewrite nth_error_None2.
            2: { rewrite repeat_length. ss. }
            econs.
          }

          rewrite repeat_nth_error_Some; eauto.
          rewrite repeat_nth_error_Some; eauto.
          rewrite repeat_nth_error_Some; eauto.
          econs. ss.
          f_equal. f_equal. nia.
      + r. clear PROG.
        i. inv MSTEPS'.
        unfold SyncSys.num_sites in *. ss.
        inv STEP; ss.
        apply DSys_filter_nb_sysstep_inv in FILTER_NB.

        hexploit DET; eauto. i. des.
        split; ss.

        subst.
        unfold empty_trace in *.
        clear - FILTER_NB CONS_EVENTS.
        apply nth_eq_list_eq.

        intro n.
        hexploit Forall3_length; try apply CONS_EVENTS.
        rewrite repeat_length.
        intros (LEN1 & LEN2).

        destruct (lt_ge_dec n (length node_states)).
        2: {
          rewrite nth_error_None2 by nia.
          rewrite nth_error_None2.
          2: { rewrite repeat_length. ss. }
          ss.
        }

        eapply Forall2_nth1 with (n:=n) in FILTER_NB.
        2: { apply repeat_nth_error_Some. ss. }
        des.
        unfold DSys.filter_nb_localstep in P_FA. ss. clarify.
        eapply Forall3_nth1 in CONS_EVENTS; eauto. des.
        clarify.
        rewrite repeat_nth_error_Some by ss.
        rewrite repeat_nth_error_Some in NTH0 by ss. clarify.
        rewrite NTH3. f_equal. f_equal. f_equal. nia.
  Qed.

End SYNC_SYS_LEMMAS.
