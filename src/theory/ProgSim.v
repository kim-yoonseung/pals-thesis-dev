From Paco Require Import paco.
From ITree Require Import ITree.

Require Import sflib ITreeTac.
Require Import StdlibExt.
Require Import SysSem.
Require Import IPModel DiscreteTimeModel.
Require Import RTSysEnv.
Require Import NWSysModel ProgSem.
Require Import OSModel OSNodes.
Require Import FMSim FMSim_Switch.

Require Import PeanoNat.
Require Import ZArith List Lia.

Set Nested Proofs Allowed.



Lemma node_state_eq_inv sysE
      (nd: @Node.t sysE) ist1 ist2
      (NST_EQ: Node.State nd ist1 =
               Node.State nd ist2)
  : ist1 = ist2.
Proof.
  inv NST_EQ. existT_elim. clarify.
Qed.


Section SIM_ITREE.
  Context `{progE: Type -> Type}.

  Variable prog: @Prog.t progE.
  Hypothesis wf_prog: Prog.wf prog.

  Let itree_t: Type := itree progE unit.
  Let state: Type := Prog.state prog.

  Inductive _sim_itree
            (sim: nat -> itree_t -> state -> Prop)
    : nat -> itree_t -> state -> Prop :=
  | SimITree_Final
      idx itr itr' pst
      (PROG_FINAL_STATE: Prog.final_state prog pst)
      (ITREE_STEPS: itree_tau_star itr itr')
      (OBS_RET: observe itr' = RetF tt)
    : _sim_itree sim idx itr pst

  | SimITree_Silent
      idx itr pst pst1
      (PROG_PROGRESS: Prog.step prog pst pst1)
      (SIM_NXT:
         forall pst'
           (PROG_SILENT_STEP: Prog.step prog pst pst'),
         exists idx' itr',
           ((itree_tau_star itr itr' /\ idx' < idx) \/
            itree_tau_plus itr itr') /\
           sim idx' itr' pst')
    : _sim_itree sim idx itr pst

  | SimITree_Event
      idx itr pst
      R (ec: progE R)
      itr' k
      (PROG_EVENT: Prog.at_event prog pst (EventCall ec))
      (* (PRECOND: precond_E ec) *)
      (ITREE_STEPS: itree_tau_star itr itr')
      (ITREE_EVENT: observe itr' = VisF ec k)
      (SIM_RET: forall (r: R) pst_r
                  (* (POSTCOND: postcond_E ec r) *)
                  (RET: Prog.after_event
                          prog pst (Event ec r) pst_r)
        ,
          exists idx', sim idx' (k r) pst_r)
    : _sim_itree sim idx itr pst
  .

  Hint Constructors _sim_itree: paco.

  Lemma sim_itree_monotone: monotone3 _sim_itree.
  Proof.
    ii. inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
      i. hexploit SIM_NXT; eauto. i.
      des; esplits; eauto.
    - econs 3; eauto. i.
      hexploit SIM_RET; eauto. i.
      des. esplits; eauto.
  Qed.

  Definition sim_itree: nat -> itree_t -> state -> Prop :=
    paco3 _sim_itree bot3.

  Hint Resolve sim_itree_monotone: paco.

  Lemma sim_itree_red_idx
        (r: nat -> itree_t -> state -> Prop)
        idx_small idx_big
        (IDX_LE: idx_small <= idx_big)
    : paco3 _sim_itree r idx_small <2= paco3 _sim_itree r idx_big.
  Proof.
    intros itr pst SMALL.
    punfold SMALL. inv SMALL.
    - pfold. econs 1; eauto.
    - pfold. econs 2; eauto.
      i. hexploit SIM_NXT; eauto. i. nbdes.
      esplits; eauto.
      des; eauto.
      left. split; eauto. nia.
    - pfold. econs 3; eauto.
  Qed.

  Lemma sim_itree_taus
        idx itr pst pst'
        (SIM: sim_itree idx itr pst)
        (TAUS: Prog.tau_steps prog pst pst')
    : exists idx' itr',
      ((itree_tau_star itr itr' /\ idx' <= idx) \/
       (itree_tau_plus itr itr')) /\
      sim_itree idx' itr' pst'.
  Proof.
    depgen itr. revert idx.
    induction TAUS; i; ss.
    { esplits; eauto.
      left. split.
      - econs.
      - reflexivity.
    }

    punfold SIM. inv SIM; cycle 2; ss.
    { exfalso.
      hexploit (Prog.step_evt_disj prog); eauto.
    }
    { exfalso.
      hexploit (Prog.final_nostep prog); eauto.
      intros [NSTEP _]. apply NSTEP. eauto.
    }

    clear PROG_PROGRESS.
    hexploit SIM_NXT; eauto.
    i. nbdes. pclearbot.

    hexploit (IHTAUS idx' itr'); eauto. i. nbdes.
    esplits.
    2: { eauto. }
    des.
    - left. split.
      + eapply itree_tau_star_trans; eauto.
      + nia.
    - right.
      eapply itree_tau_plus_star_plus; eauto.
    - right.
      eapply itree_tau_star_plus_plus; eauto.
    - right.
      eapply itree_tau_plus_app; eauto.
  Qed.

  Lemma sim_itree_silent
        idx itr pst pst1 pst2
        (SIM: sim_itree idx itr pst)
        (TAUS: Prog.tau_steps prog pst pst1)
        (SILENT_STEP: Prog.step prog pst1 pst2)
    : exists idx' itr',
      ((itree_tau_star itr itr' /\ idx' < idx) \/
       (itree_tau_plus itr itr'))
      /\
      sim_itree idx' itr' pst2.
  Proof.
    hexploit sim_itree_taus; eauto.
    intros (idx1 & itr1 & IDX_STEP1 & SIM1).
    punfold SIM1. inv SIM1; ss; cycle 2.
    - exfalso.
      hexploit (Prog.step_evt_disj _ wf_prog); eauto.
    - exfalso.
      hexploit (Prog.final_nostep _ wf_prog); eauto.
      intros [NSTEP _]. apply NSTEP. eauto.
    - hexploit SIM_NXT; try apply SILENT_STEP.
      i. nbdes. pclearbot.
      esplits; eauto.
      des; ss.
      + left. split.
        * eapply itree_tau_star_trans; eauto.
        * nia.
      + right.
        eapply itree_tau_plus_star_plus; eauto.
      + right.
        eapply itree_tau_star_plus_plus; eauto.
      + right.
        eapply itree_tau_plus_app; eauto.
  Qed.

  Lemma sim_itree_event
        idx itr pst pst' R (ec: progE R)
        (SIM: sim_itree idx itr pst)
        (TAUS: Prog.tau_steps prog pst pst')
        (AT_EVT: Prog.at_event prog pst' (EventCall ec))
    : exists itr' k,
      itree_tau_star itr itr' /\
      observe itr' = VisF ec k /\
      (* precond_E ec /\ *)
      (* sim_itree 0 itr' pst' /\ *)
      (forall retv pst_r
         (* (POSTCOND: postcond_E ec retv) *)
         (AFT_EVT: Prog.after_event
                     prog pst' (Event ec retv) pst_r)
        ,
          exists idx', sim_itree idx' (k retv) pst_r)
  .
  Proof.
    depgen itr. revert idx.
    induction TAUS; i; ss.
    { punfold SIM. inv SIM.
      - exfalso.
        hexploit (Prog.final_nostep _ wf_prog); eauto.
        intro C. apply C. eauto.
      - exfalso.
        hexploit (Prog.step_evt_disj _ wf_prog); eauto.
        (* intro C. apply C. eauto. *)
      - hexploit (Prog.at_event_det _ wf_prog).
        { apply PROG_EVENT. }
        { apply AT_EVT. }
        i. clarify. existT_elim. subst.
        clear AT_EVT.
        esplits; eauto.
        i. hexploit SIM_RET; eauto.
        i. des. pclearbot.
        eauto.
    }

    punfold SIM. inv SIM; cycle 2.
    { exfalso.
      hexploit (Prog.step_evt_disj _ wf_prog); eauto.
      (* intro C. apply C. *)
      (* split; eauto. *)
    }
    { exfalso.
      hexploit (Prog.final_nostep _ wf_prog); eauto.
      intros [NSTEP NEVT].
      apply NSTEP. eauto.
    }

    hexploit SIM_NXT.
    { eapply STEP1. }
    i. nbdes. pclearbot.

    hexploit IHTAUS.
    { eauto. }
    { eauto. }
    i. rename itr' into itr_m. nbdes.

    esplits.
    + eapply (itree_tau_star_trans _ _ itr itr_m itr'); ss.
      des; ss.
      eapply itree_tau_plus_star. ss.
    + eauto.
    + eauto.
    (* + eauto. *)
  Qed.

  Lemma sim_itree_final
        idx itr pst pst'
        (SIM: sim_itree idx itr pst)
        (TAUS: Prog.tau_steps prog pst pst')
        (SILENT_STEP: Prog.final_state prog pst')
    : exists itr',
      itree_tau_star itr itr' /\
      observe itr' = RetF tt.
  Proof.
    depgen itr. revert idx.
    induction TAUS; i; ss.
    { hexploit (Prog.final_nostep _ wf_prog); eauto.
      intros [NSTEP NEVT].
      punfold SIM. inv SIM; ss; cycle 1.
      - exfalso. apply NSTEP. eauto.
      - exfalso. apply NEVT. eauto.
      - eauto.
    }

    punfold SIM. inv SIM; ss; cycle 2.
    - exfalso.
      hexploit (Prog.step_evt_disj _ wf_prog); eauto.
      (* intro C. apply C. split; eauto. *)
    - exfalso.
      hexploit (Prog.final_nostep _ wf_prog); eauto.
      intros [NSTEP NEVT]. apply NSTEP. eauto.
    - clear PROG_PROGRESS.
      hexploit SIM_NXT; eauto.
      i. nbdes. pclearbot.
      hexploit IHTAUS; eauto.
      i. nbdes.
      esplits; eauto.
      eapply itree_tau_star_trans; eauto.
      des; ss.
      eapply itree_tau_plus_star. ss.
  Qed.


  Inductive sim_itree_prog (itr: itree_t): Prop :=
    SimITreeProg
      (INIT_EXISTS: exists st1, Prog.initial_state prog st1)
      (SIM_INIT: forall st_init
                   (PROG_INIT_STATE: Prog.initial_state
                                       prog st_init),
          exists idx, sim_itree idx itr st_init)
  .

End SIM_ITREE.

Hint Resolve sim_itree_monotone: paco.


Section SIM_ITREE_ADEQ.
  Context `{SystemEnv} (* `{sysE: Type -> Type}. *).
  (* Context `{event_conds sysE}. *)

  Context `{obsE: Type -> Type}.
  Notation progE := (osE +' obsE).
  Variable ip: ip_t.
  Hypothesis LOCAL_IP: IP.local_ip ip = true.

  Let itree_t: Type := itree progE unit.

  Variable prog: @Prog.t progE.
  Hypothesis wf_prog: Prog.wf prog.
  Variable prog_itree: itree_t.
  Variable tsg: nat -> tsp.

  Let prog_src: Prog.t := prog_of_itree _ prog_itree.
  Let nd_src: Node.t := OSNode.as_node ip prog_src tsg.
  Let nd_tgt: Node.t := OSNode.as_node ip prog tsg.

  Lemma itree_idx_prog_step
        idx itr idx' itr'
        (IDX_STEP : (itree_tau_star itr itr' /\
                     idx' < idx) \/
                    (itree_tau_plus itr itr'))
    : exists pst',
      Prog.tau_steps prog_src (idx, itr) pst' /\
      Prog.step prog_src pst' (idx', itr').
  Proof.
    des.
    - induction IDX_STEP; ss.
      + exists (S idx', itr).
        split.
        * eapply iprog_tau_idx_decr; ss.
        * econs.
      + des.
        esplits; eauto.
        eapply Prog.tau_steps_app.
        { apply iprog_tau_idx_zero. }
        econs; ss.
        { econs; eauto. }
        eauto.
    - r in IDX_STEP.
      destruct IDX_STEP as
          (itr_f & TAU_STAR_F & OBS_TAU_F).
      esplits.
      { eapply iprog_itree_tau_star_until_zero; eauto. }
      econs; ss.
  Qed.


  Lemma sim_fmsim
        (SIM: sim_itree_prog prog prog_itree)
    : fmsim_nodes nd_src nd_tgt.
  Proof.
    rr.
    split.
    { ss. }
    i. rr in INIT_TGT. subst.
    esplits; ss.

    rename gtm_init into gtm.
    revert gtm.
    pcofix CIH_OFF.

    (* i. eapply consume_boot_delay; eauto. *)
    (* generalize (DTime.uadd gtm n) as gtm'. *)
    (* clear gtm n. *)
    (* intro gtm. *)

    i. pfold. econs.
    { eauto. }
    i. destruct dmss as [| dms []]; ss.
    inv STEPS_TGT. inv REST_STEPS.
    inv STEP; ss.

    (* inv ACCEPT. *)
    inv SIM.
    inv ESTEP; ss.
    2: {
      inv IST_ADV_LCLOCK.
      esplits; eauto.
      - econs; eauto; ss.
        + econs; ss.
          * eapply OSNode.Estep_Off.
          * econs; ss.
        + econs 1.
      - ss.
      - econs; ss.
    }

    inv INIT_PROC.
    2: { exfalso. eauto. }
    inv IST_ADV_LCLOCK.

    clear INIT_EXISTS.
    hexploit SIM_INIT; eauto.
    clear SIM_INIT.
    intro SIM_ITR. des.
    rename lat_i into lat.

    esplits.
    { econs; ss.
      - econs; ss.
        + eapply OSNode.Estep_Boot with (lat_i:=lat); eauto.
          econs; eauto.
          instantiate (1:= (idx, prog_itree)). ss.
        + econs; eauto.
      - ss.
      - econs; eauto.
    }
    { unfold DSys.filter_nb_localstep in NOT_NB.
      ss. clarify. }
    { econs; ss. }

    left. ss.
    clear dms WF_DMSS.
    (* fold OS.init_state. *)
    assert (COSP_SRC: OSNode.corr_os_prog prog_src
                        OS.init_state (idx, prog_itree)) by ss.
    assert (COSP_TGT: OSNode.corr_os_prog prog
                        OS.init_state pst) by ss.
    revert COSP_SRC COSP_TGT.

    generalize OS.wf_init as WF_OS.
    generalize OS.init_state as os.
    rewrite DTime_uadd_one.
    clear VALID_CLOCK_SKEW.
    rr in ADV_LCLOCK.
    destruct ADV_LCLOCK as [_ VALID_CSKEW].
    revert VALID_CSKEW.

    rename gtm into gtm'.
    generalize (DTime.succ gtm') as gtm.
    clear gtm' ltm_i.
    rename ltm' into ltm.
    revert ltm lat.
    clear_tt.
    clear NOT_NB PROG_INIT_STATE.
    revert pst idx SIM_ITR.
    generalize prog_itree as itr.

    pcofix CIH_LIVE. i.

    (* live step *)
    pfold. econs.
    { eauto. }
    i. destruct dmss as [| dms []]; ss.
    clear_tt.

    assert (WF_DMS: Forall Packet.msg_wf dms)
      by (inv WF_DMSS; ss).
    inv STEPS_TGT. inv REST_STEPS. ss.
    inv STEP. ss.
    inv ESTEP; ss; cycle 2.
    { (* fail *)
      inv IST_ADV_LCLOCK.
      esplits; eauto; ss.
      2: { econs; ss. }

      econs; ss.
      - econs; ss.
        + eapply OSNode.Estep_Off; eauto.
        + econs; eauto.
      - ss.
      - econs 1.
    }
    { (* latency *)
      (* inv ACCEPT. *)
      inv IST_ADV_LCLOCK.
      esplits; ss.
      { econs; ss.
        - econs; ss.
          + eapply OSNode.Estep_Latency; ss.
          + econs; eauto.
        - ss.
        - econs 1.
      }
      { econs; ss. }
      right. ss.
      rewrite DTime_uadd_one.
      eapply CIH_LIVE; eauto.
      - inv ADV_LCLOCK. ss.
      - inv WF_DMSS.
        eapply OS.wf_accept_msgs; try reflexivity; ss.
      - eapply OSNode.accept_msgs_corr_os_prog. ss.
      - eapply OSNode.accept_msgs_corr_os_prog. ss.
    }

    destruct os as [skts tmr sts]. ss.
    (* proc_step *)
    inv PROC_STEP; ss; cycle 1.
    - (* os_step *)
      inv IST_ADV_LCLOCK.
      hexploit OS.wf_accept_msgs; eauto. intro WF_OS_ACC.
      hexploit OS.wf_preserve; eauto. i. des.

      esplits.
      { econs; ss.
        - econs; ss.
          + econs; ss.
            eapply OSNode.ProcStep_OSStep; eauto.
          + econs; eauto.
        - ss.
        - econs 1.
      }
      { unfold DSys.filter_nb_localstep in NOT_NB.
        ss. clarify. }
      { econs; ss. }

      right.
      rewrite DTime_uadd_one.
      eapply CIH_LIVE; eauto.
      + inv ADV_LCLOCK. ss.
      + eapply OSNode.os_step_corr_os_prog; try apply OS_STEP. ss.
      + eapply OSNode.os_step_corr_os_prog; try apply OS_STEP. ss.

    - (* os_ret *)
      (* inv ACCEPT. ss. *)
      inv IST_ADV_LCLOCK.
      destruct os_evt as [R os_e retv].
      hexploit OS.wf_accept_msgs; eauto. intro WF_OS_ACC.
      hexploit OS.wf_ret; eauto.
      intros [WF_OS' POSTCOND_OSE].

      inv OS_RET. existT_elim. clarify.
      unfold OSNode.corr_os_prog in *.

      hexploit COSP_TGT; ss.
      i. des. rename PROG_EVT into PROG_EVT_TGT.
      clear COSP_TGT.
      hexploit COSP_SRC; ss.
      i. des. rename PROG_EVT into PROG_EVT_SRC.
      clear COSP_SRC.
      clarify. existT_elim.
      inv PROG_EVT_SRC.

      punfold SIM_ITR. inv SIM_ITR; ss.
      + exfalso.
        hexploit (Prog.final_nostep _ wf_prog); eauto.
        i. des. eauto.
      + exfalso.
        hexploit (Prog.step_evt_disj _ wf_prog); eauto.
      + inv ITREE_STEPS.
        2: { congruence. }
        rewrite ITREE_EVENT in OBS.
        clarify. existT_elim.

        hexploit (Prog.at_event_det _ wf_prog).
        { apply PROG_EVENT. }
        { apply PROG_EVT_TGT. }
        i. clarify. existT_elim. clarify. clear_tt.

        hexploit SIM_RET; eauto.
        (* { cbv. eauto. } *)
        intro SIM_ITR. des.
        pclearbot.

        esplits; ss.
        { econs; ss.
          - econs; ss.
            + eapply OSNode.Estep_RunProcess; ss.
              eapply OSNode.ProcStep_OSReturn; ss.
              instantiate (1:= (idx', k retv)).
              econs; eauto.
            + econs; eauto.
          - ss.
          - econs 1.
        }
        { econs; econs; ss. }

        rewrite DTime_uadd_one. ss.
        right.
        eapply CIH_LIVE; ss.
        inv ADV_LCLOCK. ss.

    - (* prog_step *)
      (* inv ACCEPT. *)
      inv IST_ADV_LCLOCK.
      inv PEFF_STEP; ss.
      + (* os_call *)
        inv OS_CALL.
        hexploit (sim_itree_event prog); eauto.
        intros (itr' & k & ITREE_TAU & OBS_EVT & SIM_AFT).
        esplits; ss.
        { econs; ss.
          - econs; ss.
            + eapply OSNode.Estep_RunProcess; ss.
              eapply OSNode.ProcStep_ProgStep; ss.
              * eapply iprog_itree_tau_star_until_zero; eauto.
              * eapply OSNode.PEffStep_OSCall
                  with (os_ec := EventCall os_e).
                -- ss. econs; eauto.
                -- econs.
            + econs; eauto.
          - ss.
          - econs 1.
        }
        { econs; ss. }

        right. ss. rewrite DTime_uadd_one.
        eapply CIH_LIVE.
        * pfold.
          econs 3; eauto.
          -- econs.
          -- i. hexploit SIM_AFT; eauto.
             i. des.
             esplits. eauto.
        * inv ADV_LCLOCK. ss.
        * eapply (OS.wf_accept_msgs dms); ss.
          { eapply OS.wf_call; eauto. ss. }
          ss.
        * intro RST. ss.
          esplits; eauto.
          econs. eauto.
          (* eapply OSNode.accept_msgs_corr_os_prog in COSP_SRC. *)
          (* eapply COSP_SRC. *)
          (* r. intros _. *)
          (* esplits; eauto; ss. *)
          (* { econs. eauto. } *)
          (* { inv OS_CALL. existT_elim. } *)
        * intro RST. ss.
          esplits; eauto.
          (* apply OSNode.accept_msgs_corr_os_prog. *)
          (* r. intros _. *)
          (* esplits; eauto; ss. *)
          (* inv OS_CALL. existT_elim. *)
      (* + (* time-limit event *) *)
      (*   hexploit (sim_itree_event prog); eauto. *)
      (*   intros (itr' & k & ITREE_TAU & OBS_EVT & SIM_AFT). *)
      (*   hexploit SIM_AFT; eauto; ss. i. des. *)

      (*   esplits; ss. *)
      (*   { econs; eauto. *)
      (*     2: { econs 1. } *)

      (*     econs; ss. *)
      (*     - eapply OSNode.Estep_RunProcess; ss. *)
      (*       eapply OSNode.ProcStep_ProgStep; ss. *)
      (*       + eapply iprog_itree_tau_star_until_zero; eauto. *)
      (*       + eapply OSNode.PEffStep_AdvTimeLimit; eauto; ss. *)
      (*         * econs; eauto. *)
      (*         * econs; eauto. *)
      (*     - econs; eauto. *)
      (*   } *)
      (*   { econs; ss. } *)

      (*   right. ss. rewrite DTime_uadd_one. *)
      (*   eapply CIH_LIVE; eauto. *)
      (*   * inv ADV_LCLOCK. ss. *)
      (*   * hexploit OS.wf_accept_msgs; eauto. *)
      (*   * congruence. *)
      (*   * congruence. *)

      + (* sys_event *)
        hexploit (sim_itree_event prog); eauto.
        intros (itr' & k & ITREE_TAU &
                OBS_EVT & SIM_AFT).
        hexploit SIM_AFT; eauto; ss. i. des.

        esplits; ss.
        { econs; eauto.
          2: { econs 1. }

          econs; ss.
          - eapply OSNode.Estep_RunProcess; ss.
            eapply OSNode.ProcStep_ProgStep; ss.
            + eapply iprog_itree_tau_star_until_zero; eauto.
            + eapply OSNode.PEffStep_SysEvent; eauto; ss.
              * econs; eauto.
              * econs; eauto.
          - econs; eauto.
        }
        { econs; ss. }

        right. ss. rewrite DTime_uadd_one.
        eapply CIH_LIVE; eauto.
        * inv ADV_LCLOCK. ss.
        * hexploit OS.wf_accept_msgs; eauto.
        * congruence.
        * congruence.

      + (* tau step *)
        hexploit (sim_itree_silent prog); eauto.
        destruct 1 as (idx' & itr' & TAU_STAR & SIM').
        eapply itree_idx_prog_step in TAU_STAR.
        des.

        esplits; ss.
        { econs; eauto.
          2: { econs 1. }
          econs; ss.
          - eapply OSNode.Estep_RunProcess; ss.
            eapply OSNode.ProcStep_ProgStep; eauto.
            eapply OSNode.PEffStep_Step; eauto.
          - econs; eauto.
        }
        { econs; ss. }

        right. rewrite DTime_uadd_one.
        apply CIH_LIVE; eauto; ss.
        * inv ADV_LCLOCK. ss.
        * eapply OS.wf_accept_msgs; eauto.
        * intro OS_RUNNING.
          unfold OS.running_state in *. ss. congruence.
        * intro OS_RUNNING.
          unfold OS.running_state in *. ss. congruence.

      + (* final *)
        hexploit (sim_itree_final prog); eauto. i. des.
        esplits; ss.
        { econs; eauto.
          2: { econs 1. }
          econs; ss.
          - eapply OSNode.Estep_RunProcess; ss.
            eapply OSNode.ProcStep_ProgStep; ss.
            + eapply iprog_itree_tau_star_until_zero; eauto.
            + eapply OSNode.PEffStep_Final; eauto; ss.
          - econs; eauto.
        }
        { econs; ss. }

        right. rewrite DTime_uadd_one. ss.
        eapply CIH_LIVE; eauto.
        * pfold. econs 1; eauto. econs.
        * inv ADV_LCLOCK. ss.
        * eapply OS.wf_accept_msgs; eauto.
        * intro OS_RUNNING.
          unfold OS.running_state in *. congruence.
        * intro OS_RUNNING.
          unfold OS.running_state in *. congruence.

      + (* stuck *)
        exfalso.
        hexploit (sim_itree_taus prog); eauto.
        intros (idx1 & itr1 & IDX_STEP1 & SIM1).

        inv PROG_STUCK.
        punfold SIM1. inv SIM1.
        * ss.
        * eapply STUCK_STEP; eauto.
        * eapply NOT_AT_EVENT; eauto.
  Qed.

End SIM_ITREE_ADEQ.
