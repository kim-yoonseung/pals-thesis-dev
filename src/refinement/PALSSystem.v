From ITree Require Import ITree.
From compcert Require Import AST Memory Maps Globalenvs.
From compcert Require Import Linking Ctypes.
From compcert Require Coqlib Clight.
From Paco Require Import paco.

Require Import List Lia ZArith.

Require Import sflib.
Require Import StdlibExt IntegersExt.
Require Import DiscreteTimeModel IPModel.
Require Import SysSem.
Require Import RTSysEnv.
Require Import MWITree.
Require Import CProgEventSem.
Require Import ProgSem.

Require Import NWSysModel.
Require Import OSModel OSNodes.
Require Import AbstMW AbstAsyncSysModel SyncSysModel.
Require Import Executable.

Require Import FMSim FMSim_Switch ProgSim.
Require Import GMSim.
Require Import VerifMain.

Require Import LinkLemmas.
Require Import AbstMWRef AmwAsyncRef AsyncSyncRef SyncExecRef.
Require Import ExecSyncRef.
Require Import SystemProgs.

Require Import VerifProgBase.



Lemma prog_genv_props
      (p: Clight.program)
      gvs gfs cenvs
      (NAMES_NOREP: Coqlib.list_norepet (prog_defs_names p))
      (IN_GVS: forall id gv, In (id, gv) gvs ->
                        In (id, Gvar gv) (prog_defs p))
      (IN_GFS: forall id gf, In (id, gf) gfs ->
                        In (id, Gfun gf) (prog_defs p))
      (IN_CENVS: forall id co, In (id, co) cenvs ->
                          (prog_comp_env p) ! id = Some co)
  : genv_props (Clight.globalenv p) gvs gfs cenvs.
Proof.
  econs.
  - i. hexploit IN_GVS; eauto. intro IN_DEFS.
    cut ((prog_defmap p) ! i = Some (Gvar gv)).
    { intro DEFMAP.
      eapply Genv.find_def_symbol in DEFMAP. des.
      esplits; eauto.
      eapply Genv.find_var_info_iff. eauto. }
    eapply prog_defmap_norepet; eauto.
  - i. hexploit IN_GFS; eauto. intro IN_DEFS.
    cut ((prog_defmap p) ! i = Some (Gfun fd)).
    { intro DEFMAP.
      eapply Genv.find_def_symbol in DEFMAP. des.
      esplits; eauto.
      rewrite Genv.find_funct_find_funct_ptr.
      apply Genv.find_funct_ptr_iff. eauto. }
    eapply prog_defmap_norepet; eauto.
  - i. hexploit IN_CENVS; eauto.
Qed.


Module PALSTask.
  Section TASK.
    Context `{rnws_params}.
    Context `{SystemEnv}.
    (* Context `{CProgSysEvent}. *)

    Record t: Type :=
      mk { tid: Tid ;
           cprog_app: Clight.program;
           cprog_tot: Clight.program;

           app_mod: @AppMod.t obsE bytes ;
           sim_app: SimApp tid cprog_tot app_mod;

           cprog_link_ok: link prog_mw cprog_app = Some cprog_tot ;

           cprog_tot_names_norep:
             Coqlib.list_norepet (prog_defs_names cprog_tot);

           gvs_ok: forall id gv,
               In (id, gv) (main_gvar_ilist tid ++ app_gvar_ilist) ->
               In (id, Gvar gv) (prog_defs cprog_tot);
           gfs_ok: forall id gf,
               In (id, gf) (main_gfun_ilist ++ app_gfun_ilist) ->
               In (id, Gfun gf) (prog_defs cprog_tot);
           cenvs_ok: forall id co,
               In (id, co) (main_cenv_ilist ++ app_cenv_ilist) ->
               (prog_comp_env cprog_tot) ! id = Some co;

           init_mem_ok: Genv.init_mem cprog_tot <> None ;
        }.
  End TASK.
End PALSTask.

Global Instance er_inh_obj: EventRetInhabit obsE.
Proof.
  econs.
  i. destruct e.
  - destruct e.
    + exists Int.zero. ss.
    + exists tt. ss.
  - destruct e.
    exists tt. ss.
Qed.

Module PALSSys.
  Record t: Type :=
    mk { RNWSParamsObj: rnws_params ;
         SystemEnvObj: SystemEnv ;

         tasks: list PALSTask.t ;

         tasks_wf: length tasks = num_tasks ;
         task_ids: iForall (fun tid task =>
                              PALSTask.tid task = tid)
                           0 tasks ;
      }.

  Section SYSTEMS.
    Variable sys: t.

    Let rnws_params_obj := RNWSParamsObj sys.
    Let system_env_obj := SystemEnvObj sys.
    Existing Instance rnws_params_obj.
    Existing Instance system_env_obj.

    (* NW + C_progs *)
    Definition as_nc: @NWSys.t obsE :=
      map (fun task => OSNode.as_node
                      (tid2ip (PALSTask.tid task))
                      (prog_of_clight
                         (PALSTask.cprog_tot task))
                      (fun tm => Z.of_nat (base_time period tm)))
          (tasks sys).

    Definition dsys_nc (tm: nat): DSys.t :=
      NWSys.as_dsys as_nc tm.

    (* NW + itree_progs *)
    Definition as_ni: @NWSys.t obsE :=
      map (fun task => OSNode.as_node
                      (tid2ip (PALSTask.tid task))
                      (prog_of_itree
                         _ (MWITree.main_itree
                              (PALSTask.tid task)
                              (PALSTask.app_mod task)))
                      (fun tm => Z.of_nat (base_time period tm)))
          (tasks sys).

    Definition dsys_ni (tm: nat): DSys.t :=
      NWSys.as_dsys as_ni tm.

    Definition as_snodes: list (@SNode.t obsE bytes) :=
      map ITrSNode.to_snode (map PALSTask.app_mod (tasks sys)).

    (* NW + amw *)
    Definition as_namw: NWSys.t :=
      imap AbstMW.as_node 0 as_snodes.

    Definition dsys_namw (tm: nat): DSys.t :=
      NWSys.as_dsys as_namw tm.

    (* abst_async *)
    Definition dsys_async (tm: nat): DSys.t :=
      AASys.as_dsys as_snodes tm.

    Definition rsz_bmsg (bs: bytes): bytes? :=
      Some (resize_bytes msg_size bs).

    (* sync *)
    Definition as_sync: SyncSys.t :=
      SyncSys.mk period as_snodes (map snd mcasts) rsz_bmsg.

    Definition dsys_sync (tm: nat): DSys.t :=
      SyncSys.as_dsys as_sync tm.

    (* exec *)
    Definition as_exec: ExecutableSpec.t :=
      ExecutableSpec.mk
        _ _
        (Z.of_nat period)
        (map PALSTask.app_mod (tasks sys))
        (map snd mcasts) rsz_bmsg.

    Definition dsys_exec (tm: nat): DSys.t :=
      ExecutableSpec.as_dsys as_exec (Z.of_nat tm) None.

  End SYSTEMS.
End PALSSys.

Ltac refl :=
  lazymatch goal with
  | |- (_ <= _)%nat => fail
  | |- (_ <= _)%Z => fail
  | |- _ => reflexivity
  end.

Lemma aux: forall n1 n2 n3 m,
    n1 (* (n1 - n2) *) <= n3 ->
    (n1 - n2) * m <= n3 * m.
Proof.
  nia.
Qed.

Lemma link_program_main_eq
      (p1 p2 p: Clight.program)
      (LINK_OK: link p1 p2 = Some p)
  : prog_main p1 = prog_main p2 /\
    prog_main p1 = prog_main p.
Proof.
  Local Transparent Linker_program Linker_prog.
  ss.
  hexploit Ctypes.Linker_program_obligation_3; eauto.
  i. des.
  unfold linkorder_program in *. ss. des.
  split; congruence.
  Local Opaque Linker_program Linker_prog.
Qed.


Section VERIF.
  Import PALSSys.
  Variable sys: PALSSys.t.

  Let rnws_params_obj := RNWSParamsObj sys.
  Let system_env_obj := SystemEnvObj sys.
  Existing Instance rnws_params_obj.
  Existing Instance system_env_obj.

  Lemma task_ips_local_aux
    : forall t,
      In t (tasks sys) ->
      IP.local_ip (tid2ip (PALSTask.tid t)) = true.
  Proof.
    intros t T_IN.
    apply In_nth_error in T_IN. des.
    pose proof (task_ids sys) as TASK_IDS.
    rewrite iForall_nth in TASK_IDS. ss.
    specialize (TASK_IDS n).
    rewrite T_IN in TASK_IDS. ss.

    hexploit (valid_task_id_ip n).
    { r. ss.
      unfold rnws_params_obj.
      rewrite <- tasks_wf.
      apply nth_error_Some. congruence.
    }
    intro TASK_ID_IP.
    eapply task_id_ip_comput in TASK_ID_IP. des; ss.
    rewrite TASK_IDS. ss.
  Qed.


  Lemma ref_nc_ni
        (tm_init: nat)
        (TIME_INIT_COND: period <= tm_init)
    : DSys.behav_sys (dsys_nc sys tm_init) <1=
      DSys.behav_sys (dsys_ni sys tm_init).
  Proof.
    eapply ref_switch_all.
    - apply Forall2_nth. i.
      destruct (lt_ge_dec n num_tasks).
      2: { rewrite nth_error_None2.
           2: { unfold as_ni. rewrite map_length.
                rewrite tasks_wf. ss. }
           rewrite nth_error_None2.
           2: { unfold as_nc. rewrite map_length.
                rewrite tasks_wf. ss. }
           econs.
      }
      unfold as_ni, as_nc.

      assert (TASK_N: exists task, nth_error (tasks sys) n = Some task).
      { eapply nth_error_Some2.
        rewrite tasks_wf. ss. }
      des.

      erewrite map_nth_error; eauto.
      erewrite map_nth_error; eauto.
      econs.

      apply sim_fmsim.
      { apply task_ips_local_aux.
        eapply nth_error_In; eauto. }
      { apply cprog_wf. }

      unshelve: eapply sim_main; eauto.
      + apply PALSTask.sim_app.
      + apply prog_genv_props; apply task.
      + eapply PALSTask.init_mem_ok.
      + hexploit link_program_main_eq.
        { apply PALSTask.cprog_link_ok. }
        i. des. eauto.

    - apply Forall_forall.
      unfold as_ni.
      intros nd IN.
      apply in_map_iff in IN. des.

      subst.
      apply OSNode.safe_node.
      eapply task_ips_local_aux; eauto.
    - apply Forall_forall.
      unfold as_nc.
      intros nd IN.
      apply in_map_iff in IN. des.

      subst.
      apply OSNode.safe_node.
      eapply task_ips_local_aux; eauto.
  Qed.

  Lemma ref_ni_amw
        (tm_init: nat)
        (TIME_INIT_COND: period <= tm_init)
    : DSys.behav_sys (dsys_ni sys tm_init) <1=
      DSys.behav_sys (dsys_namw sys tm_init).
  Proof.
    apply ref_switch_all.
    - apply Forall2_nth. i.
      destruct (lt_ge_dec n num_tasks).
      2: { rewrite nth_error_None2.
           2: { unfold as_namw. rewrite imap_length.
                unfold as_snodes.
                rewrite map_length.
                rewrite map_length.
                rewrite tasks_wf. ss. }
           rewrite nth_error_None2.
           2: { unfold as_ni. rewrite map_length.
                rewrite tasks_wf. ss. }
           econs.
      }
      unfold as_ni, as_nc.

      assert (TASK_N: exists task, nth_error (tasks sys) n = Some task).
      { eapply nth_error_Some2.
        rewrite tasks_wf. ss. }
      des.

      unfold as_namw.
      erewrite map_nth_error; eauto.
      erewrite imap_nth_error_iff; eauto. ss.
      unfold as_snodes.
      rewrite map_map.
      erewrite map_nth_error; eauto.
      ss. econs.

      assert (TASK_TID: PALSTask.tid task = n).
      { specialize (task_ids sys) as TASK_IDS.
        rewrite iForall_nth in TASK_IDS.
        specialize (TASK_IDS n). ss.
        rewrite TASK_N in TASK_IDS. ss. }
      rewrite TASK_TID.

      pose (app_mod := PALSTask.app_mod task).
      fold app_mod.

      eapply sim_abst_mw.
      apply valid_task_id_ip; auto.

    - apply Forall_nth.
      unfold as_namw. i.
      rewrite imap_nth_error_iff. ss.
      destruct (nth_error (as_snodes sys) n) eqn: SNODE_N; ss.
      eapply AbstMW.safe_node.
      r.
      apply nth_error_Some1' in SNODE_N.
      unfold as_snodes in SNODE_N.
      rewrite map_length in SNODE_N.
      rewrite map_length in SNODE_N.
      rewrite tasks_wf in SNODE_N. ss.

    - apply Forall_forall.
      unfold as_ni.
      intros nd IN.
      apply in_map_iff in IN. des.

      subst.
      apply OSNode.safe_node.
      eapply task_ips_local_aux; eauto.
  Qed.



  Lemma ref_amw_async
        (tm_init: nat)
        (TIME_INIT_COND: period <= tm_init)
    : DSys.behav_sys (dsys_namw sys tm_init) <1=
      DSys.behav_sys (dsys_async sys tm_init).
  Proof.
    (* subst rnws_params_obj system_env_obj cprog_sys_event_obj. *)
    assert (SAFE_TGT: DSys.safe (dsys_namw sys tm_init)).
    { apply NWSys.safe_nodes_safe.
      apply Forall_nth. i. r.
      unfold as_namw.

      rewrite imap_nth_error_iff. ss.
      unfold as_snodes.
      rewrite Coqlib.list_map_nth.
      rewrite Coqlib.list_map_nth.
      destruct (nth_error (tasks sys) n) as [nd|] eqn: TASK_N; ss.

      assert (valid_task_id n).
      (* hexploit (valid_task_id_ip n). *)
      { r.
        replace num_tasks with (length (tasks sys)).
        2: { unfold rnws_params_obj.
             unfold system_env_obj.
             apply tasks_wf. }
        eapply nth_error_Some1'; eauto. }

      eapply AbstMW.safe_node; eauto.
    }

    eapply fmsim_adequacy; eauto.
    econs. i.

    esplits.
    { econs. }
    inv INIT_TGT.

    assert (exists (amw_sts: list AbstMW.state),
               <<AMW_STS: amw_sts =
                          imap (fun tid nd =>
                                  AbstMW.State tid (tid2ip tid)
                                               nd AbstMW.Off)
                               0 (as_snodes sys)>> /\
               <<AMW_LSTS: iForall3 amw_lst 0
                                    (as_snodes sys) nsts_init amw_sts>>).
    { esplits; eauto.
      apply iForall3_nth. i.
      rewrite imap_nth_error_iff. ss.
      rewrite Forall2_nth in INIT_NODE_STATES.
      specialize (INIT_NODE_STATES n).

      unfold as_namw in *.
      rewrite imap_nth_error_iff in INIT_NODE_STATES. ss.

      inv INIT_NODE_STATES.
      - destruct (nth_error (as_snodes sys) n); ss.
        econs.
      - destruct (nth_error (as_snodes sys) n); ss.
        econs.
        clarify.
        match goal with
        | H: Node.init _ _ |- _ => inv H
        end.
        ss. subst. econs.
    }
    des.
    guardH AMW_STS.

    eapply fmsim_running; try refl; eauto.
    - unfold as_snodes.
      rewrite map_length.
      rewrite map_length.
      rewrite tasks_wf. ss.
    - apply NW.wf_init.
    - r. i. ss.
    - fold rnws_params_obj system_env_obj.
      ss. nia.
    - rewrite AMW_STS.
      apply Forall2_nth. i.
      rewrite imap_nth_error_iff.
      rewrite imap_nth_error_iff.
      ss.
      destruct (nth_error (as_snodes sys) n) eqn: SNODE_N; ss.
      2: { econs. }
      econs.

      assert (VTID: valid_task_id n).
      { r. unfold as_snodes in SNODE_N.
        apply nth_error_Some1' in SNODE_N.
        rewrite map_length in SNODE_N.
        rewrite map_length in SNODE_N.
        rewrite tasks_wf in SNODE_N. ss. }

      econs 1; eauto.
      + eapply valid_task_id_ip. ss.
      + assert (forall m (M_UB: m < length (get_mcast_of n)),
                   exists (mip: ip_t),
                     (fun m mip =>
                        exists mid,
                          nth_error (get_mcast_of n) m = Some mid /\
                          mcast_id_ip mid mip)
                       m mip) as AUX.
        { i.
          hexploit (nth_error_Some2 _ (get_mcast_of n) m).
          { eauto. }
          i. des.

          rewrite NTH_EX.
          renames e1 NTH_EX into mid GET_MCAST_M.

          hexploit get_mcast_of_spec; eauto.
          { eapply nth_error_In; eauto. }
          i. des.

          esplits; eauto.
          r. esplits; eauto.
        }
        apply exists_list in AUX.
        destruct AUX as (mips & LEN_MIPS & MIPS_PROP). des.

        econs; ss.
        instantiate (1:= mips).
        apply Forall2_nth. intro m.
        destruct (nth_error mips m) eqn: MIPS_M.
        2: { rewrite nth_error_None2.
             2: {
               fold rnws_params_obj system_env_obj.
               rewrite <- LEN_MIPS.
               apply nth_error_None; eauto.
             }
             econs.
        }

        hexploit MIPS_PROP; eauto.
        intros (mid & GET_MCAST_N & MCAST_ID_IP).
        fold rnws_params_obj system_env_obj.
        rewrite GET_MCAST_N.
        econs; eauto.

      + econs; eauto.
        * unfold AANode.init_inbox.
          rewrite repeat_length. ss.
        * ss. unfold NW.init.
          unfold nw_msgs_to. ss.
          unfold Node.distr_msgs_to. ss.
        * unfold nw_msgs_to. ss.
          nia.

    - apply iForall_nth. i. ss.
      rewrite imap_nth_error_iff. ss.
      destruct (nth_error (as_snodes sys) n); ss.
      econs; ss.
      unfold AANode.init_inbox.
      rewrite repeat_length. ss.
    - rewrite AMW_STS.
      apply iForall_nth. i. ss.
      rewrite imap_nth_error_iff. ss.
      destruct (nth_error (as_snodes sys) n) eqn:SNODE_N; ss.
      econs; ss.
      + eapply valid_task_id_ip.
        r.
        unfold as_snodes in SNODE_N.
        apply nth_error_Some1' in SNODE_N.
        rewrite map_length in SNODE_N.
        rewrite map_length in SNODE_N.
        rewrite tasks_wf in SNODE_N. ss.
      + econs.
  Qed.

  Lemma ref_async_sync
        (tm_init: nat)
        (TIME_INIT_COND: period <= tm_init)
    : DSys.behav_sys (dsys_async sys tm_init) <1=
      DSys.behav_sys (dsys_sync sys tm_init).
  Proof.
    assert (SAFE_TGT: DSys.safe (dsys_async sys tm_init)).
    { apply AASys.safe. }

    apply fmsim_adequacy; eauto.
    econs. i.
    esplits.
    { econs. }

    inv INIT_TGT.

    assert (LEN_EQ: length (as_snodes sys) = num_tasks).
    { unfold as_snodes.
      do 2 rewrite map_length.
      rewrite tasks_wf. ss. }

    eapply async_sync_fmsim_states; eauto.
    - rewrite imap_length. ss.
    - ss. rewrite LEN_EQ. ss.
  Qed.

  Lemma period_positive: 0 < period.
  Proof.
    generalize period_cond. nia.
  Qed.

  Lemma ref_sync_exec
        (tm_init: nat)
        (TIME_INIT_COND: period <= tm_init)
    : DSys.behav_sys (dsys_sync sys tm_init) <1=
      DSys.behav_sys (dsys_exec sys tm_init).
  Proof.
    assert (SAFE_TGT: DSys.safe (dsys_sync sys tm_init)).
    { apply SyncSys.safe.
      econs.
      apply period_positive. }

    apply fmsim_adequacy; eauto.
    econs. i.
    esplits.
    { econs. }

    inv INIT_TGT.

    assert (LEN_EQ: length (as_snodes sys) = num_tasks).
    { unfold as_snodes.
      do 2 rewrite map_length.
      rewrite tasks_wf. ss. }

    eapply sync_exec_fmsim_states; eauto.
    eapply period_positive.
  Qed.

  Lemma ref_exec_sync
        (tm_init: nat)
        (TIME_INIT_COND: period <= tm_init)
    : DSys.behav_sys (dsys_exec sys tm_init) <1=
      DSys.behav_sys (dsys_sync sys tm_init).
  Proof.
    apply gmsim_adequacy; eauto.
    econs.
    { esplits. ss. }
    i.
    esplits.
    { econs. }

    inv INIT_TGT.

    assert (LEN_EQ: length (as_snodes sys) = num_tasks).
    { unfold as_snodes.
      do 2 rewrite map_length.
      rewrite tasks_wf. ss. }

    eapply exec_sync_gmsim_states; eauto.
    eapply period_positive.
  Qed.


  Theorem impl_spec_refinement1
        (tm_init: nat)
        (TIME_INIT_COND: period <= tm_init)
    : DSys.behav_sys (dsys_nc sys tm_init) <1=
      DSys.behav_sys (dsys_exec sys tm_init).
  Proof.
    i.
    apply ref_sync_exec; eauto.
    apply ref_async_sync; eauto.
    apply ref_amw_async; eauto.
    apply ref_ni_amw; eauto.
    apply ref_nc_ni; eauto.
  Qed.

  Theorem impl_spec_refinement
        (tm_init: nat)
        (TIME_INIT_COND: period <= tm_init)
    : DSys.behav_sys2 _ (dsys_nc sys tm_init) <1=
      DSys.behav_sys2 _ (dsys_exec sys tm_init).
  Proof.
    eapply DSys.behav1_refine_impl_behav2_refine.
    eapply impl_spec_refinement1. ss.
  Qed.

  Theorem exec_sync_models_equiv1
          tm_init
          (TIME_INIT_COND: period <= tm_init)
    : forall beh,
      DSys.behav_sys (dsys_exec sys tm_init) beh <->
      DSys.behav_sys (dsys_sync sys tm_init) beh.
  Proof.
    i. split.
    - apply ref_exec_sync. ss.
    - apply ref_sync_exec. ss.
  Qed.

  Theorem exec_sync_models_equiv
          tm_init
          (TIME_INIT_COND: period <= tm_init)
    : forall beh,
      DSys.behav_sys2 _ (dsys_exec sys tm_init) beh <->
      DSys.behav_sys2 _ (dsys_sync sys tm_init) beh.
  Proof.
    i. split.
    - eapply DSys.behav1_refine_impl_behav2_refine.
      apply ref_exec_sync. ss.
    - eapply DSys.behav1_refine_impl_behav2_refine.
      apply ref_sync_exec. ss.
  Qed.

End VERIF.
