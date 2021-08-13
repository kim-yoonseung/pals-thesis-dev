From ITree Require Import ITree.
From compcert Require Coqlib.
From compcert Require Import
     AST Memory Globalenvs Maps Values Linking
     Ctypes Clight Clightdefs.

Require Import ZArith String Bool List Lia.

Require Import sflib.
Require Import StdlibExt IntegersExt.
Require Import DiscreteTimeModel IPModel.

Require Import SysSem.
Require Import NWSysModel.
Require Import OSModel OSNodes.
Require Import RTSysEnv.
Require Import CProgEventSem.
Require Import SyncSysModel.
Require Import ProgSem.
Require Import LinkLemmas.

Require Import config_prm main_prm SystemProgs.
Require Import VerifProgBase.
Require Import MWLinkInversion.
Require Import PALSSystem.

Require Import ctrl.
Require Import AcStSystem.

Local Opaque Z.to_nat Z.of_nat PTree.combine.

Import ITreeNotations.
Import ListNotations.

Import ActiveStandby.

Set Nested Proofs Allowed.


Lemma mw_controller_link_check_ok
      dm1 dm2 (tid: Z)
      (DM1: dm1 = prog_defmap prog_mw)
      (DM2: dm2 = prog_defmap (ctrl.prog tid))
  : PTree_Properties.for_all
      dm1 (link_prog_check prog_mw (ctrl.prog tid)) = true.
Proof.
  subst dm1.
  eapply link_prog_check_lemma.
  { eapply prog_mw_linked. }
  i.
  simpl in IN_DEFS3.
  des; inv IN_DEFS3;
    (split; [by intuition | ]);
    (i; split; [by intuition | ]);
    first [ eapply link_prog_merge_exts_aux; eauto; fail
          | ss; clarify; fail ].
Qed.


Definition ctrl_gvar_ilist: list (ident * globvar Ctypes.type) :=
  [(_grant_msg, v_grant_msg);
  (_state, v_state)].

Definition ctrl_gfun_ilist: list (ident * Clight.fundef) :=
  [(_qrange_sanitize, Internal f_qrange_sanitize);
  (_adv_qidx, Internal f_adv_qidx);
  (_check_dev_id, Internal f_check_dev_id);
  (_copy_state_from_hb, Internal f_copy_state_from_hb);
  (_sync_istate, Internal f_sync_istate);
  (_try_add_queue, Internal f_try_add_queue);
  (_try_release, Internal f_try_release);
  (_apply_devmsg, Internal f_apply_devmsg);
  (_reduce_timeout, Internal f_reduce_timeout);
  (_update_queue, Internal f_update_queue);
  (_update_istate, Internal f_update_istate);
  (_update_owner, Internal f_update_owner);
  (_send_hb, Internal f_send_hb);
  (_job_controller, Internal f_job_controller);
  (_job, Internal f_job)].

Definition co_def_ctrl_state: composite_definition :=
  Composite __ctrl_state Struct ((_arr, (tarray tschar 8)) :: nil) noattr.


Program Definition co_ctrl_state: composite :=
  {| co_su := Struct ;
     co_members := [(_arr, tarray (Tint I8 Signed noattr) 8)] ;
     co_attr := noattr ;
     co_sizeof := 8 ;
     co_alignof := 1 ;
     co_rank := 1 ;
  |}.
Next Obligation.
  ss.
Qed.
Next Obligation.
  exists 0. ss.
Qed.
Next Obligation.
  solve_divide.
Qed.


Definition ctrl_cenv_ilist: list (ident * Ctypes.composite) :=
  [(__ctrl_state, co_ctrl_state)].

Definition ctrl_AST_prog (tid: Z)
  : AST.program Clight.fundef type :=
  let p1 := prog_mw in
  let p2 := ctrl.prog tid in
  let dm1 := prog_defmap p1 in
  let dm2 := prog_defmap p2 in
  {|
    AST.prog_defs := PTree.elements (PTree.combine link_prog_merge dm1 dm2);
    AST.prog_public := AST.prog_public p1 ++ AST.prog_public p2;
    AST.prog_main := AST.prog_main p1 |}.

Lemma ctrl_AST_prog_linked tid
  : link_prog prog_mw (ctrl.prog tid) = Some (ctrl_AST_prog tid).
Proof.
  unfold link_prog.
  erewrite mw_controller_link_check_ok; eauto.
Qed.

Definition prog_ctrl_types: list composite_definition :=
  prog_mw_types ++ [co_def_ctrl_state].

Definition prog_ctrl (tid: Z): Clight.program :=
  let p1 := prog_mw in
  let p2 := ctrl.prog tid in
  Clightdefs.mkprogram
    prog_ctrl_types
    (PTree.elements (PTree.combine link_prog_merge (prog_defmap p1) (prog_defmap p2)))
    (AST.prog_public p1 ++ AST.prog_public p2)
    (AST.prog_main p1)
    I
.

Lemma prog_ctrl_types_linked tid
  : link_composite_defs (prog_types prog_mw)
                        (prog_types (ctrl.prog tid)) =
    Some prog_ctrl_types.
Proof.
  ss.
Qed.

Lemma prog_ctrl_linked tid
  : link_program prog_mw (ctrl.prog tid) = Some (prog_ctrl tid).
Proof.
  apply link_program_eq.
  - apply ctrl_AST_prog_linked.
  - apply prog_ctrl_types_linked.
  - ss.
Qed.


Lemma prog_ctrl_defs_norep tid
  : Coqlib.list_norepet (prog_defs_names (prog_ctrl tid)).
Proof.
  unfold prog_defs_names.
  rewrite program_impl_prog_defs.

  erewrite linked_prog_defs.
  2: { eapply prog_ctrl_linked. }

  apply PTree.elements_keys_norepet.
Qed.

Lemma prog_ctrl_link_task_id tid
  : link (main_prm.v_TASK_ID) (v_TASK_ID tid) =
    Some (v_TASK_ID tid).
Proof. ss. Qed.

Lemma prog_ctrl_gvs_ok (tid: nat)
  : forall id gv,
    In (id, gv) (main_gvar_ilist tid ++ ctrl_gvar_ilist) ->
    In (id, Gvar gv) (prog_defs (prog_ctrl (Z.of_nat tid))).
Proof.
  intros id gv IN_APP.
  erewrite linked_prog_defs by apply prog_ctrl_linked.
  apply PTree.elements_correct.
  rewrite PTree.gcombine by ss.

  apply in_app_or in IN_APP. des.
  - (* in_main_gvar *)
    simpl in IN_APP.
    unfold link_prog_merge.
    des; inv IN_APP; ss.
  - (* in_ctrl_gvar *)
    simpl in IN_APP.
    des; ss; clarify.
Qed.

Lemma prog_ctrl_gfs_ok tid
  : forall id gf,
    In (id, gf) (main_gfun_ilist ++ ctrl_gfun_ilist) ->
    In (id, Gfun gf) (prog_defs (prog_ctrl tid)).
Proof.
  intros id gf IN_APP.
  erewrite linked_prog_defs by apply prog_ctrl_linked.
  apply PTree.elements_correct.
  rewrite PTree.gcombine by ss.

  apply in_app_or in IN_APP. des.
  - (* in_main_gvar *)
    simpl in IN_APP.
    des; inv IN_APP; intuition.
  - (* in_ctrl_gvar *)
    simpl in IN_APP.
    des; ss; clarify.
Qed.

Lemma prog_ctrl_cenvs_ok tid
  : forall id co,
    In (id, co) (main_cenv_ilist ++ ctrl_cenv_ilist) ->
    (prog_comp_env (prog_ctrl tid)) ! id = Some co.
Proof.
  intros id gf IN_APP.
  eapply co_in_either_composites.
  { apply prog_ctrl_linked. }

  (* left. *)

  apply in_app_or in IN_APP. des.
  - (* in_main_cenv *)
    left.
    apply MainIListSound.check_cenv.
    ss.
  - right.
    simpl in IN_APP.
    des; clarify.
    s. f_equal.
    eapply composite_eq; eauto.
Qed.


Local Transparent Linker_def.

Lemma prog_ctrl_init_mem_ok tid
  : Genv.init_mem (prog_ctrl tid) <> None.
Proof.
  cut (exists m, Genv.init_mem (prog_ctrl tid) = Some m).
  { i. des. congruence. }
  apply Genv.init_mem_exists.
  intros id v IN.

  rewrite program_impl_prog_defs in IN.
  erewrite linked_prog_defs in IN by apply prog_ctrl_linked.
  apply PTree.elements_complete in IN.
  rewrite PTree.gcombine in IN by ss.
  destruct ((prog_defmap (prog tid)) ! id) as [gd|] eqn: GD_CON.
  { apply in_prog_defmap in GD_CON.
    simpl in GD_CON.
    destruct gd as [gf | gv].
    { exfalso.
      clear - IN.
      destruct ((prog_defmap prog_mw) ! id); ss.
      destruct g; ss. ss.
      ss. desf.
    }

    des; inv GD_CON.
    - rewrite prog_mw_defmap_task_id in IN.
      ss. rewrite prog_ctrl_link_task_id in IN. clarify.
      split.
      + unfold gvar_init. ss.
        split; ss. solve_divide.
      + i. ss. des; ss.
    - assert (MW_NONE: (prog_defmap prog_mw) ! _grant_msg = None).
      { clear. ss. }
      rewrite MW_NONE in IN.
      clear MW_NONE.
      ss. clarify.
      split; ss.
      + splits; try solve_divide; ss.
      + i. des; ss.
    - assert (MW_NONE: (prog_defmap prog_mw) ! _state = None).
      { clear. ss. }
      rewrite MW_NONE in IN.
      clear MW_NONE.
      ss. clarify.
      split; ss.
      + splits; try solve_divide; ss.
      + i. des; ss.
  }
  { clear GD_CON.
    unfold link_prog_merge in IN.
    destruct ((prog_defmap prog_mw) ! id) as [gd|] eqn: DEF_MW.
    2: { ss. }
    clarify.

    apply prog_mw_gvar_init in DEF_MW. des.
    splits; ss.
    i. exfalso.
    eapply DEF_MW0; eauto.
  }
Qed.

Local Opaque Linker_def.

Definition genv_props_ctrl (tid: nat)
  : genv_props (Clight.globalenv (prog_ctrl (Z.of_nat tid)))
               (main_gvar_ilist tid ++ ctrl_gvar_ilist)
               (main_gfun_ilist ++ ctrl_gfun_ilist)
               (main_cenv_ilist ++ ctrl_cenv_ilist).
Proof.
  apply prog_genv_props.
  - apply prog_ctrl_defs_norep.
  - apply prog_ctrl_gvs_ok.
  - apply prog_ctrl_gfs_ok.
  - apply prog_ctrl_cenvs_ok.
Qed.

Definition genv_props_main (tid: nat)
  : genv_props (Clight.globalenv (prog_ctrl (Z.of_nat tid)))
               (main_gvar_ilist tid)
               (main_gfun_ilist)
               (main_cenv_ilist).
Proof.
  eapply genv_props_incl.
  - apply genv_props_ctrl.
  - apply incl_appl. ss.
  - apply incl_appl. ss.
  - apply incl_appl. ss.
Qed.
