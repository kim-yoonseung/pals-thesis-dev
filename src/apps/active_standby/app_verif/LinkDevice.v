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

Require Import dev.
Require Import AcStSystem.

Local Opaque Z.to_nat Z.of_nat PTree.combine.

Import ITreeNotations.
Import ListNotations.

Import ActiveStandby.

Set Nested Proofs Allowed.


Lemma mw_device_link_check_ok
      dm1 dm2 (tid: Z)
      (DM1: dm1 = prog_defmap prog_mw)
      (DM2: dm2 = prog_defmap (dev.prog tid))
  : PTree_Properties.for_all
      dm1 (link_prog_check prog_mw (dev.prog tid)) = true.
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


Definition dev_gvar_ilist: list (ident * globvar Ctypes.type) :=
  [(_acq_msg, v_acq_msg); (_rel_msg, v_rel_msg);
  (_state, v_state)].

Definition dev_gfun_ilist: list (ident * Clight.fundef) :=
  [(_sync_dev_state, Internal f_sync_dev_state);
  (_get_new_demand, Internal f_get_new_demand);
  (_update_demand, Internal f_update_demand);
  (_run_device, Internal f_run_device);
  (_job_device, Internal f_job_device);
  (_job, Internal f_job);
  (_check_demand,
   External check_demand_ef Tnil tint cc_default);
  (_use_resource,
   External use_resource_ef Tnil tvoid cc_default);
  (_write_log,
   External write_log_ef (Tcons tint Tnil) tvoid cc_default)].

Definition co_def_dev_state: composite_definition :=
  Composite __dev_state Struct
            ((_is_owner, tschar) :: (_demand, tschar) :: nil)
            noattr.

Program Definition co_dev_state: composite :=
  {| co_su := Struct ;
     co_members := [(_is_owner, tschar);
                   (_demand, tschar)] ;
     co_attr := noattr ;
     co_sizeof := 2 ;
     co_alignof := 1 ;
     co_rank := 0 ;
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


Definition dev_cenv_ilist: list (ident * Ctypes.composite) :=
  [(__dev_state, co_dev_state)].

Definition dev_AST_prog (tid: Z)
  : AST.program Clight.fundef type :=
  let p1 := prog_mw in
  let p2 := dev.prog tid in
  let dm1 := prog_defmap p1 in
  let dm2 := prog_defmap p2 in
  {|
    AST.prog_defs := PTree.elements (PTree.combine link_prog_merge dm1 dm2);
    AST.prog_public := AST.prog_public p1 ++ AST.prog_public p2;
    AST.prog_main := AST.prog_main p1 |}.

Lemma dev_AST_prog_linked tid
  : link_prog prog_mw (dev.prog tid) = Some (dev_AST_prog tid).
Proof.
  unfold link_prog.
  erewrite mw_device_link_check_ok; eauto.
Qed.

Definition prog_dev_types: list composite_definition :=
  prog_mw_types ++ [co_def_dev_state].

Definition prog_dev (tid: Z): Clight.program :=
  let p1 := prog_mw in
  let p2 := dev.prog tid in
  Clightdefs.mkprogram
    prog_dev_types
    (PTree.elements (PTree.combine link_prog_merge (prog_defmap p1) (prog_defmap p2)))
    (AST.prog_public p1 ++ AST.prog_public p2)
    (AST.prog_main p1)
    I
.

Lemma prog_dev_types_linked tid
  : link_composite_defs (prog_types prog_mw)
                        (prog_types (dev.prog tid)) =
    Some prog_dev_types.
Proof.
  ss.
Qed.

Lemma prog_dev_linked tid
  : link_program prog_mw (dev.prog tid) = Some (prog_dev tid).
Proof.
  apply link_program_eq.
  - apply dev_AST_prog_linked.
  - apply prog_dev_types_linked.
  - ss.
Qed.


Lemma prog_dev_defs_norep tid
  : Coqlib.list_norepet (prog_defs_names (prog_dev tid)).
Proof.
  unfold prog_defs_names.
  rewrite program_impl_prog_defs.

  erewrite linked_prog_defs.
  2: { eapply prog_dev_linked. }

  apply PTree.elements_keys_norepet.
Qed.

Lemma prog_dev_link_task_id tid
  : link (main_prm.v_TASK_ID) (v_TASK_ID tid) =
    Some (v_TASK_ID tid).
Proof. ss. Qed.

Lemma prog_dev_gvs_ok (tid: nat)
  : forall id gv,
    In (id, gv) (main_gvar_ilist tid ++ dev_gvar_ilist) ->
    In (id, Gvar gv) (prog_defs (prog_dev (Z.of_nat tid))).
Proof.
  intros id gv IN_APP.
  erewrite linked_prog_defs by apply prog_dev_linked.
  apply PTree.elements_correct.
  rewrite PTree.gcombine by ss.

  apply in_app_or in IN_APP. des.
  - (* in_main_gvar *)
    simpl in IN_APP.
    unfold link_prog_merge.
    des; inv IN_APP; ss.
  - (* in_dev_gvar *)
    simpl in IN_APP.
    des; ss; clarify.
Qed.

Lemma prog_dev_gfs_ok tid
  : forall id gf,
    In (id, gf) (main_gfun_ilist ++ dev_gfun_ilist) ->
    In (id, Gfun gf) (prog_defs (prog_dev tid)).
Proof.
  intros id gf IN_APP.
  erewrite linked_prog_defs by apply prog_dev_linked.
  apply PTree.elements_correct.
  rewrite PTree.gcombine by ss.

  apply in_app_or in IN_APP. des.
  - (* in_main_gvar *)
    simpl in IN_APP.
    des; inv IN_APP; intuition.
  - (* in_dev_gvar *)
    simpl in IN_APP.
    des; ss; clarify.
Qed.

Lemma prog_dev_cenvs_ok tid
  : forall id co,
    In (id, co) (main_cenv_ilist ++ dev_cenv_ilist) ->
    (prog_comp_env (prog_dev tid)) ! id = Some co.
Proof.
  intros id gf IN_APP.
  eapply co_in_either_composites.
  { apply prog_dev_linked. }

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

Lemma prog_dev_init_mem_ok tid
  : Genv.init_mem (prog_dev tid) <> None.
Proof.
  cut (exists m, Genv.init_mem (prog_dev tid) = Some m).
  { i. des. congruence. }
  apply Genv.init_mem_exists.
  intros id v IN.

  rewrite program_impl_prog_defs in IN.
  erewrite linked_prog_defs in IN by apply prog_dev_linked.
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
      ss. rewrite prog_dev_link_task_id in IN. clarify.
      split.
      + unfold gvar_init. ss.
        split; ss. solve_divide.
      + i. ss. des; ss.
    - assert (MW_NONE: (prog_defmap prog_mw) ! _acq_msg = None).
      { clear. ss. }
      rewrite MW_NONE in IN.
      clear MW_NONE.
      ss. clarify.
      split; ss.
      + splits; try solve_divide; ss.
      + i. des; ss.
    - assert (MW_NONE: (prog_defmap prog_mw) ! _rel_msg = None).
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

Definition genv_props_dev (tid: nat)
  : genv_props (Clight.globalenv (prog_dev (Z.of_nat tid)))
               (main_gvar_ilist tid ++ dev_gvar_ilist)
               (main_gfun_ilist ++ dev_gfun_ilist)
               (main_cenv_ilist ++ dev_cenv_ilist).
Proof.
  apply prog_genv_props.
  - apply prog_dev_defs_norep.
  - apply prog_dev_gvs_ok.
  - apply prog_dev_gfs_ok.
  - apply prog_dev_cenvs_ok.
Qed.

Definition genv_props_main (tid: nat)
  : genv_props (Clight.globalenv (prog_dev (Z.of_nat tid)))
               (main_gvar_ilist tid)
               (main_gfun_ilist)
               (main_cenv_ilist).
Proof.
  eapply genv_props_incl.
  - apply genv_props_dev.
  - apply incl_appl. ss.
  - apply incl_appl. ss.
  - apply incl_appl. ss.
Qed.
