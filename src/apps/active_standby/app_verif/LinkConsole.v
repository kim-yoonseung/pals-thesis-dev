From ITree Require Import ITree.
From compcert Require Coqlib.
From compcert Require Import AST Memory Globalenvs Maps Values Linking
     Ctypes  Clight Clightdefs.

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

Require Import console.
Require Import AcStSystem.


Local Opaque Z.to_nat Z.of_nat PTree.combine.

Import ITreeNotations.
Import ListNotations.

Import ActiveStandby.

Set Nested Proofs Allowed.


Lemma mw_console_link_check_ok
      dm1 dm2
      (DM1: dm1 = prog_defmap prog_mw)
      (DM2: dm2 = prog_defmap console.prog)
  : PTree_Properties.for_all
      dm1 (link_prog_check prog_mw console.prog) = true.
Proof.
  subst dm1.
  eapply link_prog_check_lemma.
  { eapply prog_mw_linked. }
  i.
  simpl in IN_DEFS3.
  des; inv IN_DEFS3;
    (split; [by intuition | ]);
    (i; split; [by intuition | ]);
    try (eapply link_prog_merge_exts_aux; eauto; fail).
  - ss. clarify.
  - ss.
  - ss.
  - ss. clarify.
  - ss.
  - ss.
  - ss. clarify.
Qed.


Definition con_gvar_ilist: list (ident * globvar Ctypes.type) :=
  [(_toggle_msg, v_toggle_msg)].

Definition con_gfun_ilist: list (ident * Clight.fundef) :=
  [(_job_console, Internal f_job_console); (_job, Internal f_job);
  (_get_user_input, External get_user_input_ef Tnil tint cc_default);
  (_write_log, External write_log_ef (Tcons tint Tnil) tvoid cc_default)].

Definition con_cenv_ilist: list (ident * Ctypes.composite) := [].


Definition con_AST_prog: AST.program Clight.fundef type :=
  let p1 := prog_mw in
  let p2 := console.prog in
  let dm1 := prog_defmap p1 in
  let dm2 := prog_defmap p2 in
  {|
    AST.prog_defs := PTree.elements (PTree.combine link_prog_merge dm1 dm2);
    AST.prog_public := AST.prog_public p1 ++ AST.prog_public p2;
    AST.prog_main := AST.prog_main p1 |}.

Lemma con_AST_prog_linked
  : link_prog prog_mw console.prog = Some con_AST_prog.
Proof.
  unfold link_prog.
  erewrite mw_console_link_check_ok; eauto.
Qed.

Definition prog_con: Clight.program :=
  let p1 := prog_mw in
  let p2 := console.prog in
  Clightdefs.mkprogram
    prog_mw_types
    (PTree.elements (PTree.combine link_prog_merge (prog_defmap p1) (prog_defmap p2)))
    (AST.prog_public p1 ++ AST.prog_public p2)
    (AST.prog_main p1)
    I
.

Lemma prog_con_types_linked
  : link_composite_defs (prog_types prog_mw)
                        (prog_types console.prog) =
    Some (prog_types prog_mw).
Proof.
  ss.
Qed.

Lemma prog_con_linked
  : link_program prog_mw console.prog = Some prog_con.
Proof.
  apply link_program_eq.
  - apply con_AST_prog_linked.
  - apply prog_con_types_linked.
  - ss.
Qed.


Lemma prog_con_defs_norep
  : Coqlib.list_norepet (prog_defs_names prog_con).
Proof.
  unfold prog_defs_names.
  rewrite program_impl_prog_defs.

  erewrite linked_prog_defs.
  2: { eapply prog_con_linked. }

  apply PTree.elements_keys_norepet.
Qed.

Lemma prog_con_link_task_id
  : link (main_prm.v_TASK_ID) (v_TASK_ID) = Some (v_TASK_ID).
Proof. ss. Qed.

Lemma prog_con_gvs_ok
  : forall id gv,
    In (id, gv) (main_gvar_ilist 0 ++ con_gvar_ilist) ->
    In (id, Gvar gv) (prog_defs prog_con).
Proof.
  intros id gv IN_APP.
  erewrite linked_prog_defs by apply prog_con_linked.
  apply PTree.elements_correct.
  rewrite PTree.gcombine by ss.

  apply in_app_or in IN_APP. des.
  - (* in_main_gvar *)
    simpl in IN_APP.
    unfold link_prog_merge.
    des; inv IN_APP; ss.
  - (* in_con_gvar *)
    simpl in IN_APP.
    des; ss.
    clarify.
Qed.

Lemma prog_con_gfs_ok
  : forall id gf,
    In (id, gf) (main_gfun_ilist ++ con_gfun_ilist) ->
    In (id, Gfun gf) (prog_defs prog_con).
Proof.
  intros id gf IN_APP.
  erewrite linked_prog_defs by apply prog_con_linked.
  apply PTree.elements_correct.
  rewrite PTree.gcombine by ss.

  apply in_app_or in IN_APP. des.
  - (* in_main_gvar *)
    simpl in IN_APP.
    des; inv IN_APP; intuition.
  - (* in_con_gvar *)
    simpl in IN_APP.
    des; ss; clarify.
Qed.

Lemma prog_con_cenvs_ok
  : forall id co,
    In (id, co) (main_cenv_ilist ++ con_cenv_ilist) ->
    (prog_comp_env prog_con) ! id = Some co.
Proof.
  intros id gf IN_APP.
  eapply co_in_either_composites.
  { apply prog_con_linked. }

  left.
  apply MainIListSound.check_cenv.
  apply in_app_or in IN_APP. des.
  - (* in_main_cenv *)
    ss.
  - ss.
Qed.


Local Transparent Linker_def.

Lemma prog_con_init_mem_ok
  : Genv.init_mem prog_con <> None.
Proof.
  cut (exists m, Genv.init_mem prog_con = Some m).
  { i. des. congruence. }
  apply Genv.init_mem_exists.
  intros id v IN.

  rewrite program_impl_prog_defs in IN.
  erewrite linked_prog_defs in IN by apply prog_con_linked.
  apply PTree.elements_complete in IN.
  rewrite PTree.gcombine in IN by ss.
  destruct ((prog_defmap prog) ! id) as [gd|] eqn: GD_CON.
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
      ss. rewrite prog_con_link_task_id in IN. clarify.
      split.
      + unfold gvar_init. ss.
        split; ss. solve_divide.
      + i. ss. des; ss.
    - assert (MW_NONE: (prog_defmap prog_mw) ! _toggle_msg = None).
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

    (* apply in_prog_defmap in DEF_MW. *)

    apply prog_mw_gvar_init in DEF_MW. des.
    splits; ss.
    i. exfalso.
    eapply DEF_MW0; eauto.
  }
Qed.

Local Opaque Linker_def.


Definition genv_props_con
  : genv_props (Clight.globalenv prog_con)
               (main_gvar_ilist 0 ++ con_gvar_ilist)
               (main_gfun_ilist ++ con_gfun_ilist)
               (main_cenv_ilist ++ con_cenv_ilist).
Proof.
  apply prog_genv_props.
  - apply prog_con_defs_norep.
  - apply prog_con_gvs_ok.
  - apply prog_con_gfs_ok.
  - apply prog_con_cenvs_ok.
Qed.
