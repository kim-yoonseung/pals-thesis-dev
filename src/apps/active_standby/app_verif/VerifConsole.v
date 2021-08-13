From ITree Require Import ITree.
From compcert Require Import Maps AST Values Memory Globalenvs Ctypes.
From compcert Require Coqlib Clight Clightdefs.
From Paco Require Import paco.

Require Import Arith ZArith Bool.
Require Import String List Lia.

Require Import sflib.
Require Import Axioms StdlibExt IntegersExt ITreeTac.

Require Import SysSem.
Require Import IPModel DiscreteTimeModel IntByteModel.
Require Import OSModel OSNodes.
Require Import ProgSem CProgEventSem.
Require Import ProgSim CProgSimLemmas.
Require Import RTSysEnv MWITree.

(* Require Import SystemParams. *)
(* Require Import SystemDefs ITreeSpec. *)
(* Require Import SystemEventSem. *)
Require Import config_prm main_prm SystemProgs.
Require Import console.
Require Import VerifProgBase.
Require Import VerifMainUtil.
Require Import PALSSystem.

Require Import AcStSystem.
Require Import LinkConsole.
Require Import SpecConsole.


Import Clight Clightdefs.
Import ITreeNotations.
(* Import ActiveStandby. *)

Set Nested Proofs Allowed.
(* Arguments app : simpl nomatch. *)
Local Transparent Archi.ptr64.
Local Opaque Z.of_nat Z.to_nat.

Opaque globalenv.


Section VERIF_CONSOLE_APP.
  (* Notation progE := (osE +' tlimE +' sysE). *)

  (* Let astate_t: Type := unit. *)
  Definition inv_con (ge: genv) (ast: unit) (m: mem): Prop :=
    forall b_tgl
      (FSYMB_TGL : Genv.find_symbol (globalenv prog_con) _toggle_msg = Some b_tgl),
      Mem.loadbytes m b_tgl 0 8 =
      Some
        [Byte (Byte.repr 1);
        Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero;
        Byte Byte.zero; Byte Byte.zero; Byte Byte.zero].

  Definition idx_con : nat := 50.

  (* Definition cprog_sig : { p : Clight.program | p =  *)
  Lemma cprog_opaque
    : exists cprog, cprog = prog_con.
  Proof.
    esplits; eauto.
  Qed.

  Let ge := Clight.globalenv prog_con.

  Let con_gvar_ids := map fst con_gvar_ilist.
  Let con_gfun_ids := map fst con_gfun_ilist.
  Let con_cenv_ids := map fst con_cenv_ilist.

  Lemma inv_con_dep_app_blocks
    : forall (ast : unit) (m m' : mem)
        (INV: inv_con ge ast m)
        (MEM_UNCH: Mem.unchanged_on (blocks_of ge con_gvar_ids) m m'),
      inv_con ge ast m'.
  Proof.
    unfold inv_con. i.
    eapply Mem.loadbytes_unchanged_on; eauto.
    unfold blocks_of.
    intros I RANGE_I.
    exists _toggle_msg.
    split.
    - clear. sIn.
    - eapply FSYMB_TGL.
  Qed.

  Lemma inv_con_init : forall m_i : mem,
      Genv.init_mem prog_con = Some m_i ->
      inv_con ge tt m_i.
  Proof.
    intros m_i INIT_MEM. r.
    intros b_tgl FSYMB_TGL.

    assert (CPROG_EQ: exists cprog, prog_con = cprog).
    { esplits; ss. }
    des. guardH CPROG_EQ.
    rewrite CPROG_EQ in *.

    assert (DEFMAP: (prog_defmap cprog) ! _toggle_msg = Some (Gvar v_toggle_msg)).
    { rewrite <- CPROG_EQ.
      change (prog_defmap prog_con) with
          (PTree.combine Linking.link_prog_merge
                         (prog_defmap prog_mw) (prog_defmap console.prog)).
      rewrite PTree.gcombine by ss.
      replace ((prog_defmap prog_mw) ! _toggle_msg) with
          (@None (globdef fundef type)).
      2: {
        change (prog_defmap prog_mw) with
            (PTree.combine Linking.link_prog_merge
                           (prog_defmap config_prog)
                           (prog_defmap main_prog)).
        rewrite PTree.gcombine by ss.
        ss.
      }
      ss.
    }

    apply Genv.find_def_symbol in DEFMAP.
    destruct DEFMAP as (b_tgl' & FSYMB_TGL' & FDEF_TGL).

    replace (Genv.globalenv cprog) with
        (genv_genv (globalenv cprog)) in FSYMB_TGL' by ss.
    fold fundef in FSYMB_TGL'.
    rewrite FSYMB_TGL in FSYMB_TGL'.
    symmetry in FSYMB_TGL'. clarify.

    eapply Genv.init_mem_characterization_gen in INIT_MEM.
    r in INIT_MEM.
    exploit INIT_MEM; eauto. s.
    intros (RANGE_PERM & PERM & LOAD & LOADBYTES).

    rewrite LOADBYTES by ss.
    ss.
  Qed.


  Local Opaque idx_psend.

  Section SIM_JOB.
    Let prog := prog_of_clight prog_con.
    Let tid := 0.

    Lemma sim_job_func_con
      : forall (r : nat -> itree progE unit -> state -> Prop)
          (b_mst : block)
          (txs idx' : nat) (ast : unit)
          (ki : list bool * unit -> itree progE unit)
          (m : mem) (kp : cont) (sytm : nat) (cflg : bool)
          (ofsc ofsn : Z) (inbc inbn : list (bytes?))
          (* (sh : list bool) *) (mcont : bytes)
          (CALL_CONT: is_call_cont kp)
          (RANGE_SYTM: IntRange.uint64 sytm)
          (RANGE_NXT_SYTM: IntRange.uint64 (sytm + period))
          (RANGE_TXS: IntRange.sint txs)
          (INV_APP: inv_con ge ast m)
          (FSYMB_MST: Genv.find_symbol ge _mstore = Some b_mst)
          (MEM_CONSTS: mem_consts ge m tid)
          (MEM_SBUF: mem_sbuf ge m (sytm + RTSysEnv.period) tid mcont)
          (MEM_MSTORE: mem_mstore ge m cflg ofsc ofsn inbc inbn)
          (MEM_SH: mem_sh ge m (repeat false num_tasks))
          (MEM_TXS: mem_txs ge m txs)
          (SIM_RET: forall (sh' : list bool) (ast' : unit)
                      (m' : mem) (mcont' : bytes)
                      (MEM_UNCH: Mem.unchanged_on (blocks_of ge app_unch_gvar_ids) m m')
                      (MEM_SH: mem_sh ge m' sh')
                      (MEM_SBUF: mem_sbuf ge m' (sytm + RTSysEnv.period) tid mcont')
                      (INV_APP: inv_con ge ast' m'),
              paco3 (_sim_itree (prog_of_clight prog_con)) r
                    idx' (ki (sh', ast')) (Returnstate Vundef kp m'))
      ,
        paco3 (_sim_itree (prog_of_clight prog_con)) r (idx' + idx_con)
              (` ret : list bool * unit <-
                       MWITree.interp_send tid con_mod txs sytm
                                           (repeat false num_tasks) ast inbc ;;
                       ki ret)
              (Callstate (Internal f_job)
                         [Vlong (IntNat.of_nat64 sytm);
                         Vptr b_mst (Ptrofs.repr ofsc)] kp m)
    .
    Proof.
      pose proof genv_props_con as GENV_PROPS.
      hexploit genv_props_incl.
      { eauto. }
      { apply incl_appl. apply incl_refl. }
      { apply incl_appl. apply incl_refl. }
      { apply incl_appl. apply incl_refl. }
      intros GENV_PROPS_MAIN. guardH GENV_PROPS_MAIN.

      pose proof cprog_opaque as CPROG_EQ. des.
      guardH CPROG_EQ.
      rewrite <- CPROG_EQ in *.
      pose (ge' := Clight.globalenv cprog).
      replace ge with ge' in *.
      2: { subst ge' ge. rewrite CPROG_EQ. ss. }

      i.
      start_func.
      { econs. }

      unfold idx_con.
      (* myguardH FSYMB_MST. *)

      fw. fw.
      { hexploit (in_gfun_ilist _job_console); [sIn|]. i. des.
        (* myguardH FDEF_SYMB. *)
        hexploit (in_gvar_ids _TASK_ID); [sIn|].
        intros (b_tid & FSYMB_TID).
        (* myguardH FSYMB_TID. *)

        econs; ss.
        - eval_comput.
          rewrite FDEF_SYMB. ss.
          (* myg_rewrite FDEF_SYMB. ss. *)
        - eval_comput.
          rewrite FSYMB_TID.
          erewrite mem_consts_task_id; cycle 1.
          { eauto. }
          { apply FSYMB_TID. }
          unfold IntNat.of_nat.
          rewrite sign_ext_byte_range.
          2: { subst tid. range_stac. }
          repr_tac.
          reflexivity.
        - eauto.
        - ss.
      }

      clear STEP_ENTRY.
      renames le LENV_EQUIV into le_caller LENV_EQUIV_CALLER.

      start_func.
      { econs. }

      fw. fw. fw. fw.
      { hexploit (in_gfun_ilist _get_user_input); [sIn|].
        i. des.
        (* myguardH FDEF_SYMB. *)

        econs; ss.
        - eval_comput.
          rewrite FDEF_SYMB. ss.
        - eval_comput. eauto.
        - eauto.
        - ss.
      }
      unfold app in LENV_EQUIV.

      pfold. econs 3; ss.
      { econs; eauto.
        - econs 2; eauto.
          { i. intro OS_CALL.
            inv OS_CALL; existT_elim; ss. }
          (* { intro TLIM_EF. ss. } *)
          econs 1; ss.
        - ss.
      }
      (* { rr. econs. } *)
      { unfold MWITree.interp_send. s.
        unfold con_job.
        erewrite (MWITree.unfold_interp_vis_sys 0 con_mod).
        2: { simpl_itree_goal. ss. }
        simpl_itree_goal.
        econs 1.
      }
      { ss. }

      intros reti pst_r (* POSTCOND *) AFT_EVT.
      (* clear POSTCOND. *)
      inv AFT_EVT. ss.

      inv CPROG_AFTER_EVENT; ss.

      symmetry in EVENT. inv EVENT.
      existT_elim. unf_resum. clarify.
      inv MATCH_RETV.
      (* 2: { exfalso. eapply unit_int_diff; eauto. } *)
      existT_elim. clarify.
      (* inv SYS_ESTEP. existT_elim. clarify. *)
      rename m' into m.

      remember (negb (Int.eq Int.zero reti)) as retb eqn:IS_NZ.
      symmetry in IS_NZ.

      exists 10. left.
      fw. upd_lenv.
      fw. fw.
      { econs. eval_comput. ss. }
      upd_lenv.
      fw.

      destruct retb.
      - (* true *)
        apply negb_true_iff in IS_NZ.
        (* apply Int.same_if_eq in IS_ONE. *)
        (* subst reti. *)

        (* unfold Int.one in LENV_EQUIV. *)
        (* rewrite sign_ext_byte_range in LENV_EQUIV. *)
        (* 2: { range_stac. } *)
        fw_tau (idx_psend + 20).
        { simpl_itree_goal. ss. }
        fw.
        { econs.
          - eval_comput.
            rewrite Int.eq_sym. fold Int.zero.
            rewrite IS_NZ. s. ss.
          - s. unfold Cop.bool_val. s.
            rewrite Int.eq_false by ss.
            ss.
        }
        s.

        hexploit (in_gvar_ids _toggle_msg); [sIn|].
        intros [b_tgl FSYMB_TGL].
        (* myguardH FSYMB_TGL. *)

        fw.
        { hexploit (in_gfun_ilist _pals_send); [sIn|].
          i. des.
          (* myguardH FDEF_SYMB. *)

          econs; ss.
          - eval_comput. rewrite FDEF_SYMB. cbn.
            reflexivity.
          - eval_comput.
            rewrite FSYMB_TGL. cbn.
            unfold Cop.sem_cast. simpl. ss.
          - eauto.
          - ss.
        }
        rewrite sign_ext_byte_range by range_stac.

        erewrite (MWITree.unfold_interp_vis_send 0 con_mod).
        2: { simpl_itree_goal. ss. }
        simpl_itree_goal. ss.

        hexploit (in_gvar_ids _send_buf); [sIn|].
        intros [b_sbuf FSYMB_SBUF].
        hexploit (in_gvar_ids _send_hist); [sIn|].
        intros [b_sh FSYMB_SH].

        (* myguardH FSYMB_SBUF. *)

        red_idx (idx_psend + 10).
        replace (Int.repr 6) with (IntNat.of_nat 6) by ss.
        replace (f_pals_send (Z.of_nat 1) (Z.of_nat 16) (Z.of_nat 8)) with
            (f_pals_send (Z.of_nat msg_size_k) (Z.of_nat max_num_tasks)
                         (Z.of_nat max_num_mcasts)) by ss.

        eapply sim_pals_send; eauto; ss.
        { unfold num_tasks. ss. nia. }
        (* { apply GENV_PROPS_MAIN. } *)
        { eapply Genv.global_addresses_distinct;
            try eassumption; ss. }
        { eapply Genv.global_addresses_distinct;
            try eassumption; ss. }
        { r in INV_APP.
          apply INV_APP.
          rewrite <- CPROG_EQ. ss. }

        clear MEM_SBUF MEM_CONSTS MEM_SH MEM_TXS. i.
        simpl_itree_goal.

        fw_tau (idx' + 10). fw. fw.
        { step_fptr_tac. }

        pfold. econs 3.
        { s. econs; eauto.
          - s.
            econs 2; eauto.
            { i. intro OS_CALL.
              inv OS_CALL; existT_elim; ss. }
            (* { intro TLIM_EF. ss. } *)
            econs 2; ss.
          - ss.
        }
        { econs 1. }
        { erewrite (MWITree.unfold_interp_vis_sys 0 con_mod).
          2: { ss. }
          simpl_itree_goal. ss. }

        intros []. i.
        inv RET. inv CPROG_AFTER_EVENT; ss.
        inv EVENT. existT_elim.
        unf_resum. subst.
        inv MATCH_RETV.
        (* { exfalso. eapply unit_int_diff; eauto. } *)
        (* inv SYS_ESTEP. existT_elim. subst. *)
        rename m'0 into m'.

        exists (idx' + 5).
        left.
        fw. fw. fw.
        simpl_itree_goal.
        fw_tau idx'.
        erewrite (MWITree.unfold_interp_ret _ con_mod) by ss.
        simpl_itree_goal.

        eapply SIM_RET.
        + eapply Mem.unchanged_on_implies; eauto.
          unfold blocks_of. ii. des.
          match goal with
          | H: Genv.find_symbol _ _ = Some _ |- _ => revert H
          end.
          eapply global_addresses_distinct'; eauto.
          ss. clear GENV_PROPS. des; clarify.
        + ss.
        + eapply MEM_SBUF.
        + unfold inv_con in *.
          rewrite <- CPROG_EQ.
          i. clarify.
          rename FSYMB_TGL0 into FSYMB_TGL.

          eapply Mem.loadbytes_unchanged_on.
          { apply MEM_UNCH. }
          { unfold blocks_of.
            ii. des.
            revert FSYMB_TGL.
            eapply global_addresses_distinct'; eauto.
            ss. des; clarify. }
          apply INV_APP.
          rewrite <- CPROG_EQ. ss.

      - (* false *)
        simpl_itree_goal.
        fw_tau (idx' + 10).
        fw.
        { econs.
          - eval_comput.
            rewrite Int.eq_sym. fold Int.zero.
            rewrite IS_NZ. ss.
          - unfold Cop.bool_val. s.
            rewrite Int.eq_true by ss. s.
            reflexivity.
        }
        s.

        fw. fw.
        { step_fptr_tac. }
        simpl_itree_interp.

        pfold. econs 3.
        { s. econs; eauto.
          - s.
            econs 2; eauto; ss.
            { intros ? ? OSE.
              inv OSE; ss. }
            econs 2. ss.
          - ss. }
        { econs 1. }
        { erewrite (MWITree.unfold_interp_vis_sys 0 con_mod).
          2: { ss. }
          simpl_itree_goal. ss. }

        intros []. i.
        inv RET. inv CPROG_AFTER_EVENT; ss.
        inv EVENT. existT_elim.
        unf_resum. subst.
        inv MATCH_RETV.
        (* inv SYS_ESTEP. existT_elim. subst. *)
        rename m' into m.

        exists (idx' + 5).
        left.
        fw. fw. fw.
        simpl_itree_goal.
        fw_tau idx'.
        erewrite (MWITree.unfold_interp_ret _ con_mod) by ss.
        simpl_itree_goal.

        eapply SIM_RET.
        + eapply Mem.unchanged_on_refl.
        + ss.
        + apply MEM_SBUF.
        + apply INV_APP.
    Qed.


    Program Definition SimApp_con : SimApp tid_con prog_con con_mod :=
      {| app_gvar_ilist := con_gvar_ilist ;
         app_gfun_ilist := con_gfun_ilist ;
         app_cenv_ilist := con_cenv_ilist ;

         inv_app := inv_con ;
         job_func := f_job ;
         idx_job := idx_con;
         sim_job_func := sim_job_func_con;
      |}.
    Next Obligation.
      ss. unfold main_gvar_ids.
      r. intros x y X_IN Y_IN.
      r in Y_IN. des; ss.
      des; clarify.
    Qed.
    Next Obligation.
      ss. unfold main_gfun_ids.
      r. intros x y X_IN Y_IN.
      r in Y_IN. des; ss.
      - des; clarify.
      - des; clarify.
      - des; clarify.
      - des; clarify.
    Qed.
    Next Obligation.
      ss.
    Qed.
    Next Obligation.
      ss.
    Qed.
    Next Obligation.
      ss. eauto.
    Qed.
    Next Obligation.
      unfold num_tasks. ss. nia.
    Qed.
    Next Obligation.
      eapply inv_con_dep_app_blocks; eauto.
    Qed.
    Next Obligation.
      apply inv_con_init. ss.
    Qed.
  End SIM_JOB.
End VERIF_CONSOLE_APP.



Program Definition task_con: PALSTask.t :=
  {| PALSTask.tid := 0 ;
     PALSTask.cprog_app := console.prog ;
     PALSTask.cprog_tot := prog_con ;
     PALSTask.app_mod := con_mod ;
     PALSTask.sim_app := SimApp_con ;
  |}.
Next Obligation.
  apply prog_con_linked.
Qed.
Next Obligation.
  apply prog_con_defs_norep.
Qed.
Next Obligation.
  apply prog_con_gvs_ok. ss.
Qed.
Next Obligation.
  apply prog_con_gfs_ok. ss.
Qed.
Next Obligation.
  apply prog_con_cenvs_ok. ss.
Qed.
Next Obligation.
  apply prog_con_init_mem_ok.
Qed.
