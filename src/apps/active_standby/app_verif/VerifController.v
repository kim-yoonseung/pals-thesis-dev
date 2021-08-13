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
Require Import ctrl.
Require Import VerifProgBase.
Require Import VerifMainUtil.
Require Import PALSSystem.

Require Import AcStSystem.
Require Import LinkController.
Require Import SpecController.
Require Import VerifController_Base.
Require Import VerifController_Sync VerifController_Updq.

Import Clight Clightdefs.
Import ITreeNotations.
(* Import ActiveStandby. *)

Import CtrlState.

Set Nested Proofs Allowed.
(* Arguments app : simpl nomatch. *)
Local Transparent Archi.ptr64.
Local Opaque Z.of_nat Z.to_nat.

(* Arguments Nat.mul: simpl never. *)
Arguments Nat.mul: simpl never.

Opaque globalenv.

Local Open Scope Z.


Section VERIF_FUNC.

  Variable tid: nat.
  Variable cprog: Clight.program.
  Variable r: nat -> itree progE unit -> Clight.state -> Prop.

  Hypothesis CTRL_TASK_ID: (tid = 1 \/ tid = 2)%nat.

  Notation prog := (prog_of_clight cprog).
  Notation ge := (globalenv cprog).


  Hypothesis GENV_PROPS
    : genv_props (globalenv cprog)
                 (main_gvar_ilist tid ++ ctrl_gvar_ilist)
                 (main_gfun_ilist ++ ctrl_gfun_ilist)
                 (main_cenv_ilist ++ ctrl_cenv_ilist).

  Let GENV_PROPS_MAIN
    : genv_props (globalenv cprog)
                 (main_gvar_ilist tid)
                 (main_gfun_ilist)
                 (main_cenv_ilist).
  Proof.
    eapply genv_props_incl.
    - apply GENV_PROPS.
    - apply incl_appl. ss.
    - apply incl_appl. ss.
    - apply incl_appl. ss.
  Qed.

  Local Opaque idx_sync idx_updq.
  Definition idx_updist: nat := idx_sync + idx_updq + 10.

  Lemma sim_update_istate
        (itr: itree progE unit)
        (m: mem) (k: cont) (idx_ret: nat)
        st inb
        b_cst b_mst ofs_inb
        (BLOCKS_DIFF: b_cst <> b_mst)
        (CALL_CONT: is_call_cont k)
        (WF_ST: CtrlState.wf st)
        (MEM_CST: mem_cst_blk m st b_cst)
        (MEM_MSTORE: Mem_inbox m b_mst ofs_inb inb)
        (RANGE_OFS_HB: 0 <= ofs_inb <= 4 + inb_sz)
        (SIM_RET:
           forall m' st'
             (ST': st' = update_istate (Z.of_nat tid) st inb)
             (MEM_CST: mem_cst_blk m' st' b_cst)
             (MEM_CH_BLK: mem_changed_block b_cst m m')
           ,
           paco3 (_sim_itree prog) r
                 idx_ret itr
                 (Returnstate Vundef k m'))
    : paco3 (_sim_itree prog) r
            (idx_ret + idx_updist)%nat itr
            (Callstate (Internal f_update_istate)
                       [Vint (IntNat.of_nat tid);
                       Vptr b_cst Ptrofs.zero;
                       Vptr b_mst (Ptrofs.repr ofs_inb)] k m).
  Proof.
    unfold idx_updist.
    start_func.
    { econs. }
    ss.

    fw. fw. fw.
    { step_fptr_tac. }
    unfold IntNat.of_nat.
    rewrite sign_ext_byte_range.
    2: { clear - CTRL_TASK_ID.
         destruct CTRL_TASK_ID; subst; ss. }

    red_idx (idx_ret + idx_updq + 5 + idx_sync)%nat.
    pose proof ptr_range_mstore as PRANGE_MSTORE.
    replace (Z.of_nat (4 + inb_nsz + inb_nsz)) with
        (4 + inb_sz + inb_sz) in PRANGE_MSTORE by nia.

    eapply sim_sync_istate; eauto.
    { ss. }
    { nia. }
    { nia. }
    clear MEM_CST. i.
    fw. fw. fw.
    { step_fptr_tac. }

    red_idx (idx_ret + 2 + idx_updq)%nat.
    eapply sim_update_queue; eauto.
    (* { ss. } *)
    (* { apply GENV_PROPS. } *)
    { ss. }
    { eapply Mem_inbox_unch; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      s. ii. des; subst. ss. }
    renames m' st' WF_ST' into m1 st1 WF_ST1.
    renames ST' MEM_CH_BLK into ST1 MEM_CH_BLK1.
    clear MEM_CST. i.

    fw. fw.

    red_idx idx_ret.
    assert (WF_ST': wf st').
    { subst st'.
      apply wf_update_queue. eauto. }

    eapply SIM_RET; eauto.
    - unfold update_istate.
      rewrite <- ST1. rewrite <- ST'.
      ss.
    - eapply Mem.unchanged_on_trans; eauto.
  Qed.

  Local Opaque idx_qs.
  Definition idx_updown: nat := idx_qs + 50.

  Lemma sim_update_owner
        (itr: itree progE unit)
        (m: mem) (k: cont) (idx_ret: nat)
        st b_cst
        (CALL_CONT: is_call_cont k)
        (WF_ST: CtrlState.wf st)
        (MEM_CST: mem_cst_blk m st b_cst)
        (SIM_RET:
           forall m' st' retz
             (ST': (st', retz) = update_owner st)
             (MEM_CST: mem_cst_blk m' st' b_cst)
             (MEM_CH_BLK: mem_changed_block b_cst m m')
           ,
           paco3 (_sim_itree prog) r
                 idx_ret itr
                 (Returnstate (Vint (Int.repr retz)) k m'))
    : paco3 (_sim_itree prog) r
            (idx_ret + idx_updown)%nat itr
            (Callstate (Internal f_update_owner)
                       [Vptr b_cst Ptrofs.zero] k m).
  Proof.
    unfold idx_updown.
    start_func.
    { econs. }
    ss.

    fw. clear STEP_ENTRY.
    fw.
    destruct st as [md tout qb qe q].
    fw.
    { econs.
      eval_comput.
      rewrite Ptrofs.add_zero_l.
      repr_tac. s.
      erewrite Mem.loadbytes_load; cycle 1.
      { s. apply MEM_CST. }
      { s. solve_divide. }
      rewrite decode_val_signed_byte. s.
      rewrite sign_ext_byte_range.
      2: { apply Byte.signed_range. }
      rewrite Byte.signed_repr.
      2: { destruct md; ss. }
      reflexivity.
    }
    upd_lenv.
    fw. fw. fw.
    { econs.
      eval_comput.
      rewrite Ptrofs.add_zero_l.
      repr_tac. s.
      erewrite Mem.loadbytes_load; cycle 1.
      { s. apply MEM_CST. }
      { ss. solve_divide. }
      rewrite decode_val_signed_byte. s.
      rewrite sign_ext_byte_range.
      2: { apply Byte.signed_range. }
      rewrite Byte.signed_repr.
      2: { inv WF_ST. ss. }
      reflexivity.
    }
    upd_lenv.
    fw. fw. fw.
    { econs. eval_comput.
      repr_tac. s.
      rewrite Ptrofs.add_zero_l.
      repr_tac.
      erewrite Mem.loadbytes_load; cycle 1.
      { s. apply MEM_CST. }
      { ss. solve_divide. }
      rewrite decode_val_signed_byte. s.
      rewrite sign_ext_byte_range.
      2: { apply Byte.signed_range. }
      rewrite Byte.signed_repr.
      2: { inv WF_ST. ss. }
      reflexivity.
    }
    upd_lenv.
    fw. fw. fw.
    { econs. eval_comput.
      repr_tac. s.
      rewrite Ptrofs.add_zero_l.
      repr_tac.
      erewrite Mem.loadbytes_load; cycle 1.
      { s. apply MEM_CST. }
      { ss. solve_divide. }
      rewrite decode_val_signed_byte. s.
      rewrite sign_ext_byte_range.
      2: { apply Byte.signed_range. }
      rewrite Byte.signed_repr.
      2: { inv WF_ST. ss. }
      reflexivity.
    }
    upd_lenv.

    fw. fw. fw.
    { econs. eval_comput.
      rewrite Ptrofs.add_zero_l.
      repr_tac. s. reflexivity.
    }
    upd_lenv.

    fw. fw. fw. fw.
    { step_fptr_tac. }

    red_idx (idx_ret + 30 + idx_qs)%nat.
    eapply sim_qrange_sanitize.
    { ss. }
    { inv WF_ST. range_stac. }

    fw. upd_lenv.
    fw.

    generalize (range_qrange_sanitize_prec qb).
    intros RANGE_QS_QB.
    assert (BMAX_AUX_4: 4 < Byte.max_signed) by ss.

    hexploit (nth_error_Some2 _ q (Z.to_nat (qrange_sanitize qb))).
    { inv WF_ST. nia. }
    intros (q_n & Q_N).

    assert (RANGE_Q_N: IntRange.sintz8 q_n).
    { inv WF_ST.
      rewrite Forall_forall in RANGE_QUEUE.
      apply RANGE_QUEUE.
      eapply nth_error_In; eauto. }

    fw.
    { econs. eval_comput.
      repr_tac.
      rewrite Z.mul_1_l.

      erewrite Mem.loadbytes_load; cycle 1.
      { s.
        erewrite loadbytes_nth_error; eauto.
        { apply MEM_CST. }
        { apply map_nth_error. s. eauto. }
        rewrite Z2Nat.id by nia.
        ss.
      }
      { s. solve_divide. }
      s.
      rewrite decode_byte.
      rewrite sign_ext_byte_range_u by ss.
      rewrite sign_ext_byte_range by ss.
      reflexivity.
    }
    upd_lenv.

    fw. fw. fw.
    { econs.
      - eval_comput.
        inv WF_ST.
        rewrite Int_eq_repr_signed; cycle 1.
        { range_stac. }
        { range_stac. }
        reflexivity.
      - rewrite bool_val_of_bool. ss.
    }

    destruct (Z.eqb_spec tout 0).
    2: {
      fw.
      { econs. eval_comput. reflexivity. }
      upd_lenv.
      fw. fw.
      { econs.
        - eval_comput. ss.
        - ss. }
      rewrite Int.eq_true by ss. s.
      fw.
      { econs.
        - eval_comput. ss.
        - instantiate (1:= Vint (Int.repr Z_mone)). ss.
        - ss.
      }
      ss.
      rewrite call_cont_is_call_cont by ss.

      red_idx idx_ret.
      eapply SIM_RET; eauto.
      apply Mem.unchanged_on_refl.
    }

    fw.
    { econs. eval_comput.
      inv WF_ST.
      rewrite Int_eq_repr_signed by range_stac.
      (* instantiate (1:= if (0 <? q_n) then Vtrue else Vfalse). *)
      (* destruct (Z.ltb_spec 0 q_n); ss. *)
      instantiate (1:= Val.of_bool (negb (qb =? qe))).
      destruct (negb (qb =? qe)); ss.
    }
    upd_lenv.

    fw. fw.
    { econs.
      - eval_comput. ss.
      - instantiate (1:= negb (qb =? qe)).
        clear.
        destruct (negb (qb =? qe)); ss.
    }
    unfold get_queue in SIM_RET.
    erewrite nth_error_nth in SIM_RET by eauto.

    destruct (Z.eqb_spec qb qe).
    { s.
      fw.
      { econs.
        - eval_comput. ss.
        - eval_comput. ss.
          (* instantiate (1:= Vint (Int.repr 5)). ss. *)
        - ss.
      }
      ss.
      rewrite call_cont_is_call_cont by ss.

      red_idx idx_ret.
      eapply SIM_RET; eauto.
      apply Mem.unchanged_on_refl.
    }
    s.

    assert (STORE: exists m',
               Mem.store Mint8signed
                         m b_cst 1 (Vint (Int.repr MAX_TIMEOUT)) = Some m').
    { apply inhabited_sig_to_exists.
      econs.
      apply Mem.valid_access_store.
      rr. split; ss.
      2: { apply Z.divide_1_l. }
      ii. apply MEM_CST. nia. }
    des.

    fw. fw.
    { econs.
      - eval_comput.
        repr_tac. s.
        rewrite Ptrofs.add_zero_l. ss.
      - eval_comput. fold MAX_TIMEOUT. ss.
      - ss.
      - eval_comput.
        rewrite sign_ext_byte_range by ss.
        repr_tac.
        eauto.
    }

    fw. fw.
    { econs.
      - eval_comput.
        instantiate (1:= Val.of_bool
                           (match md with
                            | Active => false
                            | _ => true
                            end)).
        clear.
        destruct md; ss.
      - rewrite bool_val_of_bool. ss.
    }

    remember (match md with
              | Active => false
              | _ => true
              end) as b eqn: AUX_B.
    destruct b.
    - (* non_active *)
      fw.
      { econs.
        - eval_comput. ss.
        - eval_comput. ss.
        - ss.
      }
      replace (Int.neg (Int.repr 1)) with (Int.repr Z_mone) by ss.
      rewrite sign_ext_byte_range by ss.
      rewrite call_cont_is_call_cont by ss.

      red_idx idx_ret.

      hexploit store_unchanged_on'; eauto.
      unfold mem_range. s. i.

      eapply SIM_RET; eauto.
      + destruct md; ss.
      + inv MEM_CST. ss.
        econs; ss.
        * eapply Mem.loadbytes_unchanged_on; eauto.
          ii. nia.
        * apply Mem.loadbytes_store_same in STORE. ss.
        * eapply Mem.loadbytes_unchanged_on; eauto.
          ii. nia.
        * eapply Mem.loadbytes_unchanged_on; eauto.
          ii. nia.
        * eapply Mem.loadbytes_unchanged_on; eauto.
          ii. nia.
        * ii. eapply Mem.perm_store_1; eauto.
      +  eapply Mem.unchanged_on_implies; eauto.
         ii. des; ss.

    - (* active *)
      destruct md; ss.

      fw.
      { econs.
        - eval_comput. ss.
        - eval_comput. ss.
        - ss.
      }
      replace (Int.neg (Int.repr 1)) with (Int.repr Z_mone) by ss.
      rewrite sign_ext_byte_range by ss.
      rewrite call_cont_is_call_cont by ss.

      red_idx idx_ret.

      hexploit store_unchanged_on'; eauto.
      unfold mem_range. s. i.

      eapply SIM_RET; eauto.
      + inv MEM_CST. ss.
        econs; ss.
        * eapply Mem.loadbytes_unchanged_on; eauto.
          ii. nia.
        * apply Mem.loadbytes_store_same in STORE. ss.
        * eapply Mem.loadbytes_unchanged_on; eauto.
          ii. nia.
        * eapply Mem.loadbytes_unchanged_on; eauto.
          ii. nia.
        * eapply Mem.loadbytes_unchanged_on; eauto.
          ii. nia.
        * ii. eapply Mem.perm_store_1; eauto.
      +  eapply Mem.unchanged_on_implies; eauto.
         ii. des; ss.
  Qed.

  Section INTERP_SEND.

    Variable txs: nat.
    Variable sytm: nat.

    Hypothesis RANGE_TXS: IntRange.sint txs.
    (* Hypothesis RANGE_TID_R: tid_r < num_tasks + num_mcasts. *)
    Hypothesis RANGE_SYTM: IntRange.uint64 sytm.
    Hypothesis RANGE_SYTM2: IntRange.uint64 (sytm + period).

    Local Opaque idx_psend.
    Definition idx_shb: nat := idx_psend + 10.

    Lemma sim_send_hb
          (ktr: list bool * CtrlState.t ->
                itree progE unit)
          (ktr_app: itree appE CtrlState.t)
          m k sh bs_old (idx_ret: nat)
          st b_cst
          b_sbuf b_sh
          (WF_ST: CtrlState.wf st)

          (MEM_CONSTS: mem_consts ge m tid)
          (MEM_SH: mem_sh ge m sh)
          (MEM_TXS: mem_txs ge m txs)
          (MEM_SBUF: mem_sbuf ge m (sytm + period) tid bs_old)
          (CALL_CONT: is_call_cont k)

          (MEM_CST: mem_cst_blk m st b_cst)
          (FSYMB_CST: Genv.find_symbol ge _state = Some b_cst)
          (FSYMB_SBUF: Genv.find_symbol ge _send_buf = Some b_sbuf)
          (FSYMB_SH: Genv.find_symbol ge _send_hist = Some b_sh)
          (SIM_RET:
             forall m' bs' sh'
               (MEM_CST: mem_cst_blk m' st b_cst)

               (MEM_CONSTS: mem_consts ge m' tid)
               (MEM_SH: mem_sh ge m' sh')
               (MEM_TXS: mem_txs ge m' txs)
               (MEM_SBUF: mem_sbuf ge m' (sytm + period) tid bs')

               (MEM_CH_BLK: mem_unchanged_except (blocks_of ge [_send_buf; _send_hist]) m m')
             ,
             paco3 (_sim_itree prog) r idx_ret
                   (ret <- interp
                            (MWITree.send_handler
                               tid txs sytm)
                            ktr_app sh' ;;
                    ktr ret)
                           (* (ktr (sh', st)) *)
                   (Returnstate Vundef k m'))
      : paco3 (_sim_itree prog) r
              (idx_ret + idx_shb)%nat
              (ret <- interp
                       (MWITree.send_handler
                          tid txs sytm)
                       (send_hb_itree
                          st (Z.of_nat tid);;
                        ktr_app)
                       sh ;;
               ktr ret)
              (Callstate (Internal f_send_hb)
                         [Vptr b_cst Ptrofs.zero;
                         Vint (IntNat.of_nat tid)] k m).
    Proof.
      unfold idx_shb.
      start_func.
      { econs. }

      fw. clear STEP_ENTRY.
      fw. fw.
      { econs.
        eval_comput.
        repr_tac.
        erewrite sign_ext_byte_range.
        2: { clear - CTRL_TASK_ID.
             destruct CTRL_TASK_ID; subst; ss. }
        replace (3 - Z.of_nat tid) with (Z.of_nat (3 - tid)).
        2: { clear - CTRL_TASK_ID.
             destruct CTRL_TASK_ID; subst; ss. }
        reflexivity.
      }
      upd_lenv.

      fw. fw.
      { hexploit (in_gfun_ilist _pals_send); [sIn|].
        i. des.
        econs.
        - ss.
        - eval_comput.
          rewrite FDEF_SYMB. eauto.
        - eval_comput.
          erewrite sign_ext_byte_range.
          2: { clear - CTRL_TASK_ID.
               destruct CTRL_TASK_ID; subst; ss. }
          replace (3 - Z.of_nat tid) with (Z.of_nat (3 - tid)).
          2: { clear - CTRL_TASK_ID.
               destruct CTRL_TASK_ID; subst; ss. }
          reflexivity.
        - eauto.
        - eauto.
      }

      red_idx (idx_psend + (idx_ret + 3))%nat.
      unfold send_hb_itree.
      replace (Z.to_nat (3 - Z.of_nat tid))
        with (3 - tid)%nat by nia.
      erewrite (MWITree.unfold_interp_vis_send
                  tid (ctrl_mod (Z.of_nat tid))).
      2: { simpl_itree_goal. ss. }
      simpl_itree_goal. s.

      change (f_pals_send (Z.of_nat 1) (Z.of_nat 16) (Z.of_nat 8)) with
          (f_pals_send (Z.of_nat msg_size_k) (Z.of_nat max_num_tasks) (Z.of_nat max_num_mcasts)).

      (* rewrite CPROG_EQ. *)
      (* unfold Ptrofs.zero. *)
      (* change (Int.repr (Z.of_nat (3 - tid))) with *)
      (*     (IntNat.of_nat (3 - tid)). *)
      eapply sim_pals_send; eauto.
      { clear - CTRL_TASK_ID.
        unfold num_tasks. s.
        destruct CTRL_TASK_ID; subst; nia. }
      (* { (* rewrite CPROG_EQ. *) *)
      (*   apply GENV_PROPS_MAIN. } *)
      { ss. }
      { unfold num_tasks. s.
        nia. }
      { eapply Genv.global_addresses_distinct; eauto. ss. }
      { eapply Genv.global_addresses_distinct; eauto. ss. }
      { range_stac. }
      { range_stac. }
      { eapply mem_cst_loadbytes; eauto. }
      i.
      fw_tau (S idx_ret).
      { simpl_itree_goal. ss. }
      fw.
      rewrite Nat.sub_0_r.

      eapply SIM_RET; eauto.
      hexploit (mem_cst_unch ge st m m').
      { clear - FSYMB_CST MEM_CST.
        ii. clarify. }
      { eapply Mem.unchanged_on_implies; eauto.
        clear - FSYMB_CST FSYMB_SBUF FSYMB_SH.
        unfold blocks_of. s.
        ii. nbdes.

        cut (b <> b).
        { ss. }
        eapply (@Genv.global_addresses_distinct
                  _ _ ge id0 id); eauto.
        des; clarify. }
      intro AUX. r in AUX.
      hexploit AUX; eauto.
    Qed.

    Local Opaque idx_updist idx_updown idx_chdev idx_shb idx_psend.

    Definition idx_job_ctrl: nat :=
      idx_updist + idx_updown + idx_chdev + idx_psend + idx_shb + 100.

    Lemma sim_job_controller
          (ktr: list bool * t -> itree progE unit)
          m k sh bs_old (idx_ret: nat)
          st inb
          b_cst b_mst ofs_inb
          (FSYMB_CST: Genv.find_symbol ge _state = Some b_cst)
          (FSYMB_MST: Genv.find_symbol ge _mstore = Some b_mst)
          (INV_CTRL: inv_ctrl ge st m)
          (MEM_CONSTS: mem_consts ge m tid)
          (MEM_SH: mem_sh ge m sh)
          (MEM_TXS: mem_txs ge m txs)
          (MEM_SBUF: mem_sbuf ge m (sytm + period) tid bs_old)
          (MEM_INB: Mem_inbox m b_mst ofs_inb inb)
          (RANGE_OFS_INB: 0 <= ofs_inb <= 4 + inb_sz)
          (CALL_CONT: is_call_cont k)
          (SIM_RET:
             forall st' m' bs' sh'
               (INV_CTRL: inv_ctrl ge st' m')
               (MEM_CONSTS: mem_consts ge m' tid)
               (MEM_SH: mem_sh ge m' sh')
               (MEM_TXS: mem_txs ge m' txs)
               (MEM_SBUF: mem_sbuf ge m' (sytm + period)
                                   tid bs')
               (MEM_UNCH: Mem.unchanged_on (blocks_of ge app_unch_gvar_ids) m m')
               (* (MEM_CH_BLK: mem_changed_block b_cst m m') *)
             ,
             paco3 (_sim_itree prog) r
                   idx_ret (ktr (sh', st'))
                   (Returnstate Vundef k m'))
      : paco3 (_sim_itree prog) r
              (idx_ret + idx_job_ctrl)%nat
              (ret <- interp (MWITree.send_handler tid txs sytm)
                            (job_controller_itree
                               (Z.of_nat tid) st (Z.of_nat sytm) inb)
                            sh ;;
               ktr ret)
              (Callstate (Internal f_job_controller)
                         [Vint (IntNat.of_nat tid);
                         Vptr b_cst Ptrofs.zero;
                         Vlong (IntNat.of_nat64 sytm);
                         Vptr b_mst (Ptrofs.repr ofs_inb)]
                         k m).
    Proof.
      unfold idx_job_ctrl.
      repeat rewrite Nat.add_assoc.

      start_func.
      { econs. }

      assert (RANGE_TID: IntRange.sint8 tid).
      { clear - CTRL_TASK_ID.
        destruct CTRL_TASK_ID;
          subst; range_stac. }

      simpl in *.
      fw. fw.

      hexploit (in_cenv_ilist __ctrl_state); [sIn|].
      intro CO_CTRL_STATE.

      fw.
      { econs.
        eval_comput.
        rewrite CO_CTRL_STATE. s.
        rewrite Ptrofs.add_zero_l.
        unfold align_attr. s.
        unfold Coqlib.align. s.
        reflexivity.
      }
      upd_lenv.
      fw. fw. fw.
      { hexploit (in_gfun_ilist _update_istate); [sIn|].
        i. des.
        econs.
        - ss.
        - eval_comput.
          rewrite FDEF_SYMB. ss.
        - eval_comput.
          unfold IntNat.of_nat.
          rewrite sign_ext_byte_range by ss.
          reflexivity.
        - eauto.
        - ss.
      }

      r in INV_CTRL. des.
      red_idx (idx_ret + idx_updown + idx_chdev + idx_shb + idx_psend + 90 + idx_updist)%nat.
      eapply sim_update_istate; eauto.
      { eapply Genv.global_addresses_distinct; eauto.
        ss. }
      { ss. }

      clear MEM_CST. i.
      guardH ST'.

      eapply mem_grant_unch_diffblk in MEM_GRANT; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_consts_unch_diffblk in MEM_CONSTS; eauto.
      2: { s. clear - MEM_CH_BLK FSYMB_CST.
           i. eapply global_addresses_distinct'; eauto.
           des; subst; ss. }
      eapply mem_sh_unch_diffblk in MEM_SH; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_txs_unch_diffblk in MEM_TXS; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_sbuf_unch_diffblk in MEM_SBUF; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      eapply Mem_inbox_unch in MEM_INB.
      2: { eapply Mem.unchanged_on_implies; eauto.
           s. i. des; subst.
           eapply Genv.global_addresses_distinct; eauto. ss. }

      fw. fw. fw. fw. fw.
      { hexploit (in_gfun_ilist _update_owner); [sIn|].
        i. des.
        econs.
        - ss.
        - eval_comput.
          rewrite FDEF_SYMB. reflexivity.
        - eval_comput. reflexivity.
        - eauto.
        - eauto.
      }

      red_idx (idx_ret + idx_shb + idx_psend + idx_chdev + 80 + idx_updown)%nat.

      eapply sim_update_owner.
      { ss. }
      { instantiate (1:= st').
        rewrite ST'.
        apply wf_update_istate. ss. }
      { ss. }

      renames st' ST' MEM_CH_BLK into st1 ST1 MEM_CH_BLK_P.
      rename m' into m1.

      clear MEM_CST. i.
      guardH ST'.

      assert (<<WF_ST': wf st'>> /\ <<RANGE_RETZ: IntRange.sintz8 retz>>).
      { eapply wf_update_owner.
        2: { symmetry. apply ST'. }
        rewrite ST1.
        eapply wf_update_istate. eauto. }
      des.

      eapply mem_grant_unch_diffblk in MEM_GRANT; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_consts_unch_diffblk in MEM_CONSTS; eauto.
      2: { s. clear - MEM_CH_BLK FSYMB_CST.
           i. eapply global_addresses_distinct'; eauto.
           des; subst; ss. }
      eapply mem_sh_unch_diffblk in MEM_SH; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_txs_unch_diffblk in MEM_TXS; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_sbuf_unch_diffblk in MEM_SBUF; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      eapply Mem_inbox_unch in MEM_INB.
      2: { eapply Mem.unchanged_on_implies; eauto.
           s. i. des; subst.
           eapply Genv.global_addresses_distinct; eauto. ss. }

      fw. upd_lenv.
      fw. fw.
      { econs.
        eval_comput.
        rewrite sign_ext_byte_range by range_stac.
        reflexivity. }
      upd_lenv.

      fw. fw. fw. fw.
      { hexploit (in_gfun_ilist _check_dev_id); [sIn|].
        i. des.
        econs.
        - ss.
        - eval_comput.
          rewrite FDEF_SYMB. reflexivity.
        - eval_comput.
          rewrite sign_ext_byte_range by range_stac.
          reflexivity.
        - eauto.
        - eauto.
      }

      red_idx (idx_ret + idx_shb + idx_psend + 70 + idx_chdev)%nat.
      eapply sim_check_dev_id.
      { ss. }
      { range_stac. }

      fw. upd_lenv.
      fw. fw.
      { econs.
        - eval_comput. reflexivity.
        - rewrite bool_val_of_bool. reflexivity.
      }

      unfold job_controller_itree.
      rewrite <- ST1.
      rewrite <- ST'.
      unfold check_dev_id.

      hexploit (in_gvar_ids _send_buf); [sIn|].
      intros (b_sbuf & FSYMB_SBUF).
      hexploit (in_gvar_ids _send_hist); [sIn|].
      intros (b_sh & FSYMB_SH).

      match goal with
      | |- context [if ?c then _ else _] =>
        destruct c eqn: COND
      end.
      - (* send grant *)

        match goal with
        | |- context [if ?c then _ else _] =>
          replace c with true
        end.

        hexploit (in_gvar_ids _grant_msg); [sIn|].
        intros (b_gr & FSYMB_GR).

        fw.
        { hexploit (in_gfun_ilist _pals_send); [sIn|].
          i. des.
          econs.
          - ss.
          - eval_comput.
            rewrite FDEF_SYMB. reflexivity.
          - eval_comput.
            rewrite FSYMB_GR.
            rewrite sign_ext_byte_range by range_stac.
            reflexivity.
          - eauto.
          - eauto.
        }

        red_idx (idx_psend + (idx_ret + idx_shb + 60))%nat.

        erewrite (MWITree.unfold_interp_vis_send
                    tid (ctrl_mod (Z.of_nat tid))).
        2: { simpl_itree_goal. ss. }
        s. simpl_itree_goal.

        change
          (Internal (f_pals_send (Z.of_nat 1) (Z.of_nat 16) (Z.of_nat 8)))
          with
            (Internal (f_pals_send (Z.of_nat msg_size_k) (Z.of_nat max_num_tasks) (Z.of_nat max_num_mcasts))).

        assert (RANGE_RETZ_PREC: 3 <= retz <= 5).
        { clear - COND.
          destruct (Z.eqb_spec retz (Z.of_nat 3)).
          { subst. nia. }
          destruct (Z.eqb_spec retz (Z.of_nat 4)).
          { subst. nia. }
          destruct (Z.eqb_spec retz (Z.of_nat 5)).
          { subst. nia. }
          ss.
        }

        replace (Int.repr retz) with
            (IntNat.of_nat (Z.to_nat retz)).
        2: { unfold IntNat.of_nat.
             rewrite Z2Nat.id by nia.
             ss. }

        eapply sim_pals_send; try assumption.
        { clear - CTRL_TASK_ID.
          unfold num_tasks. ss.
          destruct CTRL_TASK_ID; subst; nia. }
        (* { rewrite CPROG_EQ. *)
        (*   eapply genv_props_main. } *)
        { ss. }
        { unfold num_tasks. s.
          clear - RANGE_RETZ_PREC.
          nia. }
        { eauto. }
        { eauto. }
        { eapply Genv.global_addresses_distinct; eauto. ss. }
        { eapply Genv.global_addresses_distinct; eauto. ss. }
        { range_stac. }
        { s. range_stac. }
        { eapply MEM_GRANT; eauto. }
        { s. eapply MEM_SBUF. }

        rename m' into m2.
        clear MEM_CONSTS MEM_SH MEM_TXS MEM_SBUF. i.

        eapply (mem_grant_unch ge m2 m') in MEM_GRANT.
        2: {
          clear - MEM_GRANT FSYMB_GR MEM_UNCH.
          eapply Mem.unchanged_on_implies; eauto.
          unfold blocks_of. s.
          ii. des; ss; subst.
          - hexploit (@Genv.global_addresses_distinct
                        _ _ ge _grant_msg _send_buf); eauto; ss.
          - hexploit (@Genv.global_addresses_distinct
                        _ _ ge _grant_msg _send_hist); eauto; ss.
        }
        eapply (Mem_inbox_unch m2 m') in MEM_INB.
        2: {
          clear - MEM_INB FSYMB_MST MEM_UNCH.
          eapply Mem.unchanged_on_implies; eauto.
          unfold blocks_of. s.
          ii. des; ss; subst.
          - hexploit (@Genv.global_addresses_distinct
                        _ _ ge _mstore _send_buf); eauto; ss.
          - hexploit (@Genv.global_addresses_distinct
                        _ _ ge _mstore _send_hist); eauto; ss.
        }
        hexploit (mem_cst_unch ge st' m2 m').
        { r. clear - FSYMB_CST MEM_CST.
          i. clarify. }
        { clear - FSYMB_CST MEM_CST MEM_UNCH.
          eapply Mem.unchanged_on_implies; eauto.
          unfold blocks_of. s.
          ii. des; ss; clarify.
          - hexploit (@Genv.global_addresses_distinct
                        _ _ ge _state _send_buf); eauto; ss.
          - hexploit (@Genv.global_addresses_distinct
                        _ _ ge _state _send_hist); eauto; ss.
        }
        unfold mem_cst.
        intro AUX.
        hexploit AUX; eauto.
        clear MEM_CST.
        intros MEM_CST. clear AUX.

        fw. fw.
        fw_tau (idx_ret + 20 + idx_shb)%nat.
        { hexploit (in_gfun_ilist _send_hb); [sIn|].
          i. des.
          econs.
          - ss.
          - eval_comput.
            rewrite FDEF_SYMB. ss.
          - eval_comput.
            unfold IntNat.of_nat.
            rewrite sign_ext_byte_range by range_stac.
            reflexivity.
          - eauto.
          - eauto.
        }
        { simpl_itree_goal. ss. }

        eapply sim_send_hb; eauto.
        { ss. }

        clear MEM_CST MEM_CONSTS MEM_SH MEM_TXS MEM_SBUF.
        renames m' MEM_CH_BLK into m3 MEM_CH_BLK3.
        renames bs' sh' into bs3 sh3.
        i.

        eapply mem_grant_unch in MEM_GRANT; eauto.
        2: {
          eapply Mem.unchanged_on_implies; eauto.
          unfold blocks_of.
          clear.
          s. ii. des; ss; subst.
          - hexploit (@Genv.global_addresses_distinct
                        _ _ ge _grant_msg _send_buf); eauto; ss.
          - hexploit (@Genv.global_addresses_distinct
                        _ _ ge _grant_msg _send_hist); eauto; ss.
        }

        erewrite (MWITree.unfold_interp_ret
                    tid (ctrl_mod (Z.of_nat tid))).
        2: { ss. }

        simpl_itree_goal.
        fw. fw.
        red_idx (idx_ret).

        eapply SIM_RET; eauto.
        + r. splits; eauto.
          clear - MEM_CST FSYMB_CST.
          ii. clarify.
        + eapply Mem.unchanged_on_trans; eauto.
          { eapply Mem.unchanged_on_implies; eauto.
            clear - FSYMB_CST.
            unfold blocks_of. s. i.
            nbdes.
            eapply Genv.global_addresses_distinct; eauto.
            des; clarify. }

          eapply Mem.unchanged_on_trans; eauto.
          { eapply Mem.unchanged_on_implies; eauto.
            clear - FSYMB_CST.
            unfold blocks_of. s. i.
            nbdes.
            eapply Genv.global_addresses_distinct; eauto.
            des; clarify. }

          eapply Mem.unchanged_on_trans; eauto.
          { eapply Mem.unchanged_on_implies; eauto.
            clear - FSYMB_SBUF FSYMB_SH.
            unfold blocks_of. s. ii.
            nbdes.
            cut (b <> b).
            { ss. }
            eapply (@Genv.global_addresses_distinct
                      _ _ ge id id0); eauto.
            des; clarify.
          }

          eapply Mem.unchanged_on_implies; eauto.
          clear - FSYMB_CST FSYMB_SH FSYMB_SBUF.
          unfold blocks_of. s. ii. nbdes.

          cut (b <> b).
          { ss. }
          eapply (@Genv.global_addresses_distinct
                    _ _ ge id0 id); eauto.
          des; clarify.

      - (* false *)
        match goal with
        | |- context [if ?c then _ else _] =>
          replace c with false
        end.

        match goal with
        | |- context [interp _ ?tr] =>
          remember tr as itr eqn: ITR_EQ
        end.

        apply eq_is_bisim in ITR_EQ.
        simpl_itree ITR_EQ.
        apply EqAxiom.bisimulation_is_eq in ITR_EQ.
        subst_itree ITR_EQ.

        fw. fw.
        { hexploit (in_gfun_ilist _send_hb); [sIn|].
          i. des.
          econs.
          - ss.
          - eval_comput.
            rewrite FDEF_SYMB. ss.
          - eval_comput.
            unfold IntNat.of_nat.
            rewrite sign_ext_byte_range by range_stac.
            reflexivity.
          - eauto.
          - eauto.
        }

        red_idx (idx_ret + 50 + idx_shb)%nat.
        eapply sim_send_hb; eauto.
        { ss. }

        clear MEM_CST MEM_CONSTS MEM_SH MEM_TXS MEM_SBUF.
        renames m' MEM_CH_BLK into m3 MEM_CH_BLK3.
        (* renames bs' sh' into bs3 sh3. *)
        i.

        eapply mem_grant_unch in MEM_GRANT; eauto.
        2: {
          eapply Mem.unchanged_on_implies; eauto.
          unfold blocks_of.
          clear.
          s. ii. des; ss; subst.
          - hexploit (@Genv.global_addresses_distinct
                        _ _ ge _grant_msg _send_buf); eauto; ss.
          - hexploit (@Genv.global_addresses_distinct
                        _ _ ge _grant_msg _send_hist); eauto; ss.
        }

        fw. fw.
        erewrite (MWITree.unfold_interp_ret
                    tid (ctrl_mod (Z.of_nat tid))).
        2: { ss. }
        simpl_itree_goal.
        red_idx idx_ret.
        eapply SIM_RET; eauto.
        + r. splits; eauto.
          clear - MEM_CST FSYMB_CST.
          ii. clarify.
        + eapply Mem.unchanged_on_trans; eauto.
          { eapply Mem.unchanged_on_implies; eauto.
            clear - FSYMB_CST.
            unfold blocks_of. s. i.
            nbdes.
            eapply Genv.global_addresses_distinct; eauto.
            des; clarify. }

          eapply Mem.unchanged_on_trans; eauto.
          { eapply Mem.unchanged_on_implies; eauto.
            clear - FSYMB_CST.
            unfold blocks_of. s. i.
            nbdes.
            eapply Genv.global_addresses_distinct; eauto.
            des; clarify. }

          eapply Mem.unchanged_on_implies; eauto.
          clear - FSYMB_CST FSYMB_SH FSYMB_SBUF.
          unfold blocks_of. s. ii. nbdes.

          cut (b <> b).
          { ss. }
          eapply (@Genv.global_addresses_distinct
                    _ _ ge id0 id); eauto.
          des; clarify.
    Qed.

  End INTERP_SEND.

  Definition idx_ctrl : nat := idx_job_ctrl + 10.

  Local Opaque idx_job_ctrl.

  Lemma sim_job_func_ctrl
    : forall (b_mst : block)
        (txs idx' : nat) (ast : CtrlState.t)
        (ki : list bool * CtrlState.t -> itree progE unit)
        (m : mem) (kp : cont) (sytm : nat) (cflg : bool)
        (ofsc ofsn : Z) (inbc inbn : list (bytes?))
        (* (sh : list bool) *) (mcont : bytes)
        (CALL_CONT: is_call_cont kp)
        (RANGE_SYTM: IntRange.uint64 sytm)
        (RANGE_NXT_SYTM: IntRange.uint64 (sytm + period))
        (RANGE_TXS: IntRange.sint txs)
        (INV_APP: inv_ctrl ge ast m)
        (FSYMB_MST: Genv.find_symbol ge _mstore = Some b_mst)
        (MEM_CONSTS: mem_consts ge m tid)
        (MEM_SBUF: mem_sbuf ge m (sytm + RTSysEnv.period) tid mcont)
        (MEM_MSTORE: mem_mstore ge m cflg ofsc ofsn inbc inbn)
        (MEM_SH: mem_sh ge m (repeat false num_tasks))
        (MEM_TXS: mem_txs ge m txs)
        (SIM_RET: forall (sh' : list bool) (ast' : CtrlState.t)
                    (m' : mem) (mcont' : bytes)
                    (MEM_UNCH: Mem.unchanged_on (blocks_of ge app_unch_gvar_ids) m m')
                    (MEM_SH: mem_sh ge m' sh')
                    (MEM_SBUF: mem_sbuf ge m' (sytm + RTSysEnv.period) tid mcont')
                    (INV_APP: inv_ctrl ge ast' m'),
            paco3 (_sim_itree prog) r
                  idx' (ki (sh', ast')) (Returnstate Vundef kp m'))
    ,
      paco3 (_sim_itree prog) r (idx' + idx_ctrl)%nat
            (` ret : list bool * CtrlState.t <-
                     MWITree.interp_send
                       tid (ctrl_mod (Z.of_nat tid)) txs sytm
                       (repeat false num_tasks) ast inbc;;
                     ki ret)
            (Callstate (Internal f_job)
                       [Vlong (IntNat.of_nat64 sytm);
                       Vptr b_mst (Ptrofs.repr ofsc)] kp m)
  .
  Proof.
    i.
    start_func.
    { econs. }

    unfold idx_ctrl. rewrite Nat.add_assoc.
    fw. clear STEP_ENTRY.

    hexploit (in_gvar_ids _TASK_ID); [sIn|].
    intros (b_tid & FSYMB_TID).
    hexploit (in_gvar_ids _state); [sIn|].
    intros (b_cst & FSYMB_CST).

    fw.
    { hexploit (in_gfun_ilist _job_controller); [sIn|].
      i. des.

      econs.
      - ss.
      - eval_comput.
        rewrite FDEF_SYMB. reflexivity.
      - eval_comput.
        rewrite FSYMB_TID.
        rewrite FSYMB_CST.
        erewrite mem_consts_task_id by eauto.
        unfold IntNat.of_nat.
        rewrite sign_ext_byte_range.
        2: {
          clear - CTRL_TASK_ID.
          destruct CTRL_TASK_ID; subst;
            range_stac.
        }
        reflexivity.
      - eauto.
      - eauto.
    }

    red_idx ((idx' + 3) + idx_job_ctrl)%nat.
    unfold MWITree.interp_send.

    eapply sim_job_controller; eauto.
    { r in MEM_MSTORE.
      hexploit MEM_MSTORE; eauto.
      intro MBLK.
      inv MBLK. eauto. }
    { r in MEM_MSTORE.
      hexploit MEM_MSTORE; eauto.
      intro MBLK.
      inv MBLK.
      clear.
      pose proof ptr_range_mstore.
      destruct cflg.
      - range_stac.
      - range_stac.
    }
    { ss. }

    i. fw. fw.
    red_idx idx'.
    eapply SIM_RET; eauto.
  Qed.

End VERIF_FUNC.


Section SIM_APP_CTRL.
  Variable tid: Tid.
  Hypothesis CTRL_TASK_ID: (tid = 1 \/ tid = 2)%nat.

  Program Definition SimApp_ctrl
    : SimApp tid (prog_ctrl (Z.of_nat tid))
             (ctrl_mod (Z.of_nat tid)) :=
    {| app_gvar_ilist := ctrl_gvar_ilist ;
       app_gfun_ilist := ctrl_gfun_ilist ;
       app_cenv_ilist := ctrl_cenv_ilist ;

       inv_app := inv_ctrl ;
       job_func := f_job ;
       idx_job := idx_ctrl;
       sim_job_func := _ ;
    |}.
  Next Obligation.
    ss. unfold main_gvar_ids.
    r. intros x y X_IN Y_IN.
    r in Y_IN. des; ss.
    - des; clarify.
    - des; clarify.
  Qed.
  Next Obligation.
    ss. unfold main_gfun_ids.
    r. intros x y X_IN Y_IN.
    r in Y_IN.
    (* clear CPROG_EQ. *)
    des; ss;
      (des; clarify).
  Qed.
  Next Obligation.
    ss.
    r. ii. ss. clarify.
    des; clarify.
  Qed.
  Next Obligation.
    ss.
  Qed.
  Next Obligation.
    ss. sIn.
  Qed.
  Next Obligation.
    unfold num_tasks. ss. nia.
  Qed.
  Next Obligation.
    (* rewrite <- CPROG_EQ in *. *)
    eapply inv_ctrl_dep_app_blocks; eauto.
  Qed.
  Next Obligation.
    (* rewrite <- CPROG_EQ in *. s. *)
    apply (inv_ctrl_init tid); ss.
  Qed.
  Next Obligation.
    assert (CPROG_EQ: exists cprog, cprog = prog_ctrl (Z.of_nat tid)).
    { esplits; eauto. }
    des.
    pose proof (genv_props_ctrl tid) as GENV_PROPS.
    rewrite <- CPROG_EQ in *.
    clear CPROG_EQ.

    eapply (sim_job_func_ctrl tid cprog); eauto.
  Qed.

End SIM_APP_CTRL.


Program Definition task_ctrl1
  : PALSTask.t :=
  {| PALSTask.tid := 1 ;
     PALSTask.cprog_app := ctrl.prog 1 ;
     PALSTask.cprog_tot := prog_ctrl 1 ;
     PALSTask.app_mod := ctrl_mod 1 ;
     PALSTask.sim_app := SimApp_ctrl 1 _ ;
  |}.
Next Obligation.
  eauto.
Qed.
Next Obligation.
  apply prog_ctrl_linked.
Qed.
Next Obligation.
  apply prog_ctrl_defs_norep.
Qed.
Next Obligation.
  replace 1 with (Z.of_nat 1) by ss.
  apply prog_ctrl_gvs_ok. ss.
Qed.
Next Obligation.
  replace 1 with (Z.of_nat 1) by ss.
  apply prog_ctrl_gfs_ok. ss.
Qed.
Next Obligation.
  replace 1 with (Z.of_nat 1) by ss.
  apply prog_ctrl_cenvs_ok. ss.
Qed.
Next Obligation.
  apply prog_ctrl_init_mem_ok.
Qed.

Program Definition task_ctrl2
  : PALSTask.t :=
  {| PALSTask.tid := 2 ;
     PALSTask.cprog_app := ctrl.prog 2 ;
     PALSTask.cprog_tot := prog_ctrl 2 ;
     PALSTask.app_mod := ctrl_mod 2 ;
     PALSTask.sim_app := SimApp_ctrl 2 _ ;
  |}.
Next Obligation.
  eauto.
Qed.
Next Obligation.
  apply prog_ctrl_linked.
Qed.
Next Obligation.
  apply prog_ctrl_defs_norep.
Qed.
Next Obligation.
  replace 2 with (Z.of_nat 2) by ss.
  apply prog_ctrl_gvs_ok. ss.
Qed.
Next Obligation.
  replace 2 with (Z.of_nat 2) by ss.
  apply prog_ctrl_gfs_ok. ss.
Qed.
Next Obligation.
  replace 2 with (Z.of_nat 2) by ss.
  apply prog_ctrl_cenvs_ok. ss.
Qed.
Next Obligation.
  apply prog_ctrl_init_mem_ok.
Qed.
