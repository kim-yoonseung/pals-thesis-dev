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
Require Import dev.
Require Import VerifProgBase.
Require Import VerifMainUtil.
Require Import PALSSystem.

Require Import AcStSystem.
Require Import LinkDevice.
Require Import SpecDevice.
Require Import VerifDevice_Base.
(* Require Import VerifController_Sync VerifController_Updq. *)

Import Clight Clightdefs.
Import ITreeNotations.
(* Import ActiveStandby. *)

Import DevState.

Set Nested Proofs Allowed.
Local Transparent Archi.ptr64.
Local Opaque Z.of_nat Z.to_nat.
Arguments Nat.mul: simpl never.

Opaque globalenv.

Local Open Scope Z.


Section VERIF_FUNC.
  Variable tid: nat.
  Variable cprog: Clight.program.
  Variable r: nat -> itree progE unit -> Clight.state -> Prop.

  Notation prog := (prog_of_clight cprog).
  Notation ge := (globalenv cprog).

  Hypothesis RANGE_TID: (tid < num_tasks)%nat.

  Hypothesis GENV_PROPS
    : genv_props (globalenv cprog)
                 (main_gvar_ilist tid ++ dev_gvar_ilist)
                 (main_gfun_ilist ++ dev_gfun_ilist)
                 (main_cenv_ilist ++ dev_cenv_ilist).

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


  Definition idx_sync: nat := 20.

  Lemma sim_sync_dev_state
        (itr: itree progE unit)
        (m: mem) (k: cont) (idx_ret: nat)
        st inb
        b_dst b_mst ofs_inb
        (BLOCKS_DIFF: b_dst <> b_mst)
        (CALL_CONT: is_call_cont k)
        (WF_ST: DevState.wf st)
        (MEM_DST: mem_dst_blk m st b_dst)
        (MEM_MSTORE: Mem_inbox m b_mst ofs_inb inb)
        (RANGE_OFS_HB: 0 <= ofs_inb <= 4 + inb_sz)
        (SIM_RET:
           forall m' st'
             (ST': st' = sync_dev_state inb st)
             (MEM_DST: mem_dst_blk m' st' b_dst)
             (MEM_CH_BLK: mem_changed_block b_dst m m')
           ,
           paco3 (_sim_itree prog) r
                 idx_ret itr
                 (Returnstate Vundef k m'))
    : paco3 (_sim_itree prog) r
            (idx_ret + idx_sync)%nat itr
            (Callstate (Internal f_sync_dev_state)
                       [Vptr b_mst (Ptrofs.repr ofs_inb);
                       Vptr b_dst Ptrofs.zero] k m).
  Proof.
    unfold idx_sync.
    start_func.
    { econs. }

    hexploit (in_cenv_ilist _inbox_t); [sIn|].
    intro CO_INBOX.
    hexploit (in_cenv_ilist _msg_entry_t); [sIn|].
    intro CO_MENTRY.
    hexploit (in_cenv_ilist __dev_state); [sIn|].
    intro CO_DEV_STATE.

    pose proof ptr_range_mstore as PRANGE_MSTORE.
    replace (Z.of_nat (4 + inb_nsz + inb_nsz)) with
        (4 + inb_sz + inb_sz) in PRANGE_MSTORE by nia.

    assert (PRANGE1: mentry_sz * 3 <= inb_sz).
    { hexploit (within_inb_nsz1 3).
      { unfold num_tasks. ss. nia. }
      nia.
    }

    fw. fw. fw.
    { econs. eval_comput.
      rewrite CO_INBOX. s.
      change main_prm._msg_entry_t with _msg_entry_t.
      rewrite CO_MENTRY.
      unfold align_attr, Coqlib.align. s.
      repr_tac.
      rewrite Z.add_0_r.
      rewrite Z.mul_1_r. ss.
    }
    upd_lenv.

    fw. fw. fw.
    { econs. eval_comput.
      rewrite CO_INBOX. s.
      change main_prm._msg_entry_t with _msg_entry_t.
      rewrite CO_MENTRY.
      unfold align_attr, Coqlib.align. s.
      repr_tac.
      rewrite Z.add_0_r. ss.
    }
    upd_lenv.

    r in MEM_MSTORE. des.
    rewrite iForall_nth in MSG_ENTRIES.

    hexploit (nth_error_Some2 _ inb 1%nat).
    { rewrite NUM_ENTRIES.
      unfold num_tasks. ss. nia. }
    i. des. renames e1 NTH_EX into ment1 MENT1.
    hexploit (nth_error_Some2 _ inb 2%nat).
    { rewrite NUM_ENTRIES.
      unfold num_tasks. ss. nia. }
    i. des. renames e1 NTH_EX into ment2 MENT2.

    hexploit (MSG_ENTRIES 1%nat).
    rewrite MENT1. s. intro MEM_MENT1.
    hexploit (MSG_ENTRIES 2%nat).
    rewrite MENT2. s. intro MEM_MENT2.

    eapply Mem_msg_entry_inv2 in MEM_MENT1. des.
    renames MENT_RCV MENT_CONT into MENT_RCV1 MENT_CONT1.
    eapply Mem_msg_entry_inv2 in MEM_MENT2. des.
    renames MENT_RCV MENT_CONT into MENT_RCV2 MENT_CONT2.

    fw. fw. fw.
    { econs.
      - eval_comput.
        rewrite CO_MENTRY. s.
        unfold align_attr, Coqlib.align. s.
        rewrite Ptrofs.add_zero.
        repr_tac.

        rewrite Nat.mul_1_r in MENT_RCV1.
        rewrite MENT_RCV1. reflexivity.
      - instantiate (1:= if ment1 then true else false).
        destruct ment1; ss.
    }

    assert (STORE: exists m',
               Mem.store Mint8signed
                         m b_dst 0 (Vint (Int.repr 1)) = Some m').
    { apply inhabited_sig_to_exists.
      econs.
      apply Mem.valid_access_store.
      rr. split; ss.
      2: { apply Z.divide_1_l. }
      ii. apply MEM_DST. nia. }
    des.

    unfold sync_dev_state in SIM_RET.
    erewrite nth_error_nth in SIM_RET; eauto.
    erewrite nth_error_nth in SIM_RET; eauto.

    destruct ment1.
    { (* Be owner *)
      fw.
      { econs. eval_comput. ss. }
      upd_lenv.
      fw. fw.
      { econs.
        - eval_comput. ss.
        - ss.
      }
      rewrite Int.eq_false by ss. s.

      fw.
      { econs.
        - eval_comput.
          rewrite CO_DEV_STATE. s.
          unfold Coqlib.align, align_attr. s.
          rewrite Ptrofs.add_zero. ss.
        - eval_comput. ss.
        - s. ss.
        - eval_comput.
          rewrite sign_ext_byte_range by range_stac.
          apply STORE.
      }

      fw.
      red_idx idx_ret.
      eapply SIM_RET; eauto.
      - eapply store_set_owner_status; eauto.
      - eapply Mem.store_unchanged_on; eauto.
    }

    fw.
    { econs. eval_comput.
      rewrite CO_MENTRY. s.
      unfold Coqlib.align, align_attr. s.
      rewrite Ptrofs.add_zero.
      repr_tac.

      replace (mentry_sz * 2) with (Z.of_nat (mentry_nsz * 2)) by nia.
      rewrite MENT_RCV2.
      instantiate (1:= if ment2 then Vtrue else Vfalse).
      destruct ment2; ss.
    }
    upd_lenv.

    fw. fw.
    { econs.
      - eval_comput. ss.
      - instantiate (1:= if ment2 then true else false).
        destruct ment2; ss.
    }

    destruct ment2.
    { (* Be owner *)
      fw.
      { econs.
        - eval_comput.
          rewrite CO_DEV_STATE. s.
          unfold Coqlib.align, align_attr. s.
          rewrite Ptrofs.add_zero. ss.
        - eval_comput. ss.
        - s. ss.
        - eval_comput.
          rewrite sign_ext_byte_range by range_stac.
          apply STORE.
      }

      fw.
      red_idx idx_ret.
      eapply SIM_RET; eauto.
      - eapply store_set_owner_status; eauto.
      - eapply Mem.store_unchanged_on; eauto.
    }

    fw.
    red_idx idx_ret.
    eapply SIM_RET; eauto.
    eapply Mem.unchanged_on_refl.
  Qed.


  Definition idx_ndmd: nat := 20.

  Lemma sim_get_new_demand
        (ktr_app: nat -> itree appE DevState.t)
        (ktr: list bool * DevState.t -> itree progE unit)
        (m: mem) (k: cont) (idx_ret: nat)
        txs sytm sh
        (CALL_CONT: is_call_cont k)
        (SIM_RET:
           forall (d: nat)
             (DMD_UBND: (d <= MAX_TIMEOUT)%nat),
           paco3 (_sim_itree prog) r
                 idx_ret (ret <- interp (MWITree.send_handler
                                          tid txs sytm)
                                       (ktr_app d)
                                       sh ;;
                          ktr ret)
                 (Returnstate (Vint (IntNat.of_nat d)) k m))
    : paco3 (_sim_itree prog) r
            (idx_ret + idx_ndmd)%nat
            (ret <- interp (MWITree.send_handler
                             tid txs sytm)
                          (d <- get_new_demand ;;
                           ktr_app d)
                          sh ;;
             ktr ret)
            (Callstate (Internal f_get_new_demand)
                       [] k m).
  Proof.
    unfold idx_ndmd.
    start_func.
    { econs. }
    ss.

    fw. clear STEP_ENTRY.
    fw. fw. fw.
    { step_fptr_tac. }

    unfold get_new_demand.
    pfold. econs 3.
    { r. ss.
      econs; eauto.
      - ss. econs 2; eauto; ss.
        { intros ? ? OSE. inv OSE; ss. }
        econs 1; eauto.
      - ss.
    }
    { erewrite (MWITree.unfold_interp_vis_sys
                  tid dev_mod).
      2: { simpl_itree_goal.
           simpl_itree_goal.
           ss. }
      unf_resum.
      simpl_itree_goal.
      econs 1.
    }
    { ss. }

    intros d_raw. i. ss.
    inv RET. inv CPROG_AFTER_EVENT; ss.
    inv EVENT.
    existT_elim. subst.
    unf_resum. subst.
    inv MATCH_RETV. existT_elim. subst.
    (* inv SYS_ESTEP. existT_elim. subst. *)
    pose (retz:= Int.signed ret).

    exists 1%nat. left.
    fw_tau (idx_ret + 30)%nat.
    { simpl_itree_goal. ss. }
    upd_lenv.

    fw. fw.
    { econs. eval_comput. ss. }
    upd_lenv.
    rewrite <- (Int.repr_signed ret) in LENV_EQUIV.

    fw. fw.
    { econs.
      - eval_comput. repr_tac0; cycle 1.
        { ss. }
        { r. apply Int.signed_range. }
        fold retz.
        reflexivity.
        (* replace 5 with (Z.of_nat MAX_TIMEOUT) by ss. *)
        (* rewrite Int.repr_signed *)
        (* rewrite <- Nat2Z_inj_ltb. *)
        (* reflexivity. *)
      - rewrite bool_val_of_bool. ss.
    }

    match goal with
    | |- context[ interp _ ?t _ ] =>
      remember t as itr eqn: ITREE
    end.
    symmetry in ITREE.
    simpl_itree_hyp ITREE.
    subst itr.

    fold retz.
    replace (MAX_TIMEOUT <? Z.to_nat retz)%nat with (5 <? retz)%Z.
    2: {
      unfold MAX_TIMEOUT.
      destruct (Z.ltb_spec 5 retz) as [LT | LE].
      - apply Z2Nat.inj_lt in LT; try nia.
        change (Z.to_nat 5) with 5%nat in LT.
        destruct (Nat.ltb_spec 5 (Z.to_nat retz)); ss.
        nia.
      - destruct (Z.ltb_spec retz 0) as [LT_Z | LE_Z].
        + rewrite Coqlib.Z_to_nat_neg by nia.
          destruct (Nat.ltb_spec 5 0); ss. nia.
        + apply Z2Nat.inj_le in LE; try nia.
          destruct (Nat.ltb_spec 5 (Z.to_nat retz)); ss.
          nia.
    }

    destruct (Z.ltb_spec 5 retz).
    { fw.
      { econs.
        - eval_comput. reflexivity.
        - ss.
        - ss.
      }
      ss. rewrite sign_ext_byte_range by ss.
      rewrite call_cont_is_call_cont by ss.

      red_idx idx_ret.
      eapply SIM_RET.
      ss.
    }

    fw.
    { econs.
      - eval_comput.
        repr_tac0; cycle 1.
        { apply Int.signed_range. }
        { ss. }
        fold retz.
        ss.
      - ss.
        instantiate (1:= (retz <? 0)).
        destruct (Z.ltb_spec retz 0); ss.
    }

    destruct (Z.ltb_spec retz 0).
    - rewrite Coqlib.Z_to_nat_neg by nia.
      fw.
      { econs.
        - eval_comput. ss.
        - ss.
        - ss.
      }
      ss.
      unfold IntNat.of_nat.
      rewrite sign_ext_byte_range.
      2: {
        assert (Z.of_nat MAX_TIMEOUT < Byte.max_signed) by ss.
        range_stac.
      }

      rewrite call_cont_is_call_cont by ss.
      red_idx idx_ret.
      eapply SIM_RET; eauto.
      nia.
    - fw.
      { econs.
        - eval_comput. ss.
        - ss.
        - ss.
      }
      ss.
      unfold IntNat.of_nat.
      rewrite sign_ext_byte_range.
      2: {
        fold retz.
        assert (5 < Byte.max_signed) by ss.
        range_stac.
      }

      rewrite call_cont_is_call_cont by ss.
      red_idx idx_ret.

      fold retz.
      replace (Int.repr retz) with (IntNat.of_nat (Z.to_nat retz)).
      2: { unfold IntNat.of_nat.
           rewrite Z2Nat.id by ss.
           ss. }
      eapply SIM_RET; eauto.
      unfold MAX_TIMEOUT.
      replace 5%nat with (Z.to_nat 5) by ss.
      apply Z2Nat.inj_le; try nia.
  Qed.


  (* Local Opaque idx_sync idx_updq. *)
  Local Opaque idx_ndmd.
  Definition idx_udmd: nat := idx_ndmd + 30.

  Lemma sim_update_demand
        (ktr_app: t * bool -> itree appE DevState.t)
        (ktr: list bool * DevState.t -> itree progE unit)
        (m: mem) (k: cont) (idx_ret: nat)
        st b_dst
        txs sytm sh
        (CALL_CONT: is_call_cont k)
        (WF_ST: DevState.wf st)
        (MEM_DST: mem_dst_blk m st b_dst)
        (SIM_RET:
           forall m' (st': t) dmd_new (retb: bool) retv
             (ST': st' = set_demand dmd_new st)
             (WF_ST': wf st')
             (MEM_DST: mem_dst_blk m' st' b_dst)
             (MEM_UNCH: mem_changed_block b_dst m m')
             (RETV: retv = if retb then Vtrue else Vfalse)
           ,
             paco3 (_sim_itree prog) r
                   idx_ret (ret <- interp (MWITree.send_handler
                                            tid txs sytm)
                                         (ktr_app (st', retb))
                                         sh ;;
                            ktr ret)
                   (Returnstate retv k m'))
    : paco3 (_sim_itree prog) r
            (idx_ret + idx_udmd)%nat
            (ret <- interp (MWITree.send_handler
                             tid txs sytm)
                          (ret <- update_demand st ;;
                           ktr_app ret)
                          sh ;;
             ktr ret)
            (Callstate (Internal f_update_demand)
                       [Vptr b_dst Ptrofs.zero] k m).
  Proof.
    unfold idx_udmd.
    start_func.
    { econs. }
    ss.

    hexploit (in_cenv_ilist __dev_state); [sIn|].
    intro CO_DEV_STATE.

    assert (MAX_TIMEOUT_BYTE_RANGE: Z.of_nat MAX_TIMEOUT < Byte.max_signed) by ss.

    fw. clear STEP_ENTRY.
    fw. fw.
    { econs.
      - eval_comput.
        rewrite CO_DEV_STATE. s.
        unfold Coqlib.align, align_attr. s.
        rewrite Ptrofs.add_zero_l.
        repr_tac.

        erewrite Mem.loadbytes_load; cycle 1.
        { apply MEM_DST. }
        { ss. solve_divide. }
        eval_comput.
        rewrite decode_byte.
        rewrite sign_ext_byte_range_u.
        2: { inv WF_ST. s.
             range_stac. }
        rewrite Int_eq_repr_signed; cycle 1.
        { inv WF_ST. s. range_stac. }
        { range_stac. }

        replace 0 with (Z.of_nat O) by ss.
        rewrite Nat2Z_inj_eqb. ss.

      - rewrite bool_val_of_bool. ss.
    }

    unfold update_demand.

    destruct (Nat.eqb_spec (demand st) O)
      as [DMD_Z | DMD_NZ].
    2: { (* ret 0 *)
      fw. fw.
      { econs.
        - eval_comput. reflexivity.
        - ss.
        - ss. }
      rewrite call_cont_is_call_cont by ss. s.

      simpl_itree_interp.
      red_idx idx_ret.
      eapply SIM_RET; eauto.
      - instantiate (1:= demand st).
        destruct st; ss.
      - apply Mem.unchanged_on_refl.
    }
    simpl_itree_interp.

    fw. fw. fw.
    { step_fptr_tac. }

    red_idx (idx_ret + 20 + idx_ndmd)%nat.
    eapply sim_get_new_demand.
    { ss. }

    i.
    fw. upd_lenv.
    fw. fw.
    { econs. eval_comput.
      unfold IntNat.of_nat.
      rewrite sign_ext_byte_range by range_stac.
      reflexivity. }
    upd_lenv.

    fw. fw.
    { econs.
      - eval_comput.
        repr_tac.
        replace 0 with (Z.of_nat O) by ss.
        rewrite <- Nat2Z_inj_ltb. reflexivity.
      - ss. rewrite bool_val_of_bool. ss.
    }

    destruct (Nat.ltb_spec 0 d).
    2: {
      fw. fw.
      { econs.
        - eval_comput. ss.
        - ss.
        - ss. }
      simpl_itree_interp.
      ss. rewrite call_cont_is_call_cont by ss.

      red_idx idx_ret.
      eapply SIM_RET; eauto.
      - instantiate (1:= demand st).
        destruct st; ss.
      - eapply Mem.unchanged_on_refl.
    }

    assert (STORE: exists m',
               Mem.store Mint8signed m b_dst 1
                         (Vint (IntNat.of_nat d)) = Some m').
    { apply inhabited_sig_to_exists.
      econs.
      apply Mem.valid_access_store.
      rr. split; ss.
      2: { apply Z.divide_1_l. }
      ii. apply MEM_DST. nia. }
    des.

    fw. fw.
    { econs.
      - eval_comput.
        rewrite CO_DEV_STATE. s.
        unfold Coqlib.align, align_attr. s.
        rewrite Ptrofs.add_zero_l. ss.
      - eval_comput. ss.
      - ss.
      - eval_comput.
        rewrite sign_ext_byte_range by range_stac.
        repr_tac.
        unfold IntNat.of_nat in STORE.
        eauto.
    }

    fw. fw.
    { econs.
      - eval_comput. ss.
      - ss.
      - ss. }

    red_idx idx_ret.
    simpl_itree_interp.
    ss. rewrite call_cont_is_call_cont by ss.

    eapply SIM_RET; eauto.
    - eapply wf_set_demand. eauto.
    - eapply store_set_demand; eauto.
    - eapply Mem.store_unchanged_on; eauto.
  Qed.


  Definition idx_rund: nat := 30.

  Lemma sim_run_device
        (ktr_app: t -> itree appE DevState.t)
        (ktr: list bool * DevState.t -> itree progE unit)
        (m: mem) (k: cont) (idx_ret: nat)
        st b_dst
        txs sytm sh
        (CALL_CONT: is_call_cont k)
        (WF_ST: DevState.wf st)
        (MEM_DST: mem_dst_blk m st b_dst)
        (SIM_RET:
           forall m' (st': t)
             (WF_ST': wf st')
             (MEM_DST: mem_dst_blk m' st' b_dst)
             (MEM_UNCH: mem_changed_block b_dst m m')
           ,
             paco3 (_sim_itree prog) r
                   idx_ret (ret <- interp (MWITree.send_handler
                                            tid txs sytm)
                                         (ktr_app st')
                                         sh ;;
                            ktr ret)
                   (Returnstate Vundef k m'))
    : paco3 (_sim_itree prog) r
            (idx_ret + idx_rund)%nat
            (ret <- interp (MWITree.send_handler
                             tid txs sytm)
                          (ret <- run_device st ;;
                           ktr_app ret)
                          sh ;;
             ktr ret)
            (Callstate (Internal f_run_device)
                       [Vptr b_dst Ptrofs.zero] k m).
  Proof.
    unfold idx_rund.
    start_func.
    { econs. }
    ss.

    hexploit (in_cenv_ilist __dev_state); [sIn|].
    intro CO_DEV_STATE.

    assert (MAX_TIMEOUT_BYTE_RANGE: Z.of_nat MAX_TIMEOUT < Byte.max_signed) by ss.

    fw. clear STEP_ENTRY.
    fw. fw.
    { econs.
      - eval_comput.
        rewrite CO_DEV_STATE. s.
        unfold Coqlib.align, align_attr. s.
        rewrite Ptrofs.add_zero_l.
        repr_tac.

        erewrite Mem.loadbytes_load; cycle 1.
        { apply MEM_DST. }
        { ss. solve_divide. }
        s.
        rewrite decode_byte.
        rewrite sign_ext_byte_range_u.
        2: { inv WF_ST. s.
             range_stac. }
        rewrite sign_ext_byte_range.
        2: { inv WF_ST. s.
             range_stac. }
        ss.
    }
    upd_lenv.

    fw. fw.
    { econs.
      - eval_comput.
        s. repr_tac0; cycle 1.
        { range_stac. }
        { inv WF_ST. s.
          range_stac. }

        replace 0 with (Z.of_nat O) by ss.
        rewrite <- Nat2Z_inj_ltb. ss.
      - ss. rewrite bool_val_of_bool. ss.
    }

    unfold run_device.

    destruct (Nat.ltb_spec 0 (demand st)).
    2: {
      simpl_itree_interp.
      fw.
      red_idx idx_ret.
      eapply SIM_RET; eauto.
      eapply Mem.unchanged_on_refl.
    }

    fw. fw.
    { step_fptr_tac. }

    pfold. econs 3.
    { r. ss.
      econs; eauto.
      - ss. econs 2; eauto; ss.
        { intros ? ? OSE. inv OSE; ss. }
        econs 2; ss.
      - ss.
    }
    { erewrite (MWITree.unfold_interp_vis_sys
                  tid dev_mod).
      2: { simpl_itree_goal.
           simpl_itree_goal.
           ss. }
      unf_resum.
      simpl_itree_goal.
      econs 1.
    }
    { ss. }

    intros []. i. ss.
    inv RET. inv CPROG_AFTER_EVENT; ss.
    inv EVENT.
    existT_elim. subst.
    unf_resum. subst.
    inv MATCH_RETV.
    (* inv SYS_ESTEP. existT_elim. subst. *)
    rename m' into m.
    exists 1%nat. left.

    fw_tau (idx_ret + 20)%nat.
    { simpl_itree_goal. ss. }

    fw. fw. fw.
    { econs. eval_comput.
      repr_tac0; cycle 1.
      { inv WF_ST. s. range_stac. }
      { range_stac. }
      replace 1 with (Z.of_nat 1) by ss.
      rewrite <- Nat2Z.inj_sub by ss.
      rewrite sign_ext_byte_range.
      2: { inv WF_ST. s. range_stac. }
      ss.
    }
    upd_lenv.

    assert (STORE: exists m',
               Mem.store Mint8signed m b_dst 1
                         (Vint (IntNat.of_nat (demand st - 1))) = Some m').
    { apply inhabited_sig_to_exists.
      econs.
      apply Mem.valid_access_store.
      rr. split; ss.
      2: { apply Z.divide_1_l. }
      ii. apply MEM_DST. nia. }
    des.

    fw. fw.
    { econs.
      - eval_comput.
        rewrite CO_DEV_STATE. s.
        unfold Coqlib.align, align_attr. s.
        rewrite Ptrofs.add_zero_l. ss.
      - eval_comput. ss.
      - ss.
      - eval_comput.
        rewrite sign_ext_byte_range.
        2: { inv WF_ST. s. range_stac. }
        repr_tac.
        unfold IntNat.of_nat in STORE.
        eauto.
    }
    fw.
    simpl_itree_interp.
    red_idx idx_ret.

    eapply SIM_RET.
    - eapply wf_reduce_demand. ss.
    - rewrite reduce_demand_eq.
      rewrite <- Nat.sub_1_r.
      eapply store_set_demand; eauto.
    - eapply Mem.store_unchanged_on; eauto.
  Qed.

  Inductive inv_mw (m: mem) txs sytm sh : Prop :=
    InvMW
      b_sbuf b_sh
      bs_old
      (MEM_CONSTS: mem_consts ge m tid)
      (MEM_SH: mem_sh ge m sh)
      (MEM_TXS: mem_txs ge m txs)
      (MEM_SBUF: mem_sbuf ge m (sytm + period) tid bs_old)

      (RANGE_TXS: IntRange.sint txs)
      (RANGE_SYTM: IntRange.uint64 sytm)
      (RANGE_SYTM2: IntRange.uint64 (sytm + period))

      (FSYMB_SBUF: Genv.find_symbol ge _send_buf = Some b_sbuf)
      (FSYMB_SH: Genv.find_symbol ge _send_hist = Some b_sh)
  .

  Lemma inv_mw_unch
        m txs sytm sh m'
        (INV: inv_mw m txs sytm sh)
        (MEM_UNCH: Mem.unchanged_on
                     (blocks_of ge main_gvar_ids) m m')
    : inv_mw m' txs sytm sh.
  Proof.
    inv INV.
    econs; eauto.
    - eapply mem_consts_unch; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      clear. unfold blocks_of.
      intros b ofs [id [IN1 FSYMB]] _. ss.
      des; ss;
        (subst; esplits; try apply FSYMB; sIn).
    - eapply mem_sh_unch; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      clear. unfold blocks_of.
      intros b ofs FSYMB _. ss.
      subst; esplits; try apply FSYMB; sIn.
    - eapply mem_txs_unch; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      clear. unfold blocks_of.
      intros b ofs FSYMB _. ss.
      subst; esplits; try apply FSYMB; sIn.
    - eapply mem_sbuf_unch; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      clear. unfold blocks_of.
      intros b ofs FSYMB _. ss.
      subst; esplits; try apply FSYMB; sIn.
  Qed.


  Local Opaque idx_psend idx_sync idx_udmd idx_rund.
  Definition idx_jobdev: nat := idx_psend + idx_sync + idx_udmd +
                              idx_rund + 50.

  Lemma sim_job_device
        (ktr: list bool * DevState.t -> itree progE unit)
        (m: mem) (k: cont) (idx_ret: nat)
        st (* b_dst *)
        txs sh sytm
        inb b_dst b_mst ofs_inb
        (CALL_CONT: is_call_cont k)
        (INV_MW: inv_mw m txs sytm sh)
        (INV_DEV: inv_dev ge st m)
        (FSYMB_DST: Genv.find_symbol ge _state = Some b_dst)
        (FSYMB_MST: Genv.find_symbol ge _mstore = Some b_mst)
        (MEM_INB: Mem_inbox m b_mst ofs_inb inb)
        (RANGE_OFS_INB: 0 <= ofs_inb <= 4 + inb_sz)

        (SIM_RET:
           forall m' (st': t) sh'
             (INV_MW: inv_mw m' txs sytm sh')
             (INV_DEV: inv_dev ge st' m')
             (MEM_UNCH: Mem.unchanged_on (blocks_of ge app_unch_gvar_ids) m m')
           ,
             paco3 (_sim_itree prog) r
                   idx_ret (ktr (sh', st'))
                   (Returnstate Vundef k m'))
    : paco3 (_sim_itree prog) r
            (idx_ret + idx_jobdev)%nat
            (ret <- interp (MWITree.send_handler
                             tid txs sytm)
                          (job_device_itree (Z.of_nat sytm) st inb)
                          sh ;;
             ktr ret)
            (Callstate (Internal f_job_device)
                       [Vint (IntNat.of_nat tid);
                       Vptr b_dst Ptrofs.zero;
                       Vlong (IntNat.of_nat64 sytm);
                       Vptr b_mst (Ptrofs.repr ofs_inb)]
                       k m).
  Proof.
    unfold idx_jobdev.
    start_func.
    { econs. }

    (* hexploit (in_cenv_ilist _inbox_t); [sIn|]. *)
    (* intro CO_INBOX. *)
    (* hexploit (in_cenv_ilist _msg_entry_t); [sIn|]. *)
    (* intro CO_MENTRY. *)
    hexploit (in_cenv_ilist __dev_state); [sIn|].
    intro CO_DEV_STATE.
    r in INV_DEV. des.
    hexploit (in_gvar_ids _rel_msg); [sIn|].
    intros (b_rel & FSYMB_REL).
    hexploit (in_gvar_ids _acq_msg); [sIn|].
    intros (b_acq & FSYMB_ACQ).

    fw. fw. fw.
    { econs.
      - eval_comput.
        rewrite CO_DEV_STATE. s.
        unfold_align.
        rewrite Ptrofs.add_zero.
        r in MEM_DST.
        hexploit MEM_DST; eauto.
        clear MEM_DST. intro MEM_DST.
        (* rewrite MEM_DST. *)

        erewrite loadbytes_load_byte; cycle 1.
        { eapply MEM_DST. }
        { destruct (owner_status st); ss.
          destruct b; ss. }
        eval_comput.
        repr_tac0; cycle 1.
        { destruct (owner_status st); ss.
          destruct b; ss. }
        { ss. }

        ss.
      - rewrite bool_val_of_bool. ss.
    }
    unfold job_device_itree.

    destruct st as [own dmd]. ss.
    destruct own as [is_owner|].
    2: { (* Uninit *)
      s.

      assert (STORE: exists m',
                 Mem.store Mint8signed m b_dst 0
                           (Vint (IntNat.of_nat 2)) = Some m').
      { apply inhabited_sig_to_exists.
        econs.
        apply Mem.valid_access_store.
        rr. split; ss.
        2: { apply Z.divide_1_l. }
        ii. apply MEM_DST; eauto. nia. }
      des.

      fw. fw.
      { econs.
        - eval_comput.
          rewrite CO_DEV_STATE. s.
          unfold_align.
          rewrite Ptrofs.add_zero. ss.
        - eval_comput. ss.
        - s. ss.
        - eval_comput.
          rewrite sign_ext_byte_range by ss.
          eauto.
      }

      fw. fw. fw.
      { step_fptr_tac.
        - rewrite FSYMB_REL. s.
          rewrite sign_ext_byte_range by ss.
          reflexivity.
      }

      hexploit store_unchanged_on'; eauto. intro UNCH.
      eapply inv_mw_unch in INV_MW.
      2: { eapply Mem.unchanged_on_implies; eauto.
           unfold mem_range. unfold blocks_of.
           clear - FSYMB_DST.
           ii. des. subst. ss.
           revert FSYMB_DST.
           des; subst; ss;
             eapply global_addresses_distinct'; eauto; ss.
      }
      inv INV_MW.
      red_idx (idx_psend + (idx_ret + 10))%nat.

      erewrite (MWITree.unfold_interp_vis_send tid dev_mod).
      2: { simpl_itree_goal. ss. }
      simpl_itree_goal. s.

      change (f_pals_send (Z.of_nat 1) (Z.of_nat 16) (Z.of_nat 8)) with
          (f_pals_send (Z.of_nat msg_size_k) (Z.of_nat max_num_tasks) (Z.of_nat max_num_mcasts)).

      eapply sim_pals_send; eauto; ss.
      { eapply Genv.global_addresses_distinct; eauto. ss. }
      { eapply Genv.global_addresses_distinct; eauto. ss. }
      { assert (b_rel <> b_dst).
        { eapply Genv.global_addresses_distinct; eauto. ss. }
        eapply Mem.loadbytes_unchanged_on; eauto.
        unfold mem_range. ii. des. ss. }
      rename m' into m1.
      i. rename m' into m_f.
      fw_tau (idx_ret + 10)%nat.
      { simpl_itree_goal. ss. }

      fw. fw. fw.
      { step_fptr_tac. }

      pfold. econs 3.
      { s. econs; eauto; s.
        - econs 2; eauto; ss.
          { intros ? ? OSE. inv OSE; ss. }
          econs 2; ss.
        - ss. }
      { econs 1. }
      { erewrite (MWITree.unfold_interp_vis_sys tid dev_mod).
        2: { simpl_itree_goal. ss. }
        simpl_itree_goal. ss. }

      intros []. i.
      inv RET. inv CPROG_AFTER_EVENT; ss.
      inv EVENT. existT_elim.
      unf_resum. subst.
      (* inv SYS_ESTEP. existT_elim. subst. *)
      inv MATCH_RETV.
      rename m' into m_f.

      exists (idx_ret + 5)%nat.
      left.
      fw. fw.
      simpl_itree_goal.
      fw_tau idx_ret.
      erewrite (MWITree.unfold_interp_ret _ dev_mod) by ss.
      simpl_itree_goal.

      rewrite call_cont_is_call_cont by ss.
      (* red_idx idx_ret. *)

      assert (UNCH_EXC: mem_unchanged_except (blocks_of ge [_send_buf; _send_hist; _state]) m m_f).
      { eapply Mem.unchanged_on_trans; eauto.
        - eapply Mem.unchanged_on_implies; try apply UNCH.
          unfold blocks_of. unfold mem_range.
          intros b ofs C _ [? ?].
          apply C. clear C.
          clarify. ss. esplits; eauto.
        - eapply Mem.unchanged_on_implies; try apply MEM_UNCH.
          unfold blocks_of.
          intros b ofs C _ [? ?].
          apply C. clear C.
          des; ss.
          des; clarify.
          + exists _send_buf; eauto.
          + exists _send_hist; eauto.
      }

      eapply SIM_RET.
      - econs; eauto.
      - assert (UNCH_AUX: Mem.unchanged_on (blocks_of ge [_acq_msg; _rel_msg]) m m_f).
        { i. eapply unchanged_on_disjoint_ids; eauto.
          r. ii. des; ss. des; subst; ss. }

        r. splits.
        + inv DST_WF.
          econs; eauto.
        + cut (mem_dst ge m1 (set_owner_status false (mk None dmd))).
          { intro MEM_DST_P.
            eapply mem_dst_unch; eauto.
            eapply Mem.unchanged_on_implies; eauto.
            unfold blocks_of. clear.
            ii. des; ss.
            cut (b <> b).
            { ss. }
            eapply (@Genv.global_addresses_distinct
                      _ _ ge id id0); eauto.
            des; subst; ss.
          }

          ii. clarify.
          eapply store_set_owner_status; eauto.
        + ii. clarify.
          eapply Mem.loadbytes_unchanged_on; eauto.
          ii. unfold blocks_of.
          esplits; eauto. sIn.
        + ii. clarify.
          eapply Mem.loadbytes_unchanged_on; eauto.
          ii. unfold blocks_of.
          esplits; eauto. sIn.

      - eapply unchanged_on_disjoint_ids; eauto.
        clear.
        ii. ss. des; subst; ss.
    }

    (* initialized state *)
    (* simpl_itree_interp. s. *)
    s.
    replace ((if is_owner then 1 else 2) =? 0) with false.
    2: { destruct is_owner; ss. }

    fw. fw. fw.
    { step_fptr_tac. }

    red_idx (idx_ret + idx_psend + idx_udmd +
             idx_rund + 40 + idx_sync)%nat.
    eapply sim_sync_dev_state; eauto.
    { eapply Genv.global_addresses_distinct;
        cycle 1; eauto. ss. }
    { ss. }

    clear MEM_DST. i.
    fw. fw. fw. fw. fw.
    { step_fptr_tac. }

    red_idx (idx_ret + idx_psend +
             idx_rund + 30 + idx_udmd)%nat.
    eapply sim_update_demand.
    { ss. }
    { eapply wf_sync_dev_state. ss. }
    { rewrite <- ST'. ss. }

    renames m' MEM_CH_BLK into m1 MEM_CH_BLK1.
    renames st' ST' into st1 ST1.
    clear MEM_DST. i.

    fw. upd_lenv.
    fw. fw.
    { econs. eval_comput. ss. }
    upd_lenv.

    fw. fw. fw.
    { econs.
      - eval_comput.
        rewrite CO_DEV_STATE. s.
        unfold_align. s.
        rewrite Ptrofs.add_zero.
        erewrite loadbytes_load_byte; cycle 1.
        { eapply MEM_DST. }
        { destruct (owner_status st') as [[]|] ; ss. }

        eval_comput.
        repr_tac0; cycle 1.
        { destruct (owner_status st') as [[]|] ; ss. }
        { range_stac. }
        reflexivity.
      - rewrite bool_val_of_bool. ss.
    }
    renames st' ST' WF_ST' into st2 ST2 WF_ST2.
    destruct st2 as [own2 dmd2]. s.
    destruct own2 as [is_owner2 |].
    2: { exfalso.
         clear - ST2.
         unfold set_demand, sync_dev_state in *. ss.
         desf. }

    assert (MAX_TIMEOUT_BYTE_RANGE: Z.of_nat MAX_TIMEOUT < Byte.max_signed) by ss.

    destruct is_owner2.
    - (* this is the owner *)
      s.
      fw. fw.
      { step_fptr_tac. }

      red_idx (idx_ret + idx_psend + 20 + idx_rund)%nat.
      eapply sim_run_device; eauto.
      { ss. }
      renames m' MEM_UNCH into m2 MEM_UNCH2.
      clear MEM_DST. i.
      renames st' WF_ST' into st3 WF_ST3.

      destruct st3 as [own3 dmd3].

      fw. fw. fw.
      { econs.
        - eval_comput.
          rewrite CO_DEV_STATE. s.
          unfold_align.
          rewrite Ptrofs.add_zero_l.
          erewrite loadbytes_load_byte; cycle 1.
          { apply MEM_DST. }
          { ss. inv WF_ST3.
            range_stac. }
          eval_comput.
          repr_tac0; cycle 1.
          { inv WF_ST3. range_stac. }
          { range_stac. }

          replace 0 with (Z.of_nat O) by ss.
          rewrite Nat2Z_inj_eqb. ss.
        - rewrite bool_val_of_bool. ss.
      }

      assert (UNCH_03: mem_unchanged_except (blocks_of ge [_state]) m m').
      { eapply Mem.unchanged_on_trans.
        { eapply Mem.unchanged_on_implies; try apply MEM_CH_BLK1.
          unfold blocks_of.
          intros b _ C _ BEQ. subst.
          apply C. clear C. ss.
          esplits; eauto. }
        eapply Mem.unchanged_on_trans.
        { eapply Mem.unchanged_on_implies; try apply MEM_UNCH2.
          unfold blocks_of.
          intros b _ C _ BEQ. subst.
          apply C. clear C. ss.
          esplits; eauto. }
        eapply Mem.unchanged_on_implies; eauto.
        unfold blocks_of.
        intros b _ C _ BEQ. subst.
        apply C. clear C. ss.
        esplits; eauto.
      }

      destruct (Nat.eqb_spec dmd3 0).
      2: {
        fw. fw.
        { step_fptr_tac. }

        pfold. econs 3.
        { s. econs; eauto; s.
          - econs 2; eauto; ss.
            { intros ? ? OSC. inv OSC; ss. }
            econs 2; ss.
          - ss. }
        { econs 1. }
        { erewrite (MWITree.unfold_interp_vis_sys tid dev_mod).
          2: { simpl_itree_goal. ss. }
          simpl_itree_goal. ss. }

        intros []. i.
        inv RET. inv CPROG_AFTER_EVENT; ss.
        inv EVENT. existT_elim.
        unf_resum. subst.
        inv MATCH_RETV.
        rename m'0 into m_f.

        exists (idx_ret + 5)%nat.
        left.
        fw.
        simpl_itree_goal.
        fw_tau idx_ret.
        erewrite (MWITree.unfold_interp_ret _ dev_mod) by ss.
        simpl_itree_goal.

        eapply SIM_RET.
        - eapply inv_mw_unch; try apply INV_MW.
          eapply unchanged_on_disjoint_ids; eauto.
          clear.
          ii. ss. des; subst; ss.
        - r. esplits; ss.
          + ii. clarify.
          + eapply mem_acq_unch; eauto.
            eapply unchanged_on_disjoint_ids; eauto.
            clear.
            ii. ss. des; subst; ss.
          + eapply mem_rel_unch; eauto.
            eapply unchanged_on_disjoint_ids; eauto.
            clear.
            ii. ss. des; subst; ss.
        - eapply unchanged_on_disjoint_ids; eauto.
          clear.
          ii. ss. des; subst; ss.
      }

      (* release resource lock *)
      renames m' MEM_UNCH into m3 MEM_UNCH3.

      assert (STORE: exists m4,
                 Mem.store Mint8signed m3 b_dst 0
                           (Vint (IntNat.of_nat 2)) = Some m4).
      { apply inhabited_sig_to_exists.
        econs.
        apply Mem.valid_access_store.
        rr. split; ss.
        2: { apply Z.divide_1_l. }
        ii. apply MEM_DST; eauto. nia. }
      des.

      fw. fw.
      { econs.
        - eval_comput.
          rewrite CO_DEV_STATE. s.
          unfold_align. rewrite Ptrofs.add_zero. ss.
        - eval_comput. ss.
        - s. ss.
        - eval_comput.
          rewrite sign_ext_byte_range by range_stac.
          eauto.
      }

      fw. fw.
      { step_fptr_tac.
        rewrite FSYMB_REL.
        rewrite sign_ext_byte_range by range_stac.
        reflexivity. }

      red_idx (idx_psend + (idx_ret + 10))%nat.

      erewrite (MWITree.unfold_interp_vis_send tid dev_mod).
      2: { simpl_itree_goal. ss. }
      simpl_itree_goal. s.

      change (f_pals_send (Z.of_nat 1) (Z.of_nat 16) (Z.of_nat 8)) with
          (f_pals_send (Z.of_nat msg_size_k) (Z.of_nat max_num_tasks) (Z.of_nat max_num_mcasts)).

      assert (UNCH04: mem_unchanged_except (blocks_of ge [_state]) m m4).
      { eapply Mem.unchanged_on_trans; try apply UNCH_03.
        eapply Mem.store_unchanged_on; eauto.
        unfold blocks_of. s.
        intros i RI C.
        apply C. clear C.
        esplits; eauto. }

      assert (INV_MW4: inv_mw m4 txs sytm sh).
      { eapply inv_mw_unch; eauto.
        eapply unchanged_on_disjoint_ids; eauto.
        clear. ii. ss. des; clarify. }

      eapply (mem_rel_unch_diffblk ge m m4) in MEM_REL; cycle 1.
      { instantiate (1:= b_dst).
        eapply Mem.unchanged_on_implies; eauto.
        unfold blocks_of. ss. ii. des; clarify. }
      { eapply global_addresses_distinct'; eauto. ss. }
      eapply (mem_acq_unch_diffblk ge m m4) in MEM_ACQ; cycle 1.
      { instantiate (1:= b_dst).
        eapply Mem.unchanged_on_implies; eauto.
        unfold blocks_of. ss. ii. des; clarify. }
      { eapply global_addresses_distinct'; eauto. ss. }

      inv INV_MW4.
      eapply sim_pals_send; eauto; ss.
      { eapply Genv.global_addresses_distinct; eauto. ss. }
      { eapply Genv.global_addresses_distinct; eauto. ss. }

      clear MEM_CONSTS MEM_SH MEM_TXS MEM_SBUF. i.
      simpl_itree_goal.

      fw_tau (idx_ret + 10)%nat.
      fw. fw.
      { step_fptr_tac. }

      pfold. econs 3.
      { s. econs; eauto; s.
        - econs 2; eauto; ss.
          { intros ? ? OSC. inv OSC; ss. }
          econs 2; ss.
        - ss. }
      { econs 1. }
      { erewrite (MWITree.unfold_interp_vis_sys tid dev_mod).
        2: { simpl_itree_goal. ss. }
        simpl_itree_goal. ss. }

      intros []. i.
      inv RET. inv CPROG_AFTER_EVENT; ss.
      inv EVENT. existT_elim.
      unf_resum. subst.
      (* inv SYS_ESTEP. existT_elim. subst. *)
      inv MATCH_RETV.
      rename m'0 into m_f.

      exists (idx_ret + 5)%nat.
      left.
      fw.
      simpl_itree_goal.
      fw_tau idx_ret.
      erewrite (MWITree.unfold_interp_ret _ dev_mod) by ss.
      simpl_itree_goal.

      eapply SIM_RET.
      + econs; eauto.
      + r.
        esplits.
        * econs. nia.
        * eapply mem_dst_unch.
          2: { eapply unchanged_on_disjoint_ids; eauto.
               clear. ii. ss. des; clarify. }
          ii. clarify.
          eapply store_set_owner_status in MEM_DST; eauto.
        * eapply mem_acq_unch; eauto.
          eapply unchanged_on_disjoint_ids; eauto.
          clear. ii. ss. des; clarify.
        * eapply mem_rel_unch; eauto.
          eapply unchanged_on_disjoint_ids; eauto.
          clear. ii. ss. des; clarify.
      + eapply Mem.unchanged_on_trans with (m2:= m4).
        * eapply Mem.unchanged_on_implies; eauto.
          unfold blocks_of.
          ii. des. ss.
          cut (b <> b).
          { ss. }
          eapply (@Genv.global_addresses_distinct
                    _ _ ge id id0); ss.
          des; clarify.
        * eapply unchanged_on_disjoint_ids; eauto.
          clear. ii. ss. des; clarify.

    - (* send ACQ *)
      s.
      fw.
      { econs.
        - eval_comput.
          instantiate (1:= retv).
          subst retv. destruct retb; ss.
        - subst retv. ss.
          instantiate (1:= retb).
          destruct retb; ss.
      }

      assert (UNCH_TOT: mem_unchanged_except
                          (blocks_of ge [_state]) m m').
      { eapply Mem.unchanged_on_trans with (m2 := m1).
        - eapply Mem.unchanged_on_implies; eauto.
          unfold blocks_of.
          intros b _ C _ AUX.
          apply C. clear C. ss. subst.
          esplits; eauto.
        - eapply Mem.unchanged_on_implies; eauto.
          unfold blocks_of.
          intros b _ C _ AUX.
          apply C. clear C. ss. subst.
          esplits; eauto.
      }

      destruct retb.
      2: {
        simpl_itree_interp.
        fw. fw.
        { step_fptr_tac. }

        pfold. econs 3.
        { s. econs; eauto; s.
          - econs 2; eauto; ss.
            { intros ? ? OSC. inv OSC; ss. }
            econs 2; ss.
          - ss. }
        { econs 1. }
        { erewrite (MWITree.unfold_interp_vis_sys tid dev_mod).
          2: { simpl_itree_goal. ss. }
          simpl_itree_goal. ss. }

        intros []. i.
        inv RET. inv CPROG_AFTER_EVENT; ss.
        inv EVENT. existT_elim.
        unf_resum. subst.
        (* inv SYS_ESTEP. existT_elim. subst. *)
        inv MATCH_RETV.
        rename m'0 into m_f.

        exists (idx_ret + 5)%nat.
        left.
        fw.
        simpl_itree_goal.
        fw_tau idx_ret.
        erewrite (MWITree.unfold_interp_ret _ dev_mod) by ss.
        simpl_itree_goal.

        eapply SIM_RET.
        - eapply inv_mw_unch; eauto.
          eapply unchanged_on_disjoint_ids; eauto.
          clear. ii. ss. des; clarify.
        - r. esplits; ss.
          * ii. clarify.
          * eapply mem_acq_unch; eauto.
            eapply unchanged_on_disjoint_ids; eauto.
            clear. ii. ss. des; clarify.
          * eapply mem_rel_unch; eauto.
            eapply unchanged_on_disjoint_ids; eauto.
            clear. ii. ss. des; clarify.
        - eapply unchanged_on_disjoint_ids; eauto.
          clear. ii. ss. des; clarify.
      }

      fw.
      { step_fptr_tac.
        rewrite FSYMB_ACQ.
        rewrite sign_ext_byte_range by range_stac.
        reflexivity. }

      red_idx (idx_psend + (idx_ret + 10))%nat.

      erewrite (MWITree.unfold_interp_vis_send tid dev_mod).
      2: { simpl_itree_goal. ss. }
      simpl_itree_goal. s.

      change (f_pals_send (Z.of_nat 1) (Z.of_nat 16) (Z.of_nat 8)) with
          (f_pals_send (Z.of_nat msg_size_k) (Z.of_nat max_num_tasks) (Z.of_nat max_num_mcasts)).

      assert (INV_MW': inv_mw m' txs sytm sh).
      { eapply inv_mw_unch; eauto.
        eapply unchanged_on_disjoint_ids; eauto.
        clear. ii. ss. des; clarify. }

      eapply (mem_rel_unch_diffblk ge m m') in MEM_REL; cycle 1.
      { instantiate (1:= b_dst).
        eapply Mem.unchanged_on_implies; eauto.
        unfold blocks_of. ss. ii. des; clarify. }
      { eapply global_addresses_distinct'; eauto. ss. }
      eapply (mem_acq_unch_diffblk ge m m') in MEM_ACQ; cycle 1.
      { instantiate (1:= b_dst).
        eapply Mem.unchanged_on_implies; eauto.
        unfold blocks_of. ss. ii. des; clarify. }
      { eapply global_addresses_distinct'; eauto. ss. }

      inv INV_MW'.
      eapply sim_pals_send; eauto; ss.
      { eapply Genv.global_addresses_distinct; eauto. ss. }
      { eapply Genv.global_addresses_distinct; eauto. ss. }
      renames m' MEM_UNCH into m2 MEM_UNCH2.

      clear MEM_CONSTS MEM_SH MEM_TXS MEM_SBUF. i.
      simpl_itree_goal.

      fw_tau (idx_ret + 10)%nat.
      fw. fw.
      { step_fptr_tac. }

      pfold. econs 3.
      { s. econs; eauto; s.
        - econs 2; eauto; ss.
          { intros ? ? OSC. inv OSC; ss. }
          econs 2; ss.
        - ss. }
      { econs 1. }
      { erewrite (MWITree.unfold_interp_vis_sys tid dev_mod).
        2: { simpl_itree_goal. ss. }
        simpl_itree_goal. ss. }

      intros []. i.
      inv RET. inv CPROG_AFTER_EVENT; ss.
      inv EVENT. existT_elim.
      unf_resum. subst.
      (* inv SYS_ESTEP. existT_elim. subst. *)
      inv MATCH_RETV.
      rename m'0 into m_f.

      exists (idx_ret + 5)%nat.
      left.
      fw.
      simpl_itree_goal.
      fw_tau idx_ret.
      erewrite (MWITree.unfold_interp_ret _ dev_mod) by ss.
      simpl_itree_goal.

      eapply SIM_RET.
      + econs; eauto.
      + r. esplits; ss.
        * eapply mem_dst_unch; eauto.
          { ii. clarify. eauto. }
          eapply unchanged_on_disjoint_ids; eauto.
          clear. ii. ss. des; clarify.
        * eapply mem_acq_unch; eauto.
          eapply unchanged_on_disjoint_ids; eauto.
          clear. ii. ss. des; clarify.
        * eapply mem_rel_unch; eauto.
          eapply unchanged_on_disjoint_ids; eauto.
          clear. ii. ss. des; clarify.
      + eapply Mem.unchanged_on_trans.
        * eapply unchanged_on_disjoint_ids; eauto.
          clear. ii. ss. des; clarify.
        * eapply unchanged_on_disjoint_ids; eauto.
          clear. ii. ss. des; clarify.
  Qed.


  Local Opaque idx_jobdev.
  Definition idx_dev : nat := idx_jobdev + 10.
  (* idx_job_ctrl + 10. *)


  (* Local Opaque idx_job_ctrl. *)

  Lemma sim_job_func_dev
    : forall (b_mst : block)
        (txs idx' : nat) (ast : DevState.t)
        (ki : list bool * DevState.t -> itree progE unit)
        (m : mem) (kp : cont) (sytm : nat) (cflg : bool)
        (ofsc ofsn : Z) (inbc inbn : list (bytes?))
        (* (sh : list bool) *) (mcont : bytes)
        (CALL_CONT: is_call_cont kp)
        (RANGE_SYTM: IntRange.uint64 sytm)
        (RANGE_NXT_SYTM: IntRange.uint64 (sytm + period))
        (RANGE_TXS: IntRange.sint txs)
        (INV_APP: inv_dev ge ast m)
        (FSYMB_MST: Genv.find_symbol ge _mstore = Some b_mst)
        (MEM_CONSTS: mem_consts ge m tid)
        (MEM_SBUF: mem_sbuf ge m (sytm + RTSysEnv.period) tid mcont)
        (MEM_MSTORE: mem_mstore ge m cflg ofsc ofsn inbc inbn)
        (MEM_SH: mem_sh ge m (repeat false num_tasks))
        (MEM_TXS: mem_txs ge m txs)
        (SIM_RET: forall (sh' : list bool) (ast' : DevState.t)
                    (m' : mem) (mcont' : bytes)
                    (MEM_UNCH: Mem.unchanged_on (blocks_of ge app_unch_gvar_ids) m m')
                    (MEM_SH: mem_sh ge m' sh')
                    (MEM_SBUF: mem_sbuf ge m' (sytm + RTSysEnv.period) tid mcont')
                    (INV_APP: inv_dev ge ast' m'),
            paco3 (_sim_itree prog) r
                  idx' (ki (sh', ast')) (Returnstate Vundef kp m'))
    ,
      paco3 (_sim_itree prog) r (idx' + idx_dev)%nat
            (` ret : list bool * DevState.t <-
                     MWITree.interp_send
                       tid dev_mod txs sytm
                       (repeat false num_tasks) ast inbc;;
                     ki ret)
            (Callstate (Internal f_job)
                       [Vlong (IntNat.of_nat64 sytm);
                       Vptr b_mst (Ptrofs.repr ofsc)] kp m)
  .
  Proof.
    (* pose proof (genv_props_ctrl tid) as GENV_PROPS. i. *)
    (* rewrite <- CPROG_EQ in *. i. *)
    i. unfold idx_dev.
    start_func.
    { econs. }

    (* pose proof cprog_opaque as CPROG_EQ. des. *)
    (* guardH CPROG_EQ. *)
    (* subst prog. subst ge. *)
    (* rewrite <- CPROG_EQ in *. *)

    fw. clear STEP_ENTRY.

    hexploit (in_gvar_ids _TASK_ID); [sIn|].
    intros (b_tid & FSYMB_TID).
    hexploit (in_gvar_ids _state); [sIn|].
    intros (b_dst & FSYMB_DST).

    fw.
    { step_fptr_tac.
      rewrite FSYMB_DST.
      rewrite FSYMB_TID.
      erewrite mem_consts_task_id; eauto.
    }

    red_idx (idx' + 5 + idx_jobdev)%nat.
    unfold MWITree.interp_send. s.

    replace (Int.sign_ext 8 (IntNat.of_nat tid)) with
        (IntNat.of_nat tid).
    2: { unfold IntNat.of_nat.
         rewrite sign_ext_byte_range.
         2: { pose proof range_num_tasks.
              range_stac. }
         ss.
    }

    hexploit (in_gvar_ids _send_hist); [sIn|].
    intros (b_sh & FSYMB_SH).
    hexploit (in_gvar_ids _send_buf); [sIn|].
    intros (b_sbuf & FSYMB_SBUF).

    unfold dev_job.
    eapply sim_job_device; eauto; ss.
    { econs; eauto. }
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

    i.
    fw. fw.

    red_idx idx'.
    inv INV_MW.
    eapply SIM_RET; eauto.
  Qed.

End VERIF_FUNC.


Section SIM_APP_DEV.
  Variable tid: Tid.
  (* Hypothesis DEV_TASK_ID: (tid = 3 \/ tid = 4 \/ tid = 5)%nat. *)
  Hypothesis DEV_TASK_ID: (tid < num_tasks)%nat.

  Program Definition SimApp_dev
    : SimApp tid (prog_dev (Z.of_nat tid)) dev_mod :=
    {| app_gvar_ilist := dev_gvar_ilist ;
       app_gfun_ilist := dev_gfun_ilist ;
       app_cenv_ilist := dev_cenv_ilist ;

       inv_app := inv_dev ;
       job_func := f_job ;
       idx_job := idx_dev;
       sim_job_func := _ ;
    |}.
  Next Obligation.
    ss. unfold main_gvar_ids.
    r. intros x y X_IN Y_IN.
    r in Y_IN. des; ss.
    - des; clarify.
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
    unfold num_tasks. ss.
  Qed.
  Next Obligation.
    eapply inv_dev_dep_app_blocks; eauto.
  Qed.
  Next Obligation.
    (* rewrite <- CPROG_EQ in *. s. *)
    apply (inv_dev_init tid); ss.
  Qed.
  Next Obligation.
    assert (CPROG_EQ: exists cprog, cprog = prog_dev (Z.of_nat tid)).
    { esplits; eauto. }
    des.
    pose proof (genv_props_dev tid) as GENV_PROPS.
    rewrite <- CPROG_EQ in *.
    clear CPROG_EQ.

    eapply (sim_job_func_dev tid cprog); eauto.
  Qed.

End SIM_APP_DEV.


Program Definition task_dev1
  : PALSTask.t :=
  {| PALSTask.tid := 3 ;
     PALSTask.cprog_app := dev.prog 3 ;
     PALSTask.cprog_tot := prog_dev 3 ;
     PALSTask.app_mod := dev_mod ;
     PALSTask.sim_app := SimApp_dev 3 _ ;
  |}.
Next Obligation.
  unfold num_tasks. ss. nia.
Qed.
Next Obligation.
  apply prog_dev_linked.
Qed.
Next Obligation.
  apply prog_dev_defs_norep.
Qed.
Next Obligation.
  replace 3 with (Z.of_nat 3) by ss.
  apply prog_dev_gvs_ok. ss.
Qed.
Next Obligation.
  replace 3 with (Z.of_nat 3) by ss.
  apply prog_dev_gfs_ok. ss.
Qed.
Next Obligation.
  replace 3 with (Z.of_nat 3) by ss.
  apply prog_dev_cenvs_ok. ss.
Qed.
Next Obligation.
  apply prog_dev_init_mem_ok.
Qed.

Program Definition task_dev2
  : PALSTask.t :=
  {| PALSTask.tid := 4 ;
     PALSTask.cprog_app := dev.prog 4 ;
     PALSTask.cprog_tot := prog_dev 4 ;
     PALSTask.app_mod := dev_mod ;
     PALSTask.sim_app := SimApp_dev 4 _ ;
  |}.
Next Obligation.
  unfold num_tasks. ss. nia.
Qed.
Next Obligation.
  apply prog_dev_linked.
Qed.
Next Obligation.
  apply prog_dev_defs_norep.
Qed.
Next Obligation.
  replace 4 with (Z.of_nat 4) by ss.
  apply prog_dev_gvs_ok. ss.
Qed.
Next Obligation.
  replace 4 with (Z.of_nat 4) by ss.
  apply prog_dev_gfs_ok. ss.
Qed.
Next Obligation.
  replace 4 with (Z.of_nat 4) by ss.
  apply prog_dev_cenvs_ok. ss.
Qed.
Next Obligation.
  apply prog_dev_init_mem_ok.
Qed.


Program Definition task_dev3
  : PALSTask.t :=
  {| PALSTask.tid := 5 ;
     PALSTask.cprog_app := dev.prog 5 ;
     PALSTask.cprog_tot := prog_dev 5 ;
     PALSTask.app_mod := dev_mod ;
     PALSTask.sim_app := SimApp_dev 5 _ ;
  |}.
Next Obligation.
  unfold num_tasks. ss.
Qed.
Next Obligation.
  apply prog_dev_linked.
Qed.
Next Obligation.
  apply prog_dev_defs_norep.
Qed.
Next Obligation.
  replace 5 with (Z.of_nat 5) by ss.
  apply prog_dev_gvs_ok. ss.
Qed.
Next Obligation.
  replace 5 with (Z.of_nat 5) by ss.
  apply prog_dev_gfs_ok. ss.
Qed.
Next Obligation.
  replace 5 with (Z.of_nat 5) by ss.
  apply prog_dev_cenvs_ok. ss.
Qed.
Next Obligation.
  apply prog_dev_init_mem_ok.
Qed.
