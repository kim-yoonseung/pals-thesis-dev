From ITree Require Import ITree.
From compcert Require Import Maps AST Values Memory Globalenvs Ctypes.
From compcert Require Coqlib Clight Clightdefs.
From Paco Require Import paco.

Require Import sflib.
Require Import Axioms StdlibExt IntegersExt ITreeTac.

Require Import SysSem.
Require Import IPModel DiscreteTimeModel IntByteModel.
Require Import OSNodes.
Require Import ProgSem CProgEventSem.
Require Import ProgSim CProgSimLemmas.
Require Import RTSysEnv MWITree.
Require Import NWSysModel.
Require Import SyncSysModel.

Require Import config_prm main_prm SystemProgs.
Require Import VerifProgBase VerifInitBase.

Require Import Arith ZArith Bool.
Require Import String List Lia.

Import Clight Clightdefs.
Import ITreeNotations.

Set Nested Proofs Allowed.

Local Transparent Archi.ptr64.
Local Opaque Int64.max_unsigned.
Local Opaque Genv.globalenv.

Arguments app: simpl nomatch. (* genv_props *)
Arguments Nat.ltb: simpl nomatch.


Section VERIF_INIT.
  Context `{SimApp}.

  Let prog: Prog.t := prog_of_clight cprog.
  Let ge := Clight.globalenv cprog.

  Context `{ genv_props
               ge
               (main_gvar_ilist tid ++ app_gvar_ilist)
               (main_gfun_ilist ++ app_gfun_ilist)
               (main_cenv_ilist ++ app_cenv_ilist) }.

  Notation sim := (paco3 (_sim_itree _)).

  (* Variable ast_i: astate_t. *)
  Hypothesis INIT_MEM_OK: Genv.init_mem cprog <> None.
  Hypothesis MAIN_IDENT: prog_main cprog = _main.

  (* Notation progE := (progE. *)

  Let prog_itree: itree progE unit :=
    MWITree.main_itree tid app_mod.

  Let genv_props_main
    : genv_props
        ge (main_gvar_ilist tid)
        main_gfun_ilist main_cenv_ilist.
  Proof.
    eapply genv_props_incl; eauto;
      apply incl_appl; ss.
  Qed.

  Definition idx_btm: nat := 10.

  Lemma sim_get_base_time
        itr k m idx
        prd tm
        (CALL_CONT: is_call_cont k)
        (RANGE_PRD: (0 < Z.of_nat prd < Int64.max_unsigned)%Z)
        (RANGE_TM: IntRange.uint64 tm)
        (SIM: forall btm
                (RANGE_BASE_TIME: btm <= tm)
                (BASE_TIME: btm = base_time prd tm),
            paco3 (_sim_itree prog) bot3 idx itr
                  (Returnstate (Vlong (IntNat.of_nat64 btm)) k m))
    : paco3 (_sim_itree prog) bot3 (idx_btm + idx) itr
            (Callstate (Internal f_get_base_time)
                       [Vlong (IntNat.of_nat64 prd);
                       Vlong (IntNat.of_nat64 tm)] k m).
  Proof.
    start_func.
    { econs. }
    ss.

    fw. fw.
    { econs.
      - eval_comput.
        unfold IntNat.of_nat64.
        unfold Int64.zero. repr_tac.
        destruct (Z.eqb_spec (Z.of_nat prd) 0).
        { destruct prd; ss. }

        rewrite Int64_modu_repr by range_stac.
        rewrite <- mod_Zmod by nia.

        assert (IntRange.uintz64 (Z.of_nat (tm mod prd))).
        { r. split; [nia|].
          cut (tm mod prd <= tm).
          { i. inv RANGE_TM. nia. }
          apply Nat.mod_le.
          nia.
        }
        repr_tac.
        rewrite <- Nat2Z.inj_sub.
        2: { apply Nat.mod_le. nia. }
        reflexivity.
      - ss.
      - ss.
    }
    fold (base_time prd tm).
    rewrite call_cont_is_call_cont by ss.
    eapply (sim_itree_red_idx prog) with (idx_small:= idx).
    { nia. }
    eapply SIM.
    - unfold base_time. nia.
    - ss.
  Qed.

  Definition idx_mcj: nat := num_mcasts * 20 + 10.

  Lemma sim_mcast_join
        idx rxs k kp m
        (CALL_CONT: is_call_cont kp)
        (RANGE_RXS: IntRange.sint rxs)
        (* (RANGE_IDX: 20 < idx) *)
        (MEM_CONSTS: mem_consts ge m tid)
        (SIM_RET: sim_itree prog idx
                            k (Returnstate Vundef kp m))
    : sim_itree prog (idx_mcj + idx)
                (MWITree.mcast_join
                   tid rxs num_tasks (map snd mcasts) ;; k)
                (Callstate (Internal (f_mcast_join
                                        (Z.of_nat max_num_tasks)
                                        (Z.of_nat max_num_mcasts)))
                           [Vint (IntNat.of_nat rxs)] kp m).
  Proof.
    r. start_func.
    { econs. }
    unfold List.app in LENV_EQUIV. ss.
    unfold idx_mcj.

    fw. clear STEP_ENTRY.
    fw. fw.
    { econs.
      eval_comput. eauto. }
    upd_lenv.
    fw.

    Inductive join_loop_inv
              (k: itree _ unit)
              (m0: mem) (rxs: nat)
              (**)
              (i: nat) (itr: itree progE unit)
              (le: PTree.t val) (m: mem)
      : Prop :=
      FetchMsgsLoopInv
        v_any
        (MEM_INVAR: m = m0)
        (ITREE: itr = MWITree.mcast_join
                        tid rxs (num_tasks + i)
                        (skipn i (map snd mcasts));; k)
        (LENV_EQUIV:
           lenv_equiv
             le
             [(_rxs__1, Vint (IntNat.of_nat rxs)); (_i, Vint (Int.repr (Z.of_nat i))); (_group_mem, v_any)])
    .

    pose proof range_num_mcasts as RANGE_NMC.

    hexploit (in_gvar_ids _NUM_TASKS); try sIn.
    intros [b_nt FSYMB_NT].
    hexploit (in_gvar_ids _NUM_MCASTS); try sIn.
    intros [b_nmc FSYMB_NMC].

    eapply (simple_for_loop cprog) with
        (idx_each := 20) (idx0 := 0)
        (id_i:= _i) (i_max := num_mcasts)
        (loop_inv := join_loop_inv k m rxs).
    { (* loop_inv at begin *)
      econs; eauto.
      ss. rewrite plus_0_r. ss. }
    (* { rewrite LENV_EQUIV. ss. } *)
    { range_stac. }
    { nia. }
    { (* loop body *)
      hexploit (in_gvar_ids _MCAST_MEMBER); try sIn.
      intros [b_mcm FSYMB_MCM].
      hexploit (in_gvar_ids _IP_ADDR); try sIn.
      intros [b_ip FSYMB_IP].
      hexploit (in_gvar_ids _TASK_ID); try sIn.
      intros [b_tid FSYMB_TID].

      clear le LENV_EQUIV. i.
      inv LINV.
      pose proof range_tid as RANGE_TID.
      pose proof range_num_tasks as RANGE_NT.
      pose proof range_max_num_tasks as RANGE_MNT.
      pose proof range_max_num_mcasts as RANGE_MNMC.

      fw. fw. fw.
      { econs.
        - eval_comput.
          rewrite FSYMB_NMC.
          erewrite mem_consts_num_mcasts by eauto.
          repr_tac1.
          rewrite <- Nat2Z_inj_ltb.
          destruct (Nat.ltb_spec i num_mcasts).
          2: { exfalso. nia. }
          reflexivity.
        - ss.
      }
      rewrite Int.eq_false by ss. s.
      fw. fw. fw.
      { econs. eval_comput.
        rewrite FSYMB_MCM. s.
        rewrite Z.max_r by nia.
        repr_tac.
        rewrite Ptrofs.add_zero_l.
        rewrite Z.mul_1_l.
        rewrite <- Nat2Z.inj_mul.
        reflexivity.
      }
      upd_lenv.

      hexploit (nth_error_Some2 _ mcasts i).
      { rewrite <- num_mcasts_eq. nia. }
      intros [[mip_bs mbrs] MCAST_I].
      desH MCAST_I.

      fw. fw.
      { econs.
        - eval_comput.
          rewrite FSYMB_TID.
          erewrite mem_consts_task_id by eauto.
          repr_tac1.
          repr_tac1.
          rewrite Z.mul_1_l.

          repr_tac0; cycle 1.
          { rewrite Nat2Z.inj_mul.
            assert (Byte.max_signed * Byte.max_signed
                    < Ptrofs.max_unsigned)%Z by ss.
            clear - RANGE_NMC RANGE_I RANGE_MNT.
            split; [nia|].
            transitivity (Byte.max_signed * Byte.max_signed)%Z.
            { range_stac. }
            { ss. }
          }
          { range_stac. }

          rewrite <- Nat2Z.inj_add.
          repr_tac0.
          2: {
            split; [nia|].
            transitivity (Byte.max_signed * Byte.max_signed + Byte.max_signed)%Z.
            { rewrite Nat2Z.inj_add.
              rewrite Nat2Z.inj_mul.
              clear - RANGE_NT RANGE_MNT RANGE_I RANGE_TID RANGE_NMC.
              rr in RANGE_NMC. rr in RANGE_NT. rr in RANGE_MNT.
              nia.
            }
            { ss. }
          }

          erewrite mem_consts_mcast_member; eauto.
        - ss.
          rewrite bool_val_of_bool.
          instantiate (1:= existsb (Nat.eqb tid) mbrs).
          desf.
      }

      apply nth_error_split in MCAST_I.
      destruct MCAST_I as (mcs1 & mcs2 & MCS_EQ & LEN_MCS1).
      replace (skipn i (map snd mcasts)) with
          (mbrs :: map snd mcs2).
      2: { rewrite MCS_EQ.
           rewrite map_app.
           rewrite skipn_app_exact.
           2: { rewrite map_length. ss. }
           ss.
      }
      s.

      destruct (existsb (Nat.eqb tid) mbrs).
      - (* send join_pkt *)


        assert (RANGE_OFS: (0 <= Z.of_nat ((num_tasks + i) * 16)
                            < Int.max_signed)%Z).
        { split; [nia| ].
          transitivity (16 * (Byte.max_signed + Byte.max_signed))%Z.
          2: { ss. }
          range_stac.
        }

        fw.
        { hexploit (in_gfun_ilist _pals_mcast_join); try sIn.
          i. des.
          econs; ss.
          - eval_comput. rewrite FDEF_SYMB. ss.
          - eval_comput.
            rewrite FSYMB_IP, FSYMB_NT.
            erewrite mem_consts_num_tasks by eauto. s.

            repr_tac.
            rewrite Ptrofs.add_zero_l.

            replace (16 * (Z.of_nat num_tasks + Z.of_nat i))%Z
              with (16 * Z.of_nat (num_tasks + i))%Z by nia.
            reflexivity.
          - eauto.
          - ss.
        }

        hexploit (ip_in_mem_exists ge tid (num_tasks + i)); eauto.
        { nia. }
        intros (mip & MIP_IN_MEM & DEST_ID_MIP & RANGE_MIP).
        assert (MCAST_ID_IP: mcast_id_ip (num_tasks + i) mip).
        { r. esplits; eauto.
          r in DEST_ID_MIP.
          unfold dest_ips in DEST_ID_MIP.
          rewrite nth_error_app2 in DEST_ID_MIP.
          2: { fold num_tasks. nia. }
          fold num_tasks in DEST_ID_MIP.
          replace (num_tasks + i - num_tasks) with i in DEST_ID_MIP by nia.
          ss.
        }

        pfold. econs 3; ss.
        { econs; eauto.
          - econs 1; eauto.
            econs 3; try reflexivity; ss.
            eauto.
          - ss.
        }
        { econs 1. }
        { apply mcast_id_ip_comput in MCAST_ID_IP.
          destruct MCAST_ID_IP as (AUX & _).
          rewrite AUX.
          simpl_itree_goal.
          simpl_itree_goal. ss. }

        i. (* clear POSTCOND. *) inv RET.
        inv CPROG_AFTER_EVENT; ss.
        symmetry in EVENT. inv EVENT.
        existT_elim. unf_resum. subst.
        (* symmetry in EVENT. inv EVENT. *)
        (* existT_elim. unf_resum. clarify. *)
        inv OS_ESTEP. existT_elim. clarify.
        exists (idx1 + 10). left.

        fw. fw.
        { econs. eauto. }
        fw.
        { econs. eval_comput.
          repr_tac.
          replace (Z.of_nat (length mcs1) + 1)%Z with
              (Z.of_nat (S (length mcs1))) by nia.
          reflexivity. }
        upd_lenv.
        fw.

        eapply (sim_itree_red_idx prog) with (idx_small:= idx1 - 20).
        { nia. }
        eapply SIM_NEXT.
        (* { apply LENV_EQUIV. } *)
        econs; eauto.
        rewrite plus_n_Sm.
        repeat f_equal.
        rewrite MCS_EQ.
        rewrite map_app. ss.
        rewrite rw_cons_app.
        rewrite app_assoc.
        rewrite skipn_app_exact.
        2: { rewrite app_length.
             rewrite map_length.
             ss. nia. }
        ss.

      - (* continue *)
        fw.
        { econs. eauto. }
        fw.
        { econs.
          eval_comput.
          repr_tac.
          replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by nia.
          reflexivity.
        }
        upd_lenv.
        fw.

        eapply (sim_itree_red_idx prog) with (idx1 - 20).
        { nia. }
        eapply SIM_NEXT.
        (* + apply LENV_EQUIV. *)
        econs; eauto.
        simpl_itree_goal.
        simpl_itree_goal.
        rewrite plus_n_Sm.
        do 2 f_equal.
        rewrite MCS_EQ.
        rewrite map_app. ss.
        rewrite rw_cons_app.
        rewrite app_assoc.
        rewrite skipn_app_exact.
        2: { rewrite app_length.
             rewrite map_length. ss. nia. }
        ss.
    }

    clear le LENV_EQUIV.
    i. inv LINV_END.
    fw.
    rewrite skipn_all2.
    2: { rewrite map_length.
         rewrite <- num_mcasts_eq. ss. }
    s.
    fw. fw.
    { econs.
      - eval_comput.
        rewrite FSYMB_NMC.
        erewrite mem_consts_num_mcasts by eauto.
        repr_tac.
        rewrite Z.ltb_irrefl.
        reflexivity.
      - ss.
    }
    rewrite Int.eq_true. s.
    fw. fw. fw.

    eapply (sim_itree_red_idx prog) with (idx_small:= idx).
    { nia. }
    simpl_itree_goal.
    eapply SIM_RET.
  Qed.

  Section SIM_INIT.

    Variable idx_run: nat.

    Hypothesis SIM_RUN_TASK: forall
        (txs rxs: nat)
        (r: nat -> itree progE unit -> Prog.state prog -> Prop)
        sytm m_i (* ast *) kp idx_fin
        sytm_dmy mcont
        ofsc ofsn
        (CALL_CONT: is_call_cont kp)
        (MEM_NB: (Genv.genv_next ge <= Mem.nextblock m_i)%positive)
        (* (INV_APP: inv_app ge ast m_i) *)
        (RANGE_SYTM: (0 < Z.of_nat (sytm + 2 * period) <=
                      Int64.max_unsigned)%Z)
        (RANGE_TXS: IntRange.sint txs)
        (RANGE_RXS: IntRange.sint rxs)
        (MEM_CONSTS: mem_consts ge m_i tid)
        (MEM_SBUF: mem_sbuf ge m_i sytm_dmy tid mcont)
        (MEM_MSTORE: mem_mstore ge m_i false ofsc ofsn
                                MWITree.init_inbox
                                MWITree.init_inbox)
        (MEM_SH: mem_sh ge m_i (repeat false num_tasks))
        (MEM_TXS: mem_txs ge m_i txs)
        (MEM_RXS: mem_rxs ge m_i rxs)
        (INV_APP_INIT: inv_app ge (AppMod.init_abst_state app_mod) m_i)
        (SIM_RET:
           forall m_f
             (* (UNCH: Mem.unchanged_on (fun _ _ => True) m_i m_f) *)
           ,
             paco3 (_sim_itree prog) r idx_fin
                   (Ret tt)
                   (Clight.Returnstate Vundef kp m_f))
      , (* exists idx_rt: nat, *)
        paco3 (_sim_itree prog) r (idx_run + idx_fin)
              (MWITree.run_task tid app_mod txs rxs sytm)
              (Clight.Callstate
                 (Internal f_run_task)
                 [Vlong (IntNat.of_nat64 sytm)] kp m_i)
    .

    Local Opaque idx_btm idx_mcj.

    (* Definition idx_init: nat := idx_btm + idx_mcj + idx_run + 100. *)
    (* Definition idx_init: nat := 10. *)

    Lemma sim_init: sim_itree_prog prog prog_itree.
    Proof.
      hexploit (in_gfun_ilist _main); [sIn|].
      intros (b_main & FSYMB_MAIN & FFUNCT_MAIN). des.

      econs.
      { (* init *)
        ss.
        apply Some_not_None in INIT_MEM_OK.
        destruct INIT_MEM_OK.

        esplits. econs; eauto.
        - rewrite MAIN_IDENT. eauto.
        - rewrite <- Genv.find_funct_find_funct_ptr. eauto.
        - ss.
      }

      rewrite Genv.find_funct_find_funct_ptr in FFUNCT_MAIN.
      i. ss.
      inv PROG_INIT_STATE.
      rewrite MAIN_IDENT in *.
      subst ge0. ss.
      unfold fundef in *.
      move FSYMB_MAIN at bottom. move FFUNCT_MAIN at bottom.
      clarify. ss.
      renames b m0 into b_main m_i.

      match goal with
      | H1: Genv.init_mem _ = Some _,
            H2: type_of_function f_main = _ |- _ =>
        rename H1 into INIT_MEM; clear H2
      end.
      pose proof range_tid as RANGE_TID.

      hexploit init_mem_consts; eauto. intros MEM_CONSTS.
      hexploit init_mem_mstore; eauto. intros MEM_MSTORE.
      hexploit init_mem_sh; eauto. intros MEM_SH.
      hexploit init_mem_sbuf; eauto. intros MEM_SBUF.
      hexploit init_mem_txs; eauto. intros MEM_TXS.
      hexploit init_mem_rxs; eauto. intros MEM_RXS.
      hexploit inv_app_init; eauto. intros INV_APP.
      assert (MEM_NXTB: (Genv.genv_next ge <= Mem.nextblock m_i)%positive).
      { ss. erewrite Genv.init_mem_genv_next; eauto. nia. }


      (* exists 100%nat. *)
      exists 30.
      unfold sim_itree.

      start_func.
      { ss. econs 1. }
      ss.
      (* rewrite app_nil_l in LENV_EQUIV. *)

      hexploit (in_gvar_ids _PALS_PERIOD); try sIn.
      intros (b_pprd & FSYMB_PPRD).

      fw. fw. fw. fw.
      { econs. eval_comput.
        rewrite FSYMB_PPRD.
        erewrite mem_consts_pals_period; eauto. }
      upd_lenv.
      fw. fw. fw.
      { hexploit (in_gvar_ids _MAX_CSKEW); try sIn.
        intro FSYMB_SK. des.
        hexploit (in_gvar_ids _MAX_NWDELAY); try sIn.
        intro FSYMB_ND. des.

        econs. eval_comput. ss.
        rewrite FSYMB_SK. rewrite FSYMB_ND.

        erewrite mem_consts_max_cskew; eauto.
        erewrite mem_consts_max_nwdelay; eauto.

        eval_comput.
        (* pose proof max_clock_skew_range as R1. *)
        (* pose proof max_nwdelay_range as R2. *)
        (* pose proof pals_period_range as R3. *)
        pose proof period_cond as PCOND.
        pose proof period_mul_10_lt_max.
        (* inv R1. inv R2. inv R3. *)
        repr_tac.
        replace (2 * Z.of_nat max_clock_skew + Z.of_nat max_nw_delay)%Z
          with (Z.of_nat (2 * max_clock_skew + max_nw_delay)) by nia.
        reflexivity.
      }
      upd_lenv.

      fw. fw. fw.
      { econs. eval_comput.
        rewrite FSYMB_PPRD.
        erewrite mem_consts_pals_period by eauto.
        pose proof range_period.
        repr_tac.
        rewrite eval_max_time.
        reflexivity.
      }
      upd_lenv.
      fw. fw.

      hexploit (in_gvar_ids _send_buf); [sIn|].
      intros (b_sbuf & FSYMB_SBUF).

      assert(MSTORE: exists m',
                Mem.store Mint8signed m_i b_sbuf 8
                          (Vint (Int.repr (Z.of_nat tid))) = Some m').
      { apply inhabited_sig_to_exists. econs.
        apply Mem.valid_access_store.
        rr. split; ss.
        - ii. eapply mem_sbuf_writable; eauto.
          ss. unfold pld_size. nia.
        - solve_divide.
      }
      des.

      assert (MEM_CH: mem_unchanged_except
                        (mem_range b_sbuf 8 9) m_i m').
      { eapply Mem.store_unchanged_on; eauto.
        unfold mem_range.
        i. ss. nia. }

      (* assert (RANGE_TID_Z: (Z.of_nat tid < 6)%Z). *)
      (* { unfold num_tasks in *. nia. } *)
      pose proof range_num_tasks as RANGE_NT.

      assert(MEM_SBUF': mem_sbuf ge m' 0 tid
                                 (List.repeat Byte.zero msg_size)).
      { ii. clarify.
        specialize (MEM_SBUF _ FIND_SYMB).
        inv MEM_SBUF.
        econs.
        - eapply Mem.loadbytes_unchanged_on; eauto.
          unfold mem_range.
          i. ss. nia.
        - erewrite Mem.load_store_same; eauto. ss.
          rewrite sign_ext_byte_range by range_stac.
          ss.
        - eapply Mem.loadbytes_unchanged_on; eauto.
          unfold mem_range.
          ii. ss. des. nia.
        - ii. eapply Mem.perm_store_1; eauto.
      }

      fw.
      { hexploit (in_gvar_ids _TASK_ID); [sIn|].
        intros FSYMB_TID. des. ss.
        econs.
        - eval_comput.
          rewrite FSYMB_SBUF. s.
          rewrite Ptrofs.add_zero_l. reflexivity.
        - eval_comput.
          rewrite FSYMB_TID.
          rewrite Ptrofs.unsigned_zero.
          erewrite mem_consts_task_id; eauto.
        - ss.
        - simpl.
          unfold IntNat.of_nat.
          rewrite sign_ext_byte_range by range_stac.
          eval_comput.
          repr_tac.
          eauto.
      }

      assert (CH_BLK: mem_changed_block b_sbuf m_i m').
      { eapply Mem.unchanged_on_implies; eauto.
        unfold mem_range. ii. nia. }

      eapply mem_consts_unch_diffblk in MEM_CONSTS; eauto.
      2: { i. eapply global_addresses_distinct'; eauto.
           ii. subst. ss. des; ss. }
      eapply mem_mstore_unch_diffblk in MEM_MSTORE; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_txs_unch_diffblk in MEM_TXS; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_rxs_unch_diffblk in MEM_RXS; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_sh_unch_diffblk in MEM_SH; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      eapply inv_app_unch_diffblk in INV_APP; eauto.
      2: { sIn. }

      eapply Pos.le_trans with (p:= Mem.nextblock m') in MEM_NXTB.
      2: { apply CH_BLK. }

      clear dependent m_i.
      renames m' MEM_SBUF' into m1 MEM_SBUF.

      fw. fw. fw. fw.
      { hexploit (in_gfun_ilist _pals_init_timer); [sIn|].
        i. des.
        econs; ss.
        - eval_comput. rewrite FDEF_SYMB. ss.
        - eval_comput. eauto.
        - eauto.
        - ss.
      }

      unfold prog_itree, MWITree.main_itree.
      pfold. econs 3; ss.
      { econs; eauto.
        - ss. econs 1; eauto.
          eapply CProgOSEC_InitTimer; ss.
        - ss. }
      (* { rr. econs. } *)
      { econs 1. }
      { simpl_itree_goal. ss. }
      i. (* inv POSTCOND. *) existT_elim. subst.
      inv RET. inv CPROG_AFTER_EVENT; ss.
      inv EVENT. existT_elim.
      unf_resum. clarify.
      inv OS_ESTEP. existT_elim. clarify.
      rename m' into m1.

      exists 10. left.
      destruct (Z.ltb_spec ret 0).
      { (* ret *)
        fw. upd_lenv.
        fw. fw.
        { econs. eval_comput. ss. }
        upd_lenv.
        fw. fw. fw.
        { econs.
          - eval_comput. ss.
          - rewrite bool_val_of_bool. simpl.
            repr_tac.
            destruct (Z.ltb_spec ret 0); ss. nia.
        }
        ss.
        fw.
        { econs; ss.
          - eval_comput. eauto.
          - ss. }
        simpl.

        pfold. econs 1; ss.
        - econs; ss.
        - econs 1.
        - ss.
      }

      (* timer init ok *)
      fw. upd_lenv.
      fw. fw.
      { econs. eval_comput. ss. }
      upd_lenv.
      fw. fw. fw.
      { econs.
        - eval_comput. ss.
        - rewrite bool_val_of_bool. simpl.
          repr_tac.
          instantiate (1:= false).
          destruct (Z.ltb_spec ret 0); ss. nia.
      }
      fw. fw. fw. fw.
      { hexploit (in_gfun_ilist _pals_current_time); [sIn|].
        i. des.
        econs; ss.
        - eval_comput. rewrite FDEF_SYMB. ss.
        - eval_comput. eauto.
        - eauto.
        - ss.
      }
      rename ret into ret_p. clear RANGE_RET.

      pfold. econs 3; ss.
      { econs; eauto.
        - econs 1; eauto.
          econs 6; ss.
        - ss. }
      (* { econs. } *)
      { econs 1. }
      { simpl_itree_goal. ss. }
      intros ctm_z. i.

      (* inv POSTCOND. *) existT_elim. clarify.

      inv RET. inv CPROG_AFTER_EVENT; ss.
      symmetry in EVENT. inv EVENT.
      existT_elim. unf_resum. clarify.
      inv OS_ESTEP. existT_elim. clarify.
      rename m' into m1.

      remember (Z.to_nat ctm_z) as ctm.
      assert (RANGE_CTM: IntRange.uint64 ctm).
      { range_stac. }
      replace (Int64.repr ctm_z) with (IntNat.of_nat64 ctm).
      2: { unfold IntNat.of_nat64. subst ctm.
           rewrite Z2Nat.id; ss.
           unfold IntRange.uintz64 in *. nia. }
      clear dependent ctm_z.

      exists (idx_btm + 50). left.
      fw. upd_lenv.
      fw. fw.
      { econs. eval_comput. ss. }
      upd_lenv.
      fw. fw. fw.

      destruct (Nat.eqb_spec ctm 0)
        as [CTM_ZERO | CTM_POS]; ss.
      { subst ctm.
        fw.
        { econs.
          - eval_comput. ss.
          - rewrite bool_val_of_bool.
            repr_tac. rewrite Z.eqb_refl. ss.
        }
        s. fw.
        { econs. eval_comput. eauto. }
        upd_lenv.
        fw. fw.
        { econs.
          - eval_comput. ss.
          - s. unfold Cop.bool_val. s.
            rewrite Int.eq_false by ss. ss. }
        s. fw.
        { econs; ss.
          - eval_comput. eauto.
          - ss. }
        s. pfold. econs 1; ss.
        - econs; ss.
        - econs 1.
        - ss.
      }
      (* 0 < ctm *)

      fw.
      { econs.
        - eval_comput. ss.
        - rewrite bool_val_of_bool.
          repr_tac.
          destruct (Nat.eqb_spec ctm 0); ss; nia.
      }
      destruct (Z.eqb_spec (Z.of_nat ctm) 0).
      { exfalso. destruct ctm; ss. }
      s.
      (* pose (max_time_z := (Int64.max_unsigned - *)
      (*                    5 * Z.of_nat pals_period)%Z). *)
      (* assert (MAX_TIME_Z: max_time_z = Z.of_nat ITrSpec.MAX_TIME). *)
      (* { subst max_time_z. unfold ITrSpec.MAX_TIME. *)
      (*   pose proof period_mul_10_lt_max. nia. } *)

      fw.
      { econs. eval_comput.
        unfold Cop.sem_notbool.
        rewrite bool_val_of_bool. simpl.

        unfold IntNat.of_nat64.
        rewrite Int64_ltu_repr; cycle 1.
        { range_stac. }
        { unfold MAX_TIME.
          range_stac. }
        rewrite <- Nat2Z_inj_ltb.

        instantiate (1:= Vint (if ctm <? MAX_TIME
                               then Int.zero else Int.one)).
        destruct (Nat.ltb_spec ctm MAX_TIME); ss.
      }
      upd_lenv.
      (* clear max_time_z MAX_TIME_Z. *)
      destruct (Nat.ltb_spec ctm MAX_TIME).
      2: {
        s. fw. fw.
        { econs.
          - eval_comput. ss.
          - ss. }
        rewrite Int.eq_false by ss.
        s. fw.
        { econs; ss.
          - eval_comput. eauto.
          - ss. }
        s. pfold. econs 1; ss.
        - econs; ss.
        - econs 1.
        - ss.
      }
      s. fw. fw.
      { econs.
        - eval_comput. ss.
        - cbn. rewrite Int.eq_true. ss. }
      s. fw. fw. fw. fw.
      { hexploit (in_gfun_ilist _get_base_time); try sIn.
        i. des.
        econs; eauto; ss.
        - eval_comput. rewrite FDEF_SYMB. ss.
        - eval_comput. reflexivity.
      }

      eapply sim_get_base_time; ss.
      { pose proof period_cond.
        pose proof period_mul_10_lt_max.
        range_stac. }
      i. guardH BASE_TIME.

      fw. upd_lenv.
      fw.

      assert (RANGE_PPRD: IntRange.uint64 period).
      { pose proof period_cond.
        pose proof period_mul_10_lt_max.
        range_stac. }
      assert (RANGE_PPRD2: IntRange.uint64 (2 * period)).
      { pose proof period_cond.
        pose proof period_mul_10_lt_max.
        range_stac. }

      assert (RANGE_BTM: IntRange.uint64 btm).
      { range_stac. }

      fw.
      { (* set nxt_base_time1 *)
        econs. eval_comput.
        repr_tac.
        replace 2%Z with (Z.of_nat 2) by ss.
        rewrite <- Nat2Z.inj_mul.
        rewrite <- Nat2Z.inj_add.
        reflexivity.
      }
      upd_lenv.

      assert (RANGE_CTM2: 0 < ctm < MAX_TIME) by nia.
      pose proof period_cond as PCOND.

      assert (UINT64_NXT_SYNC:
                IntRange.uint64 (btm + period + period + period)).
      { unfold MAX_TIME in *.
        range_stac. }

      assert (UINT64_NXT_SYNC_D:
                IntRange.uint64 (btm + period + period + period - DELTA)).
      { unfold MAX_TIME in *.
        range_stac. }

      (* fw. fw. fw. *)
      (* { hexploit (in_gfun_ilist _pals_set_timelimit); try sIn. *)
      (*   i. des. *)
      (*   econs; ss. *)
      (*   - eval_comput. rewrite FDEF_SYMB. ss. *)
      (*   - eval_comput. *)
      (*     repr_tac. *)
      (*     rewrite <- Nat2Z.inj_add. *)
      (*     rewrite <- Nat2Z.inj_sub by nia. *)

      (*     replace (max_clock_skew + (max_clock_skew + 0) + *)
      (*              max_nw_delay) with DELTA. *)
      (*     2: { unfold DELTA. nia. } *)
      (*     reflexivity. *)
      (*   - eauto. *)
      (*   - ss. *)
      (* } *)

      (* assert ((btm + pals_period + pals_period) - *)
      (*         (2 * max_cskew + max_nwdelay) <= *)
      (*         Z.to_nat Int64.max_unsigned). *)
      (* { unfold MAX_TIME in *. ss. nia. } *)

      (* pfold. econs 3; ss. *)
      (* { econs; eauto. *)
      (*   - econs 2; try reflexivity. *)
      (*     ss. *)
      (*   - ss. *)
      (* } *)
      (* { econs. ss. } *)
      (* { econs 1. } *)
      (* { simpl_itree_goal. *)
      (*   rewrite <- BASE_TIME. ss. } *)

      (* intros []. i. *)
      (* inv RET. inv CPROG_AFTER_EVENT; ss. *)
      (* symmetry in EVENT. inv EVENT. *)
      (* rename m' into m1. *)

      (* tx *)
      (* exists 10. left. *)
      fw. fw. fw. fw.
      { hexploit (in_gfun_ilist _pals_socket); try sIn. i. des.
        econs; ss.
        - eval_comput. rewrite FDEF_SYMB. ss.
        - eval_comput. eauto.
        - eauto.
        - ss.
      }

      pfold. econs 3; ss.
      { econs; eauto. ss.
        - econs 1; eauto.
          econs 1; ss.
        - ss. }
      { econs 1. }
      { simpl_itree_goal. ss. }

      intro txs_z. i.
      (* inv POSTCOND. *) existT_elim. subst.
      inv RET. inv CPROG_AFTER_EVENT; ss.
      symmetry in EVENT. inv EVENT.
      existT_elim. unf_resum. clarify.
      inv OS_ESTEP. existT_elim. clarify. clear_tt.
      rename m' into m1.
      rename RANGE_RET into RANGE_TXS_Z.

      hexploit (in_gvar_ids _txs); try sIn.
      intros [b_txs FSYMB_TXS].

      exists 10. left.
      fw. upd_lenv.
      fw.

      assert(MSTORE_TX: exists m',
                Mem.store Mint32 m1 b_txs 0
                          (Vint (Int.repr txs_z)) = Some m').
      { apply inhabited_sig_to_exists. econs.
        apply Mem.valid_access_store.
        rr. split; ss.
        - ii. eapply mem_skt_writable; eauto.
        - solve_divide.
      }
      des.

      fw.
      { econs.
        - eval_comput. rewrite FSYMB_TXS. ss.
        - eval_comput. ss.
        - ss.
        - ss. eval_comput. cbn. eauto.
      }

      assert (CH_BLK: mem_changed_block b_txs m1 m').
      { eapply Mem.unchanged_on_implies; eauto.
        eapply store_unchanged_on'; eauto.
        unfold mem_range. ii. nia. }

      eapply mem_consts_unch_diffblk in MEM_CONSTS; eauto.
      2: { i. eapply global_addresses_distinct'; eauto.
           ii. subst. ss. des; ss. }
      eapply mem_mstore_unch_diffblk in MEM_MSTORE; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_sh_unch_diffblk in MEM_SH; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      (* eapply mem_txs_unch_diffblk in MEM_TXS; eauto. *)
      (* 2: { eapply global_addresses_distinct'; eauto. ss. } *)
      eapply mem_rxs_unch_diffblk in MEM_RXS; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_sbuf_unch_diffblk in MEM_SBUF; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      eapply inv_app_unch_diffblk in INV_APP; eauto.
      2: { sIn. }

      eapply Pos.le_trans with (p:= Mem.nextblock m') in MEM_NXTB.
      2: { apply CH_BLK. }
      rename m' into m2.
      clear CH_BLK.

      (* rx *)
      fw. fw. fw. fw.
      { hexploit (in_gfun_ilist _pals_socket); try sIn. i. des.
        econs; ss.
        - eval_comput. rewrite FDEF_SYMB. ss.
        - eval_comput. eauto.
        - eauto.
        - ss.
      }

      pfold. econs 3; ss.
      { econs; eauto. ss.
        - econs 1; eauto.
          econs 1; ss.
        - ss. }
      { econs 1. }
      { simpl_itree_goal. ss. }

      intro rxs_z. i.
      (* inv POSTCOND. *) existT_elim. subst.
      inv RET. inv CPROG_AFTER_EVENT; ss.
      symmetry in EVENT. inv EVENT.
      existT_elim. unf_resum. clarify.
      inv OS_ESTEP. existT_elim. clarify. clear_tt.
      rename m' into m2.
      rename RANGE_RET into RANGE_RXS_Z.

      hexploit (in_gvar_ids _rxs); try sIn.
      intros [b_rxs FSYMB_RXS].

      exists 30. left.
      fw. upd_lenv.
      fw.

      assert(MSTORE_RX: exists m',
                Mem.store Mint32 m2 b_rxs 0
                          (Vint (Int.repr rxs_z)) = Some m').
      { apply inhabited_sig_to_exists. econs.
        apply Mem.valid_access_store.
        rr. split; ss.
        - ii. eapply mem_skt_writable; eauto.
        - solve_divide.
      }
      des.

      fw.
      { econs.
        - eval_comput. rewrite FSYMB_RXS. ss.
        - eval_comput. ss.
        - ss.
        - ss. eval_comput. cbn. eauto.
      }

      assert (CH_BLK: mem_changed_block b_rxs m2 m').
      { eapply Mem.unchanged_on_implies; eauto.
        eapply store_unchanged_on'; eauto.
        unfold mem_range. ii. nia. }

      eapply mem_consts_unch_diffblk in MEM_CONSTS; eauto.
      2: { i. eapply global_addresses_distinct'; eauto.
           ii. subst. ss. des; ss. }
      eapply mem_mstore_unch_diffblk in MEM_MSTORE; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_sh_unch_diffblk in MEM_SH; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      (* eapply mem_txs_unch_diffblk in MEM_TXS; eauto. *)
      (* 2: { eapply global_addresses_distinct'; eauto. ss. } *)
      (* eapply mem_rxs_unch_diffblk in MEM_RXS; eauto. *)
      (* 2: { eapply global_addresses_distinct'; eauto. ss. } *)
      eapply mem_sbuf_unch_diffblk in MEM_SBUF; eauto.
      2: { eapply global_addresses_distinct'; eauto. ss. }
      eapply inv_app_unch_diffblk in INV_APP; eauto.
      2: { sIn. }
      eapply Pos.le_trans with (p:= Mem.nextblock m') in MEM_NXTB.
      2: { apply CH_BLK. }
      rename m' into m3.

      assert (LOAD_TX: Mem.load Mint32 m3 b_txs 0 =
                       Some (Vint (Int.repr txs_z))).
      { erewrite Mem.load_unchanged_on; eauto.
        { ss. i.
          eapply Genv.global_addresses_distinct; eauto. ss. }
        erewrite Mem.load_store_same; eauto. ss. }
      assert (PERM_TX: Mem.range_perm m3 b_txs 0 4 Cur Writable).
      { eapply Mem_range_perm_unchanged_on; eauto.
        { eapply Mem.unchanged_on_implies; eauto.
          unfold mem_range. i. des. subst.
          eapply Genv.global_addresses_distinct; eauto. ss. }
        ii. eapply Mem.perm_store_1; eauto.
        eapply MEM_TXS; eauto.
      }

      assert (LOAD_RX: Mem.load Mint32 m3 b_rxs 0 =
                       Some (Vint (Int.repr rxs_z))).
      { erewrite Mem.load_store_same; eauto. ss. }
      assert (PERM_RX: Mem.range_perm m3 b_rxs 0 4 Cur Writable).
      { ii. eapply Mem.perm_store_1; eauto.
        eapply MEM_RXS; eauto. }

      fw. fw. fw.
      (* tx *)
      fw.
      { econs.
        - eval_comput.
          rewrite FSYMB_TXS.
          rewrite Ptrofs.unsigned_zero.
          rewrite LOAD_TX. ss.
        - ss. rewrite bool_val_of_bool.
          repr_tac. reflexivity.
      }

      destruct (Z.ltb_spec txs_z 0).
      { (* txs < 0 *)
        ss.
        fw.
        { econs. eval_comput. eauto. }
        upd_lenv.
        fw. fw.
        { econs.
          - eval_comput. ss.
          - ss.
        }
        rewrite Int.eq_false by ss.
        s. fw.
        { econs; ss.
          - eval_comput. eauto.
          - ss.
        }
        s.
        pfold. econs 1.
        - econs; ss.
        - econs 1.
        - ss.
      }

      (* rx *)
      fw.
      { econs.
        eval_comput.
        rewrite FSYMB_RXS. cbn.
        rewrite Ptrofs.unsigned_zero.
        rewrite LOAD_RX. ss.
        repr_tac. unfold Val.of_bool.
        instantiate (1:= Vint (if (rxs_z <? 0)%Z then Int.one else Int.zero)).
        destruct (Z.ltb_spec rxs_z 0); ss.
      }
      upd_lenv.
      fw.
      destruct (Z.ltb_spec rxs_z 0).
      { (* rxs < 0 *)
        fw.
        { econs.
          - eval_comput. ss.
          - s. ss.
        }
        rewrite Int.eq_false by ss.
        s. fw.
        { econs; ss.
          - eval_comput. eauto.
          - ss.
        }
        s.
        pfold. econs 1.
        - econs; ss.
        - econs 1.
        - ss.
      }

      remember (Z.to_nat txs_z) as txs.
      assert (RANGE_TXS: IntRange.sint txs).
      { range_stac. }

      clear MEM_TXS.
      assert (MEM_TXS: mem_txs ge m3 txs).
      { ii. ss. clarify.
        econs; eauto.
        rewrite LOAD_TX.
        unfold IntNat.of_nat. repeat f_equal.
        nia.
      }
      replace (Int.repr txs_z) with (IntNat.of_nat txs) in LENV_EQUIV.
      2: { unfold IntNat.of_nat. f_equal. nia. }
      clear dependent txs_z.

      remember (Z.to_nat rxs_z) as rxs.
      assert (RANGE_RXS: IntRange.sint rxs).
      { range_stac. }

      clear MEM_RXS.
      assert (MEM_RXS: mem_rxs ge m3 rxs).
      { ii. ss. clarify.
        econs; eauto.
        rewrite LOAD_RX.
        unfold IntNat.of_nat. repeat f_equal.
        nia.
      }
      replace (Int.repr rxs_z) with (IntNat.of_nat rxs) in LENV_EQUIV.
      2: { unfold IntNat.of_nat. f_equal. nia. }
      clear dependent rxs_z.

      clear dependent m1. clear dependent m2.
      rename m3 into m1.

      fw.
      { econs.
        - eval_comput. ss.
        - ss.
      }

      rewrite Int.eq_true. s.
      fw. fw. fw.
      { hexploit (in_gfun_ilist _pals_wait_timer); try sIn.
        i. des.
        econs; ss.
        - eval_comput. rewrite FDEF_SYMB. ss.
        - eval_comput. ss.
        - eauto.
        - ss.
      }

      (* assert(RANGE_WAIT_TIME: IntRange.uint64 (btm + pals_period)). *)
      (* { econs. pose proof period_condition. nia. } *)

      pfold. econs 3; ss.
      { econs; eauto.
        - econs 1; eauto.
          econs 8; try reflexivity.
          range_stac.
        - ss.
      }
      { econs 1. }
      { simpl_itree_goal.
        rewrite <- BASE_TIME.
        ss. }
      i. inv RET. (* clear POSTCOND. *)
      inv CPROG_AFTER_EVENT; ss.
      symmetry in EVENT. inv EVENT.
      existT_elim. unf_resum. clarify.
      inv OS_ESTEP. existT_elim. clarify.
      rename m' into m1.

      exists 10. left.
      fw. clear dependent r.
      fw. fw. fw. fw.
      { hexploit (in_gfun_ilist _pals_bind); try sIn.
        i. des.
        hexploit (in_gvar_ids _PORT); try sIn.
        intro FSYMB_PN. des.

        econs; ss.
        - eval_comput.
          rewrite FDEF_SYMB. ss.
        - eval_comput.
          rewrite FSYMB_RXS. rewrite FSYMB_PN.
          cbn. erewrite mem_skt_id; eauto.
          erewrite mem_consts_port; eauto.
        - eauto.
        - ss.
      }

      pose proof range_port as RANGE_PORT.
      pfold. econs 3; ss.
      { econs; eauto.
        - econs 1; eauto.
          econs 2; try reflexivity; eauto.
        - ss. }
      (* { econs; eauto. } *)
      { econs 1. }
      { simpl_itree_goal. ss. }
      intro ret_bind. i.
      (* inv POSTCOND. *) existT_elim. clarify.
      inv RET. inv CPROG_AFTER_EVENT; ss.
      symmetry in EVENT. inv EVENT.
      existT_elim. unf_resum. clarify.
      inv OS_ESTEP. existT_elim. subst.
      rename m' into m1.

      exists (idx_mcj + idx_run + 30). left.
      fw. upd_lenv.
      fw. fw.
      { econs. eval_comput. ss. }
      upd_lenv.
      fw. fw.

      destruct (Z.ltb_spec ret_bind 0).
      { (* bind failed *)
        fw.
        { econs.
          - eval_comput. ss.
          - rewrite bool_val_of_bool. repr_tac.
            destruct (Z.ltb_spec ret_bind 0); ss. nia.
        }
        s. fw.
        { econs.
          - eval_comput. eauto.
          - ss.
          - ss.
        }
        s.
        pfold. econs 1; ss.
        - econs; ss.
        - econs 1.
        - ss.
      }

      fw.
      { econs.
        - eval_comput. ss.
        - rewrite bool_val_of_bool. repr_tac.
          instantiate (1:= false).
          destruct (Z.ltb_spec ret_bind 0); ss; nia.
      }
      s. fw. fw. fw.
      { hexploit (in_gfun_ilist _mcast_join); try sIn.
        i. des.
        econs; ss.
        - eval_comput. rewrite FDEF_SYMB. ss.
        - eval_comput. rewrite FSYMB_RXS. cbn.
          erewrite mem_skt_id; eauto.
        - eauto.
        - ss.
      }

      assert (RANGE_NNSYTM: IntRange.uint64 (btm + period * 6)).
      { unfold MAX_TIME in *.
        range_stac. }
      assert (RANGE_DELTA: IntRange.uint64 DELTA).
      { unfold DELTA.
        range_stac. }

      red_idx (idx_mcj + (idx_run + 20)).
      eapply sim_mcast_join; ss.
      fw. fw. fw. fw.
      { (* set nxt_base_time 2 *)
        econs. eval_comput.
        repr_tac.
        replace 2%Z with (Z.of_nat 2) by ss.
        rewrite <- Nat2Z.inj_mul.
        rewrite <- Nat2Z.inj_add.
        reflexivity.
      }
      upd_lenv.

      (* fw. fw. fw. *)
      (* { hexploit (in_gfun_ilist _pals_set_timelimit); try sIn. *)
      (*   i. des. *)
      (*   econs; ss. *)
      (*   - eval_comput. rewrite FDEF_SYMB. ss. *)
      (*   - eval_comput. *)
      (*     repr_tac. *)
      (*     rewrite <- Nat2Z.inj_add. *)
      (*     rewrite <- Nat2Z.inj_sub by nia. *)

      (*     replace (max_clock_skew + (max_clock_skew + 0) + max_nw_delay) with DELTA. *)
      (*     2: { unfold DELTA. nia. } *)
      (*     replace (btm + period + (period + (period + 0)) + period) with (btm + period * 4) by nia. *)
      (*     reflexivity. *)
      (*   - eauto. *)
      (*   - ss. *)
      (* } *)

      (* pfold. econs 3; ss. *)
      (* { econs; eauto. *)
      (*   - econs 2; try reflexivity. *)
      (*     range_stac. *)
      (*   - ss. } *)
      (* { econs 1. } *)
      (* { simpl_itree_goal. *)
      (*   unfold DELTA. ss. *)
      (*   do 3 f_equal. *)
      (*   - nia. *)
      (*   - reflexivity. *)
      (* } *)

      (* i. (* clear POSTCOND. *) *)
      (* inv RET. inv CPROG_AFTER_EVENT; ss. *)
      (* symmetry in EVENT. inv EVENT. *)
      (* existT_elim. unf_resum. clarify. *)
      (* rename m' into m1. *)

      (* exists (idx_run + 10). left. *)
      fw. fw. fw.
      { hexploit (in_gfun_ilist _run_task); try sIn.
        i. des.
        econs; ss.
        - eval_comput. rewrite FDEF_SYMB. ss.
        - eval_comput.
          replace (btm + period + (period + (period + 0))) with
              (btm + period * 3) by nia.
          reflexivity.
        - eauto.
        - ss.
      }

      match goal with
      | |- sim _ _ (MWITree.run_task _ _ _ _ ?tm1)
              (Callstate _ [Vlong (Int64.repr (Z.of_nat ?tm2))] _ _) =>
        replace tm1 with (btm + period * 4) in * by nia;
          replace tm2 with (btm + period * 4) in * by nia
      end.
      (* replace (btm + period + period * 2) with (btm + period * 3) by nia. *)

      eapply SIM_RUN_TASK; eauto.
      { ss. }
      { unfold MAX_TIME in *.
        range_stac. }

      i. fw. fw. fw.
      { econs.
        - eval_comput. eauto.
        - ss.
        - ss. }
      ss. pfold. econs 1; ss.
      - econs; ss.
      - econs 1.
      - ss.
    Qed.

  End SIM_INIT.
End VERIF_INIT.
