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

Import Clight Clightdefs.
Import ITreeNotations.
Import ActiveStandby.

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
  (* Hypothesis CPROG_EQ: __guard__ (cprog = prog_ctrl (Z.of_nat tid)). *)
  (* Notation prog := (prog_of_clight (prog_ctrl (Z.of_nat tid))). *)
  Notation prog := (prog_of_clight cprog).
  Notation ge := (globalenv cprog).


  Hypothesis GENV_PROPS
    : genv_props ge
                 (main_gvar_ilist tid ++ ctrl_gvar_ilist)
                 (main_gfun_ilist ++ ctrl_gfun_ilist)
                 (main_cenv_ilist ++ ctrl_cenv_ilist).

  Definition idx_cpy_hb: nat := 100.

  Inductive copy_hb_linv
            (itr0: itree progE unit) (m0: mem)
            (bs: list byte)
            b_s ofs_s b_d ofs_d
            (i: nat) (itr: itree progE unit)
            (le: PTree.t val) (m: mem): Prop :=
    CopyHBLInv
      (* (MEM_CONSTS: mem_consts ge m tid) *)
      (ITR_INV: itr = itr0)
      (LENV_EQUIV: lenv_equiv
                     le [(_hb, Vptr b_s (Ptrofs.repr ofs_s));
                        (_st, Vptr b_d (Ptrofs.repr ofs_d));
                        (_i, Vint (IntNat.of_nat i))])
      (LBS_SRC: Mem.loadbytes m b_s (ofs_s + 1) 7 =
                Some (inj_bytes bs))
      (PERM_DST: Mem.range_perm m b_d 0 8 Cur Writable)
      (SBS_DST: ((i = 1 /\ m = m0) \/
                 (1 < i /\ Mem.storebytes
                            m0 b_d (ofs_d + 1)
                            (firstn (i - 1) (inj_bytes bs)) = Some m))%nat)
  (* (PERM_DST: Mem.range_perm m b_d ofs_d (ofs_d + (Z.of_nat msg_size)) Cur Writable) *)
  .


  Lemma sim_copy_state_from_hb
        (itr: itree progE unit)
        (m: mem) (k: cont) (idx_ret: nat)
        st hb
        b_cst b_hb ofs_hb
        (BLOCKS_DIFF: b_cst <> b_hb)
        (CALL_CONT: is_call_cont k)
        (WF_ST: CtrlState.wf st)
        (RANGE_OFS_HB1: 0 <= ofs_hb <= Ptrofs.max_unsigned)
        (RANGE_OFS_HB2: 0 <= ofs_hb + 8 <= Ptrofs.max_unsigned)
        (MEM_CST: mem_cst_blk m st b_cst)
        (MEM_HB: Mem.loadbytes m b_hb ofs_hb 8 =
                 Some (inj_bytes hb))
        (SIM_RET:
           forall m' st'
             (ST': st' = copy_state_from_hb (mode st) hb)
             (MEM_CST: mem_cst_blk m' st' b_cst)
             (MEM_CH_BLK: mem_changed_block b_cst m m')
           ,
             paco3 (_sim_itree prog) r
                   idx_ret itr
                   (Returnstate Vundef k m'))
    : paco3 (_sim_itree prog) r
            (idx_ret + idx_cpy_hb)%nat itr
            (Callstate (Internal f_copy_state_from_hb)
                       [Vptr b_cst Ptrofs.zero;
                       Vptr b_hb (Ptrofs.repr ofs_hb)] k m).
  Proof.
    unfold idx_cpy_hb.

    replace 8 with (1 + 7) in MEM_HB by ss.
    eapply Mem.loadbytes_split in MEM_HB; try nia.
    destruct MEM_HB as (bs1 & bs & LBS1 & LBS & BS_EQ).

    apply Mem.loadbytes_length in LBS1.
    destruct bs1 as [| b1 []]; ss.
    destruct hb as  [| hb1 hb']; ss. clarify.

    assert(LEN_BS: length hb' = 7%nat).
    { eapply Mem.loadbytes_length in LBS.
      unfold inj_bytes in LBS.
      rewrite map_length in LBS. ss. }

    assert(LEN_INJ_BS: length (inj_bytes hb') = 7%nat).
    { unfold inj_bytes. rewrite map_length. ss. }

    start_func.
    { econs. }

    fw. clear STEP_ENTRY.
    fw. fw.
    { econs. eval_comput. eauto. }
    fw. upd_lenv.

    (* replace 7%Z with (Z.of_nat msg_size%nat) by ss. *)
    (* fold_for_loop _i . *)

    eapply simple_for_loop_gen
      with (idx_each:= 10%nat) (idx0:= 0%nat)
           (i_min := 1%nat) (i_max := 8%nat)
           (loop_inv := copy_hb_linv itr m hb'
                                     b_hb ofs_hb b_cst 0).
    { econs; eauto.
      ii. eapply MEM_CST. ss. }
    { nia. }
    { range_stac. }
    { nia. }
    { (* loop body *)
      clear dependent le. i.
      clear LBS MEM_CST.
      inv LINV.
      (* assert (I_LT: (Z.of_nat i < Z.of_nat msg_size)%Z) by nia. *)
      guardH SBS_DST.

      (* assert (SINT_I: IntRange.sint i). *)
      (* { clear - I_LT SINT_MSZ. *)
      (*   range_stac. } *)

      assert (8 < Int.max_signed) by ss.

      fw. fw. fw.
      { econs.
        - eval_comput.
          repr_tac.
          destruct (Z.ltb_spec (Z.of_nat i) 8); ss.
          nia.
        - ss.
      }
      rewrite Int.eq_false by ss. s.
      fw.

      assert (LOAD_I: exists b bs_r,
                 Mem.load Mint8signed m1 b_hb
                          (ofs_hb + Z.of_nat i) =
                 Some (Vint (Int.repr (Byte.signed b))) /\
                 hb' = firstn (i - 1) hb' ++ b :: bs_r).
      { clear - LEN_BS RANGE_I LBS_SRC.
        replace 7 with
            (Z.of_nat (i - 1) + (1 + Z.of_nat (7 - i)))%Z in LBS_SRC by nia.

        assert (BS_N: exists a, nth_error hb' (i - 1) = Some a).
        { apply Some_not_None.
          apply nth_error_Some. nia. }
        des.
        apply nth_error_split in BS_N. des. subst.

        apply Mem_loadbytes_split' in LBS_SRC; try nia.
        destruct LBS_SRC as (LB1 & LB').
        apply Mem_loadbytes_split' in LB'; try nia.
        destruct LB' as (LB2 & LB_R).
        rewrite Nat2Z.id in LB2.
        replace (Z.to_nat 1) with 1%nat in * by ss.
        unfold inj_bytes in LB2.
        rewrite map_app in LB2.
        erewrite skipn_app_exact in LB2.
        2: { rewrite map_length. ss. }
        ss.
        esplits.
        2: { rewrite firstn_app_exact; eauto. }
        erewrite Mem.loadbytes_load; eauto.
        { rewrite decode_val_signed_byte. reflexivity. }
        { replace (ofs_hb + Z.of_nat i) with
              (ofs_hb + 1 + Z.of_nat (i - 1)) by nia.
          eauto. }
        { apply Z.divide_1_l. }
      }
      destruct LOAD_I as (b & bs_r & LOAD_I & BS_EQ).

      assert (STORE_BYTE: exists m',
                   Mem.store
                     Mint8signed m1 b_cst (Z.of_nat i)
                     (Vint (Int.repr (Byte.signed b))) =
                   Some m').
      { apply inhabited_sig_to_exists.
        econs.
        apply Mem.valid_access_store.
        rr. split; ss.
        2: { apply Z.divide_1_l. }
        ii. apply PERM_DST. nia. }
      des.

      fw.
      { econs.
        - eval_comput.
          repr_tac. s.
          rewrite Z.mul_1_l.
          reflexivity.
        - eval_comput.
          repr_tac.
          rewrite Z.mul_1_l.
          eauto.
          (* cbn. *)
          (* repr_tac. *)
        - simpl.
          eval_comput.
          rewrite sign_ext_byte_range.
          2: { eapply Byte.signed_range. }
          eauto.
        - eval_comput.
          repr_tac.
          eauto.
      }

      fw.
      { econs; eauto. }
      fw.
      { econs. eval_comput.
        unfold IntNat.of_nat.
        repr_tac.
        replace (Z.of_nat i + 1)%Z
          with (Z.of_nat (S i)) by nia.
        reflexivity. }
      upd_lenv.

      fw.
      red_idx (idx1 - 10)%nat.

      eapply SIM_NEXT.
      assert (mem_unchanged_except
                (fun b ofs => b = b_cst /\ ofs = Z.of_nat i)%Z
                m1 m').
      { eapply Mem.store_unchanged_on; eauto.
        intros ofs' OFS C. apply C.
        split; ss.
        exfalso. nia. }

      eapply Mem.store_storebytes in STORE_BYTE. ss.
      unfold encode_int in *. ss.
      erewrite int_and_byte_repr in STORE_BYTE.
      2: { apply Byte.signed_range. }
      rewrite Byte.repr_signed in STORE_BYTE.
      rewrite rev_if_be_single in *.

      econs; eauto.
      + eapply Mem.loadbytes_unchanged_on; eauto.
        ii. des; ss. nia.
      + ii. eapply Mem.perm_storebytes_1; eauto.
      + right. splits; [nia|].
        unguardH SBS_DST. desH SBS_DST.
        * subst. ss. subst. ss.
        * replace (S i - 1)%nat with (S (i - 1))%nat by nia.
          erewrite firstn_snoc_nth with
              (d:= Byte Byte.zero); eauto.
          2: {
            rewrite BS_EQ.
            unfold inj_bytes.
            rewrite map_length. rewrite app_length.
            rewrite firstn_length_le by nia.
            ss. nia.
          }

          eapply Mem.storebytes_concat; eauto.
          assert (LEN_FIRSTN: length (firstn (i - 1) (inj_bytes hb')) = (i - 1)%nat).
          { apply firstn_length_le. nia. }
          rewrite LEN_FIRSTN.

          assert (nth_error (inj_bytes hb') (i - 1) =
                  Some (Byte b)).
          { unfold inj_bytes in *.
            rewrite BS_EQ. rewrite map_app.
            rewrite <- map_firstn in LEN_FIRSTN.
            rewrite nth_error_app2.
            2: { rewrite map_length in *. nia. }
            rewrite LEN_FIRSTN.
            rewrite Nat.sub_diag. ss. }
          erewrite nth_error_nth; eauto. s.
          replace (1 + Z.of_nat (i - 1)) with (Z.of_nat i) by nia.
          ss.
    }

    (* after loop *)
    clear dependent le. i.
    inv LINV_END.

    fw. fw. fw.
    { econs.
      - eval_comput.
        repr_tac.
        rewrite Z.ltb_irrefl. ss.
      - ss.
    }
    rewrite Int.eq_true. simpl.
    fw. fw. fw.

    red_idx idx_ret.

    rewrite firstn_all2 in SBS_DST by nia.
    eapply SIM_RET; eauto.
    - des.
      { exfalso. ss. }
      eapply loadbytes_mem_cst; cycle 2.
      { unfold copy_state_from_hb.
        instantiate (1:= Byte.repr (mode_to_Z (mode st))::hb').
        unfold of_bytes. ss.
        (* f_equal. *)
        (* rewrite Byte.signed_repr. *)
        (* 2: { destruct (mode st); ss. } *)
        (* destruct (mode st); ss. } *)
      }
      { eauto. }

      (* unfold copy_state_from_hb. s. *)
      (* econs; eauto. *)
      (* s. *)
      (* repeat rewrite Byte.repr_signed. *)
      unfold inj_bytes. ss.
      replace 8 with (1 + 7) by ss.
      rewrite rw_cons_app.
      apply Mem.loadbytes_concat; try nia.
      + eapply Mem.loadbytes_unchanged_on.
        { eapply storebytes_unchanged_on'; eauto. }
        { unfold mem_range.
          ii. des; ss. nia. }
        hexploit mem_cst_mode; eauto.
      + s. apply Mem.loadbytes_storebytes_same in SBS_DST0.
        rewrite LEN_INJ_BS in SBS_DST0.
        replace (Z.of_nat 7) with 7 in SBS_DST0 by ss.
        rewrite SBS_DST0.
        f_equal.
    - des.
      + subst. apply Mem.unchanged_on_refl.
      + eapply Mem.unchanged_on_implies.
        { eapply storebytes_unchanged_on'; eauto. }
        unfold mem_range.
        ii. des; ss.
  Qed.


  Local Opaque idx_cpy_hb.
  Definition idx_sync: nat := idx_cpy_hb + 30.

  Lemma sim_sync_istate
        (itr: itree progE unit)
        (m: mem) (k: cont) (idx_ret: nat)
        st inb
        b_cst b_mst ofs_inb
        (BLOCKS_DIFF: b_cst <> b_mst)
        (CALL_CONT: is_call_cont k)
        (WF_ST: CtrlState.wf st)
        (MEM_CST: mem_cst_blk m st b_cst)
        (MEM_MSTORE: Mem_inbox m b_mst ofs_inb inb)
        (RANGE_OFS_HB1: 0 <= ofs_inb <= Ptrofs.max_unsigned)
        (RANGE_OFS_HB2: 0 <= ofs_inb + inb_sz <= Ptrofs.max_unsigned)
        (SIM_RET:
           forall m' st'
             (ST': st' = sync_istate (Z.of_nat tid) st inb)
             (WF_ST': CtrlState.wf st')
             (MEM_CST: mem_cst_blk m' st' b_cst)
             (MEM_CH_BLK: mem_changed_block b_cst m m')
           ,
           paco3 (_sim_itree prog) r
                 idx_ret itr
                 (Returnstate Vundef k m'))
    : paco3 (_sim_itree prog) r
            (idx_ret + idx_sync)%nat itr
            (Callstate (Internal f_sync_istate)
                       [Vint (IntNat.of_nat tid);
                       Vptr b_cst Ptrofs.zero;
                       Vptr b_mst (Ptrofs.repr ofs_inb)] k m).
  Proof.
    unfold idx_sync.
    start_func.
    { econs. }
    ss.
    fw. fw. fw.
    { econs.
      eval_comput.
      repr_tac.
      rewrite sign_ext_byte_range.
      2: { clear - CTRL_TASK_ID.
           destruct CTRL_TASK_ID; subst; range_stac. }
      reflexivity.
    }
    upd_lenv.

    hexploit (in_cenv_ilist _inbox_t); [sIn|].
    intros CO_INBOX.
    hexploit (in_cenv_ilist _msg_entry_t); [sIn|].
    intros CO_MENT.

    fw. fw. fw.
    { econs.
      eval_comput.
      rewrite CO_INBOX. s.
      change main_prm._msg_entry_t with _msg_entry_t.
      rewrite CO_MENT.
      s. unfold align_attr. s.
      repr_tac.
      unfold Coqlib.align. s.
      rewrite Z.mul_0_r.
      rewrite Z.add_0_r.
      repr_tac.
      rewrite Z.add_0_r.
      reflexivity.
    }
    upd_lenv.

    fw. fw. fw.
    { econs.
      eval_comput.
      rewrite CO_INBOX. s.
      change main_prm._msg_entry_t with _msg_entry_t.
      rewrite CO_MENT.
      s. unfold align_attr. s.
      repr_tac.
      unfold Coqlib.align. s.
      rewrite Z.add_0_r.
      repr_tac0; cycle 1.
      { ss. }
      { hexploit (within_inb_nsz1 (3 - tid)%nat).
        { unfold num_tasks. ss. nia. }
        nia. }
      reflexivity.
    }
    upd_lenv.

    assert (RANGE_MODE: (0 <= mode_to_Z (mode st) < Byte.max_signed)).
    { destruct (mode st); ss. }

    fw. fw. fw.
    { econs.
      eval_comput.
      repr_tac. s.
      rewrite Ptrofs.add_zero_l.
      repr_tac.
      erewrite Mem.loadbytes_load; cycle 1.
      { apply mem_cst_mode; eauto. }
      { ss. solve_divide. }
      rewrite decode_val_signed_byte.
      rewrite Byte.signed_repr by range_stac.
      rewrite sign_ext_byte_range by range_stac.
      reflexivity.
    }
    upd_lenv.
    fw. fw.
    { econs.
      - eval_comput.
        repr_tac.
        reflexivity.
      - rewrite bool_val_of_bool. reflexivity.
    }

    assert (exists ment_hb,
               <<INB_HB: nth_error inb (3 - tid) = Some ment_hb>> /\
               <<MSG_HB: Mem_msg_entry m b_mst ofs_inb (3 - tid) ment_hb>>).
    { clear - CTRL_TASK_ID MEM_MSTORE.
      r in MEM_MSTORE. des.

      hexploit (nth_error_Some2 _ inb (3 - tid)).
      { rewrite NUM_ENTRIES.
        unfold num_tasks. ss.
        destruct CTRL_TASK_ID; subst; nia. }
      i. des.
      esplits; eauto.

      rewrite iForall_nth in MSG_ENTRIES.
      specialize (MSG_ENTRIES (3 - tid)%nat).
      rewrite NTH_EX in MSG_ENTRIES. ss.
    }

    assert (exists ment_tgl,
               <<INB_TGL: nth_error inb O = Some ment_tgl>> /\
               <<MSG_TGL: Mem_msg_entry m b_mst ofs_inb 0 ment_tgl>>).
    { clear - MEM_MSTORE.
      r in MEM_MSTORE. des.

      hexploit (nth_error_Some2 _ inb O).
      { rewrite NUM_ENTRIES.
        unfold num_tasks. ss. nia. }
      i. des.
      esplits; eauto.

      rewrite iForall_nth in MSG_ENTRIES.
      specialize (MSG_ENTRIES O).
      rewrite NTH_EX in MSG_ENTRIES. ss.
    }
    des.

    assert (OTID_WITHIN_INB_NSZ:
              forall ofs
                (VALID_ENTRY_AREA: (ofs <= 16)%nat),
                (16 * (3 - tid) + ofs <= inb_nsz)%nat).
    {
      i. hexploit (within_inb_nsz2 (3 - tid)%nat ofs).
      { unfold num_tasks. s. nia. }
      { ss. }
      clear.
      replace mentry_nsz with 16%nat by ss.
      nia. }

    eapply Mem_msg_entry_inv2 in MSG_HB. des.
    renames MENT_RCV MENT_CONT into HB_RCV HB_CONT.
    eapply Mem_msg_entry_inv2 in MSG_TGL. des.
    renames MENT_RCV MENT_CONT into TGL_RCV TGL_CONT.

    destruct (mode st) eqn: MODE_ST.
    - (* uninit *)
      ss.
      fw.
      { econs.
        - eval_comput.
          rewrite CO_MENT. s.
          unfold align_attr. s.
          unfold Coqlib.align. s.
          unfold mentry_nsz. s.

          replace (Z.of_nat 16 * (3 - Z.of_nat tid)) with
              (Z.of_nat (16 * (3 - tid))) by nia.

          hexploit (OTID_WITHIN_INB_NSZ O).
          { nia. }
          rewrite Nat.add_0_r. i.

          repr_tac.
          rewrite Z.add_0_r.

          unfold mentry_nsz in HB_RCV. simpl in HB_RCV.
          rewrite HB_RCV.

          instantiate (1:= if ment_hb then Vtrue else Vfalse).
          clear.
          destruct ment_hb; ss.
        - instantiate (1:= if ment_hb then true else false).
          clear.
          destruct ment_hb; ss.
      }

      destruct ment_hb as [hb_cont|].
      + (* hb received *)
        fw. fw.
        { hexploit (in_gfun_ilist _copy_state_from_hb); [sIn|].
          i. des.
          econs.
          - ss.
          - eval_comput.
            rewrite FDEF_SYMB. reflexivity.
          - eval_comput.
            rewrite CO_MENT. s.
            unfold align_attr. s.
            unfold Coqlib.align. s.
            unfold mentry_nsz. s.

            replace (Z.of_nat 16 * (3 - Z.of_nat tid)) with
                (Z.of_nat (16 * (3 - tid))) by nia.

            repr_tac0; cycle 1.
            { hexploit (OTID_WITHIN_INB_NSZ O).
              { nia. }
              i. nia. }
            { range_stac. }
            reflexivity.
          - eauto.
          - ss.
        }

        red_idx (idx_ret + 10 + idx_cpy_hb)%nat.
        eapply sim_copy_state_from_hb; eauto.
        { ss. }
        { hexploit (OTID_WITHIN_INB_NSZ 1%nat).
          { nia. }
          i. nia. }
        { hexploit (OTID_WITHIN_INB_NSZ (1 + 8)%nat).
          { nia. }
          i. nia. }

        clear MEM_CST. i.
        guardH ST'.
        fw. fw.

        assert (MEM_STORE: exists m_f, Mem.store Mint8signed m' b_cst 0 (Vint (Int.repr 2)) = Some m_f).
        { apply inhabited_sig_to_exists.
          econs.
          apply Mem.valid_access_store.
          rr. split; ss.
          2: { apply Z.divide_1_l. }
          ii. eapply MEM_CST. nia. }
        des.

        fw.
        { econs.
          - eval_comput.
            repr_tac. s.
            rewrite Ptrofs.add_zero_l. reflexivity.
          - eval_comput. reflexivity.
          - ss.
          - eval_comput.
            repr_tac.
            rewrite sign_ext_byte_range by range_stac.
            eauto.
        }
        fw.
        red_idx idx_ret.
        eapply SIM_RET; eauto.
        * apply wf_sync_istate. ss.
        * unfold sync_istate.
          rewrite MODE_ST.
          replace (Z.to_nat (3 - Z.of_nat tid))
            with (3 - tid)%nat by nia.
          erewrite nth_error_nth; eauto. s.

          hexploit (store_set_mode Standby); eauto.
          intro MEM_CST_BLK'.

          cut (set_mode Standby st' =
               copy_state_from_hb Standby hb_cont).
          { intro R. rewrite <- R. ss. }
          clear - ST'. unguard. subst.
          unfold copy_state_from_hb in *.
          unfold set_mode in *. ss.
        * eapply Mem.unchanged_on_trans; eauto.
          eapply Mem.store_unchanged_on; eauto.
      + (* hb not received *)

        assert (MEM_STORE: exists m_f, Mem.store Mint8signed m b_cst 0 (Vint (Int.repr (Z.of_nat tid))) = Some m_f).
        { apply inhabited_sig_to_exists.
          econs.
          apply Mem.valid_access_store.
          rr. split; ss.
          2: { apply Z.divide_1_l. }
          ii. eapply MEM_CST. nia. }
        des.

        fw.
        { econs.
          - eval_comput.
            repr_tac. s.
            rewrite Ptrofs.add_zero_l. reflexivity.
          - eval_comput. reflexivity.
          - ss.
          - eval_comput.
            repr_tac.
            assert (IntRange.sint8 tid).
            { clear - CTRL_TASK_ID.
              destruct CTRL_TASK_ID; subst; ss. }
            rewrite sign_ext_byte_range by range_stac.
            eauto.
        }

        fw.
        red_idx idx_ret.
        eapply SIM_RET; eauto.
        * apply wf_sync_istate. ss.
        * unfold sync_istate.
          rewrite MODE_ST.
          replace (Z.to_nat (3 - Z.of_nat tid))
            with (3 - tid)%nat by nia.
          erewrite nth_error_nth; eauto. s.

          hexploit (store_set_mode (default_mode (Z.of_nat tid))); eauto.
          cut (mode_to_Z (default_mode (Z.of_nat tid)) =
               Z.of_nat tid).
          { intro R. rewrite R. ss. }
          destruct CTRL_TASK_ID; subst; ss.
        * eapply Mem.store_unchanged_on; eauto.

    - (* active mode *)
      s.
      fw.
      { econs.
        - eval_comput.
          repr_tac.
          rewrite Z.eqb_refl. ss.
        - ss.
      }
      rewrite Int.eq_false by ss. s.
      fw. fw.
      { econs.
        - eval_comput.
          rewrite CO_MENT. s.
          unfold align_attr. s.
          unfold Coqlib.align. s.
          rewrite Ptrofs.add_zero.
          unfold mentry_nsz. s.

          replace (Z.of_nat 16 * (3 - Z.of_nat tid)) with
              (Z.of_nat (16 * (3 - tid))) by nia.

          repr_tac0; cycle 1.
          { hexploit (OTID_WITHIN_INB_NSZ O).
            { nia. }
            i. nia. }
          unfold mentry_nsz in HB_RCV. simpl in HB_RCV.
          rewrite HB_RCV.

          instantiate (1:= if ment_hb then Vtrue else Vfalse).
          destruct ment_hb; ss.
        - instantiate (1:= if ment_hb then true else false).
          destruct ment_hb; ss.
      }

      destruct ment_hb as [hb_cont | ].
      2: {
        (* hb not received *)
        fw.
        { econs. eval_comput. reflexivity. }
        upd_lenv.

        fw. fw.
        { econs.
          - eval_comput. reflexivity.
          - ss.
        }
        rewrite Int.eq_true. s.
        fw.

        red_idx idx_ret.
        eapply SIM_RET; eauto.
        - eapply wf_sync_istate. ss.
        - unfold sync_istate.
          rewrite MODE_ST.
          replace (Z.to_nat (3 - Z.of_nat tid))
            with (3 - tid)%nat by nia.
          erewrite nth_error_nth; eauto. ss.
        - apply Mem.unchanged_on_refl.
      }

      rewrite Nat.mul_0_r in TGL_RCV.
      replace (ofs_inb + Z.of_nat 0) with ofs_inb in TGL_RCV by nia.

      fw.
      { econs.
        eval_comput.
        rewrite CO_MENT. s.
        unfold align_attr. s.
        unfold Coqlib.align. s.
        rewrite Ptrofs.add_zero.
        repr_tac.

        rewrite TGL_RCV.
        instantiate (1:= if ment_tgl then Vtrue else Vfalse).
        destruct ment_tgl; ss.
      }
      upd_lenv.

      fw. fw.
      { econs.
        - eval_comput. ss.
        - ss.
          instantiate (1:= if ment_tgl then true else false).
          destruct ment_tgl; ss.
      }
      destruct ment_tgl.
      2: {
        fw.
        red_idx idx_ret.
        eapply SIM_RET; eauto.
        - eapply wf_sync_istate. ss.
        - unfold sync_istate.
          rewrite MODE_ST.
          replace (Z.to_nat (3 - Z.of_nat tid))
            with (3 - tid)%nat by nia.
          erewrite nth_error_nth; eauto. ss.
          erewrite nth_error_nth; eauto. ss.
        - apply Mem.unchanged_on_refl.
      }


      assert (MEM_STORE: exists m_f, Mem.store Mint8signed m b_cst 0 (Vint (Int.repr 2)) = Some m_f).
      { apply inhabited_sig_to_exists.
        econs.
        apply Mem.valid_access_store.
        rr. split; ss.
        2: { apply Z.divide_1_l. }
        ii. eapply MEM_CST. nia. }
      des.

      fw.
      { econs.
        - eval_comput.
          repr_tac. s.
          rewrite Ptrofs.add_zero. reflexivity.
        - eval_comput. reflexivity.
        - ss.
        - eval_comput.
          rewrite sign_ext_byte_range by range_stac.
          eauto.
      }

      fw.
      red_idx idx_ret.
      eapply SIM_RET; eauto.
      + eapply wf_sync_istate. ss.
      + unfold sync_istate.
        rewrite MODE_ST.
        replace (Z.to_nat (3 - Z.of_nat tid))
          with (3 - tid)%nat by nia.
        erewrite nth_error_nth; eauto. ss.
        erewrite nth_error_nth; eauto. ss.

        hexploit (store_set_mode Standby); eauto.
      + eapply Mem.store_unchanged_on; eauto.

    - (* Standby mode *)
      ss.
      fw.
      { econs.
        - eval_comput.
          repr_tac. s. ss.
        - ss.
      }
      rewrite Int.eq_true by ss. s.

      fw.
      { econs.
        - eval_comput.
          rewrite CO_MENT. s.
          unfold align_attr. s.
          unfold Coqlib.align. s.
          unfold mentry_nsz. s.

          replace (Z.of_nat 16 * (3 - Z.of_nat tid)) with
              (Z.of_nat (16 * (3 - tid))) by nia.

          hexploit (OTID_WITHIN_INB_NSZ O).
          { nia. }
          rewrite Nat.add_0_r. i.

          repr_tac.
          rewrite Z.add_0_r.

          unfold mentry_nsz in HB_RCV. simpl in HB_RCV.
          rewrite HB_RCV.

          instantiate (1:= if ment_hb then Vtrue else Vfalse).
          clear.
          destruct ment_hb; ss.
        - instantiate (1:= if ment_hb then true else false).
          clear.
          destruct ment_hb; ss.
      }

      destruct ment_hb as [hb_cont|].
      + (* hb received *)
        fw. fw.
        { hexploit (in_gfun_ilist _copy_state_from_hb); [sIn|].
          i. des.
          econs.
          - ss.
          - eval_comput.
            rewrite FDEF_SYMB. reflexivity.
          - eval_comput.
            rewrite CO_MENT. s.
            unfold align_attr. s.
            unfold Coqlib.align. s.
            unfold mentry_nsz. s.

            replace (Z.of_nat 16 * (3 - Z.of_nat tid)) with
                (Z.of_nat (16 * (3 - tid))) by nia.

            repr_tac0; cycle 1.
            { hexploit (OTID_WITHIN_INB_NSZ O).
              { nia. }
              i. nia. }
            { range_stac. }
            reflexivity.
          - eauto.
          - ss.
        }

        red_idx (idx_ret + 10 + idx_cpy_hb)%nat.
        eapply sim_copy_state_from_hb; eauto.
        { ss. }
        { hexploit (OTID_WITHIN_INB_NSZ 1%nat).
          { nia. }
          i. nia. }
        { hexploit (OTID_WITHIN_INB_NSZ (1 + 8)%nat).
          { nia. }
          i. nia. }

        clear MEM_CST. i.
        guardH ST'.
        fw.

        fw. fw.
        { econs.
          - eval_comput.
            rewrite CO_MENT. s.
            unfold align_attr. s.
            unfold Coqlib.align. s.

            repr_tac.
            rewrite Z.add_0_r.

            replace (ofs_inb + Z.of_nat (mentry_nsz * 0))
              with ofs_inb in TGL_RCV by nia.

            eapply Mem.load_unchanged_on in TGL_RCV; cycle 1.
            { eapply MEM_CH_BLK. }
            { ii. subst. ss. }

            rewrite TGL_RCV.

            instantiate (1:= if ment_tgl then Vtrue else Vfalse).
            clear.
            destruct ment_tgl; ss.
          - instantiate (1:= if ment_tgl then true else false).
            clear.
            destruct ment_tgl; ss.
        }

        destruct ment_tgl.
        2: {
          fw.
          red_idx idx_ret.

          eapply SIM_RET; eauto.
          * apply wf_sync_istate. ss.
          * unfold sync_istate.
            rewrite MODE_ST.
            replace (Z.to_nat (3 - Z.of_nat tid))
              with (3 - tid)%nat by nia.
            erewrite nth_error_nth; eauto. s.
            erewrite nth_error_nth; eauto. s.

            rewrite MODE_ST in ST'.
            rewrite <- ST'. ss.
        }

        assert (MEM_STORE: exists m_f, Mem.store Mint8signed m' b_cst 0 (Vint (Int.repr 1)) = Some m_f).
        { apply inhabited_sig_to_exists.
          econs.
          apply Mem.valid_access_store.
          rr. split; ss.
          2: { apply Z.divide_1_l. }
          ii. eapply MEM_CST. nia. }
        des.

        fw.
        { econs.
          - eval_comput.
            repr_tac. s.
            rewrite Ptrofs.add_zero_l. reflexivity.
          - eval_comput. reflexivity.
          - ss.
          - eval_comput.
            repr_tac.
            rewrite sign_ext_byte_range by range_stac.
            eauto.
        }
        fw.
        red_idx idx_ret.
        eapply SIM_RET; eauto.
        * apply wf_sync_istate. ss.
        * unfold sync_istate.
          rewrite MODE_ST.
          replace (Z.to_nat (3 - Z.of_nat tid))
            with (3 - tid)%nat by nia.
          erewrite nth_error_nth; eauto. s.
          erewrite nth_error_nth; eauto. s.

          hexploit (store_set_mode Active); eauto.
          intro MEM_CST_BLK'.

          cut (set_mode Active st' =
               copy_state_from_hb Active hb_cont).
          { intro R. rewrite <- R. ss. }
          clear - ST'. unguard. subst.
          unfold copy_state_from_hb in *.
          unfold set_mode in *. ss.
        * eapply Mem.unchanged_on_trans; eauto.
          eapply Mem.store_unchanged_on; eauto.
      + (* hb not received *)

        assert (MEM_STORE: exists m_act, Mem.store Mint8signed m b_cst 0 (Vint (Int.repr 1)) = Some m_act).
        { apply inhabited_sig_to_exists.
          econs.
          apply Mem.valid_access_store.
          rr. split; ss.
          2: { apply Z.divide_1_l. }
          ii. eapply MEM_CST. nia. }
        des.

        fw. fw.
        { econs.
          - eval_comput.
            repr_tac. s.
            rewrite Ptrofs.add_zero_l. reflexivity.
          - eval_comput. reflexivity.
          - ss.
          - eval_comput.
            repr_tac.
            rewrite sign_ext_byte_range by range_stac.
            eauto.
        }

        fw. fw.
        { econs.
          - eval_comput.
            rewrite Ptrofs.add_zero_l.
            repr_tac. s.
            erewrite Mem.loadbytes_load; cycle 1.
            { erewrite Mem.loadbytes_store_other; eauto.
              { apply mem_cst_tout; eauto. }
              ss. nia.
            }
            { ss. solve_divide. }
            eval_comput.
            instantiate (1:= if (timeout st) =? MAX_TIMEOUT
                             then Vtrue else Vfalse).

            rewrite decode_byte.
            rewrite sign_ext_byte_range_u.
            2: { inv WF_ST. ss. }
            rewrite Int_eq_repr_signed; cycle 1.
            { inv WF_ST. s.
              range_stac. }
            { range_stac. }
            desf.
          - ss.
            instantiate (1:= timeout st =? MAX_TIMEOUT).
            desf.
        }

        fold MAX_TIMEOUT.
        destruct (Z.eqb_spec (timeout st) MAX_TIMEOUT).
        2: {
          fw.
          red_idx idx_ret.
          eapply SIM_RET; eauto.
          * apply wf_sync_istate. ss.
          * unfold sync_istate.
            rewrite MODE_ST.
            replace (Z.to_nat (3 - Z.of_nat tid))
              with (3 - tid)%nat by nia.
            erewrite nth_error_nth; eauto. s.

            unfold activate_nhb.
            destruct st as [md tout qb qe q]. ss.
            destruct (Z.eqb_spec tout MAX_TIMEOUT); ss.
            hexploit (store_set_mode Active); eauto.
          * eapply Mem.store_unchanged_on; eauto.
        }

        assert (MEM_STORE_F: exists m_f, Mem.store Mint8signed m_act b_cst 1 (Vint (Int.repr 0)) = Some m_f).
        { apply inhabited_sig_to_exists.
          econs.
          apply Mem.valid_access_store.
          rr. split; ss.
          2: { apply Z.divide_1_l. }
          ii.
          eapply Mem.perm_store_1; eauto.
          eapply MEM_CST. nia. }
        des.

        fw.
        { econs; ss.
          - eval_comput.
            repr_tac. s.
            rewrite Ptrofs.add_zero_l. reflexivity.
          - eval_comput. reflexivity.
          - ss.
          - eval_comput.
            repr_tac.
            rewrite sign_ext_byte_range.
            2: { range_stac. }
            eauto.
        }

        fw.
        red_idx idx_ret.
        eapply SIM_RET; eauto.
        * apply wf_sync_istate. ss.
        * unfold sync_istate.
          rewrite MODE_ST.
          replace (Z.to_nat (3 - Z.of_nat tid))
            with (3 - tid)%nat by nia.
          erewrite nth_error_nth; eauto. s.

          unfold activate_nhb.
          destruct st as [md tout qb qe q]. ss.
          destruct (Z.eqb_spec tout MAX_TIMEOUT); ss.

          econs; ss.
          -- erewrite Mem.loadbytes_store_other; eauto.
             2: { nia. }
             apply Mem.loadbytes_store_same in MEM_STORE.
             simpl in MEM_STORE.
             rewrite MEM_STORE. ss.
          -- apply Mem.loadbytes_store_same in MEM_STORE_F.
             simpl in MEM_STORE_F.
             rewrite MEM_STORE_F. ss.
          -- erewrite Mem.loadbytes_store_other; eauto.
             2: { ss. nia. }
             erewrite Mem.loadbytes_store_other; eauto.
             apply MEM_CST.
          -- erewrite Mem.loadbytes_store_other; eauto.
             erewrite Mem.loadbytes_store_other; eauto.
             apply MEM_CST.
          -- erewrite Mem.loadbytes_store_other; eauto.
             erewrite Mem.loadbytes_store_other; eauto.
             apply MEM_CST.
          -- ii.
             eapply Mem.perm_store_1; eauto.
             eapply Mem.perm_store_1; eauto.
             apply MEM_CST. ss.
        * eapply Mem.unchanged_on_trans.
          { eapply Mem.store_unchanged_on; eauto. }
          { eapply Mem.store_unchanged_on; eauto. }
  Qed.

End VERIF_FUNC.
