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


Fixpoint adv_qidx_n (n: nat) (i:Z): Z :=
  match n with
  | O => i
  | S n' => adv_qidx (adv_qidx_n n' i)
  end.

Lemma range_adv_qidx_n_prec
  : forall n i
      (RANGE_I: 0 <= i < 4),
    0 <= adv_qidx_n n i < 4.
Proof.
  i. destruct n; ss.
  apply range_qrange_sanitize_prec.
Qed.


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

  Local Opaque idx_qs idx_aqi.
  Definition idx_addq: nat := idx_qs + (idx_aqi + 30) * 3 + 30.

  (* Ltac step_fptr_tac := *)
  (*   match goal with *)
  (*   | |- context [Evar ?fid] => *)
  (*     hexploit (in_gfun_ilist fid); [sIn|]; []; *)
  (*     i; des; *)
  (*     econs; [ss| eval_comput | eval_comput | eauto | ss] *)
  (*   end. *)

  Inductive addq_linv
            (itr0: itree progE unit) (m0: mem)
            b_cst id_dev md tout qb qe q
            (i: nat) (itr: itree progE unit)
            (le: PTree.t val) (m: mem): Prop :=
    AddqLoopInv
      st csr
      v_d1 v_d2 v_d3
      (ITR_INVAR: itr = itr0)
      (MEM_INVAR: m = m0)
      (STATE: st = mk md tout qb qe q)
      (RES_EQ: try_add_queue st id_dev =
               try_add_queue_loop st id_dev (3 - i) csr)
      (* (CURSOR: csr = qrange_sanitize (qb + Z.of_nat i)) *)
      (CURSOR: csr = adv_qidx_n i (qrange_sanitize qb))
      (* qrange_sanitize (qb + Z.of_nat i)) *)
      (LENV_EQUIV:
         lenv_equiv le
                    [(_id_dev, Vint (Int.repr id_dev));
                    (_st, Vptr b_cst Ptrofs.zero);
                    (_qb, Vint (Int.repr qb));
                    (_qe, Vint (Int.repr qe));
                    (_q, Vptr b_cst (Ptrofs.repr 4));
                    (_csr, Vint (Int.repr csr));
                    (_i, Vint (Int.repr (Z.of_nat i)));
                    (_tid, v_d1); (_t'3, v_d2); (_t'2, v_d3);
                    (_t'1, Vint (Int.repr (qrange_sanitize qb)))])
  .


  Lemma sim_try_add_queue
        (itr: itree progE unit)
        (m: mem) (k: cont) (idx_ret: nat)
        st id_dev b_cst
        (CALL_CONT: is_call_cont k)
        (WF_ST: CtrlState.wf st)
        (MEM_CST: mem_cst_blk m st b_cst)
        (* (MEM_MSTORE: Mem_inbox m b_mst ofs_inb inb) *)
        (* (RANGE_OFS_HB: 0 <= ofs_inb <= Ptrofs.max_unsigned) *)
        (RANGE_ID_DEV: IntRange.sintz8 id_dev)
        (SIM_RET:
           forall m' st'
             (ST': st' = try_add_queue st id_dev)
             (MEM_CST: mem_cst_blk m' st' b_cst)
             (MEM_CH_BLK: mem_changed_block b_cst m m')
           ,
           paco3 (_sim_itree prog) r
                 idx_ret itr
                 (Returnstate Vundef k m'))
    : paco3 (_sim_itree prog) r
            (idx_ret + idx_addq)%nat itr
            (Callstate (Internal f_try_add_queue)
                       [Vptr b_cst Ptrofs.zero;
                       Vint (Int.repr id_dev)] k m).
  Proof.
    unfold idx_addq.
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

    red_idx (idx_ret + 3 * (idx_aqi + 30) + 15 + idx_qs)%nat.
    eapply sim_qrange_sanitize.
    { ss. }
    { inv WF_ST. range_stac. }

    fw. upd_lenv.
    fw. fw.
    { econs. eval_comput.
      rewrite sign_ext_byte_range.
      2: { apply range_qrange_sanitize. }
      reflexivity.
    }
    upd_lenv.

    fw. fw. fw.
    { econs. eval_comput. reflexivity. }
    upd_lenv.
    fw.

    eapply simple_for_loop
      with
        (i_max := 3%nat) (idx_each := (idx_aqi + 30)%nat)
        (idx0 := (idx_ret + 5)%nat)
        (loop_inv := addq_linv itr m b_cst id_dev
                               md tout qb qe q).
    { econs; eauto. ss. }
    { range_stac. }
    { nia. }
    { (* loop body *)
      clear le LENV_EQUIV.
      i. inv LINV.

      pose (cursor := adv_qidx_n i (qrange_sanitize qb)).
      fold cursor in LENV_EQUIV, RES_EQ.

      fw. fw. fw.
      { econs.
        - eval_comput.
          repr_tac.
          replace 3 with (Z.of_nat 3) by ss.
          rewrite <- Nat2Z_inj_ltb.
          destruct (Nat.ltb_spec i 3); ss.
          exfalso. nia.
        - ss.
      }
      rewrite Int.eq_false by ss. s.


      assert (CURSOR_SMALL: 0 <= cursor < 4).
      { apply range_adv_qidx_n_prec.
        apply range_qrange_sanitize_prec. }
      assert (BYTE_4_AUX: 4 < Byte.max_signed) by ss.

      assert (ADV_QIDX_SMALL: (0 <= adv_qidx cursor < 4)).
      { apply range_adv_qidx_prec. }

      fw. fw. fw.
      { econs.
        - eval_comput.
          rewrite Int_eq_repr_signed; cycle 1.
          { range_stac. }
          { inv WF_ST. range_stac. }
          reflexivity.
        - rewrite bool_val_of_bool.
          reflexivity.
      }

      replace (3 - i)%nat with (S (3 - (S i))) in RES_EQ by nia.
      simpl in RES_EQ.

      destruct (Z.eqb_spec cursor qe) as [CEQ|CNE]; ss.
      { (* reached end_of_queue *)
        guardH CEQ.
        fw.

        assert (STORE_BYTE: exists m',
                   Mem.store
                     Mint8signed m b_cst (4 + cursor)
                     (Vint (Int.repr id_dev)) = Some m').
        { apply inhabited_sig_to_exists.
          econs.
          apply Mem.valid_access_store.
          rr. split; ss.
          2: { apply Z.divide_1_l. }
          ii. apply MEM_CST. nia. }
        des.

        fw.
        { econs.
          - eval_comput.
            repr_tac.
            rewrite Z.mul_1_l. reflexivity.
          - eval_comput.
            reflexivity.
          - ss.
          - eval_comput.
            repr_tac.
            rewrite sign_ext_byte_range by ss.
            eauto.
        }
        fw. fw. fw. fw.
        { step_fptr_tac. }

        red_idx (idx1 - idx_aqi - 15 + idx_aqi)%nat.
        eapply sim_adv_qidx; eauto.
        { eapply GENV_PROPS. }
        { ss. }
        { range_stac. }
        fw. upd_lenv.

        assert (STORE_F:
                  exists m_f, Mem.store Mint8signed
                                   m' b_cst 3 (Vint (Int.repr (adv_qidx cursor))) = Some m_f).
        { apply inhabited_sig_to_exists.
          econs.
          apply Mem.valid_access_store.
          rr. split; ss.
          2: { apply Z.divide_1_l. }
          ii.
          eapply Mem.perm_store_1; eauto.
          apply MEM_CST. nia. }
        des.

        fw. fw.
        { econs.
          - eval_comput.
            repr_tac. s.
            rewrite Ptrofs.add_zero_l.
            reflexivity.
          - eval_comput. reflexivity.
          - ss.
          - eval_comput.
            rewrite sign_ext_byte_range by range_stac.
            repr_tac.
            eauto.
        }
        fw. fw. fw. fw.

        assert (MEM_UNCH_TOT:
                  mem_unchanged_except
                    (fun b ofs => b = b_cst /\
                               (ofs = 3 \/ 4 <= ofs < 8))
                    m m_f).
        { eapply Mem.unchanged_on_trans.
          - eapply Mem.store_unchanged_on; eauto.
            s. ii. des. nia.
          - eapply Mem.store_unchanged_on; eauto.
            s. ii. des. nia.
        }

        red_idx idx_ret.
        eapply SIM_RET; eauto.
        - rewrite RES_EQ.
          inv MEM_CST.
          econs; ss.
          + erewrite Mem.loadbytes_unchanged_on; eauto.
            s. nia.
          + erewrite Mem.loadbytes_unchanged_on; eauto.
            s. nia.
          + erewrite Mem.loadbytes_unchanged_on; eauto.
            s. nia.
          + apply Mem.loadbytes_store_same in STORE_F. ss.
            rewrite STORE_F.
            unfold encode_int. ss.
            rewrite rev_if_be_single. ss.
            rewrite Int.unsigned_repr by range_stac.
            reflexivity.
          + eapply Mem.loadbytes_unchanged_on.
            { eapply store_unchanged_on'; eauto. }
            { i. unfold mem_range. ss. nia. }

            eapply (set_queue_mem cursor id_dev); eauto.
          + ii.
            eapply Mem.perm_store_1; eauto.
            eapply Mem.perm_store_1; eauto.
        - eapply Mem.unchanged_on_implies; eauto.
          s. ii. des; ss.
      }

      (* not reached the end yet *)
      fw. fw.

      assert (NCSR: exists ncsr, Z.of_nat ncsr = cursor).
      { exists (Z.to_nat cursor). nia. }
      des.

      hexploit (nth_error_Some2 _ q ncsr).
      { inv WF_ST. nia. }
      i. des. renames e1 NTH_EX into q_c Q_C.

      assert (RANGE_Q_C: IntRange.sintz8 q_c).
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
          - eapply mem_cst_q; eauto.
          - s. apply map_nth_error_iff.
            esplits; eauto.
        }
        { s. solve_divide. }
        { rewrite decode_val_signed_byte.
          rewrite Byte.signed_repr by ss.
          rewrite sign_ext_byte_range by ss.
          reflexivity. }
      }
      upd_lenv.
      fw. fw. fw.
      { econs.
        - eval_comput.
          rewrite Int_eq_repr_signed by range_stac.
          reflexivity.
        - rewrite bool_val_of_bool. reflexivity.
      }

      unfold get_queue in RES_EQ.
      erewrite nth_error_nth in RES_EQ.
      2: { rewrite <- NCSR.
           rewrite Nat2Z.id. eauto. }

      destruct (Z.eqb_spec q_c id_dev) as [EQ_CUR | NEQ_CUR].
      { (* id_dev already in queue *)
        guardH EQ_CUR.
        fw. fw. fw.

        red_idx idx_ret.
        eapply SIM_RET; eauto.
        - rewrite RES_EQ. ss.
        - apply Mem.unchanged_on_refl.
      }

      fw. fw. fw.
      { step_fptr_tac. }

      red_idx (idx1 - idx_aqi - 15 + idx_aqi)%nat.
      eapply sim_adv_qidx.
      { apply GENV_PROPS. }
      { ss. }
      { range_stac. }
      fw. upd_lenv.
      fw. fw.
      { econs. eval_comput.
        rewrite sign_ext_byte_range by range_stac.
        reflexivity. }
      upd_lenv.

      fw.
      { econs. eauto. }
      repeat (rewrite <- Nat.add_assoc; ss).
      fw.
      { econs. eval_comput.
        repr_tac.
        replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by nia.
        reflexivity. }
      fw. upd_lenv.

      red_idx (idx1 - (idx_aqi + 30))%nat.
      eapply SIM_NEXT.
      econs; eauto.
    }

    clear le LENV_EQUIV.
    i. inv LINV_END.
    fw. fw. fw.
    { econs.
      - eval_comput.
        repr_tac.
        replace (Z.of_nat 3) with 3 by ss.
        rewrite Z.ltb_irrefl. ss.
      - ss.
    }

    rewrite Int.eq_true by ss. s.
    fw. fw.
    red_idx (idx_ret + 1)%nat.
    fw.

    red_idx idx_ret.
    eapply SIM_RET; eauto.
    - rewrite RES_EQ. ss.
    - apply Mem.unchanged_on_refl.
  Qed.


  Definition idx_rel: nat := idx_qs + 50.

  Lemma sim_try_release
        (itr: itree progE unit)
        (m: mem) (k: cont) (idx_ret: nat)
        st id_dev b_cst
        (CALL_CONT: is_call_cont k)
        (WF_ST: CtrlState.wf st)
        (MEM_CST: mem_cst_blk m st b_cst)
        (RANGE_ID_DEV: IntRange.sintz8 id_dev)
        (* (MEM_MSTORE: Mem_inbox m b_mst ofs_inb inb) *)
        (* (RANGE_OFS_HB: 0 <= ofs_inb <= Ptrofs.max_unsigned) *)
        (SIM_RET:
           forall m' st'
             (ST': st' = try_release st id_dev)
             (MEM_CST: mem_cst_blk m' st' b_cst)
             (MEM_CH_BLK: mem_changed_block b_cst m m')
           ,
           paco3 (_sim_itree prog) r
                 idx_ret itr
                 (Returnstate Vundef k m'))
    : paco3 (_sim_itree prog) r
            (idx_ret + idx_rel)%nat itr
            (Callstate (Internal f_try_release)
                       [Vptr b_cst Ptrofs.zero;
                       Vint (Int.repr id_dev)] k m).
  Proof.
    unfold idx_rel.
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

    fw. fw. fw.
    { econs.
      - eval_comput.
        inv WF_ST.
        rewrite Int_eq_repr_signed by range_stac.
        reflexivity.
      - rewrite bool_val_of_bool. reflexivity.
    }

    destruct (Z.eqb_spec qb qe).
    { s.
      (* destruct (Z.ltb_spec 0 tout). *)
      (* 2: { (* do nothing *) *)
      fw.
      { econs. eval_comput. reflexivity. }
      upd_lenv.
      fw. fw.
      { econs.
        - eval_comput. reflexivity.
        - ss. }
      rewrite Int.eq_true by ss. s.
      fw.

      red_idx idx_ret.
      eapply SIM_RET; eauto.
      apply Mem.unchanged_on_refl.
    }

    s.
    fw. fw.
    { step_fptr_tac. }

    red_idx (idx_ret + 20 + idx_qs)%nat.
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
      rewrite Int_eq_repr_signed; cycle 1.
      { range_stac. }
      { range_stac. }
      instantiate (1:= if (q_n =? id_dev) then Vtrue else Vfalse).
      destruct (Z.eqb_spec q_n id_dev); ss.
    }

    upd_lenv.
    fw.

    unfold get_queue in SIM_RET.
    erewrite nth_error_nth in SIM_RET.
    2: { eauto. }

    destruct (Z.eqb_spec q_n id_dev).
    2: { (* do nothing *)
      fw.
      { econs.
        - eval_comput. ss.
        - ss.
      }
      rewrite Int.eq_true by ss. s.
      fw.

      red_idx idx_ret.
      eapply SIM_RET; eauto.
      apply Mem.unchanged_on_refl.
    }

    (* update timeout *)
    fw.
    { econs.
      - eval_comput. reflexivity.
      - ss. }
    rewrite Int.eq_false by ss. s.

    assert (STORE_F:
              exists m_f, Mem.store Mint8signed
                               m b_cst 1 (Vint (Int.repr 1)) = Some m_f).
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
        repr_tac0; cycle 1.
        { range_stac. }
        { inv WF_ST. range_stac. }
        reflexivity.
      - s. rewrite bool_val_of_bool.
        reflexivity.
    }

    destruct (Z.ltb_spec 0 tout).
    2: {
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
      apply Mem.unchanged_on_refl.
    }

    destruct (Z.ltb_spec tout MAX_TIMEOUT).
    2: {
      ss.
      fw.
      { econs. eval_comput.
        inv WF_ST.
        repr_tac.
        fold MAX_TIMEOUT.
        instantiate (1:= Vfalse).
        destruct (Z.ltb_spec tout MAX_TIMEOUT); ss.
        exfalso. nia.
      }
      fw. upd_lenv.
      fw.
      { econs.
        - eval_comput. ss.
        - ss.
      }
      rewrite Int.eq_true. s.
      fw.
      red_idx idx_ret.
      eapply SIM_RET; eauto.
      apply Mem.unchanged_on_refl.
    }

    fw.
    { econs. eval_comput.
      inv WF_ST.
      repr_tac.
      fold MAX_TIMEOUT.
      destruct (Z.ltb_spec tout MAX_TIMEOUT); ss.
      exfalso. nia.
    }
    rewrite Int.eq_false by ss.
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
        repr_tac. s.
        rewrite Ptrofs.add_zero_l. ss.
      - eval_comput. ss.
      - s. ss.
      - eval_comput.
        rewrite sign_ext_byte_range by ss.
        repr_tac. eauto.
    }

    fw.
    red_idx idx_ret.
    eapply SIM_RET; eauto.
    - inv MEM_CST.
      hexploit store_unchanged_on'; eauto. i.

      econs; ss.
      + eapply Mem.loadbytes_unchanged_on; eauto.
        unfold mem_range. ii. nia.
      + apply Mem.loadbytes_store_same in STORE_F. ss.
      + eapply Mem.loadbytes_unchanged_on; eauto.
        unfold mem_range. ii. nia.
      + eapply Mem.loadbytes_unchanged_on; eauto.
        unfold mem_range. ii. nia.
      + eapply Mem.loadbytes_unchanged_on; eauto.
        unfold mem_range. ii. nia.
      + ii. eapply Mem.perm_store_1; eauto.
    - eapply Mem.store_unchanged_on; eauto.
  Qed.


  Definition idx_appdev: nat := idx_addq + idx_rel + 20.

  Lemma sim_apply_devmsg
        (itr: itree progE unit)
        (m: mem) (k: cont) (idx_ret: nat)
        st id_dev ment
        b_cst b_mst ofs_inb
        (BLOCKS_DIFF: b_cst <> b_mst)
        (CALL_CONT: is_call_cont k)
        (WF_ST: CtrlState.wf st)
        (MEM_CST: mem_cst_blk m st b_cst)
        (MEM_MSTORE: Mem_msg_entry m b_mst ofs_inb id_dev ment)
        (ID_DEV_UBND: (id_dev < num_tasks)%nat)
        (RANGE_OFS_INB: 0 <= ofs_inb <= 4 + inb_sz)
        (* (RANGE_OFS_HB: 0 <= ofs_inb + Z.of_nat (mentry_nsz * id_dev) <= Ptrofs.max_unsigned) *)
        (SIM_RET:
           forall m' st'
             (ST': st' = apply_devmsg st (Z.of_nat id_dev) ment)
             (MEM_CST: mem_cst_blk m' st' b_cst)
             (MEM_CH_BLK: mem_changed_block b_cst m m')
           ,
           paco3 (_sim_itree prog) r
                 idx_ret itr
                 (Returnstate Vundef k m'))
    : paco3 (_sim_itree prog) r
            (idx_ret + idx_appdev)%nat itr
            (Callstate (Internal f_apply_devmsg)
                       [ Vptr b_cst Ptrofs.zero;
                       Vint (IntNat.of_nat id_dev);
                       Vptr b_mst (Ptrofs.repr (ofs_inb + Z.of_nat (mentry_nsz * id_dev)))] k m).
  Proof.
    unfold idx_appdev.

    start_func.
    { econs. }
    ss.

    hexploit (in_cenv_ilist _msg_entry_t); [sIn|].
    intros CO_MENTRY.

    hexploit Mem_msg_entry_inv2; eauto. i. des.

    generalize (within_inb_nsz2 id_dev); eauto.
    intro RANGE_MENTRY_AUX.
    pose proof ptr_range_mstore as PRANGE_MSTORE.
    replace (Z.of_nat (4 + inb_nsz + inb_nsz)) with
        (4 + inb_sz + inb_sz) in PRANGE_MSTORE by ss.

    fw. fw.
    { hexploit (RANGE_MENTRY_AUX O); eauto.
      { nia. }
      rewrite Nat.add_0_r. intro AUX.
      clear RANGE_MENTRY_AUX.

      econs.
      - eval_comput.
        rewrite CO_MENTRY. s.
        unfold align_attr. s.
        unfold Coqlib.align. s.
        repr_tac.
        rewrite Z.add_0_r.
        rewrite MENT_RCV.
        instantiate (1:= if ment then Vtrue else Vfalse).
        destruct ment; ss.
      - instantiate (1:= if ment then true else false).
        destruct ment; ss.
    }

    destruct ment as [msg_dev|].
    2: { (* do nothing *)
      fw.
      red_idx idx_ret.
      eapply SIM_RET; eauto.
      apply Mem.unchanged_on_refl.
    }

    hexploit MENT_CONT; eauto.
    clear MENT_CONT. intro MENT_CONT.

    hexploit Mem.loadbytes_length; eauto.
    rewrite Nat2Z.id.
    intro LEN_INJ_MSG.

    destruct msg_dev as [| mdev_h mdev_t]; ss.

    replace (Z.of_nat 8) with (1 + 7) in MENT_CONT by ss.
    eapply Mem_loadbytes_split' with (n1:= 1) in MENT_CONT; try nia.
    rewrite rw_cons_app in MENT_CONT.
    replace (Z.to_nat 1) with 1%nat in MENT_CONT by ss.
    rewrite firstn_app_exact in MENT_CONT by ss.
    rewrite skipn_app_exact in MENT_CONT by ss.
    des.

    fw. fw.
    { econs.
      eval_comput.
      instantiate (1:= Vint (Int.repr (Byte.signed mdev_h))).

      rewrite CO_MENTRY. s.
      unfold align_attr. s.
      unfold Coqlib.align. s.

      hexploit (RANGE_MENTRY_AUX O); eauto.
      { nia. }
      rewrite Nat.add_0_r. intro AUX0.
      hexploit (RANGE_MENTRY_AUX 1%nat); eauto.
      { unfold mentry_nsz. nia. }
      intro AUX1.

      repr_tac.
      erewrite Mem.loadbytes_load; cycle 1.
      { s. rewrite Z.add_0_r.
        apply MENT_CONT. }
      { s. solve_divide. }
      s.
      rewrite decode_byte.
      rewrite <- (Byte.repr_signed mdev_h).
      rewrite sign_ext_byte_range_u.
      2: { apply Byte.signed_range. }
      rewrite sign_ext_byte_range.
      2: { apply Byte.signed_range. }
      rewrite Byte.signed_repr.
      2: { apply Byte.signed_range. }
      ss.
    }
    upd_lenv.

    fw. fw.
    { econs.
      - eval_comput.
        rewrite Int_eq_repr_signed; cycle 1.
        { generalize (Byte.signed_range mdev_h).
          range_stac. }
        { range_stac. }
        reflexivity.
      - rewrite bool_val_of_bool. reflexivity.
    }

    destruct (Z.eqb_spec (Byte.signed mdev_h) 1).
    - fw.
      { step_fptr_tac. }

      red_idx (idx_ret + 10 + idx_addq)%nat.
      unfold IntNat.of_nat.

      assert (RANGE_ID_DEV: IntRange.sintz8 (Z.of_nat id_dev)).
      { pose proof range_num_tasks as RANGE_NT.
        range_stac. }

      rewrite sign_ext_byte_range by range_stac.
      eapply sim_try_add_queue; eauto.
      { ss. }

      clear MEM_CST. i.
      fw. fw.

      red_idx idx_ret.
      eapply SIM_RET; eauto.
    - fw.
      { step_fptr_tac. }

      red_idx (idx_ret + 10 + idx_rel)%nat.
      unfold IntNat.of_nat.

      assert (RANGE_ID_DEV: IntRange.sintz8 (Z.of_nat id_dev)).
      { pose proof range_num_tasks as RANGE_NT.
        range_stac. }

      rewrite sign_ext_byte_range by range_stac.
      eapply sim_try_release; eauto.
      { ss. }

      clear MEM_CST. i.
      fw. fw.

      red_idx idx_ret.
      eapply SIM_RET; eauto.
  Qed.


  Definition idx_redto: nat := idx_aqi + 50.

  Lemma sim_reduce_timeout
        (itr: itree progE unit)
        (m: mem) (k: cont) (idx_ret: nat)
        st b_cst
        (CALL_CONT: is_call_cont k)
        (WF_ST: CtrlState.wf st)
        (MEM_CST: mem_cst_blk m st b_cst)
        (SIM_RET:
           forall m' st'
             (ST': st' = reduce_timeout st)
             (MEM_CST: mem_cst_blk m' st' b_cst)
             (MEM_CH_BLK: mem_changed_block b_cst m m')
           ,
           paco3 (_sim_itree prog) r
                 idx_ret itr
                 (Returnstate Vundef k m'))
    : paco3 (_sim_itree prog) r
            (idx_ret + idx_redto)%nat itr
            (Callstate (Internal f_reduce_timeout)
                       [Vptr b_cst Ptrofs.zero] k m).
  Proof.
    unfold idx_redto.
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

    fw. fw.
    { econs.
      - eval_comput.
        rewrite Int_eq_repr_signed; cycle 1.
        { inv WF_ST. range_stac. }
        { range_stac. }
        ss.
      - rewrite bool_val_of_bool. reflexivity.
    }
    destruct (Z.eqb_spec tout 1).
    { (* tout = 1 *)
      fw.

      assert (STORE1: exists m1,
                 Mem.store Mint8signed m b_cst 1
                           (Vint (Int.repr 0)) = Some m1).
      { apply inhabited_sig_to_exists.
        econs.
        apply Mem.valid_access_store.
        rr. split; ss.
        2: { apply Z.divide_1_l. }
        ii. apply MEM_CST. nia. }
      des.

      fw.
      { econs.
        - eval_comput.
          repr_tac. s.
          rewrite Ptrofs.add_zero_l. reflexivity.
        - eval_comput. ss.
        - s. ss.
        - eval_comput.
          rewrite sign_ext_byte_range.
          2: { range_stac. }
          repr_tac.
          eauto.
      }

      fw. fw. fw.
      { step_fptr_tac. }

      red_idx (idx_ret + 30 + idx_aqi)%nat.
      eapply sim_adv_qidx; eauto.
      { apply GENV_PROPS. }
      { ss. }
      { inv WF_ST. range_stac. }
      fw. upd_lenv.

      fw.

      assert (STORE2: exists m2,
                 Mem.store Mint8signed m1 b_cst 2
                           (Vint (Int.repr (adv_qidx qb))) = Some m2).
      { apply inhabited_sig_to_exists.
        econs.
        apply Mem.valid_access_store.
        rr. split; ss.
        2: { apply Z.divide_1_l. }
        ii. eapply Mem.perm_store_1; eauto.
        apply MEM_CST. nia. }
      des.

      fw.
      { econs.
        - eval_comput.
          repr_tac. s.
          rewrite Ptrofs.add_zero_l. reflexivity.
        - eval_comput. reflexivity.
        - ss.
        - eval_comput.
          rewrite sign_ext_byte_range.
          2: { apply range_adv_qidx. }
          repr_tac.
          eauto.
      }

      fw.
      red_idx idx_ret.

      assert (MEM_UNCH: mem_unchanged_except
                          (fun b ofs => b = b_cst /\
                                     (ofs = 1 \/ ofs = 2))
                          m m2).
      { eapply Mem.unchanged_on_trans with (m2:= m1).
        - eapply Mem.store_unchanged_on; eauto.
          s. ii. nia.
        - eapply Mem.store_unchanged_on; eauto.
          s. ii. nia. }

      eapply SIM_RET; eauto.
      - inv MEM_CST.
        econs; ss.
        + eapply Mem.loadbytes_unchanged_on; eauto.
          s. ii. nia.
        + eapply Mem.loadbytes_unchanged_on.
          { eapply store_unchanged_on'; eauto. }
          { unfold mem_range. s. i. nia. }
          eapply Mem.loadbytes_store_same in STORE1. ss.
        + eapply Mem.loadbytes_store_same in STORE2. ss.
          rewrite STORE2.
          unfold encode_int. s.
          rewrite rev_if_be_single.
          unfold inj_bytes. s.
          do 3 f_equal.
          symmetry.
          apply signed_byte_int_unsigned_repr_eq.
        + eapply Mem.loadbytes_unchanged_on; eauto.
          s. ii. nia.
        + eapply Mem.loadbytes_unchanged_on; eauto.
          s. ii. nia.
        + ii. eapply Mem.perm_store_1; eauto.
          eapply Mem.perm_store_1; eauto.
      - eapply Mem.unchanged_on_implies; eauto.
        ii. des; ss.
    }

    fw.
    { econs.
      - eval_comput.
        inv WF_ST.
        repr_tac. ss.
      - rewrite bool_val_of_bool. ss.
    }

    destruct (Z.ltb_spec 1 tout).
    { (* 1 < tout *)

      assert (STORE1: exists m1,
                 Mem.store Mint8signed m b_cst 1
                           (Vint (Int.repr (tout - 1))) = Some m1).
      { apply inhabited_sig_to_exists.
        econs.
        apply Mem.valid_access_store.
        rr. split; ss.
        2: { apply Z.divide_1_l. }
        ii. apply MEM_CST. nia. }
      des.

      fw.
      { econs.
        - eval_comput.
          repr_tac. s.
          rewrite Ptrofs.add_zero_l. reflexivity.
        - eval_comput. ss.
        - s. ss.
        - eval_comput.
          inv WF_ST.
          repr_tac.
          rewrite sign_ext_byte_range.
          2: { range_stac. }
          eauto.
      }

      fw.
      red_idx idx_ret.

      hexploit store_unchanged_on'; eauto.
      s. unfold mem_range. intro MEM_UNCH.

      eapply SIM_RET; eauto.
      - inv MEM_CST.
        econs; ss.
        + eapply Mem.loadbytes_unchanged_on; eauto.
          s. ii. nia.
        + eapply Mem.loadbytes_store_same in STORE1.
          ss. rewrite STORE1.
          unfold encode_int. s.
          rewrite rev_if_be_single.
          unfold inj_bytes. s.
          do 3 f_equal.
          symmetry.
          apply signed_byte_int_unsigned_repr_eq.
        + eapply Mem.loadbytes_unchanged_on; eauto.
          s. ii. nia.
        + eapply Mem.loadbytes_unchanged_on; eauto.
          s. ii. nia.
        + eapply Mem.loadbytes_unchanged_on; eauto.
          s. ii. nia.
        + ii. eapply Mem.perm_store_1; eauto.
      - eapply Mem.unchanged_on_implies; eauto.
        ii. des; ss.
    }

    (* do nothing *)
    fw.
    red_idx idx_ret.
    eapply SIM_RET; eauto.
    eapply Mem.unchanged_on_refl.
  Qed.


  Local Opaque idx_appdev idx_redto.
  Definition idx_updq: nat := (idx_appdev + 20) * 3 + idx_redto + 20.


  Inductive updq_linv
            (itr0: itree progE unit) (m0: mem)
            st inb b_cst b_mst ofs_inb
            (* md tout qb qe q *)
            (i: nat) (itr: itree progE unit)
            (le: PTree.t val) (m: mem): Prop :=
    UpdqLoopInv
      st1 v_d1 v_d2
      (ITR_INVAR: itr = itr0)
      (* (MEM_INVAR: m = m0) *)
      (WF_ST1: wf st1)
      (MEM_CST: mem_cst_blk m st1 b_cst)
      (MEM_CH_BLK: mem_changed_block b_cst m0 m)
      (RES_EQ: update_queue st inb =
               reduce_timeout (update_queue_loop
                                 inb (imap (fun n _ => Z.of_nat n) (3 + i) (repeat tt (3 - i))) st1))
      (LENV_EQUIV:
         lenv_equiv le
                    [(_inbox, Vptr b_mst (Ptrofs.repr ofs_inb));
                    (_st, Vptr b_cst Ptrofs.zero);
                    (_devmsg, v_d1);
                    (_i, Vint (IntNat.of_nat i)); (_id_dev, v_d2)])
  .

  Lemma sim_update_queue
        (itr: itree progE unit)
        (m: mem) (k: cont) (idx_ret: nat)
        st inb
        b_cst b_mst ofs_inb
        (BLOCKS_DIFF: b_cst <> b_mst)
        (CALL_CONT: is_call_cont k)
        (WF_ST: CtrlState.wf st)
        (MEM_CST: mem_cst_blk m st b_cst)
        (MEM_INB: Mem_inbox m b_mst ofs_inb inb)
        (RANGE_OFS_HB: 0 <= ofs_inb <= 4 + inb_sz)
        (SIM_RET:
           forall m' st'
             (ST': st' = update_queue st inb)
             (MEM_CST: mem_cst_blk m' st' b_cst)
             (MEM_CH_BLK: mem_changed_block b_cst m m')
           ,
           paco3 (_sim_itree prog) r
                 idx_ret itr
                 (Returnstate Vundef k m'))
    : paco3 (_sim_itree prog) r
            (idx_ret + idx_updq)%nat itr
            (Callstate (Internal f_update_queue)
                       [Vptr b_cst Ptrofs.zero;
                       Vptr b_mst (Ptrofs.repr ofs_inb)] k m).
  Proof.
    unfold idx_updq.
    start_func.
    { econs. }
    ss.

    fw. fw. fw. fw.
    { econs. eval_comput. ss. }
    upd_lenv.

    fw.

    hexploit (in_cenv_ilist _inbox_t); [sIn|].
    intros CO_INBOX.
    hexploit (in_cenv_ilist _msg_entry_t); [sIn|].
    intros CO_MENTRY.

    assert (BYTE_RANGE_AUX: 6 < Byte.max_signed) by ss.

    eapply simple_for_loop with
        (i_max := 3%nat) (idx_each := (idx_appdev + 20)%nat)
        (idx0 := 0%nat)
        (loop_inv := updq_linv itr m st inb
                               b_cst b_mst ofs_inb).
    { econs; eauto.
      eapply Mem.unchanged_on_refl. }
    { range_stac. }
    { nia. }
    { (* loop body *)
      clear le LENV_EQUIV MEM_CST.
      i. inv LINV.

      fw. fw. fw.
      { econs.
        - eval_comput. repr_tac.
          replace 3 with (Z.of_nat 3) by ss.
          rewrite <- Nat2Z_inj_ltb.
          destruct (Nat.ltb_spec i 3).
          2: { exfalso. nia. }
          reflexivity.
        - ss.
      }

      rewrite Int.eq_false by ss. s.
      fw. fw. fw.
      { econs. eval_comput.
        repr_tac.
        replace 3 with (Z.of_nat 3) by ss.
        rewrite <- Nat2Z.inj_add.
        rewrite sign_ext_byte_range.
        2: { range_stac. }
        reflexivity.
      }
      upd_lenv.

      fw. fw. fw.
      { econs.
        eval_comput.
        rewrite CO_INBOX. s.
        unfold align_attr. s.
        unfold Coqlib.align. s.
        change main_prm._msg_entry_t with _msg_entry_t.
        rewrite CO_MENTRY. s.
        rewrite Ptrofs.add_zero.

        repr_tac.

        pose proof (within_inb_nsz2 (3 + i)) as WITHIN_INB_AUX.
        pose proof ptr_range_mstore as PRANGE_MSTORE.

        hexploit (WITHIN_INB_AUX O).
        { unfold num_tasks. ss. nia. }
        { nia. }
        intro AUX_ZERO.

        repr_tac0; cycle 1.
        { nia. }
        { nia. }

        rewrite <- Nat2Z.inj_mul.
        reflexivity.
      }
      upd_lenv.

      fw. fw.
      { step_fptr_tac. }

      rewrite sign_ext_byte_range by range_stac.
      red_idx (idx1 - 15 - idx_appdev + idx_appdev)%nat.

      r in MEM_INB. des.
      hexploit (nth_error_Some2 _ inb (3 + i)).
      { rewrite NUM_ENTRIES.
        unfold num_tasks. ss. nia. }
      i. des. renames e1 NTH_EX into ment MENT.

      rewrite iForall_nth in MSG_ENTRIES.
      specialize (MSG_ENTRIES (3 + i)%nat).
      rewrite MENT in MSG_ENTRIES.
      rewrite Nat.add_comm in MENT. ss.

      eapply sim_apply_devmsg; eauto.
      { ss. }
      { eapply Mem_msg_entry_unch.
        { eauto. }
        eapply Mem.unchanged_on_implies.
        { eapply MEM_CH_BLK. }
        i. des. subst.
        clear - BLOCKS_DIFF.
        congruence.
      }
      { unfold num_tasks. ss. nia. }

      rename MEM_CH_BLK into MEM_CH_BLK1.
      clear MEM_CST. i.

      red_idx (idx1 - (idx_appdev + 15))%nat.
      fw. fw.
      { econs. eauto. }
      fw.
      { econs. eval_comput.
        repr_tac.
        replace 1 with (Z.of_nat 1) by ss.
        rewrite <- Nat2Z.inj_add.
        reflexivity.
      }
      upd_lenv.

      fw.
      red_idx (idx1 - (idx_appdev + 20))%nat.

      assert (WF_ST': wf st').
      { subst st'.
        apply wf_apply_devmsg; eauto.
        range_stac. }

      eapply SIM_NEXT.
      econs; eauto.
      - eapply Mem.unchanged_on_trans; eauto.
      - rewrite RES_EQ. s.
        replace (3 - i)%nat with (S (2 - i))%nat by nia.
        s. rewrite Nat2Z.id.
        erewrite nth_error_nth.
        2: { rewrite Nat.add_comm in MENT. ss. eauto. }
        rewrite <- ST'. reflexivity.
      - replace (Z.of_nat (i + 1)) with (Z.of_nat (S i)) in LENV_EQUIV by nia.
        eauto.
    }

    clear le LENV_EQUIV.
    clear MEM_CST.
    i. inv LINV_END.

    red_idx (idx_ret + idx_redto + 10)%nat.

    fw. fw. fw.
    { econs.
      - eval_comput.
        repr_tac.
        destruct (Z.ltb_spec (Z.of_nat 3) 3).
        { exfalso. nia. }
        reflexivity.
      - ss.
    }

    rewrite Int.eq_true by ss. s.
    fw. fw. fw. fw.
    { step_fptr_tac. }

    red_idx (idx_ret + 3 + idx_redto)%nat.
    eapply sim_reduce_timeout; eauto.
    { ss. }

    rename MEM_CH_BLK into MEM_CH_BLK_P.
    clear MEM_CST. i.

    fw. fw.
    red_idx idx_ret.

    assert (WF_ST': wf st').
    { subst st'.
      eapply wf_reduce_timeout. ss. }

    eapply SIM_RET; eauto.
    - rewrite <- ST' in RES_EQ.
      rewrite RES_EQ. ss.
    - eapply Mem.unchanged_on_trans; eauto.
  Qed.

End VERIF_FUNC.
