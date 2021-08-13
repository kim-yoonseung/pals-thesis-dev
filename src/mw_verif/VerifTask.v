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
Require Import OSNodes.

Require Import ProgSem CProgEventSem.
Require Import ProgSim CProgSimLemmas.
Require Import RTSysEnv MWITree.
Require Import NWSysModel.
Require Import SyncSysModel.

Require Import config_prm main_prm SystemProgs.
Require Import VerifProgBase.
Require Import VerifMainUtil VerifFetchMsgs.

Import Clight Clightdefs.
Import ITreeNotations.

Set Nested Proofs Allowed.

Local Transparent Archi.ptr64.
Local Opaque Int64.max_unsigned Int.max_unsigned.
Local Opaque Genv.globalenv.
Local Opaque Z.of_nat.

Local Opaque idx_fch idx_get_inb.

Arguments DELTA: simpl never.


Section INIT_MSG_STORE.
  Context `{SystemEnv}.
  (* Context `{CProgSysEvent}. *)
  Variable cprog: Clight.program.

  Let prog: Prog.t := prog_of_clight cprog.
  Let ge := Clight.globalenv cprog.
  Variable tid: nat.
  Hypothesis RANGE_TID: (tid < num_tasks)%nat.
  Context `{genv_props ge (main_gvar_ilist tid)
                       main_gfun_ilist main_cenv_ilist}.
  (* Notation progE := (OSModel.osE +' OSNodes.tlimE +' extcallE). *)

  Variable r: nat -> itree progE unit -> Prog.state prog -> Prop.
  (* Let GVB_IDXS_MAIN := gvb_idxs_main. *)

  (* Lemma fold_mentry_sz' *)
  (*   : Z.of_nat (S max_msg_size) = mentry_sz. *)
  (* Proof. *)
  (*   unfold mentry_sz. nia. *)
  (* Qed. *)


  Inductive init_inbox_loop_inv
            (itr_i: itree progE unit)
            (inb0: MWITree.inbox_t)
            b pofsv m_i (* i_max *)
            (i: nat) (itr: itree progE unit)
            (le: PTree.t val) (m: mem): Prop :=
    InitInboxLoopInv
      ments_p ments_n
      (MEM_CONSTS: mem_consts ge m tid)
      (* (OFFSET: pofsv = Ptrofs.unsigned pofs) *)
      (MENTS_PREV: iForall (Mem_msg_entry m b pofsv)
                           0 ments_p)
      (MENTS_PREV_INIT:
         MWITree.reset_inbox (firstn i inb0) = ments_p)
      (MENTS_NEXT_EQ: skipn i inb0 = ments_n)
      (MENTS_NEXT: iForall (Mem_msg_entry m b pofsv)
                           i ments_n)
      (ITREE_INVAR: itr = itr_i)
      (MENTS_RANGE_PERM: Mem.range_perm m b pofsv
                                        (pofsv + inb_sz)
                                        Cur Writable)
      (UNCH: mem_unchanged_except
               (fun b' ofs' =>
                  b' = b /\
                  (pofsv <= ofs' < pofsv + inb_sz)%Z)
               m_i m)
      (LENV_EQUIV: lenv_equiv
                     le [(_inb, Vptr b (Ptrofs.repr pofsv));
                        (_i, Vint (IntNat.of_nat i))])
  .

  Definition idx_iinb: nat := num_tasks * 10 + 10.


  Lemma firstn_snoc_nth_error A
        (l: list A) (a: A) n
        (NTH: nth_error l n = Some a)
    : firstn (S n) l = snoc (firstn n l) a.
  Proof.
    unfold snoc.
    depgen n.
    induction l as [| h t IH]; i; ss.
    { destruct n; ss. }
    destruct n as [| n']; ss.
    { inv NTH. ss. }

    hexploit IH; eauto.
    intro EXP_IH. rewrite EXP_IH. ss.
  Qed.



  Lemma sim_init_inbox
        (b_mst: block)
        idx itr k m
        (* pofs *) pofsv inb
        (CALL_CONT: is_call_cont k)
        (MEM_CONSTS: mem_consts ge m tid)
        (* (POFSV: pofsv = Ptrofs.unsigned pofs) *)
        (POFSV_BOUND: (0 <= pofsv <= inb_sz + 4)%Z)
        (FSYMB_MST : Genv.find_symbol ge _mstore = Some b_mst)
        (MEM_INBOX: Mem_inbox m b_mst pofsv inb)
        (AFT: forall m' inb'
                (RESET_INB: inb' = MWITree.reset_inbox inb)
                (MEM_CONSTS: mem_consts ge m' tid)
                (MEM_INBOX: Mem_inbox m' b_mst pofsv inb')
                (MEM_UNCH: mem_unchanged_except
                             (fun b ofs' =>
                                b = b_mst /\
                                pofsv <= ofs' <
                                pofsv + inb_sz)%Z
                             m m'),
            paco3 (_sim_itree prog) r idx
                  itr (Clight.Returnstate Vundef k m'))
    : paco3 (_sim_itree prog) r (idx_iinb + idx)
            itr
            (Clight.Callstate
               (Internal (main_prm.f_init_inbox
                            (Z.of_nat max_num_tasks)))
               [Vptr b_mst (Ptrofs.repr pofsv)] k m).
  Proof.
    (* pose (pofsv' := pofsv). subst pofsv. *)
    (* fold pofsv' in AFT. fold pofsv' in MEM_INBOX. *)
    (* rename pofsv' into pofsv. *)

    start_func.
    { econs. }

    unfold idx_iinb.
    fw. clear STEP_ENTRY.
    fw. fw.
    { econs. eval_comput. ss. }
    upd_lenv.
    fw.
    (* loop *)
    (* replace 6%Z with (Z.of_nat 6%nat) by ss. *)
    (* fold_for_loop _i . *)

    hexploit (in_gvar_ids _NUM_TASKS); [sIn|].
    intros (b_nt & FSYMB_NT).
    pose proof range_num_tasks as RANGE_NT.
    rr in MEM_INBOX.

    eapply simple_for_loop
      with (idx_each:= 10) (idx0:= 0)
           (i_max := num_tasks)
           (loop_inv := init_inbox_loop_inv
                          itr inb b_mst pofsv m).
    { econs; eauto; ss.
      - econs.
      - apply MEM_INBOX.
      - eapply MEM_INBOX.
      - rr. apply Mem.unchanged_on_refl.
    }
    (* { apply LENV_EQUIV. } *)
    { range_stac. }
    { nia. }
    { (* body *)
      clear le LENV_EQUIV.
      clear MEM_CONSTS.
      i. unfold for_loop_stmt. ss.
      inv LINV. des.

      (* make range props of i in advance *)
      (* assert (RANGE_I_Z: (0 <= Z.of_nat i <= 6)%Z) by nia. *)
      (* assert (RANGE_I_INT: (Int.min_signed <= Z.of_nat i <= Int.max_signed)%Z). *)
      (* { split. *)
      (*   - pose proof Int.min_signed_neg. nia. *)
      (*   - etransitivity; try apply RANGE_I_Z. ss. } *)
      (* assert (RANGE_I_UINT: (0 <= Z.of_nat i <= Int.max_unsigned)%Z). *)
      (* { split; try apply RANGE_I_Z. *)
      (*   etransitivity; try apply RANGE_I_Z. ss. } *)
      (* assert (RANGE_I_POFS: (0 <= Z.of_nat i <= Ptrofs.max_unsigned)%Z). *)
      (* { split; try apply RANGE_I_Z. *)
      (*   etransitivity; try apply RANGE_I_Z. ss. } *)

      assert (WITHIN_INBOX_SZ: (0 < mentry_nsz * i + 1 <= inb_nsz)%nat).
      { split; [nia|].
        apply within_inb_nsz2.
        - nia.
        - unfold mentry_nsz. nia.
      }

      (* guardH RANGE_I_Z. guardH RANGE_I_INT. *)
      (* guardH RANGE_I_UINT. guardH RANGE_I_POFS. *)

      fw. fw. fw.
      { econs.
        - eval_comput.
          rewrite FSYMB_NT.
          erewrite mem_consts_num_tasks by eauto.
          repr_tac.
          rewrite <- Nat2Z_inj_ltb. reflexivity.
        - instantiate (1:= true).
          s.
          destruct (Nat.ltb_spec i num_tasks); ss. nia.
      }
      ss.

      fw.
      assert (exists inb_x,
                 <<INB_X: nth_error inb i = Some inb_x>> /\
                 <<SKIPN_RW: skipn i inb = inb_x :: skipn (S i) inb>>).
      { hexploit (nth_error_Some2 _ inb i).
        { nia. }
        i. des.
        esplits; eauto.
        apply nth_error_split in NTH_EX. des. clarify.
        rewrite skipn_app_exact by ss.
        rewrite rw_cons_app. rewrite app_assoc.
        rewrite skipn_app_exact.
        2: { rewrite app_length. ss. nia. }
        ss.
      }
      des.
      (* destruct inb_x as [rcv_x bs_x]. *)
      rewrite SKIPN_RW in MENTS_NEXT. clear SKIPN_RW.
      inv MENTS_NEXT.

      match goal with
      | H: Mem_msg_entry _ _ _ _ _ |- _ =>
           (* , *)
           (* H': _ = skipn i inb |- _ => *)
        rename H into MENT_CUR (* ; rename H' into INB_SKIPN *)
      end.

      (* make mem beforehand *)
      assert (MEM_STORE: exists m2,
                 Mem.store Mint8signed m1 b_mst
                           (pofsv + (Z.of_nat (mentry_nsz * i)))
                           (Vint Int.zero) = Some m2).
      { apply inhabited_sig_to_exists.
        econs.
        (* unfold mentry_sz. *)
        apply Mem.valid_access_store.
        r. split; ss.
        - ii.
          eapply MENTS_RANGE_PERM. nia.
        - apply Z.divide_1_l.
      }
      des.
      pose proof ptr_range_mstore as PTR_RANGE_MSTORE.
      pose proof range_mentry_nsz as RANGE_MENTRY_NSZ.

      fw.
      { econs.
        - eval_comput. s. fold_cenv.
          erewrite (in_cenv_ilist _msg_entry_t) by sIn.
          rewrite Ptrofs.add_zero.
          rewrite Ptrofs.add_zero.
          repr_tac1.
          simpl co_sizeof.
          (* replace (Z.of_nat (S max_msg_size)) with mentry_sz. *)
          (* 2: { unfold mentry_sz. nia. } *)
          repr_tac1. repr_tac1.
          rewrite <- Nat2Z.inj_mul.
          reflexivity.
        - eval_comput. eauto.
        - ss.
        - eval_comput.
          repr_tac1.
          replace (Int.sign_ext 8 (Int.repr 0)) with Int.zero by ss.
          eauto.
      }

      fw.
      { econs; eauto. }
      fw.
      { econs.
        eval_comput.
        repr_tac.
        replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by nia.
        reflexivity.
      }
      upd_lenv.

      fw.
      fold_for_loop _i.

      eapply (sim_itree_red_idx prog) with (idx_small:= idx1 - 10).
      { nia. }

      eapply SIM_NEXT.
      (* { apply LENV_EQUIV. } *)
      { econs; eauto.
        - eapply mem_consts_unch_diffblk; eauto.
          2: { instantiate (1:= b_mst).
               i. eapply global_addresses_distinct'; eauto.
               ss. des; clarify. }
          eapply Mem.unchanged_on_implies.
          { eapply store_unchanged_on'; eauto. }
          unfold mem_range. ss.
          ii. des; clarify.
        - erewrite firstn_snoc_nth_error; eauto.
          unfold snoc.
          unfold MWITree.reset_inbox in *.
          rewrite map_app.
          eapply iForall_app; eauto.
          + eapply iForall_Mem_msg_entry_unch; eauto.
            eapply Mem.unchanged_on_implies; eauto.
            { eapply store_unchanged_on'; eauto. }
            unfold mem_range. ss.
            rewrite map_length.
            rewrite firstn_length_le by nia.
            ii. des; ss. nia.

          + ss. rewrite map_length.
            rewrite firstn_length_le by nia.
            econs; ss.
            2: { econs. }

            r in MENT_CUR.
            eapply Mem.loadbytes_store_same in MEM_STORE.
            ss.

            (* (* replace mentry_esz with (1 + Z.of_nat msg_size)%Z. *) *)
            (* (* 2: { unfold mentry_ensz. nia. } *) *)

            (* unfold mentry_to_bytes. s. *)
            (* rewrite rw_cons_app. *)

            (* apply Mem.loadbytes_concat; [ | | nia | nia]. *)
            (* * eapply Mem.loadbytes_store_same in MEM_STORE. ss. *)
            (* * erewrite Mem.loadbytes_store_other; eauto. *)
            (*   2: { do 3 right. ss. nia. } *)
            (*   replace mentry_esz with (1 + Z.of_nat msg_size)%Z *)
            (*     in MENT_CUR. *)
            (*   2: { unfold mentry_ensz. nia. } *)

            (*   unfold mentry_to_bytes in MENT_CUR. *)
            (*   apply Mem_loadbytes_split' in MENT_CUR; [|nia..]. *)
            (*   ss. destruct MENT_CUR. *)
            (*   eauto. *)
        - eapply iForall_Mem_msg_entry_unch; eauto.
          eapply Mem.unchanged_on_implies; eauto.
          { eapply store_unchanged_on'; eauto. }
          unfold mem_range. ss.
          (* rewrite map_length. *)
          (* rewrite firstn_length_le by nia. *)
          ii. des; ss. nia.
        - ii. eapply Mem.perm_store_1; eauto.
        - eapply Mem.unchanged_on_trans.
          2: {
            eapply Mem.store_unchanged_on; eauto.
            i. intro C. apply C.
            split; ss.
            nia.
          }
          ss.
      }
    }

    i. ss.
    clear dependent le. clear MEM_CONSTS.
    inv LINV_END. des.

    fw. fw. fw.
    { econs.
      - eval_comput.
        rewrite FSYMB_NT.
        erewrite mem_consts_num_tasks by eauto.
        repr_tac.
        rewrite Z.ltb_irrefl. ss.
      - ss.
    }
    rewrite Int.eq_true. ss.

    fw. fw. fw.
    eapply (sim_itree_red_idx prog) with (idx_small := idx).
    { nia. }

    eapply AFT; eauto.
    rewrite firstn_all2 in MENTS_PREV.
    { r. esplits; eauto.
      unfold MWITree.reset_inbox.
      rewrite map_length. ss. }
    { nia. }
  Qed.


  Definition idx_swinb := idx_iinb + 20.

  Lemma sim_switch_inbox
        m0 k itr idx_ret
        cf ofsc ofsn
        inbc inbn
        (CALL_CONT: is_call_cont k)
        (MEM_CONSTS: mem_consts ge m0 tid)
        (MEM_MSTORE: mem_mstore ge m0 cf ofsc ofsn inbc inbn)
        (SIM_RET:
           forall m' cf' inbn' ofsc' ofsn'
             (* (INBN_EQV': inbox_equiv *)
             (*               MWITree.init_inbox inbn_t') *)
             (* (INBN_INIT': Forall (fun x => fst x = false) inbn') *)
             (RESET_INBC: inbn' = MWITree.reset_inbox inbc)
             (MEM_MSTORE: mem_mstore ge m' cf' ofsc' ofsn'
                                     inbn inbn')
             (UNCH: mem_changed_gvar_id ge _mstore m0 m')
           ,
             paco3 (_sim_itree prog) r idx_ret
                   itr
                   (Returnstate Vundef k m'))
    : paco3 (_sim_itree prog) r (idx_swinb + idx_ret)
            itr (Callstate (Internal f_switch_inbox)
                           [] k m0).
  Proof.
    start_func.
    { econs. }

    unfold idx_swinb.
    fw. clear STEP_ENTRY.
    fw.

    hexploit (in_gvar_ids _mstore); [sIn|].
    destruct 1 as [b_mst FSYMB_MST].
    specialize (MEM_MSTORE _ FSYMB_MST).

    fw.
    { econs. eval_comput.
      rewrite FSYMB_MST. s.
      rewrite Ptrofs.add_zero_l.
      rewrite Ptrofs.unsigned_repr by ss.
      apply MEM_MSTORE.
    }
    upd_lenv.

    fw. fw. fw.
    { hexploit (in_gfun_ilist _init_inbox); [sIn|]. i. des.
      econs; eauto; ss.
      - eval_comput.
        rewrite FDEF_SYMB. ss.
      - eval_comput.
        rewrite FSYMB_MST. s.
        fold_cenv.
        erewrite (in_cenv_ilist _inbox_t) by sIn.
        s. rewrite Ptrofs.add_zero_l.
        pose proof ptr_range_inb_sz.
        repr_tac0; cycle 1.
        { nia. }
        { desf; ss. }
        repr_tac0; cycle 1.
        { ss. }
        { desf; ss.
          - unfold Int.one.
            rewrite Int.signed_repr by ss.
            nia.
          - unfold Int.zero.
            rewrite Int.signed_repr by ss.
            nia.
        }
        replace (inb_sz * Int.signed (if cf then Int.one else Int.zero))%Z with
            (Z.of_nat (if cf then inb_nsz else 0)).
        2: {
          unfold Int.one, Int.zero.
          destruct cf; ss.
          - rewrite Int.signed_repr by ss. nia.
          - rewrite Int.signed_repr by ss. nia.
        }
        reflexivity.
    }

    eapply (sim_itree_red_idx prog) with (idx_small:= idx_iinb + (idx_ret + 12)).
    { nia. }
    eapply sim_init_inbox with (inb:= inbc); eauto; ss.
    { destruct cf; nia. }
    { inv MEM_MSTORE.
      destruct cf; ss.  }

    clear MEM_CONSTS.
    i. clarify.
    rename m' into m1.

    fw. fw.
    inv MEM_MSTORE.

    assert (STORE_CF: exists m2,
               Mem.store Mint32 m1 b_mst 0 (Vint (Int.repr (if cf then 0%Z else 1%Z))) = Some m2).
    { apply inhabited_sig_to_exists.
      econs.
      apply Mem.valid_access_store.
      rr. split; ss.
      - ii. eapply Mem.perm_unchanged_on; eauto.
        ss. nia.
      - solve_divide.
    }
    des.

    fw.
    { econs.
      - eval_comput.
        rewrite FSYMB_MST. s.
        rewrite Ptrofs.add_zero_l. reflexivity.
      - eval_comput.
        instantiate (1:= Vint (Int.repr (if cf then 0%Z else 1%Z))).
        destruct cf; ss.
      - ss.
      - eval_comput.
        eauto.
    }
    fw.
    apply (sim_itree_red_idx prog) with (idx_small:= idx_ret).
    { nia. }

    assert (MEM_UNCH_TOT:
              mem_unchanged_except
                (fun b ofs =>
                   b = b_mst /\
                   ((0 <= ofs < 4) \/
                    (if cf then
                       (4 + Z.of_nat inb_nsz <= ofs <
                        4 + Z.of_nat (inb_nsz + inb_nsz))
                     else
                       (4 <= ofs < 4 + Z.of_nat inb_nsz))))%Z
                m0 m2).
    { eapply Mem.unchanged_on_trans.
      - eapply Mem.unchanged_on_implies; eauto.
        ii. des; ss. clarify.
        desf; nia.
      - eapply Mem.unchanged_on_implies; eauto.
        { eapply store_unchanged_on'; eauto. }
        unfold mem_range.
        ii. ss.
        destruct cf; nia.
    }

    eapply SIM_RET; eauto.
    { econs; eauto.
      - instantiate (1:= negb cf).
        ss. clarify.
        erewrite Mem.load_store_same; eauto.
        destruct cf; ss.
      - ii.
        eapply Mem.perm_store_1; eauto.
        eapply Mem.perm_unchanged_on; eauto.
        { ss. ii. des; ss. clarify.
          destruct cf; nia. }
        ss. clarify.
        apply mem_mst_curflag_writable. eauto.
      - ss. clarify.
        destruct cf; ss.
        + eapply Mem_inbox_unch; eauto.
          eapply Mem.unchanged_on_implies; eauto.
          ii. ss. nia.
        + eapply Mem_inbox_unch; eauto.
          eapply Mem.unchanged_on_implies; eauto.
          ii. ss. nia.
        (*   eapply Mem.unchanged_on_trans. *)
        (*   { eapply Mem.unchanged_on_implies; eauto. *)
        (*     ss. ii. des; clarify. nia. } *)
        (*   { eapply Mem.unchanged_on_implies; eauto. *)
        (*     { eapply store_unchanged_on'; eauto. } *)
        (*     ss. unfold mem_range. *)
        (*     ii. des; clarify. nia. } *)
        (* + eapply Mem_inbox_unch; eauto. *)
        (*   eapply Mem.unchanged_on_trans. *)
        (*   { eapply Mem.unchanged_on_implies; eauto. *)
        (*     ss. ii. des; clarify. nia. } *)
        (*   { eapply Mem.unchanged_on_implies; eauto. *)
        (*     { eapply store_unchanged_on'; eauto. } *)
        (*     ss. unfold mem_range. *)
        (*     ii. des; clarify. nia. } *)
      - ss. clarify.
        destruct cf; ss.
        + eapply Mem_inbox_unch; eauto.
          eapply Mem.unchanged_on_implies; eauto.
          { eapply store_unchanged_on'; eauto. }
          ss. unfold mem_range.
          ii. des; clarify. nia.
        + eapply Mem_inbox_unch; eauto.
          eapply Mem.unchanged_on_implies; eauto.
          { eapply store_unchanged_on'; eauto. }
          ss. unfold mem_range.
          ii. des; clarify. nia.
    }

    r. i. ss. clarify.
    eapply Mem.unchanged_on_implies; eauto.
    ss. ii. ss. des; ss.
  Qed.

End INIT_MSG_STORE.


Section RUN_TASK.
  (* Context `{SystemEnv}. *)
  Context `{SimApp}.

  (* Variable cprog: Clight.program. *)
  Variable txs rxs: nat.

  Let prog: Prog.t := prog_of_clight cprog.
  Let ge := globalenv cprog.
  Notation progE := (OSModel.osE +' obsE).

  Context `{genv_props
              ge (main_gvar_ilist tid ++ app_gvar_ilist)
              (main_gfun_ilist ++ app_gfun_ilist)
              (main_cenv_ilist ++ app_cenv_ilist)}.

  (* For global variable invariants *)
  Let gprops_main
    : genv_props ge (main_gvar_ilist tid)
                 main_gfun_ilist main_cenv_ilist.
  Proof.
    eapply genv_props_incl; eauto;
      apply incl_appl; ss.
  Qed.

  Variable r: nat -> itree progE unit -> Prog.state prog -> Prop.

  (* Variable kp: Clight.cont. *)
  (* Variable idx_fin: nat. *)
  (* Hypothesis KP: *)
  (*   is_call_cont kp /\ *)
  (*   forall m, paco3 (_sim_itree prog) r idx_fin *)
  (*              (Ret tt) *)
  (*              (Returnstate Vundef kp m). *)

  Let tid_sign_ext_noeff:
    Int.sign_ext 8 (IntNat.of_nat tid) =
    IntNat.of_nat tid.
  Proof.
    assert (IntRange.sint8 tid).
    { pose proof range_tid.
      pose proof range_num_tasks.
      range_stac. }

    unfold IntNat.of_nat.
    rewrite sign_ext_byte_range by ss.
    ss.
  Qed.

  Inductive main_loop_inv
            (itr: itree progE unit)
            (le: PTree.t val) (m: mem): Prop :=
    MainLoopInv
      ast sytm sytm_dmy mcont_dmy
      cflg ofsc ofsn
      inbc inbn (* sh *)
      (* inbc_t inbn_t *)
      v_dmy
      (RANGE_SYTM: (0 < Z.of_nat (sytm + 2 * period) <= Int64.max_unsigned)%Z)
      (LENV_EQUIV: lenv_equiv le [(_cur_base_time, Vlong (IntNat.of_nat64 sytm));
                                 (_pprd, Vlong (IntNat.of_nat64 period));
                                 (_dlt, Vlong (Int64.repr (Z.of_nat DELTA)));
                                 (_maxt, Vlong (Int64.repr MAX_TIME_Z));
                                 (_t'1, v_dmy)])

      (MEM_NB: (Genv.genv_next ge <= Mem.nextblock m)%positive)

      (ITREE: itr =
              MWITree.main_loop
                tid app_mod MWITree.ltb_max_time
                txs rxs (inbc, inbn)
                ast sytm)

      (MEM_SBUF : mem_sbuf ge m sytm_dmy tid mcont_dmy)
      (MEM_CONSTS : mem_consts ge m tid)
      (MEM_MSTORE : mem_mstore ge m cflg ofsc ofsn inbc inbn)
      (MEM_SH : mem_sh ge m (repeat false num_tasks))
      (MEM_TXS : mem_txs ge m txs)
      (MEM_RXS : mem_rxs ge m rxs)
      (INV_APP: inv_app ge ast m)
      (* (INBC_EQV: inbox_equiv inbc_s inbc_t) *)
      (* (INBN_EQV: inbox_equiv inbn_s inbn_t) *)
  .

  (* TODO *)

  Let eval_loop_cond
      le m tm
      (RANGE_TM: IntRange.uint64 tm)
      (LE_CBT : le ! _cur_base_time =
                Some (Vlong (IntNat.of_nat64 tm)))
      (LE_MAXT: le ! _maxt =
                Some (Vlong (Int64.repr
                               (Int64.max_unsigned -
                                10 * Z.of_nat period))))
    : eval_expr_c (globalenv cprog) empty_env le m
                  (Ebinop Cop.Olt (Etempvar _cur_base_time tulong)
                          (Etempvar _maxt tulong) tint) =
      Some (Vint (if tm <? MAX_TIME
                  then Int.one else Int.zero)).
  Proof.
    ss. rewrite LE_CBT. rewrite LE_MAXT.
    eval_comput.
    repr_tac.

    pose proof period_mul_10_lt_max.
    unfold Int64.ltu.
    rewrite Int64.unsigned_repr.
    2: { range_stac. }

    rewrite Z.mul_comm.
    fold MAX_TIME_Z.
    rewrite <- max_time_to_z.

    unfold IntNat.of_nat64.
    rewrite Int64.unsigned_repr by ss.

    match goal with
    | |- context[Coqlib.zlt ?a ?b] =>
      destruct (Coqlib.zlt a b)
    end.
    - destruct (Nat.ltb_spec tm MAX_TIME); ss.
      nia.
    - destruct (Nat.ltb_spec tm MAX_TIME); ss.
      nia.
  Qed.

  (* Let eval_loop_cond *)
  (*       le m v sytm *)
  (*       _cur_base_time *)
  (*       b_pprd *)
  (*       (RANGE_SYTM: (0 < Z.of_nat (sytm + 2 * pals_period) <= Int64.max_unsigned)%Z) *)
  (*       (LENV_EQUIV: le ! _cur_base_time = *)
  (*                    Some (Vlong (IntNat.of_nat64 sytm))) *)
  (*       (FSYMB_PPRD : Genv.find_symbol ge _PALS_PERIOD = Some b_pprd) *)
  (*       (LOAD_PPRD : Mem.load Mint64 m b_pprd 0 = *)
  (*                    Some (Vlong (IntNat.of_nat64 pals_period))) *)
  (*       (VAL: v = if (Z.of_nat sytm <? Int64.max_unsigned - *)
  (*                                      5 * Z.of_nat pals_period)%Z *)
  (*                 then Vtrue else Vfalse) *)
  (*   : eval_expr_c *)
  (*       (globalenv cprog) empty_env le m *)
  (*       (Ebinop Cop.Olt (Etempvar _cur_base_time tulong) *)
  (*               (Ebinop Cop.Osub (Econst_long (Int64.repr (-1)) tulong) *)
  (*                       (Ebinop Cop.Omul (Econst_int (Int.repr 5) tint) (Evar _PALS_PERIOD tulong) tulong) tulong) tint) = *)
  (*     Some v. *)
  (* Proof. *)
  (*   assert (0 <= Z.of_nat sytm <= Int64.max_unsigned)%Z by nia. *)
  (*   ss. *)
  (*   rewrite LENV_EQUIV. *)
  (*   rewrite FSYMB_PPRD. cbn. *)
  (*   rewrite Ptrofs.unsigned_zero. *)
  (*   rewrite LOAD_PPRD. *)
  (*   replace (IntNat.of_nat64 sytm) with (Int64.repr (Z.of_nat sytm)) by ss. *)
  (*   rewrite eval_max_time; eauto. *)

  (*   unfold Int64.ltu. *)
  (*   rewrite Int64.unsigned_repr by ss. *)
  (*   rewrite Int64.unsigned_repr. *)
  (*   2: { pose proof period_mul_10_lt_max. nia. } *)
  (*   match goal with *)
  (*   | |- context[Coqlib.zlt ?a ?b] => *)
  (*     destruct (Z.ltb_spec a b) *)
  (*   end. *)
  (*   - desf. *)
  (*   - desf. nia. *)
  (* Qed. *)

  Definition idx_run: nat := 30.

  Lemma sim_run_task
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
        (INV_APP: inv_app ge (AppMod.init_abst_state app_mod) m_i)
        (SIM_RET:
           forall m_f
             (* (UNCH: Mem.unchanged_on (fun _ _ => True) m_i m_f) *)
           ,
             paco3 (_sim_itree prog) r idx_fin
                   (Ret tt)
                   (Clight.Returnstate Vundef kp m_f))
    : (* exists idx_rt: nat, *)
      paco3 (_sim_itree prog) r (idx_run + idx_fin)
            (MWITree.run_task
               tid app_mod txs rxs sytm)
            (Clight.Callstate
               (Internal main_prm.f_run_task)
               [Vlong (IntNat.of_nat64 sytm)] kp m_i)
  .
  Proof.
    guardH RANGE_SYTM.
    unfold idx_run.
    rewrite plus_comm.

    (* remember m_i as m1 eqn:MEM_EQ. *)
    (* guardH MEM_EQ. *)

    start_func.
    { econs. }
    ss.
    fw. clear STEP_ENTRY.

    hexploit (in_gvar_ids _send_buf); [sIn|].
    intros [b_sbuf FSYMB_SBUF].
    hexploit (in_gvar_ids _mstore); [sIn|].
    intros [b_mst FSYMB_MST].

    hexploit (in_gvar_ids _PALS_PERIOD); [sIn|].
    intros (b_pprd & FSYMB_PPRD).
    hexploit (in_gvar_ids _MAX_CSKEW); [sIn|].
    intros (b_sk & FSYMB_SK).
    hexploit (in_gvar_ids _MAX_NWDELAY); [sIn|].
    intros (b_nd & FSYMB_ND).

    fw. fw.
    { econs.
      eval_comput.
      rewrite FSYMB_PPRD.
      erewrite mem_consts_pals_period; eauto.
    }
    upd_lenv.

    pose proof max_clock_skew_range as RANGE_SK.
    pose proof max_nw_delay_range as RANGE_ND.
    pose proof period_cond as PRD_COND.
    pose proof period_mul_10_lt_max as PRD_LT.

    fw. fw. fw.
    { econs. eval_comput.
      rewrite FSYMB_SK, FSYMB_ND.
      erewrite mem_consts_max_cskew; eauto.
      erewrite mem_consts_max_nwdelay; eauto.
      eval_comput.
      repr_tac.
      replace 2%Z with (Z.of_nat 2) by ss.
      rewrite <- Nat2Z.inj_mul.
      rewrite <- Nat2Z.inj_add.
      fold DELTA.
      reflexivity.
    }
    assert (DELTA_LT: DELTA < period).
    { unfold DELTA. nia. }
    upd_lenv.

    fw. fw. fw.
    { econs. eval_comput.
      rewrite FSYMB_PPRD.
      erewrite mem_consts_pals_period by eauto.
      repr_tac.

      rewrite eval_max_time.
      reflexivity.
    }
    upd_lenv.
    fw.

    (* Swhile *)
    eapply (sim_itree_red_idx prog) with
        (idx_small:= idx_fin + 15 + 5).
    { nia. }

    match goal with
    | |- context[Swhile ?e ?s] =>
      pose (while_cond_expr := e);
        pose (loop_body_stmt := s)
    end.

    eapply sim_while with (linv := main_loop_inv).
    { econs; eauto.
      - rewrite max_time_to_z in LENV_EQUIV. ss.
      - unfold MWITree.run_task. eauto.
    }
    { clear dependent m_i. clear dependent le.
      clear ofsc ofsn sytm_dmy sytm RANGE_SYTM.
      i. inv LINV.

      hexploit mem_consts_pals_period; eauto.
      intro LOAD_PPRD.

      esplits; ss.
      - rewrite LENV_EQUIV. ss.
        rewrite LENV_EQUIV. ss.
      - ss.
        rewrite bool_val_of_bool.

        unfold Int64.ltu.
        rewrite Int64.unsigned_repr.
        2: { unfold MAX_TIME_Z. nia. }
        unfold IntNat.of_nat64.
        rewrite Int64.unsigned_repr.
        2: { pose proof period_mul_10_lt_max. nia. }
        instantiate (1:= (sytm <? MAX_TIME)).
        rewrite <- max_time_to_z.
        destruct (Nat.ltb_spec sytm MAX_TIME);
          destruct (Coqlib.zlt (Z.of_nat sytm)
                               (Z.of_nat MAX_TIME)); ss; nia.
    }
    { (* loop body *)
      clear dependent m_i. clear dependent le.
      clear dependent sytm.
      clear ofsc ofsn sytm_dmy.
      i. inv LOOP_INV.
      renames m_c le_c into m1 le.

      fold loop_body_stmt in CIH.
      fold while_cond_expr in EVAL_EXPR, COND_TRUE, CIH.
      fold while_cond_expr.

      assert (UINT64_SYTM: IntRange.uint64 sytm).
      { rr. nia. }

      assert (SYTM_LT_MAX: sytm < MAX_TIME).
      { subst while_cond_expr. ss.
        erewrite eval_loop_cond in EVAL_EXPR; eauto; cycle 1.
        { rewrite LENV_EQUIV. ss. }
        { rewrite LENV_EQUIV.
          rewrite Z.mul_comm.
          fold MAX_TIME_Z. ss. }
        destruct (Nat.ltb_spec sytm MAX_TIME); ss.
        exfalso. clarify.
      }

      assert (RANGE_NSYTM: (Z.of_nat (sytm + period * 3)
                            <= Int64.max_unsigned)%Z).
      { unfold MAX_TIME in SYTM_LT_MAX. ss. nia. }

      (* seq *)
      fw.

      assert (MEM_STORE: exists m2,
                 Mem.store Mint64 m1 b_sbuf 0
                           (Vlong (IntNat.of_nat64 (sytm + period))) = Some m2 /\
                 mem_sbuf ge m2 (sytm + period) tid mcont_dmy).
      { specialize (MEM_SBUF _ FSYMB_SBUF).
        inv MEM_SBUF.

        assert (exists m', Mem.store Mint64 m1 b_sbuf 0
                                (Vlong (IntNat.of_nat64 (sytm + period))) = Some m').
        { apply inhabited_sig_to_exists.
          econs.
          apply Mem.valid_access_store.
          rr. split; ss.
          - ii. eapply mem_sbuf_writable.
            unfold pld_size. nia.
          - solve_divide.
        }
        des.
        esplits; eauto.
        ii. ss. clarify.
        econs.
        - change 8%Z with (size_chunk Mint64).
          erewrite Mem.loadbytes_store_same; eauto. ss.
        - erewrite Mem.load_store_other; eauto.
          right. right. ss.
        - erewrite Mem.loadbytes_store_other; eauto.
          right. right. right. ss.
        - ii. eapply Mem.perm_store_1; eauto.
      }
      clear MEM_SBUF.
      destruct MEM_STORE as (m2 & MEM_STORE & MEM_SBUF).

      fw.
      { econs.
        - eval_comput.
          rewrite FSYMB_SBUF. s.
          unfold Ptrofs.zero.
          repr_tac. s. reflexivity.
        - eval_comput. repr_tac.
          rewrite <- Nat2Z.inj_add. reflexivity.
        - ss.
        - ss.
          eval_comput.
          eauto.
      }

      assert (MEM_CHB: mem_changed_block b_sbuf m1 m2).
      { eapply Mem.store_unchanged_on; eauto. }

      eapply mem_consts_unch_diffblk in MEM_CONSTS; cycle 1; eauto.
      { i. ss.
        eapply (global_addresses_distinct' ge); eauto.
        des; clarify. }
      eapply mem_txs_unch_diffblk in MEM_TXS; cycle 1; eauto.
      { eapply global_addresses_distinct' with (id:= _send_buf); eauto; ss. }
      eapply mem_rxs_unch_diffblk in MEM_RXS; cycle 1; eauto.
      { eapply global_addresses_distinct' with (id:=_send_buf); eauto; ss. }
      eapply mem_mstore_unch_diffblk in MEM_MSTORE; cycle 1; eauto.
      { eapply global_addresses_distinct' with (id:=_send_buf); eauto; ss. }
      eapply mem_sh_unch_diffblk in MEM_SH; cycle 1; eauto.
      { eapply global_addresses_distinct' with (id:=_send_buf); eauto; ss. }

      eapply inv_app_unch_diffblk in INV_APP; cycle 1; eauto.
      { sIn. }
      assert (MEM_NB': (Genv.genv_next ge <= Mem.nextblock m2)%positive).
      { apply Mem.unchanged_on_nextblock in MEM_CHB.
        unfold Coqlib.Ple in MEM_CHB.
        ss. nia. }
      clear dependent m1. renames m2 MEM_NB' into m1 MEM_NB.

      (* skip *)
      fw. fw. fw.
      { hexploit (in_gfun_ilist _pals_wait_timer).
        { sIn. }
        i. des.
        econs; ss.
        - eval_comput.
          rewrite FDEF_SYMB. ss.
        - eval_comput. reflexivity.
        - eauto.
        - ss.
      }

      (* wait_timer *)
      pfold. econs 3; ss.
      { econs; eauto.
        - ss.
          econs; eauto.
          eapply CProgOSEC_WaitTimer with (tm:=sytm); ss.
        - ss. }
      { rewrite MWITree.unfold_main_loop.
        replace (MWITree.ltb_max_time sytm) with true.
        2: { unfold MWITree.ltb_max_time.
             destruct (Nat.ltb_spec sytm MAX_TIME); ss.
             nia. }
        unfold MWITree.loop_body.
        simpl_itree_goal.
        econs 1.
      }
      { simpl_itree_goal. ss. }

      intros retz pst_ret (* POSTCOND_SETT *) AFT_EVT.
      exists (idx_fch + (idx_get_inb + idx_job + idx_fin + 40 +
                    (idx_rst_sh + (idx_swinb + 20)))).
      left. simpl_itree_goal.

      inv AFT_EVT.
      inv CPROG_AFTER_EVENT; ss.
      symmetry in EVENT. inv EVENT. existT_elim.
      unf_resum. subst.
      inv OS_ESTEP. existT_elim. clarify.
      rename m' into m1.

      hexploit (in_gvar_ids _rxs); [sIn|].
      intros (b_rxs & FSYMB_RXS).

      fw. fw. fw. fw.
      { hexploit (in_gfun_ilist _fetch_msgs); eauto.
        { sIn. }
        i. des.

        econs; ss.
        - eval_comput.
          rewrite FDEF_SYMB. ss.
        - eval_comput.
          rewrite FSYMB_RXS.
          erewrite mem_skt_id; eauto.
        - eauto.
        - eauto.
      }

      (* callstate *)
      (* ss. *)
      (* eapply (sim_itree_red_idx prog) with *)
      (*         (idx_small:= (idx_fch + (idx_fin + idx_job + 30) + 50). *)
      (* { nia. } *)

      eapply sim_fetch_msgs; ss; eauto.
      { eapply range_tid. }
      clear inbc inbn MEM_MSTORE.
      intros m2 inbc inbn. i.

      assert (MEM_CHB: mem_changed_block b_mst m1 m2).
      { eapply Mem.unchanged_on_implies; eauto. }

      eapply mem_consts_unch_diffblk in MEM_CONSTS; cycle 1; eauto.
      { i. eapply global_addresses_distinct'; eauto.
        ss. des; clarify. }
      eapply mem_txs_unch_diffblk in MEM_TXS; cycle 1; eauto.
      { i. eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_rxs_unch_diffblk in MEM_RXS; cycle 1; eauto.
      { i. eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_sbuf_unch_diffblk in MEM_SBUF; cycle 1; eauto.
      { i. eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_sh_unch_diffblk in MEM_SH; cycle 1; eauto.
      { i. eapply global_addresses_distinct'; eauto. ss. }
      eapply inv_app_unch_diffblk in INV_APP; cycle 1; eauto.
      { sIn. }
      assert (MEM_NB': (Genv.genv_next ge <= Mem.nextblock m2)%positive).
      { apply Mem.unchanged_on_nextblock in MEM_CHB.
        unfold Coqlib.Ple in MEM_CHB. ss. nia. }
      clear dependent m1. renames m2 MEM_NB' into m1 MEM_NB.

      simpl_itree_goal.
      fw. fw. fw. fw. fw.
      { hexploit (in_gfun_ilist _get_cur_inbox); eauto.
        { sIn. }
        i. des.
        econs; ss.
        - eval_comput. rewrite FDEF_SYMB. ss.
        - eval_comput. eauto.
        - eauto.
        - ss.
      }

      red_idx (idx_get_inb + (idx_job + idx_rst_sh + idx_swinb + 50)).

      eapply sim_get_cur_inbox; eauto; ss.
      { apply range_tid. }
      intros b_mst' FSYMB_MST'.
      ss. clarify. rename FSYMB_MST' into FSYMB_MST.

      fw. upd_lenv.
      fw.
      (* call job *)
      fw.
      { hexploit (in_gfun_ilist _job).
        { cut (In (_job, Internal job_func) app_gfun_ilist).
          { i. sIn. }
          apply job_func_in_app_gfun_ilist.
        }
        i. des.

        econs; ss.
        - eval_comput.
          rewrite FDEF_SYMB. ss.
        - eval_comput. reflexivity.
        - eauto.
        - ss. apply job_func_type.
      }

      red_idx ((idx_rst_sh + (idx_swinb + 30)) + idx_job).
      eapply (sim_job_func r' ); eauto; ss.
      { range_stac. }

      unfold VerifProgBase.ge. fold ge.
      clear MEM_SH MEM_SBUF INV_APP. i.

      eapply mem_consts_unch in MEM_CONSTS; cycle 1; eauto.
      { eapply Mem.unchanged_on_implies; eauto.
        i. eapply blocks_of_ge_incl; eauto.
        rr. unfold main_const_ids. ss. i.
        des; sIn.
      }
      eapply mem_mstore_unch in MEM_MSTORE; cycle 1; eauto.
      { eapply Mem.unchanged_on_implies; eauto.
        i. r. esplits; eauto. sIn. }
      eapply mem_txs_unch in MEM_TXS; cycle 1; eauto.
      { eapply Mem.unchanged_on_implies; eauto.
        i. r. esplits; eauto. sIn. }
      eapply mem_rxs_unch in MEM_RXS; cycle 1; eauto.
      { eapply Mem.unchanged_on_implies; eauto.
        i. r. esplits; eauto. sIn. }
      assert (MEM_NB': (Genv.genv_next ge <= Mem.nextblock m')%positive).
      { apply Mem.unchanged_on_nextblock in UNCH_MAIN.
        unfold Coqlib.Ple in *. ss. nia. }
      clear dependent m1.
      renames m' INV_APP' MEM_NB' into m1 INV_APP MEM_NB.

      fw. fw. fw. fw.
      { econs. eval_comput.
        repr_tac. rewrite <- Nat2Z.inj_add.
        reflexivity. }
      upd_lenv.
      simpl_itree_goal.

      (* fw. fw. fw. *)
      (* { hexploit (in_gfun_ilist _pals_set_timelimit); [sIn|]. *)
      (*   i. des. *)

      (*   econs; ss. *)
      (*   - eval_comput. rewrite FDEF_SYMB. ss. *)
      (*   - eval_comput. *)
      (*     repr_tac. *)
      (*     rewrite <- Nat2Z.inj_add. *)
      (*     rewrite <- Nat2Z.inj_sub by nia. *)
      (*     eauto. *)
      (*   - eauto. *)
      (*   - ss. *)
      (* } *)

      (* pfold. econs 3; ss. *)
      (* { econs; eauto. *)
      (*   - ss. *)
      (*     econs 2; try reflexivity. *)
      (*     range_stac. *)
      (*   - ss. } *)
      (* { econs. } *)
      (* { replace (sytm + period + (period - DELTA)) with *)
      (*       (sytm + period + period - DELTA) by nia. *)
      (*   simpl_itree_goal. *)
      (*   ss. } *)

      (* intros [] pst_r AFT_EVT. *)
      (* inv AFT_EVT. ss. *)
      (* inv CPROG_AFTER_EVENT; ss. *)
      (* clarify. ss. existT_elim. subst. *)
      (* simpl_itree_goal. *)
      (* rename m' into m1. *)

      (* exists (idx_rst_sh + (idx_swinb + 20)). left. *)

      fw. fw. fw.
      { hexploit (in_gfun_ilist _reset_send_hist); [sIn|].
        i. des.
        econs; ss.
        - eval_comput. rewrite FDEF_SYMB. ss.
        - eval_comput. ss.
        - eauto.
        - ss.
      }

      eapply sim_reset_send_hist; try eapply range_tid; eauto; ss.
      clear sh' MEM_CONSTS MEM_SH. i.

      hexploit (in_gvar_ids _send_hist); [sIn|].
      intros (b_sh & FSYMB_SH). ss.

      assert (MEM_CHB: mem_changed_block b_sh m1 m').
      { apply MEM_UNCH. ss. }
      clear MEM_UNCH.

      eapply mem_txs_unch_diffblk in MEM_TXS; cycle 1; eauto.
      { i. eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_rxs_unch_diffblk in MEM_RXS; cycle 1; eauto.
      { i. eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_sbuf_unch_diffblk in MEM_SBUF; cycle 1; eauto.
      { i. eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_mstore_unch_diffblk in MEM_MSTORE; cycle 1; eauto.
      { i. eapply global_addresses_distinct'; eauto. ss. }

      eapply inv_app_unch_diffblk in INV_APP; cycle 1; eauto.
      { sIn. }
      assert (MEM_NB': (Genv.genv_next ge <= Mem.nextblock m')%positive).
      { apply Mem.unchanged_on_nextblock in MEM_CHB.
        unfold Coqlib.Ple in MEM_CHB. ss. nia. }
      clear dependent m1. renames m' MEM_NB' into m1 MEM_NB.

      fw. fw. fw.
      { hexploit (in_gfun_ilist _switch_inbox); [sIn|].
        i. des.
        econs; ss.
        - eval_comput. rewrite FDEF_SYMB. ss.
        - eval_comput. ss.
        - eauto.
        - ss.
      }

      eapply sim_switch_inbox; eauto; ss.
      { eapply range_tid. }
      rename ofsc into ofsc_p.
      clear cflg ofsn MEM_MSTORE.
      intros m' cflg inbn_t' ofsc ofsn. i.

      assert (MEM_CHB: mem_changed_block b_mst m1 m').
      { apply UNCH. ss. }
      clear UNCH.

      eapply mem_consts_unch_diffblk in MEM_CONSTS; cycle 1; eauto.
      { i. eapply global_addresses_distinct'; eauto.
        ss. des; clarify. }
      eapply mem_txs_unch_diffblk in MEM_TXS; cycle 1; eauto.
      { i. eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_rxs_unch_diffblk in MEM_RXS; cycle 1; eauto.
      { i. eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_sbuf_unch_diffblk in MEM_SBUF; cycle 1; eauto.
      { i. eapply global_addresses_distinct'; eauto. ss. }
      eapply mem_sh_unch_diffblk in MEM_SH; cycle 1; eauto.
      { i. eapply global_addresses_distinct'; eauto. ss. }
      eapply inv_app_unch_diffblk in INV_APP; cycle 1; eauto.
      { sIn. }
      assert (MEM_NB': (Genv.genv_next ge <= Mem.nextblock m')%positive).
      { apply Mem.unchanged_on_nextblock in MEM_CHB.
        unfold Coqlib.Ple in MEM_CHB. ss. nia. }
      clear dependent m1. renames m' MEM_NB' into m1 MEM_NB.

      (* ret *)
      fw. fw_tau (S (idx_fin + 25)).
      { econs. eauto. }

      red_idx (S (idx_fin + 15 + 5)).
      fw_r.
      rewrite Nat.sub_0_r.
      eapply CIH.
      subst inbn_t'.
      econs; try eapply LENV_EQUIV; eauto.
      - range_stac.
      - subst. ss.
    }

    i.
    fw.
    red_idx idx_fin.

    clear sytm RANGE_SYTM LENV_EQUIV MEM_SBUF MEM_CONSTS
          MEM_TXS MEM_RXS INV_APP.
    clear ofsc ofsn sytm_dmy MEM_MSTORE.
    inv LOOP_INV.

    ss. erewrite eval_loop_cond in EVAL_EXPR; cycle 2.
    { rewrite LENV_EQUIV. ss. }
    { rewrite Z.mul_comm.
      rewrite LENV_EQUIV. ss. }
    2: { range_stac. }

    unfold MWITree.ltb_max_time.
    rewrite MWITree.unfold_main_loop.
    destruct (Nat.ltb_spec sytm MAX_TIME); clarify.

    eapply paco3_mon.
    eapply SIM_RET. eauto.
  Qed.

End RUN_TASK.
