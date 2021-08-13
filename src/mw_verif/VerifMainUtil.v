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
Require Import OSNodes OSModel.
Require Import ProgSem CProgEventSem.
Require Import ProgSim CProgSimLemmas.
Require Import RTSysEnv MWITree.

(* Require Import SystemParams. *)
(* Require Import SystemDefs ITreeSpec. *)
(* Require Import SystemEventSem. *)
(* Require Import main_p main_pi. *)
Require Import config_prm main_prm SystemProgs.
Require Import VerifProgBase.


Import Clight Clightdefs.
Import ITreeNotations.

Generalizable Variable sysE.
Set Nested Proofs Allowed.


Local Transparent Archi.ptr64.
Local Opaque Int64.max_unsigned Int.max_unsigned.
Local Opaque Int.min_signed Int.max_signed.

(* Local Opaque Z.le Z.lt. *)
Local Opaque Genv.globalenv.

Arguments Nat.ltb: simpl nomatch.


Lemma send_hist_write_one
      tid' sh
      (TID': tid' < length sh)
  : exists sh1 sh_x sh2,
    <<LEN_SH1: length sh1 = tid'>> /\
    <<SH_DIV: sh = sh1 ++ sh_x :: sh2>> /\
    <<CHK_W: check_send_hist_write sh [tid'] =
             sh1 ++ true :: sh2>>.
Proof.
  unfold check_send_hist_write.
  hexploit (nth_error_Some2 _ sh tid'); eauto. i. des.
  hexploit nth_error_split; eauto. i. des.
  esplits; eauto.

  subst.
  rewrite imap_app. ss. f_equal.
  { apply nth_eq_list_eq. i.
    rewrite imap_nth_error_iff.
    destruct (nth_error l1 n) eqn: NTH1; ss.
    eapply nth_error_Some1' in NTH1.
    destruct (Nat.eqb_spec n (length l1)); ss. nia.
  }
  rewrite Nat.eqb_refl. ss. f_equal.

  apply nth_eq_list_eq. i.
  rewrite imap_nth_error_iff.
  destruct (nth_error l2 n) eqn: NTH2; ss.
  desf.
  exfalso.
  rewrite orb_true_iff in *. des; ss.
  desf.
  hexploit beq_nat_true; eauto. i. nia.
Qed.


Section SIM_UTILS.
  Context `{SystemEnv}.
  (* Context `{CProgSysEvent}. *)
  Existing Instance cprog_event_instance.
  (* Context `{cprog_event (@progE sysE)}. *)
  Variable cprog: Clight.program.

  (* Let cprog_event_obj: cprog_event (@progE sysE) := *)
  (*   @cprog_event_instance sysE. *)
  (* Existing Instance cprog_event_obj. *)

  Let prog: Prog.t := prog_of_clight cprog.
  Let ge := Clight.globalenv cprog.
  Variable tid: nat.
  Hypothesis RANGE_TID: (tid < num_tasks)%nat.
  Context `{genv_props ge (main_gvar_ilist tid)
                       main_gfun_ilist main_cenv_ilist}.

  (* Let progE := @progE extcallE. *)

  Variable r: nat -> itree progE unit -> Prog.state prog -> Prop.

  Notation sim := (paco3 _).

  Inductive mcpy_linv
            (itr0: itree progE unit) (m0: mem)
            (bs: list byte)
            b_s ofs_s b_d ofs_d
            (i: nat) (itr: itree progE unit)
            (le: PTree.t val) (m: mem): Prop :=
    MsgCopyLoopInv
      (MEM_CONSTS: mem_consts ge m tid)
      (ITR_INV: itr = itr0)
      (LENV_EQUIV: lenv_equiv
                     le [(_dst, Vptr b_d (Ptrofs.repr ofs_d));
                        (_src, Vptr b_s (Ptrofs.repr ofs_s));
                        (_i, Vint (IntNat.of_nat i))])
      (LBS_SRC: Mem.loadbytes m b_s ofs_s (Z.of_nat msg_size) =
                Some (inj_bytes bs))
      (SBS_DST: (i = 0 /\ m = m0) \/
                (0 < i /\ Mem.storebytes m0 b_d ofs_d (firstn i (inj_bytes bs)) = Some m))
      (PERM_DST: Mem.range_perm m b_d ofs_d (ofs_d + (Z.of_nat msg_size)) Cur Writable)
  .

  Definition idx_msg_copy: nat := 10 + (msg_size * 10 + 10).

  Lemma load_send_hist
        tid' m sh b_sh
        (MEM_SH_BLK: mem_sh_blk m sh b_sh)
        (TID: tid' < num_tasks)
    : exists sh_tid,
      <<SH_N: nth_error sh tid' = Some sh_tid>> /\
      <<SH_LOAD: Mem.load Mint8signed m b_sh (Z.of_nat tid') =
                 Some (if sh_tid then Vtrue else Vfalse)>>.
  Proof.
    hexploit mem_sh_blk_length; eauto. intro LEN_SH.
    hexploit (nth_error_Some2 _ sh tid').
    { nia. }
    i. des.
    esplits; eauto.

    cut (Mem.loadbytes m b_sh (Z.of_nat tid')
                       (size_chunk Mint8signed) =
         Some [bool2memval e1]).
    { intro LBS.
      eapply Mem.loadbytes_load in LBS.
      2: { ss. solve_divide. }
      rewrite LBS.
      destruct e1; ss. }

    hexploit mem_sh_loadbytes; eauto. intro LBS.
    replace (Z.of_nat tid') with (0 + Z.of_nat tid')%Z by ss.
    erewrite Mem_loadbytes_sublist; cycle 1; eauto.
    { nia. }
    { ss. }
    { ss. nia. }
    ss. rewrite Nat2Z.id.

    hexploit nth_error_split; eauto. i. des. subst.
    rewrite map_app.
    rewrite skipn_app_exact.
    2: { rewrite map_length. ss. }
    ss.
  Qed.

  Lemma store_send_hist
        (bv: bool) v
        tid' m b_sh
        sh1 sh_x0 sh2
        (MEM_SH_BLK: mem_sh_blk m (sh1 ++ sh_x0 :: sh2) b_sh)
        (LEN_SH1: length sh1 = tid')
        (BOOL_VAL: v = if bv then Vtrue else Vfalse)
    : exists m',
      <<SH_STORE: Mem.store Mint8signed m b_sh (Z.of_nat tid') v = Some m'>> /\
      <<MEM_SH_BLK': mem_sh_blk m' (sh1 ++ bv :: sh2) b_sh>>.
  Proof.
    guardH BOOL_VAL.
    hexploit mem_sh_blk_length; eauto. intro LEN_SH.
    inv MEM_SH_BLK.

    hexploit (Mem.valid_access_store
                m Mint8signed b_sh (Z.of_nat (length sh1)) v).
    { r. split; ss.
      - ii. apply mem_sh_writable.
        split.
        + nia.
        + cut (length sh1 < num_tasks).
          { nia. }
          rewrite <- LEN_SH.
          rewrite app_length. ss. nia.
      - solve_divide.
    }

    destruct 1 as [m' STORE].
    esplits; eauto.

    rewrite app_length in LEN_SH. ss.

    rewrite <- LEN_SH in mem_sh_loadbytes.
    rewrite Nat2Z.inj_add in mem_sh_loadbytes.
    eapply Mem.loadbytes_split in mem_sh_loadbytes; try nia.
    destruct mem_sh_loadbytes as
        (bs1 & bs' & LBS1 & LBS' & BS_EQ).
    rewrite map_app in BS_EQ. ss.

    apply app_eqlen_inv in BS_EQ.
    2: { rewrite map_length.
         apply Mem.loadbytes_length in LBS1.
         rewrite Nat2Z.id in LBS1. ss. }
    destruct BS_EQ as (BS1_EQ & BS_EQ').

    rewrite pos_of_succ_nat_eq in LBS'.
    replace (Z.of_nat (S (Datatypes.length sh2))) with
        (1 + Z.of_nat (length sh2))%Z in LBS' by nia.

    eapply Mem.loadbytes_split in LBS'; try nia.
    destruct LBS' as (bs_x & bs2 & LBS_X & LBS2 & BS_EQ'').
    rewrite BS_EQ'' in BS_EQ'. clear BS_EQ''.

    apply Mem.loadbytes_length in LBS_X.
    destruct bs_x as [| x []]; ss.
    clarify.

    assert (UNCH: Mem.unchanged_on
                    (fun b ofs => b <> b_sh \/
                               ofs <> (Z.of_nat (length sh1)))
                    m m').
    { eapply Mem.store_unchanged_on; eauto.
      i. ss.
      ii. des; ss. nia. }

    eapply Mem.loadbytes_unchanged_on in LBS1; eauto.
    2: { i. ss. right. nia. }
    eapply Mem.loadbytes_unchanged_on in LBS2; eauto.
    2: { i. ss. right. nia. }

    assert (BVAL: v = Vint (Int.repr (if bv then 1 else 0)%Z)).
    { rewrite BOOL_VAL. desf. }
    clear BOOL_VAL. subst v.

    econs.
    - rewrite <- LEN_SH.
      rewrite Nat2Z.inj_add.
      erewrite Mem.loadbytes_concat; eauto; try nia.
      { rewrite map_app. eauto. }
      replace (Z.of_nat (S (Datatypes.length sh2))) with
          (1 + Z.of_nat (length sh2))%Z by nia.
      ss.
      erewrite Mem.loadbytes_concat; eauto; try nia.
      { instantiate (1:= [bool2memval bv]). ss. }

      eapply Mem.load_store_same in STORE. ss.
      apply Mem.load_loadbytes in STORE.
      destruct STORE as (bs_x & LB_X & BS_X_EQ). ss.
      rewrite LB_X.

      apply Mem.loadbytes_length in LB_X.
      destruct bs_x as [| y []]; ss.
      destruct y; ss.

      hexploit (decode_byte_one_inv (if bv then 1 else 0)%Z); eauto.
      { desf; range_stac. }
      { rewrite <- BS_X_EQ.
        desf. }
      intro R. rewrite R.
      destruct bv; ss.

    - ii. eapply Mem.perm_store_1; eauto.
  Qed.

  Lemma sim_msg_copy
        idx_r itr k m0 bs
        b_s ofs_s
        b_d ofs_d
        (MEM_CONSTS: mem_consts ge m0 tid)
        (CALL_CONT: is_call_cont k)
        (BLOCK_NEQ: b_s <> b_d)
        (DEST_BLOCK_NOT_CONSTS:
           ~ blocks_of ge main_const_ids b_d 0)
        (OFS_SRC: (0 <= ofs_s <= Ptrofs.max_unsigned)%Z)
        (OFS_SRC2: (0 <= ofs_s + Z.of_nat msg_size <= Ptrofs.max_unsigned)%Z)
        (OFS_DST: (0 <= ofs_d <= Ptrofs.max_unsigned)%Z)
        (OFS_DST2: (0 <= ofs_d + Z.of_nat msg_size <= Ptrofs.max_unsigned)%Z)
        (LBS_SRC: Mem.loadbytes m0 b_s ofs_s (Z.of_nat msg_size) =
                  Some (inj_bytes bs))
        (PERM_DST: Mem.range_perm
                     m0 b_d ofs_d
                     (ofs_d + Z.of_nat msg_size)%Z
                     Cur Writable)
        (SIM_RET:
           forall m'
             (MEM_CONSTS: mem_consts ge m' tid)
             (MEM_STORE: (msg_size = 0 /\ m' = m0) \/
                         (0 < msg_size /\
                          Mem.storebytes
                            m0 b_d ofs_d (inj_bytes bs) = Some m'))
           ,
             paco3 (_sim_itree prog) r idx_r
                   itr
                   (Clight.Returnstate
                      Vundef k m'))

    : paco3 (_sim_itree prog) r (idx_msg_copy + idx_r)
            itr
            (Clight.Callstate
               (Internal f_msg_copy)
               [Vptr b_s (Ptrofs.repr ofs_s);
               Vptr b_d (Ptrofs.repr ofs_d)] k m0).
  Proof.
    unfold idx_msg_copy.
    assert(LEN_BS: length bs = msg_size).
    { eapply Mem.loadbytes_length in LBS_SRC.
      unfold inj_bytes in LBS_SRC.
      rewrite map_length in LBS_SRC.
      rewrite Nat2Z.id in LBS_SRC. ss. }
    assert(LEN_INJ_BS: length (inj_bytes bs) = msg_size).
    { unfold inj_bytes. rewrite map_length. ss. }

    start_func.
    { ss. econs 1. }

    fw. clear STEP_ENTRY.
    fw. fw.
    { econs. eval_comput. eauto. }
    fw. upd_lenv.

    (* replace 7%Z with (Z.of_nat msg_size%nat) by ss. *)
    fold_for_loop _i .

    hexploit (in_gvar_ids _MSG_SIZE); [sIn|].
    intros (b_msg & FSYMB_MSZ).

    pose proof range_msg_size as SINT_MSZ.

    eapply simple_for_loop
      with (idx_each:= 10) (idx0:= idx_r)
           (i_max := msg_size)
           (loop_inv := mcpy_linv itr m0 bs b_s ofs_s
                                  b_d ofs_d).
    { econs; eauto; ss. }
    { range_stac. }
    { nia. }
    { (* loop body *)
      clear dependent le. i.
      clear LBS_SRC PERM_DST.
      clear MEM_CONSTS.
      inv LINV.
      assert (I_LT: (Z.of_nat i < Z.of_nat msg_size)%Z) by nia.
      guardH SBS_DST.

      assert (SINT_I: IntRange.sint i).
      { clear - I_LT SINT_MSZ.
        range_stac. }

      fw. fw. fw.
      { econs.
        - eval_comput.
          rewrite FSYMB_MSZ.
          cbn. rewrite Ptrofs.unsigned_zero.
          erewrite mem_consts_msg_size by eauto.
          unfold IntNat.of_nat.

          repr_tac.
          destruct (Z.ltb_spec (Z.of_nat i) (Z.of_nat msg_size))
            as [LT|GE].
          2: { apply Nat2Z.inj_le in GE.
               exfalso. nia. }
          reflexivity.

        - simpl. cbn.
          rewrite Int.eq_false by ss.
          simpl. reflexivity.
      }
      ss.
      fw.

      assert (LOAD_I: exists b bs_r,
                 Mem.load Mint8signed m1 b_s
                          (ofs_s + Z.of_nat i) =
                 Some (Vint (Int.repr (Byte.signed b))) /\
                 bs = firstn i bs ++ b :: bs_r).
      { clear - LEN_BS RANGE_I LBS_SRC.
        replace (Z.of_nat msg_size) with
            (Z.of_nat i + (1 + Z.of_nat (msg_size - i - 1)))%Z in LBS_SRC by nia.

        assert (BS_N: exists a, nth_error bs i = Some a).
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
        { ss. apply Z.divide_1_l. }
      }
      destruct LOAD_I as (b & bs_r & LOAD_I & BS_EQ).

      assert (STORE_BYTE: exists m',
                   Mem.store
                     Mint8signed m1 b_d (ofs_d + Z.of_nat i)
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
          repr_tac.
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
      eapply (sim_itree_red_idx prog) with (idx_small:=idx1 - 10).
      { nia. }

      eapply SIM_NEXT.
      (* - rewrite LENV_EQUIV. ss. *)
      assert (mem_unchanged_except
                (fun b ofs => b = b_d /\ ofs = ofs_d + Z.of_nat i)%Z
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
      + eapply mem_consts_unch_diffblk; eauto.
        { eapply Mem.storebytes_unchanged_on; eauto. }
        ii. apply DEST_BLOCK_NOT_CONSTS.
        r. esplits; eauto.
      + eapply Mem.loadbytes_unchanged_on; eauto.
        ii. des; ss.
      + right. splits; [nia|].
        unguardH SBS_DST. desH SBS_DST.
        * subst. ss.
          ss. rewrite Z.add_0_r in *.
          subst. ss.
        * erewrite firstn_snoc_nth with (d:= Byte Byte.zero); eauto.
          2: {
            rewrite BS_EQ.
            unfold inj_bytes.
            rewrite map_length. rewrite app_length.
            rewrite firstn_length_le by nia.
            ss. nia.
          }

          eapply Mem.storebytes_concat; eauto.
          assert (LEN_FIRSTN: length (firstn i (inj_bytes bs)) = i).
          { apply firstn_length_le. nia. }
          rewrite LEN_FIRSTN.

          assert (nth_error (inj_bytes bs) i =
                  Some (Byte b)).
          { unfold inj_bytes in *.
            rewrite BS_EQ. rewrite map_app.
            rewrite <- map_firstn in LEN_FIRSTN.
            rewrite nth_error_app2.
            2: { rewrite map_length in *. nia. }
            rewrite LEN_FIRSTN.
            rewrite Nat.sub_diag. ss. }
          erewrite nth_error_nth; eauto.
      + ii. eapply Mem.perm_storebytes_1; eauto.
    }

    (* after loop *)
    clear dependent le. i.
    inv LINV_END.

    fw. fw. fw.
    { econs.
      - eval_comput.
        rewrite FSYMB_MSZ. cbn.
        rewrite Ptrofs.unsigned_zero.
        erewrite mem_consts_msg_size by eauto.

        repr_tac.
        (* eval_comput. repr_tac. *)
        (* unfold msg_size. *)
        rewrite Z.ltb_irrefl. simpl. reflexivity.
      - ss.
    }
    rewrite Int.eq_true. simpl.
    fw. fw. fw.

    eapply (sim_itree_red_idx prog) with (idx_small:= idx_r).
    { nia. }

    (* des. *)
    (* { eapply SIM_RET; eauto. } *)
    eapply SIM_RET; eauto.
    des.
    - left. eauto.
    - right. split; ss.
      rewrite <- LEN_INJ_BS in SBS_DST0.
      rewrite firstn_all in SBS_DST0. ss.
  Qed.


  Definition idx_rst_sh: nat := num_tasks * 10 + 10.

  Inductive rst_sh_linv
            (itr0: itree progE unit) (m0: mem)
            (b_sh: block)
            (i: nat) (itr: itree progE unit)
            (le: PTree.t val) (m: mem): Prop :=
    ResetSendHistLoopInv
      sh'
      (MEM_CONSTS: mem_consts ge m tid)
      (MEM_SH_BLK: mem_sh_blk m (repeat false i ++ sh') b_sh)
      (MEM_CH_BLK: mem_changed_block b_sh m0 m)
      (ITR_INV: itr = itr0)
      (SINT_RANGE_I: IntRange.sint i)
      (LENV_EQUIV: lenv_equiv
                     le [(_i, Vint (IntNat.of_nat i))])
  .


  Lemma sim_reset_send_hist
        idx_r itr kp m0 sh
        (CALL_CONT: is_call_cont kp)
        (MEM_CONSTS: mem_consts ge m0 tid)
        (MEM_SH: mem_sh ge m0 sh)
        (SIM_RET:
           forall m' sh'
             (RESET_SH: sh' = List.repeat false num_tasks)
             (MEM_CONSTS: mem_consts ge m' tid)
             (MEM_SH: mem_sh ge m' sh')
             (MEM_UNCH: mem_changed_gvar_id ge _send_hist m0 m')
           ,
             paco3 (_sim_itree prog) r idx_r
                   itr (Clight.Returnstate Vundef kp m'))
    : paco3 (_sim_itree prog) r (idx_rst_sh + idx_r)
            itr
            (Clight.Callstate
               (Internal (f_reset_send_hist
                            (Z.of_nat max_num_tasks)))
               [] kp m0).
  Proof.
    start_func.
    { econs. }

    unfold idx_rst_sh.
    fw. fw. fw.
    { econs. eval_comput. eauto. }
    upd_lenv.

    fw.
    hexploit (in_gvar_ilist _send_hist); [sIn|].
    intros (b_sh & FSYMB_SH & _).
    hexploit (in_gvar_ilist _NUM_TASKS); [sIn|].
    intros (b_nt & FSYMB_NT & _).
    des.

    pose proof range_num_tasks as SINT8_NT.
    (* assert (SINT_RANGE_NT: IntRange.sint num_tasks). *)
    (* {  *)
    (*   apply int_range_sint8_sint. *)
    (*   apply range_num_tasks. } *)

    eapply simple_for_loop
      with (idx_each:= 10) (idx0:= 0)
           (i_max := num_tasks)
           (loop_inv := rst_sh_linv itr m0 b_sh); eauto.
    { econs; ss; eauto.
      r. apply Mem.unchanged_on_refl. }
    (* { rewrite LENV_EQUIV. ss. } *)
    { range_stac. }
    { nia. }
    { (* loop body *)
      clear dependent le. clear MEM_CONSTS.
      i. inv LINV.

      assert (I_VPTR: (0 <= Z.of_nat i <= Ptrofs.max_unsigned)%Z).
      { split; [nia |].
        apply Z.lt_le_incl.
        transitivity (Z.of_nat num_tasks).
        { nia. }
        clear - SINT8_NT.
        range_stac.
      }

      assert (SINT_RANGE_S_I: IntRange.sint (S i)).
      { range_stac. }

      fw. fw. fw.
      { econs.
        - eval_comput.
          rewrite FSYMB_NT. unfold deref_loc_c. s.
          rewrite Ptrofs.unsigned_zero.
          erewrite mem_consts_num_tasks by eauto.

          repr_tac.
          instantiate (1:= Vtrue).
          destruct (Z.ltb_spec (Z.of_nat i)
                               (Z.of_nat num_tasks)) as [LT|GE]; ss.
          apply Nat2Z.inj_le in GE. nia.
        - ss.
      }
      rewrite Int.eq_false by ss.
      ss. fw.

      destruct sh' as [| x sh'].
      { exfalso.
        hexploit mem_sh_blk_length; eauto.
        rewrite app_length. rewrite repeat_length. ss.
        nia. }

      hexploit (store_send_hist false); eauto. i. des.
      rewrite repeat_length in SH_STORE.

      fw.
      { econs.
        - eval_comput.
          rewrite FSYMB_SH. cbn.
          repr_tac.
          rewrite Z.mul_1_l.
          rewrite Ptrofs.add_zero_l.
          reflexivity.
        - eval_comput. eauto.
        - ss.
        - ss.
          eval_comput. cbn.
          repr_tac. eauto.
      }

      assert (CH_BLK: mem_changed_block b_sh m1 m').
      { eapply Mem.store_unchanged_on; eauto. }

      eapply mem_consts_unch_diffblk in MEM_CONSTS; eauto.
      2: { i. eapply global_addresses_distinct' with
                  (id:= _send_hist); eauto.
           ii. subst. ss. des; ss. }

      fw.
      { econs. eauto. }
      fw.
      { econs. eval_comput.
        repr_tac.
        replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by nia.
        reflexivity.
      }
      upd_lenv.

      fw.
      eapply (sim_itree_red_idx prog) with (idx_small:= idx1 - 10).
      { nia. }

      eapply SIM_NEXT.
      (* - rewrite LENV_EQUIV. ss. *)
      econs; eauto.
      + replace (S i) with (i + 1) by nia.
        rewrite repeat_app.
        rewrite <- app_assoc. ss. eauto.
      + eapply Mem.unchanged_on_trans; eauto.
    }

    clear dependent le. clear MEM_CONSTS.
    i. inv LINV_END.

    fw. fw. fw.
    { econs.
      - eval_comput.
        rewrite FSYMB_NT. cbn.
        rewrite Ptrofs.unsigned_zero.
        erewrite mem_consts_num_tasks; eauto.
      - ss. repr_tac.
        rewrite Z.ltb_irrefl. ss.
    }
    rewrite Int.eq_true. ss.
    fw. fw. fw.

    eapply (sim_itree_red_idx prog) with (idx_small:= idx_r).
    { nia. }
    eapply SIM_RET; eauto.
    - destruct sh'.
      2: { exfalso.
           hexploit mem_sh_blk_length; eauto.
           rewrite app_length, repeat_length. ss. nia. }
      rewrite app_nil_r in *.
      ii. ss. clarify.
    - ii. ss. clarify.
  Qed.


  Definition idx_ch_sh: nat := 10 + (num_tasks * 30 + 20).

  Inductive ch_sh_linv
            (itr0: itree progE unit) (m0: mem)
            (* (bs: list byte) *)
            (* b_s ofs_s b_d ofs_d *)
            (sh: list bool) (b_sh b_mcm: block)
            (tid_d: nat) (midx: nat) (mbrs: list Tid)
            (i: nat) (itr: itree progE unit)
            (le: PTree.t val) (m: mem): Prop :=
    CheckSendHistLoopInv
      (* (MEM_CONSTS: mem_consts ge m tid) *)
      (* (MEM_SH_BLK: mem_sh_blk m sh b_sh) *)
      (MEM_INV: m = m0)
      (ITR_INV: itr = itr0)
      (SINT_RANGE_I: IntRange.sintz (Z.of_nat i))
      (LENV_EQUIV: lenv_equiv
                     le [(_id_dest, Vint (IntNat.of_nat tid_d));
                        (_i, Vint (IntNat.of_nat i));
                        (_group_mem, Vptr b_mcm (Ptrofs.repr (Z.of_nat (max_num_tasks * midx))))
      ])
      (CHECKED_BEFORE_I: forall tid' (BEF_I: tid' < i),
          In tid' mbrs -> nth_error sh tid' = Some false)
  .


  Inductive ch_sh_w_linv
            (itr0: itree progE unit) (m0: mem)
            (* (bs: list byte) *)
            (* b_s ofs_s b_d ofs_d *)
            (sh: list bool) (b_sh b_mcm: block)
            (tid_d: nat) (midx: nat) (mbrs: list Tid)
            (i: nat) (itr: itree progE unit)
            (le: PTree.t val) (m: mem): Prop :=
    CheckSendHistWriteLoopInv
      sh1 sh2 sh1'
      (MEM_CONSTS: mem_consts ge m tid)
      (MEM_SH_BLK: mem_sh_blk m (sh1' ++ sh2) b_sh)
      (MEM_CH_BLK: mem_changed_block b_sh m0 m)
      (* (MEM_INV: m = m0) *)
      (ITR_INV: itr = itr0)
      (SINT_RANGE_I: IntRange.sintz (Z.of_nat i))
      (LENV_EQUIV: lenv_equiv
                     le [(_id_dest, Vint (IntNat.of_nat tid_d));
                        (_i, Vint (IntNat.of_nat i));
                        (_group_mem, Vptr b_mcm (Ptrofs.repr (Z.of_nat (max_num_tasks * midx))))
      ])
      (SH_DIV: sh = sh1 ++ sh2)
      (LEN_SH1: length sh1 = i)
      (CHK_WR: check_send_hist_write sh1 mbrs = sh1')
  .

  Lemma sim_check_send_hist
        idx_r itr kp m0
        tid_d sh
        (CALL_CONT: is_call_cont kp)
        (RANGE_TID_D: tid_d < num_tasks + num_mcasts)
        (MEM_CONSTS: mem_consts ge m0 tid)
        (MEM_SH: mem_sh ge m0 sh)
        (SIM_RET:
           forall m' sh' ret
             (CHECK_SEND_HIST:
                (check_send_hist sh tid_d = Some sh' /\
                 ret = Int.one) \/
                (check_send_hist sh tid_d = None /\ sh' = sh /\
                 ret = Int.zero))
             (MEM_CONSTS: mem_consts ge m' tid)
             (MEM_SH: mem_sh ge m' sh')
             (MEM_UNCH: mem_changed_gvar_id ge _send_hist m0 m')
           ,
             paco3 (_sim_itree prog) r idx_r
                   itr (Clight.Returnstate (Vint ret) kp m'))

    : paco3 (_sim_itree prog) r (idx_ch_sh + idx_r)
            itr
            (Clight.Callstate
               (Internal (f_check_send_hist
                            (Z.of_nat max_num_tasks)
                            (Z.of_nat max_num_mcasts)))
               [Vint (IntNat.of_nat tid_d)] kp m0).
  Proof.
    unfold idx_ch_sh.
    start_func.
    { econs. }

    hexploit (in_gvar_ilist _NUM_TASKS); [sIn|].
    intros (b_nt & FSYMB_NT & _).
    hexploit (in_gvar_ilist _NUM_MCASTS); [sIn|].
    intros (b_nmc & FSYMB_NMC & _).
    des.

    assert (INT_RANGE_TID_D: IntRange.sintz (Z.of_nat tid_d)).
    { pose proof range_valid_dest_ids as VD.
      fold num_tasks num_mcasts in VD.
      range_stac. }
    assert (INT_RANGE_NUM_TASKS: IntRange.sint num_tasks).
    { pose proof range_num_tasks.
      range_stac. }
    assert (INT_RANGE_NUM_MCASTS: IntRange.sint num_mcasts).
    { pose proof range_num_mcasts.
      range_stac. }

    fw. fw. fw.
    { econs.
      - eval_comput.
        rewrite FSYMB_NT. cbn.
        rewrite Ptrofs.unsigned_zero.
        erewrite mem_consts_num_tasks by eauto.
        instantiate (1:= if (tid_d <? num_tasks) then Vtrue else Vfalse).
        repr_tac.

        destruct (Z.ltb_spec (Z.of_nat tid_d)
                             (Z.of_nat num_tasks)) as [LT|GE].
        + apply Nat2Z.inj_lt in LT.
          destruct (Nat.ltb_spec tid_d num_tasks); ss.
          nia.
        + apply Nat2Z.inj_le in GE.
          destruct (Nat.ltb_spec tid_d num_tasks); ss.
          nia.
      - instantiate (1:= (tid_d <? num_tasks)).
        destruct (Nat.ltb_spec tid_d num_tasks); ss.
    }

    hexploit (in_gvar_ilist _send_hist); [sIn|].
    intros (b_sh & FSYMB_SH & _).
    r in MEM_SH. hexploit MEM_SH; eauto.
    clear MEM_SH.
    intro MEM_SH_BLK.

    assert (TID_D_VALID_PTR:
              (0 <= Z.of_nat tid_d <= Ptrofs.max_unsigned)%Z).
    { cut (Z.of_nat tid_d < Ptrofs.max_unsigned)%Z.
      { i. nia. }
      range_stac. }

    destruct (Nat.ltb_spec tid_d num_tasks) as [LT|GE].
    - (* unicast *)
      hexploit (load_send_hist tid_d); eauto.
      i. des.

      fw.
      { econs.
        - eval_comput.
          rewrite FSYMB_SH.
          cbn.
          repr_tac.
          rewrite Ptrofs.add_zero_l.
          repr_tac.
          rewrite Z.mul_1_l.
          rewrite SH_LOAD.

          eval_comput.
          instantiate (1:= if sh_tid then Vfalse else Vtrue).
          destruct sh_tid; ss.
        - instantiate (1:= negb sh_tid).
          ss.
          destruct sh_tid; ss.
      }

      destruct sh_tid; ss.
      { (* already sent *)
        fw.
        { econs.
          - eval_comput. eauto.
          - eval_comput. ss.
          - ss.
        }
        ss.

        eapply (sim_itree_red_idx prog) with (idx_small:= idx_r).
        { nia. }
        rewrite call_cont_is_call_cont by ss.
        eapply SIM_RET; eauto.
        - right.
          splits; eauto.
          unfold check_send_hist.
          destruct (Nat.ltb_spec tid_d num_tasks).
          + unfold check_send_hist_read.
            rewrite SH_N. ss.
          + exfalso. nia.
        - r. i. ss. clarify.
        - r. i. apply Mem.unchanged_on_refl.
      }

      (* available *)
      fw.

      hexploit (send_hist_write_one tid_d sh).
      { hexploit mem_sh_blk_length; eauto. nia. }
      i. des.
      guardH SH_DIV. guardH LEN_SH1.

      hexploit (store_send_hist true Vtrue tid_d); eauto.
      { rewrite <- SH_DIV. eauto. }
      i. des.

      fw.
      { econs.
        - eval_comput.
          rewrite FSYMB_SH. cbn.
          repr_tac.
          rewrite Ptrofs.add_zero_l.
          rewrite Z.mul_1_l. reflexivity.
        - eval_comput. eauto.
        - ss.
        - eval_comput. cbn.
          repr_tac. eauto.
      }

      fw. fw.
      { econs.
        - eval_comput. ss.
        - eval_comput. ss.
        - econs.
      }

      ss. rewrite call_cont_is_call_cont by ss.
      eapply (sim_itree_red_idx prog) with (idx_small:= idx_r).
      { nia. }

      eapply SIM_RET.
      + left.
        split; ss.
        unfold check_send_hist.
        destruct (Nat.ltb_spec tid_d num_tasks).
        2: { nia. }
        unfold check_send_hist_read.
        rewrite SH_N. ss.
      + eapply mem_consts_unch_diffblk; eauto.
        { instantiate (1:= b_sh).
          eapply Mem.store_unchanged_on; eauto. }
        i. eapply global_addresses_distinct' with (id:= _send_hist); eauto.
        ii. subst. ss. des; ss.
      + ii. ss.
        rewrite CHK_W. clarify.
      + r. i. ss. clarify.
        eapply Mem.store_unchanged_on; eauto.

    - (* multicast *)
      ss.
      fw.
      { econs.
        - eval_comput.
          rewrite FSYMB_NT, FSYMB_NMC.
          cbn.
          erewrite mem_consts_num_tasks; eauto.
          erewrite mem_consts_num_mcasts; eauto.
          s.
          repr_tac1.

          rewrite <- Nat2Z.inj_add.
          pose proof range_valid_dest_ids.
          fold num_tasks num_mcasts in *.
          repr_tac1.
          rewrite <- Nat2Z_inj_ltb.
          unfold Val.of_bool. reflexivity.
        - s. instantiate (1:= tid_d <? num_tasks + num_mcasts).
          desf.
      }

      destruct (Nat.ltb_spec tid_d (num_tasks + num_mcasts))
        as [LT2 | GE2].
      2: {
        fw. fw.
        { econs.
          - eval_comput. ss.
          - eval_comput. ss.
          - econs.
        }
        eapply (sim_itree_red_idx prog) with (idx_small:= idx_r).
        { nia. }
        rewrite call_cont_is_call_cont by ss.
        eapply SIM_RET; eauto.
        - right. split; ss.
          unfold check_send_hist.
          destruct (Nat.ltb_spec tid_d num_tasks); ss.
          2: { nia. }
          unfold check_send_hist_read.
          rewrite nth_error_None2.
          2: { erewrite mem_sh_blk_length; eauto. }
          ss.
        - ii. ss. des. clarify.
        - r. i. apply Mem.unchanged_on_refl.
      }

      hexploit (in_gvar_ilist _MCAST_MEMBER); [sIn|].
      intros (b_mcm & FSYMB_MCM & _). des.

      pose (midx := tid_d - num_tasks).
      assert (SINT_MIDX: IntRange.sint midx).
      { range_stac. }

      fw. fw.
      { econs.
        eval_comput.
        rewrite FSYMB_MCM, FSYMB_NT. cbn.
        rewrite Ptrofs.unsigned_zero.
        erewrite mem_consts_num_tasks by eauto.

        rewrite Z.max_r by nia.
        rewrite Z.mul_1_l.

        pose proof range_max_num_tasks.
        repr_tac.
        rewrite Ptrofs.add_zero_l.
        rewrite <- Nat2Z.inj_sub by nia.
        fold midx.
        rewrite <- Nat2Z.inj_mul.
        reflexivity.
      }
      upd_lenv.
      fw. fw. fw. fw.
      { econs. eval_comput. ss. }
      upd_lenv.
      fw.

      assert (exists (mip_bs: _)(mbrs: list Tid),
                 <<MCASTS_N: nth_error mcasts midx = Some (mip_bs, mbrs)>>).
      { hexploit (nth_error_Some2 _ mcasts midx).
        { subst midx.
          rewrite <- num_mcasts_eq. nia. }
        intros [[] ?].
        esplits; eauto. }
      des.

      assert (RANGE_MBRS:
                forall j (RANGE_J: j <= num_tasks),
                  (Z.of_nat (max_num_tasks * midx + j) <= Ptrofs.max_unsigned)%Z).
      { i.
        cut (Z.of_nat (max_num_tasks * (midx + 1))
             <= Ptrofs.max_unsigned)%Z.
        { pose proof num_tasks_bound.
          fold num_tasks in *. nia. }

        assert (midx + 1 <= length mcasts).
        { apply nth_error_Some1' in MCASTS_N. nia. }
        cut (Z.of_nat max_num_tasks <= Byte.max_signed /\
             Z.of_nat (length mcasts) <= Byte.max_signed)%Z.
        { i. des.
          transitivity (Byte.max_signed * Byte.max_signed)%Z.
          { nia. }
          apply Z.lt_le_incl. ss.
        }

        split.
        - pose proof range_max_num_tasks as RANGE_MNT.
          range_stac.
        - pose proof range_num_mcasts as RANGE_NMC.
          rewrite <- num_mcasts_eq.
          range_stac.
      }

      eapply simple_for_loop
        with (idx_each:= 10) (idx0:= idx_r + 3)
             (i_max := num_tasks)
             (loop_inv := ch_sh_linv itr m0 sh b_sh b_mcm
                                     tid_d midx mbrs).
      { econs; eauto.
        { ss. }
        i. nia. }
      (* { rewrite LENV_EQUIV. ss. } *)
      { ss. }
      { nia. }
      { (* loop body *)
        clear le LENV_EQUIV.
        i. inv LINV.

        assert (PTR_RANGE_I: (0 <= Z.of_nat i <= Ptrofs.max_unsigned)%Z).
        { range_stac. }

        assert (SINTZ_RANGE_S_I: IntRange.sint (S i)).
        { range_stac. }

        fw. fw. fw.
        { econs.
          - eval_comput.
            rewrite FSYMB_NT. cbn.
            rewrite Ptrofs.unsigned_zero.
            erewrite mem_consts_num_tasks; eauto.
          - s. repr_tac.
            rewrite <- Nat2Z_inj_ltb.
            instantiate (1:= true).
            destruct (Nat.ltb_spec i num_tasks) as [LT1|GE1]; ss.
            exfalso. nia.
        }
        ss.
        fw. fw.
        { econs.
          - eval_comput.
            repr_tac1.
            repr_tac1.
            rewrite Z.mul_1_l.

            hexploit (RANGE_MBRS 0).
            { nia. }
            rewrite plus_0_r. i.

            repr_tac1.
            rewrite <- Nat2Z.inj_add.

            rewrite Ptrofs.unsigned_repr.
            2: {
              clear - RANGE_MBRS RANGE_I.
              split; [nia|].
              eapply RANGE_MBRS. nia.
            }
            erewrite mem_consts_mcast_member; eauto.
            (* nia. *)
          - instantiate (1:= existsb (Nat.eqb i) mbrs).
            desf.
        }

        destruct (existsb (Nat.eqb i) mbrs) eqn: IS_I_MBR.
        2: {
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
          eapply (sim_itree_red_idx prog) with (idx_small := idx1 - 10).
          { nia. }

          eapply SIM_NEXT.
          (* - rewrite LENV_EQUIV. ss. *)
          econs; eauto.
          i.
          assert (tid' < i \/ tid' = i) by nia.
          des.
          { eauto. }
          subst tid'.

          exfalso.
          apply existsb_false_iff in IS_I_MBR.
          rewrite Forall_forall in IS_I_MBR.
          hexploit IS_I_MBR; eauto.
          rewrite Nat.eqb_refl. ss.
        }

        (* [tid = i] is a member *)
        hexploit (load_send_hist i); eauto.
        (* { nia. } *)
        intros (sh_i & SH_I & LOAD_SH_I). des.
        fw.
        { econs.
          - eval_comput.
            rewrite FSYMB_SH. cbn.
            repr_tac.
            rewrite Ptrofs.add_zero_l.
            rewrite Z.mul_1_l.
            rewrite Ptrofs.unsigned_repr by ss.
            rewrite LOAD_SH_I.
            instantiate (1:= if sh_i then Vtrue else Vfalse).
            destruct sh_i; ss.
          - ss. instantiate (1:= sh_i).
            desf.
        }

        destruct sh_i.
        - (* not available *)
          fw.
          { eapply step_return_1; ss.
            - eval_comput. ss.
            - ss.
          }
          ss.
          rewrite call_cont_is_call_cont by ss.
          eapply (sim_itree_red_idx prog) with (idx_small:= idx_r).
          { nia. }
          eapply SIM_RET; ss.
          + right.
            splits; eauto.
            unfold check_send_hist.
            destruct (Nat.ltb_spec tid_d num_tasks); ss.
            { exfalso. nia. }
            fold midx.
            rewrite MCASTS_N.

            cut (andb_all (map (check_send_hist_read sh) mbrs) = false).
            { intro R. rewrite R. ss. }

            apply andb_all_false_iff.
            apply in_map_iff.
            exists i. split.
            * unfold check_send_hist_read.
              desf.
            * apply existsb_exists in IS_I_MBR. des.
              hexploit beq_nat_true; eauto. i. subst. ss.
          + ii. ss. clarify.
          + ii. apply Mem.unchanged_on_refl.

        - (* i available *)
          fw.
          { econs. eauto. }
          fw.
          { econs. eval_comput.
            repr_tac.
            replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by nia.
            reflexivity.
          }
          upd_lenv.
          fw.
          eapply (sim_itree_red_idx prog) with (idx_small:= idx1 - 10).
          { nia. }

          eapply SIM_NEXT; ss.
          (* + rewrite LENV_EQUIV. ss. *)
          econs; eauto.
          i.
          assert (tid' < i \/ tid' = i) by nia.
          des.
          { eauto. }
          subst i. ss.
      }

      (* after loop *)
      clear le LENV_EQUIV.
      i. inv LINV_END.
      clear SINT_RANGE_I.
      rename le_e into le.
      rename CHECKED_BEFORE_I into SH_CHECKED.

      eapply (sim_itree_red_idx prog) with
          (idx_small:= num_tasks * 20 + 19 + idx_r).
      { nia. }

      fw. fw. fw.
      { econs.
        - eval_comput.
          rewrite FSYMB_NT. cbn.
          rewrite Ptrofs.unsigned_zero.
          erewrite mem_consts_num_tasks; eauto.
        - s. instantiate (1:= false).
          repr_tac.
          rewrite Z.ltb_irrefl. ss.
      }
      ss.
      fw. fw. fw. fw. fw. fw.
      { econs. eval_comput. ss. }
      upd_lenv.
      fw.

      eapply simple_for_loop
        with (idx_each:= 15) (idx0:= 0)
             (i_max := num_tasks)
             (loop_inv := ch_sh_w_linv itr m0 sh b_sh b_mcm
                                       tid_d midx mbrs).
      { econs; eauto.
        { instantiate (1:= sh).
          instantiate (1:= []). ss. }
        { r. apply Mem.unchanged_on_refl. }
        { range_stac. }
        { ss. }
        { ss. }
      }
      (* { rewrite LENV_EQUIV. ss. } *)
      { ss. }
      { nia. }
      { (* body *)
        clear le LENV_EQUIV.
        clear MEM_CONSTS MEM_SH_BLK.
        i. inv LINV.
        remember (length sh1) as i eqn: I_EQ.
        guardH I_EQ.

        destruct sh2 as [| h_sh2 t_sh2].
        { exfalso.
          hexploit mem_sh_blk_length; eauto.
          rewrite app_nil_r.
          unfold check_send_hist_write.
          rewrite imap_length.
          rewrite <- I_EQ. nia.
        }

        assert (PTR_RANGE_I: (0 <= Z.of_nat i <= Ptrofs.max_unsigned)%Z).
        { range_stac. }
        assert (SINTZ_RANGE_S_I: IntRange.sint (S i)).
        { range_stac. }

        fw. fw. fw.
        { econs.
          - eval_comput.
            rewrite FSYMB_NT. cbn.
            rewrite Ptrofs.unsigned_zero.
            erewrite mem_consts_num_tasks; eauto.
          - s. repr_tac.
            instantiate (1:= true).
            destruct (Z.ltb_spec (Z.of_nat i)
                                 (Z.of_nat num_tasks)) as [LT1|GE1]; ss.
            apply Nat2Z.inj_le in GE1.
            exfalso. nia.
        }
        ss.
        fw. fw.
        { econs.
          - eval_comput.
            repr_tac1. repr_tac1.
            rewrite Z.mul_1_l.

            hexploit (RANGE_MBRS 0).
            { nia. }
            rewrite plus_0_r. i.
            repr_tac1.

            rewrite <- Nat2Z.inj_add.
            rewrite Ptrofs.unsigned_repr.
            2: {
              clear - RANGE_MBRS RANGE_I.
              split; [nia|].
              eapply RANGE_MBRS. nia.
            }
            erewrite mem_consts_mcast_member; eauto.
            (* nia. *)
          - instantiate (1:= existsb (Nat.eqb i) mbrs).
            desf.
        }

        destruct (existsb (Nat.eqb i) mbrs) eqn: IS_I_MBR.
        2: {
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
          eapply (sim_itree_red_idx prog) with (idx_small := idx1 - 15).
          { nia. }

          eapply SIM_NEXT.
          (* - rewrite LENV_EQUIV. ss. *)
          assert (CHW': check_send_hist_write (sh1 ++ [h_sh2]) mbrs =
                        check_send_hist_write sh1 mbrs ++ [h_sh2]).
          { unfold check_send_hist_write.

            rewrite imap_app. ss.
            rewrite <- I_EQ.
            rewrite IS_I_MBR. ss.
          }
          econs; try apply CHW'; eauto.
          + rewrite <- app_assoc. ss. eauto.
          + rewrite <- app_assoc. ss.
          + rewrite app_length. ss.
            rewrite <- I_EQ. nia.
        }

        (* [tid = i] is a member *)
        hexploit (store_send_hist true Vtrue i); eauto.
        { unfold check_send_hist_write.
          rewrite imap_length. ss. }
        i. des.
        fw.
        { econs.
          - eval_comput.
            rewrite FSYMB_SH. cbn.
            repr_tac.
            rewrite Ptrofs.add_zero_l.
            rewrite Z.mul_1_l.
            reflexivity.
          - eval_comput. ss.
          - ss.
          - eval_comput. cbn.
            repr_tac. eauto.
        }

        fw.
        { econs. eauto. }
        fw.
        { econs. eval_comput.
          repr_tac.
          replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by nia.
          ss.
        }
        upd_lenv.
        fw.

        eapply (sim_itree_red_idx prog) with (idx_small:= idx1 - 15).
        { nia. }
        eapply SIM_NEXT.
        (* - rewrite LENV_EQUIV. ss. *)
        assert (CHW': check_send_hist_write (sh1 ++ [h_sh2]) mbrs =
                      check_send_hist_write sh1 mbrs ++ [true]).
        { unfold check_send_hist_write.
          rewrite imap_app. ss.
          rewrite <- I_EQ.
          rewrite IS_I_MBR. ss. }
        assert (CH_BLK': mem_changed_block b_sh m1 m').
        { eapply Mem.store_unchanged_on; eauto. }

        econs; try apply CHW'; eauto.
        + eapply mem_consts_unch_diffblk; eauto.
          i. eapply global_addresses_distinct' with (id:= _send_hist); eauto.
          ii. subst. ss. des; ss.
        + instantiate (1:= t_sh2).
          rewrite <- app_assoc. ss.
        + eapply Mem.unchanged_on_trans; eauto.
        + rewrite <- app_assoc. ss.
        + rewrite app_length. ss.
          rewrite <- I_EQ. nia.
      }

      (* after *)
      clear dependent le.
      clear MEM_CONSTS MEM_SH_BLK.
      i. inv LINV_END.

      destruct sh2.
      2: {
        exfalso.
        hexploit mem_sh_blk_length; eauto.
        unfold check_send_hist_write.
        rewrite app_length, imap_length. ss.
        nia.
      }
      rewrite app_nil_r in *.

      eapply (sim_itree_red_idx prog) with
          (idx_small:= 10 + idx_r).
      { nia. }

      fw. fw. fw.
      { econs.
        - eval_comput. rewrite FSYMB_NT. cbn.
          rewrite Ptrofs.unsigned_zero.
          erewrite mem_consts_num_tasks by eauto.
          repr_tac.
          rewrite Z.ltb_irrefl. reflexivity.
        - ss.
      }

      rewrite Int.eq_true. ss.
      fw. fw. fw. fw.
      { econs.
        - eval_comput. ss.
        - eval_comput. ss.
        - econs.
      }

      ss. rewrite call_cont_is_call_cont by ss.
      eapply (sim_itree_red_idx prog) with (idx_small:= idx_r).
      { nia. }
      eapply SIM_RET; eauto.
      + left. split; ss.
        unfold check_send_hist.
        destruct (Nat.ltb_spec tid_d num_tasks); ss.
        { exfalso. nia. }
        fold midx.
        rewrite MCASTS_N.

        replace (andb_all (map (check_send_hist_read sh1) mbrs)) with true.
        2: { symmetry.
             apply andb_all_true_iff.
             i. rewrite in_map_iff in IN.
             unfold check_send_hist_read in IN.
             des.

             assert (x < num_tasks).
             { hexploit mcast_members_valid; eauto.
               rewrite Forall_nth.
               intro AUX. specialize (AUX midx).
               rewrite MCASTS_N in AUX. ss.
               rewrite Forall_forall in AUX.
               fold num_tasks in AUX.
               eapply AUX; eauto. }

             hexploit (SH_CHECKED x).
             { eauto. }
             { eauto. }
             intro NTH_X.
             rewrite NTH_X in IN.
             destruct b; ss.
        }
        reflexivity.
      + ii. ss. clarify.
      + ii. ss. clarify.
  Qed.

  Local Opaque idx_ch_sh idx_msg_copy.

  Definition idx_psend: nat := 5 + (idx_ch_sh + idx_msg_copy + 20).

  (* Lemma byte_max_signed_lt_int *)
  (*   : (Byte.max_signed < Int.max_signed)%Z. *)
  (* Proof. ss. Qed. *)

  Lemma sim_pals_send
        idx_r k kp m0 txs sh
        tid_r b_buf ofs_buf bs
        b_sbuf b_sh sytm bs_old
        (CALL_CONT: is_call_cont kp)
        (RANGE_TXS: IntRange.sint txs)
        (RANGE_TID_R: tid_r < num_tasks + num_mcasts)
        (RANGE_SYTM: IntRange.uint64 sytm)
        (RANGE_SYTM2: IntRange.uint64 (sytm + period))
        (FSYMB_SBUF: Genv.find_symbol ge _send_buf = Some b_sbuf)
        (FSYMB_SH: Genv.find_symbol ge _send_hist = Some b_sh)
        (BLOCK_NEQ_SBUF: b_buf <> b_sbuf)
        (BLOCK_NEQ_SH: b_buf <> b_sh)
        (OFS_BUF1: (0 <= ofs_buf <= Ptrofs.max_unsigned)%Z)
        (OFS_BUF2: (0 <= ofs_buf + Z.of_nat msg_size <= Ptrofs.max_unsigned)%Z)
        (LBS_BUF: Mem.loadbytes m0 b_buf ofs_buf
                                (Z.of_nat msg_size) =
                  Some (inj_bytes bs))
        (MEM_CONSTS: mem_consts ge m0 tid)
        (MEM_SH: mem_sh ge m0 sh)
        (MEM_TXS: mem_txs ge m0 txs)
        (MEM_SBUF: mem_sbuf ge m0 (sytm + period) tid bs_old)
        (SIM_RET:
           forall m' sh' bs'
             (MEM_CONSTS: mem_consts ge m' tid)
             (MEM_SH: mem_sh ge m' sh')
             (MEM_TXS: mem_txs ge m' txs)
             (MEM_SBUF: mem_sbuf ge m' (sytm + period) tid bs')
             (MEM_UNCH: mem_unchanged_except
                          (blocks_of ge [_send_buf; _send_hist])
                          m0 m')
           ,
             paco3 (_sim_itree prog) r idx_r
                   (k (sh', tt))
                   (Clight.Returnstate Vundef kp m'))

    : paco3 (_sim_itree prog) r (idx_psend + idx_r)
            (r <- MWITree.bsendE_itree
                   tid txs sytm sh
                   tid_r bs ;; k r)
            (Clight.Callstate
               (Internal (f_pals_send (Z.of_nat msg_size_k)
                                      (Z.of_nat max_num_tasks)
                                      (Z.of_nat max_num_mcasts)))
               [Vint (IntNat.of_nat tid_r);
               Vptr b_buf (Ptrofs.repr ofs_buf)] kp m0).
  Proof.
    start_func.
    { ss. econs 1. }
    unfold idx_psend.
    fw. fw.

    assert (INT_RANGE_TID_R: IntRange.sint8 tid_r).
    { pose proof range_valid_dest_ids as VALID.
      pose proof num_tasks_bound as NT_B.
      pose proof num_mcasts_bound as NMC_B.
      unfold num_tasks, num_mcasts in *.
      range_stac. }

    (* check_send_hist(tid) *)
    fw.
    { hexploit (in_gfun_ilist _check_send_hist); [sIn|].
      i. des.
      econs; ss.
      - eval_comput.
        rewrite FDEF_SYMB. cbn. ss.
      - eval_comput.
        unfold IntNat.of_nat.
        rewrite sign_ext_byte_range by ss.
        reflexivity.
      - eauto.
      - ss.
    }

    eapply (sim_itree_red_idx prog) with
        (idx_small:= idx_ch_sh + (idx_msg_copy + 20 + idx_r)).
    { nia. }

    eapply sim_check_send_hist; eauto.
    { ss. }
    clear MEM_CONSTS MEM_SH. i.

    eapply mem_txs_unch_diffblk in MEM_TXS; eauto; cycle 1.
    { r. apply MEM_UNCH. eauto. }
    { eapply global_addresses_distinct'; eauto. ss. }
    eapply mem_sbuf_unch_diffblk in MEM_SBUF; eauto; cycle 1.
    { r. apply MEM_UNCH. eauto. }
    { eapply global_addresses_distinct'; eauto. ss. }
    eapply Mem.loadbytes_unchanged_on in LBS_BUF; eauto.

    des.
    2: {
      subst.
      fw. upd_lenv.
      fw. fw.
      { econs.
        - eval_comput. ss.
        - simpl. ss.
      }
      fw.
      unfold MWITree.bsendE_itree.
      rewrite CHECK_SEND_HIST.
      simpl_itree_goal.

      eapply (sim_itree_red_idx prog) with (idx_small:= idx_r).
      { nia. }
      eapply SIM_RET; eauto.
      eapply Mem.unchanged_on_implies.
      { apply MEM_UNCH; eauto. }
      intros b ofs C VB. ss.
      ii. subst.
      apply C. r.
      esplits; eauto. ss. eauto.
    }

    unfold MWITree.bsendE_itree.
    rewrite CHECK_SEND_HIST.
    subst.

    fw. upd_lenv.
    fw. fw.
    { econs.
      - eval_comput. ss.
      - simpl. ss.
    }
    rewrite Int.eq_false by ss. ss.
    fw.

    hexploit (in_gvar_ids _IP_ADDR); [sIn|].
    intros [b_ips FSYMB_IPS].
    fw.
    { econs. eval_comput.
      rewrite FSYMB_IPS. cbn.
      repr_tac.
      rewrite Ptrofs.add_zero_l.

      repr_tac.
      reflexivity.
    }
    upd_lenv.

    fw. fw. fw.
    { hexploit (in_gfun_ilist _msg_copy); [sIn|].
      i. des.
      econs; ss.
      - eval_comput. ss.
        rewrite FDEF_SYMB. ss.
      - eval_comput. ss.
        rewrite FSYMB_SBUF. simpl.
        unfold Coqlib.align, align_attr. simpl.
        rewrite Ptrofs.add_zero_l. reflexivity.
      - eauto.
      - ss.
    }

    eapply (sim_itree_red_idx prog) with
        (idx_small:= (idx_msg_copy + (10 + idx_r))).
    { nia. }
    eapply sim_msg_copy; eauto; ss.
    { unfold blocks_of.
      ii. des.
      hexploit (global_addresses_distinct'
                  ge _send_buf b_sbuf id); eauto.
      ii. subst.
      ss. des; ss. }
    { replace (9 + Z.of_nat msg_size)%Z with (Z.of_nat pld_size).
      2: { unfold pld_size. nia. }
      clear. pose proof range_pld_size.
      range_stac. }
    { specialize (MEM_SBUF _ FSYMB_SBUF).
      ii. eapply mem_sbuf_writable; eauto.
      unfold pld_size. nia. }

    rename m' into m. clear MEM_CONSTS.
    i. guardH MEM_STORE.

    assert(MEM_UNCH_STORE: mem_changed_block b_sbuf m m').
    { desH MEM_STORE.
      - clarify. r. apply Mem.unchanged_on_refl.
      - eapply Mem.unchanged_on_implies.
        { eapply storebytes_unchanged_on'; eauto. }
        unfold mem_range. ii. des. ss.
    }

    assert (LEN_BS: length (inj_bytes bs) = msg_size).
    { eapply Mem.loadbytes_length in LBS_BUF.
      rewrite Nat2Z.id in LBS_BUF. ss. }
    eapply mem_txs_unch_diffblk in MEM_TXS; eauto.
    2: { eapply global_addresses_distinct'; eauto. ss. }
    eapply mem_sh_unch_diffblk in MEM_SH; eauto.
    2: { eapply global_addresses_distinct'; eauto. ss. }
    rename MEM_SBUF into MEM_SBUF_P.

    assert (MEM_SBUF: mem_sbuf ge m' (sytm + period) tid bs).
    { desH MEM_STORE.
      { clarify.
        rewrite MEM_STORE in *.
        assert (bs = []).
        { destruct bs; ss. }
        subst bs.
        assert (bs_old = []).
        { hexploit mem_sbuf_content; eauto.
          intro LB.
          apply Mem.loadbytes_length in LB.
          rewrite MEM_STORE in LB. ss.
          destruct bs_old; ss. }
        subst bs_old. ss.
      }
      r in MEM_SBUF_P.
      hexploit MEM_SBUF_P; eauto.
      inversion 1.
      r. i. ss. clarify.
      hexploit storebytes_unchanged_on'; eauto. intro ST_UNCH.

      econs.
      - eapply Mem.loadbytes_unchanged_on; eauto.
        unfold mem_range. ii. des; ss. nia.
      - eapply Mem.load_unchanged_on; eauto.
        unfold mem_range. ii. des; ss. nia.
      - rewrite <- LEN_BS.
        eapply Mem.loadbytes_storebytes_same; eauto.
      - ii. eapply Mem.perm_storebytes_1; eauto.
    }
    assert (MEM_UNCH': mem_unchanged_except
                         (blocks_of ge [_send_buf; _send_hist])
                         m0 m').
    { r.
      eapply Mem.unchanged_on_trans with (m2 := m).
      - eapply Mem.unchanged_on_implies; eauto.
        intros b ofs BLKS_OF VB. ii. ss. subst.
        apply BLKS_OF. r.
        esplits; eauto. ss. eauto.
      - eapply Mem.unchanged_on_implies; eauto.
        intros b ofs BLKS_OF VB. ii. ss. subst.
        apply BLKS_OF. r.
        esplits; eauto. ss. eauto.
    }
    clear MEM_SBUF_P MEM_UNCH_STORE MEM_STORE.
    clear m MEM_UNCH LBS_BUF.
    rename MEM_UNCH' into MEM_UNCH.

    fw. fw. fw.
    { hexploit (in_gfun_ilist _pals_sendto); [sIn|].
      i. nbdes.
      hexploit (in_gvar_ids _txs); [sIn|].
      intros [b_txs FSYMB_TXS].
      hexploit (in_gvar_ids _PORT); [sIn|].
      intros [b_pn FSYMB_PN].
      hexploit (in_gvar_ids _MSG_SIZE); [sIn|].
      intros [b_msz FSYMB_MSZ].

      econs; ss.
      - eval_comput. rewrite FDEF_SYMB. ss.
      - eval_comput.
        rewrite FSYMB_TXS. rewrite FSYMB_PN.
        rewrite FSYMB_SBUF. rewrite FSYMB_MSZ. cbn.
        rewrite Ptrofs.unsigned_zero.

        erewrite mem_skt_id; eauto.
        erewrite mem_consts_port; eauto.
        erewrite mem_consts_msg_size; eauto.
        ss.
      - eauto.
      - ss.
    }

    hexploit (ip_in_mem_exists ge tid tid_r); eauto.
    intro IP_DEST. des.

    simpl_itree_goal.
    pfold. econs 3.
    { ss. econs; ss.
      econs 1; eauto.

      eapply CProgOSEC_Sendto with
          (sid:=txs) (pn_dest:=port) (sz_buf:=pld_size);
        eauto; ss.
      - apply range_pld_size.
      - eapply range_port.
      - unfold pld_size.
        pose proof range_msg_size.
        repr_tac1.
        rewrite Nat2Z.inj_add. ss.
      - rewrite Ptrofs.unsigned_zero.
        eapply mem_sbuf_loadbytes; eauto.
    }
    { econs 1. }
    { simpl_itree_goal. ss.
      unfold serialize_msg. ss.

      replace (resize_bytes msg_size bs) with bs.
      2: {
        unfold resize_bytes.
        rewrite <- LEN_BS.
        unfold inj_bytes. rewrite map_length.
        rewrite firstn_all.
        rewrite Nat.sub_diag. ss.
        rewrite app_nil_r. ss.
      }

      replace (tid2ip tid_r) with ip_dest.
      2: { unfold tid2ip.
           unfold dest_id_ip in *.
           erewrite nth_error_nth; eauto. }
      ss.
    }
    rename m' into m.
    i. ss.
    (* inv POSTCOND. *) inv RET.
    existT_elim. clarify.
    inv CPROG_AFTER_EVENT; ss.
    symmetry in EVENT.
    inv EVENT. existT_elim. clarify. ss.
    unf_resum. subst.
    inv OS_ESTEP. existT_elim. subst.

    exists (idx_r + 2).
    left.
    fw. fw.
    rewrite plus_0_r.
    simpl_itree_goal.

    eapply SIM_RET; eauto.
  Qed.


  Lemma inbox_insert_msg_fail
        m b ofs tid_s bs inb
        (MEM_INB : Mem_inbox m b ofs inb)
        (TID_TOO_BIG: (num_tasks <= tid_s)%nat)
    : MWITree.insert_msg inb tid_s bs = inb.
  Proof.
    assert (LEN_INB: length inb = num_tasks).
    { apply MEM_INB. }
    rewrite <- LEN_INB in TID_TOO_BIG.
    clear m b ofs LEN_INB MEM_INB.

    depgen tid_s.
    induction inb as [| h t IH]; i; ss.
    destruct tid_s as [| tid_s]; ss.
    { nia. }
    rewrite IH; ss. nia.
  Qed.

  Lemma inbox_insert_msg_succ
        inb1 inb2 ment
        tid_s bs inb
        (INB: inb = inb1 ++ [ment] ++ inb2)
        (LEN_INB1: length inb1 = tid_s)
    : MWITree.insert_msg inb tid_s bs =
      inb1 ++ [Some bs] ++ inb2.
  Proof.
    depgen inb. depgen tid_s.
    induction inb1 as [| ent_h inb1 IH]; i; ss.
    { subst. ss. }
    destruct inb as [| ent_h' inb]; ss.
    clarify.
    rewrite IH; eauto.
  Qed.


  (* Lemma inbox_ofs_valid_ptrofs *)
  (*   : ((Z.of_nat max_msg_size + 1) * (Z.of_nat max_num_tasks) *)
  (*      < Ptrofs.max_unsigned)%Z. *)
  (* Proof. *)
  (*   cut ((Z.of_nat max_msg_size + 1 < 2 ^ 16) /\ *)
  (*        (Z.of_nat max_num_tasks < 2 ^ 8))%Z. *)
  (*   { i. des. *)
  (*     transitivity (2 ^ 16 * 2 ^ 8)%Z. *)
  (*     - nia. *)
  (*     - rewrite <- Z.pow_add_r by nia. *)
  (*       replace Ptrofs.max_unsigned with (Z.pow 2 64 - 1)%Z by ss. *)
  (*       nia. *)
  (*   } *)

  (*   split. *)
  (*   - pose proof packet_length_bound as PKTLEN. *)
  (*     apply Nat2Z.inj_lt in PKTLEN. *)

  (*     eapply Z.lt_le_trans. *)
  (*     { unfold max_msg_size. *)
  (*       etransitivity. *)
  (*       2: { apply PKTLEN. } *)
  (*       nia. } *)
  (*     { unfold NWSysModel.Packet.maxlen. *)
  (*       rewrite Z2Nat.id by nia. *)
  (*       nia. } *)
  (*   - pose proof range_max_num_tasks as MNT. *)
  (*     apply IntRange.sint8_sintz8 in MNT. *)
  (*     r in MNT. *)
  (*     eapply Z.le_lt_trans. *)
  (*     { apply MNT. } *)
  (*     ss. *)
  (* Qed. *)

  Definition idx_ins_msg: nat := idx_msg_copy + 20.

  Lemma sim_insert_msg
        m0 k idx_r itr
        inb tid_s bs
        b_mst ofs_inb
        b_buf ofs_buf
        (CALL_CONT: is_call_cont k)
        (RANGE_TID_S: IntRange.sintz (Z.of_nat tid_s))
        (FSYMB_MST: Genv.find_symbol ge _mstore = Some b_mst)
        (BLK_DIFF: b_mst <> b_buf)
        (OFS_SRC: (0 <= ofs_buf <= Ptrofs.max_unsigned)%Z)
        (OFS_SRC2: (0 <= ofs_buf + Z.of_nat msg_size
                    <= Ptrofs.max_unsigned)%Z)
        (OFS_DST1: (0 <= ofs_inb)%Z)
        (OFS_DST2: (ofs_inb + inb_sz <= Ptrofs.max_unsigned)%Z)
        (BUF_LOAD: Mem.loadbytes m0 b_buf ofs_buf (Z.of_nat msg_size) = Some (inj_bytes bs))
        (MEM_INB: Mem_inbox m0 b_mst ofs_inb inb)
        (MEM_CONSTS: mem_consts ge m0 tid)
        (* (INB_EQV: inbox_equiv inb_s inb_t) *)
        (SIM_RET:
           forall m' inb'
             (MEM_CH_MST: mem_unchanged_except
                            (mem_range b_mst ofs_inb (ofs_inb + inb_sz))
                            m0 m')
             (MEM_INB: Mem_inbox m' b_mst ofs_inb inb')
             (MEM_CONSTS: mem_consts ge m' tid)
             (INB_INSERT: MWITree.insert_msg inb tid_s bs = inb')
           ,
             paco3 (_sim_itree (prog_of_clight cprog))
                   r idx_r itr
                   (Clight.Returnstate Vundef k m'))
    : paco3 (_sim_itree prog) r (idx_ins_msg + idx_r)
            itr
            (Clight.Callstate
               (Internal (f_insert_msg (Z.of_nat msg_size_k)))
               [Vptr b_mst (Ptrofs.repr ofs_inb);
               Vint (IntNat.of_nat tid_s);
               Vptr b_buf (Ptrofs.repr ofs_buf)] k m0).
  Proof.
    (* pre_start_func *)
    assert (ALLOC: alloc_variables
                     ge empty_env m0
                     (fn_vars (f_insert_msg (Z.of_nat msg_size_k)))
                     empty_env m0).
    { ss. econs. }
    guardH OFS_SRC.

    (* assert (INB_SZ_NNEG: (0 <= inb_sz)%Z). *)
    (* { apply range_inb_sz_precise. } *)
    assert (RANGE_OFS_INB:
              (0 <= ofs_inb <= Ptrofs.max_unsigned)%Z).
    { range_stac. }
    assert (RANGE_OFS_INB_SZ:
              (0 <= ofs_inb + inb_sz <= Ptrofs.max_unsigned)%Z).
    { nia. }
    clear OFS_DST1 OFS_DST2.
    guardH RANGE_OFS_INB. guardH RANGE_OFS_INB_SZ.

    start_func. ss.
    unfold idx_ins_msg.
    fw. fw. fw.
    { econs.
      - eval_comput.
        repr_tac.
        reflexivity.
      - simpl. rewrite bool_val_of_bool.
        reflexivity.
    }

    destruct (Z.ltb_spec (Z.of_nat tid_s) 0)
      as [?|TID_OK]; ss.
    { (* id neg *)
      exfalso. nia. }

    fw.
    { econs.
      hexploit (in_gvar_ids _NUM_TASKS); [sIn|]. ss.
      destruct 1 as [b_nt FSYMB_NT].

      eval_comput.
      rewrite FSYMB_NT. cbn.
      erewrite mem_consts_num_tasks; eauto.

      pose proof range_num_tasks.
      repr_tac.
      rewrite <- Nat2Z_inj_ltb.

      instantiate (1:= Vint (if (tid_s <? num_tasks)%nat
                             then Int.one else Int.zero)).

      destruct (Nat.ltb_spec tid_s num_tasks) as [LT | GE]; ss.
    }

    upd_lenv.
    fw. fw.
    { econs.
      - eval_comput. ss.
      - instantiate (1:= (tid_s <? num_tasks)).
        desf.
    }

    destruct (Nat.ltb_spec tid_s num_tasks) as [LT|GE].
    2: {
      fw.
      eapply (sim_itree_red_idx prog)
        with (idx_small:= idx_r).
      { nia. }
      eapply SIM_RET; eauto.
      - eapply Mem.unchanged_on_refl.
      - eapply inbox_insert_msg_fail; eauto.
    }

    assert (RANGE_PTR: (0 <= ofs_inb +
                            Z.of_nat (mentry_nsz * tid_s + mentry_nsz)
                        <= Ptrofs.max_unsigned)%Z).
    { (* pose proof range_mentry_sz_precise. *)
      hexploit (within_inb_nsz2 tid_s mentry_nsz); try nia.
      i. unguard.
      nia. }
    guardH RANGE_PTR.

    fw.
    (* assign *)
    rr in MEM_INB. des.
    assert (ENTRIES_DIV: exists inb1 inb2 omsg,
               <<INB_DIV: inb = inb1 ++ [omsg] ++ inb2>> /\
               <<LEN_INB1: length inb1 = tid_s>> /\
               <<ENTRIES_INB1: iForall (Mem_msg_entry m0 b_mst ofs_inb)
                                       0 inb1>> /\
               <<ENTRY_X: Mem_msg_entry m0 b_mst ofs_inb
                                        tid_s omsg>> /\
               <<ENTRIES_INB2: iForall (Mem_msg_entry m0 b_mst ofs_inb)
                                       (S tid_s) inb2>>).
    { hexploit (nth_error_Some2 _ inb tid_s).
      { nia. }
      i. des. rename NTH_EX into INB_S.
      (* destruct e1 as [rcv cont]. *)

      hexploit nth_error_split; eauto.
      intros (l1 & l2 & INB_EQ & LEN1).

      subst inb.
      clear - MSG_ENTRIES LEN1.
      apply iForall_app_inv in MSG_ENTRIES. des.
      renames IFA1 IFA2 into ENTRIES1 ENTRIES'. ss.
      inv ENTRIES'.
      rewrite Nat.add_0_r in *.
      esplits; eauto.
    }

    des.
    guardH LEN_INB1.

    rr in ENTRY_X. ss.
    assert(MSTORE: exists m',
              Mem.store Mint8signed
                        m0 b_mst (ofs_inb + Z.of_nat (mentry_nsz * tid_s))
                        (Vint (Int.repr 1)) = Some m').
    { hexploit Mem.valid_access_store; eauto.
      2: { inversion 1. esplits; eauto. }
      r. ss. splits.
      2: { solve_divide. }

      ii. apply INBOX_PERM.
      hexploit (within_inb_nsz2 tid_s 1); ss.
      { unfold mentry_nsz. nia. }
      hexploit (within_inb_nsz2 tid_s 0); ss.
      { unfold mentry_nsz. nia. }
      rewrite Nat.add_0_r. i.
      nia.
    }
    des.

    assert (VALID_PTR_MENTRY_SZ: (0 <= mentry_sz <= Ptrofs.max_unsigned)%Z).
    { clear.
      (* pose proof range_mentry_sz_precise. *)
      pose proof range_mentry_nsz.
      range_stac. }
    assert (VALID_PTR_ACCESS:
              (0 <= Z.of_nat (mentry_nsz * tid_s) <= Ptrofs.max_unsigned)%Z).
    { unguard. nia. }

    fw.
    { econs.
      - eval_comput. s.
        unguard.
        repr_tac1.
        repr_tac1.
        repr_tac1.
        rewrite Ptrofs.add_zero.

        rewrite <- Nat2Z.inj_mul.
        reflexivity.

      - eval_comput. ss.
      - simpl.
        eval_comput.
        rewrite sign_ext_byte_range by range_stac.
        reflexivity.
      - simpl.
        eval_comput.
        rewrite Ptrofs.unsigned_repr.
        2: { unguard. nia. }
        eauto.
    }
    fw. fw.
    { hexploit (in_gfun_ilist _msg_copy); [sIn|].
      i. des.
      econs; ss.
      - eval_comput.
        rewrite FDEF_SYMB.
        cbn. reflexivity.
      - eval_comput. s.
        unguard.
        repr_tac.

        replace (ofs_inb + mentry_sz * Z.of_nat tid_s + 1)%Z with
            (ofs_inb + Z.of_nat (mentry_nsz * tid_s + 1))%Z by nia.
        reflexivity.
      - eauto.
      - ss.
    }

    hexploit storebytes_unchanged_on'.
    { apply Mem.store_storebytes. eauto. }
    ss.
    rewrite Int.unsigned_repr by range_stac.
    unfold encode_int. ss.
    rewrite rev_if_be_single. ss.
    rewrite Zlength_correct. ss.
    intro MEM_UNCH.

    eapply mem_consts_unch_diffblk in MEM_CONSTS; eauto; cycle 1.
    { r. eapply Mem.unchanged_on_implies; eauto.
      instantiate (1:= b_mst).
      unfold mem_range. ii. des; ss. }
    { i. eapply global_addresses_distinct'; eauto.
      ii. subst. ss. des; ss. }

    assert (INBOX_PERM' : Mem.range_perm m' b_mst ofs_inb (ofs_inb + inb_sz) Cur Writable).
    { ii. eapply Mem.perm_store_1; eauto. }

    eapply iForall_Mem_msg_entry_unch in ENTRIES_INB1; eauto.
    2: {
      eapply Mem.unchanged_on_implies; eauto.
      unfold mem_range.
      rewrite LEN_INB1.
      intros b ofs [] VB C. des. subst. ss.
      nia.
    }

    eapply iForall_Mem_msg_entry_unch in ENTRIES_INB2; eauto.
    2: {
      eapply Mem.unchanged_on_implies; eauto.
      unfold mem_range.
      intros b ofs [] VB C. des. subst. ss.
      nia.
    }

    eapply (sim_itree_red_idx prog) with
        (idx_small:= idx_msg_copy + (5 + idx_r)).
    { nia. }

    eapply sim_msg_copy; eauto; ss.
    { unfold blocks_of. ii. des. ss.
      eapply (global_addresses_distinct' ge _mstore b_mst id); eauto.
      des; subst; ss. }
    { cut (1 <= mentry_sz)%Z.
      { unguard. nia. }
      unfold mentry_nsz. nia. }
    { clear - RANGE_OFS_INB RANGE_PTR.
      unguard.
      pose proof msg_size_bound'.
      rewrite <- Z.add_assoc.
      rewrite <- Nat2Z.inj_add.

      assert (1 + max_msg_size = mentry_nsz)%nat.
      { unfold mentry_nsz. nia. }
      nia.  }
    { eapply Mem.loadbytes_unchanged_on; eauto.
      unfold mem_range.
      ii. des. congruence. }
    { (* replace (ofs_inb + Z.of_nat (mentry_nsz * tid_s + 1) + Z.of_nat msg_size)%Z with *)
      (*     (ofs_inb + Z.of_nat (mentry_nsz * tid_s + mentry_ensz))%Z. *)
      (* 2: { unfold mentry_ensz. nia. } *)

      ii. eapply Mem.perm_unchanged_on; eauto.
      - unfold mem_range. ss. ii. des. nia.
      - eapply INBOX_PERM.
        split.
        + nia.
        + hexploit (within_inb_nsz2 tid_s mentry_ensz).
          { nia. }
          { eapply range_mentry_ensz. }
          unfold mentry_ensz. nia.
    }

    rename m' into m.
    clear MEM_CONSTS.
    intros m' MEM_CONSTS MSTORE2.
    fw. fw.

    eapply (sim_itree_red_idx prog) with (idx_small:= idx_r).
    { nia. }

    assert (LEN_BS: length (inj_bytes bs) = msg_size).
    { eapply Mem.loadbytes_length in BUF_LOAD.
      rewrite Nat2Z.id in BUF_LOAD. ss. }

    eapply SIM_RET; eauto.
    - pose proof num_tasks_bound.
      fold num_tasks in *.

      des.
      + clarify.
        eapply Mem.unchanged_on_implies; eauto.
        unfold mem_range.
        intros b ofs C VB ?. des. subst.

        assert (ofs = ofs_inb + Z.of_nat (mentry_nsz * tid_s))%Z by nia.
        subst ofs.
        apply C. split; ss.

        split; [nia |].
        hexploit (within_inb_nsz2 tid_s 1); eauto.
        { unfold mentry_nsz. nia. }
        i. nia.

      + eapply Mem.unchanged_on_trans.
        * eapply Mem.unchanged_on_implies; eauto.
          unfold mem_range.
          intros b ofs C VB ?.
          assert (ofs = ofs_inb + Z.of_nat (mentry_nsz * tid_s))%Z by nia.
          subst ofs.
          des. subst.

          apply C. split; ss.

          split; [nia |].
          hexploit (within_inb_nsz2 tid_s 1); eauto.
          { unfold mentry_nsz. nia. }
          i. nia.

        * eapply Mem.unchanged_on_implies; eauto.
          { apply storebytes_unchanged_on'; eauto. }
          unfold mem_range. rewrite Zlength_correct.
          rewrite LEN_BS.

          (* replace (ofs_inb + Z.of_nat (mentry_nsz * tid_s + 1) + Z.of_nat msg_size)%Z with *)
          (*     (ofs_inb + Z.of_nat (mentry_nsz * tid_s + mentry_ensz))%Z. *)
          (* 2: { unfold mentry_nsz, mentry_ensz. nia. } *)

          intros b ofs C VB ?. des. subst.

          apply C. split; ss.
          split; [nia |].
          hexploit (within_inb_nsz2 tid_s mentry_ensz); eauto.
          { apply range_mentry_ensz. }
          unfold mentry_ensz. nia.

    - r.
      assert (MEM_UNCH':
                mem_unchanged_except
                  (mem_range b_mst
                             (ofs_inb + Z.of_nat (mentry_nsz * tid_s + 1))
                             (ofs_inb + Z.of_nat (mentry_nsz * tid_s + mentry_ensz)))
                  m m').
      { des.
        - subst. apply Mem.unchanged_on_refl.
        - (* rewrite pos_of_succ_nat_eq in *. *)
          (* replace (Z.of_nat (S max_msg_size)) with *)
          (*     (Z.of_nat max_msg_size + 1)%Z in * by nia. *)
          eapply Mem.storebytes_unchanged_on; eauto.
          unfold mem_range.
          rewrite LEN_BS.

          intros i RANGE_I C.
          apply C.
          split; ss.
          unfold mentry_ensz. nia.
      }

      split.
      + erewrite (inbox_insert_msg_succ inb1 inb2); eauto.
        eapply iForall_app; eauto.
        { eapply iForall_Mem_msg_entry_unch; eauto.
          des.
          - subst. apply Mem.unchanged_on_refl.
          - eapply Mem.storebytes_unchanged_on; eauto.
            rewrite LEN_BS. rewrite LEN_INB1. ss.
            clear.
            intros i C1 C2. des.
            nia.
        }
        ss. econs.
        2: {
          rewrite LEN_INB1.
          eapply iForall_Mem_msg_entry_unch; eauto.
          des.
          - subst. apply Mem.unchanged_on_refl.
          - (* unfold mentry_sz. *)
            (* rewrite msg_entry_sz_eq. *)
            eapply Mem.storebytes_unchanged_on; eauto.
            rewrite LEN_BS.

            cut (1 + Z.of_nat msg_size <= mentry_sz)%Z.
            { nia. }
            clear.
            unfold mentry_nsz.
            pose proof msg_size_bound'. nia.
        }
        { r. ss.
          rewrite LEN_INB1.
          (* unfold mentry_ensz. *)
          replace mentry_esz with (1 + Z.of_nat msg_size)%Z.
          2: { unfold mentry_ensz. nia. }

          erewrite Mem.loadbytes_concat with (bytes1 := [Byte Byte.one]); ss.
          - (* unfold mentry_sz. *)
            (* rewrite msg_entry_sz_eq. *)
            eapply Mem.loadbytes_unchanged_on with (m:=m); eauto.
            { unfold mem_range.
              (* rewrite LEN_INB1. *)
              intros i C1 C2. nia. }
            eapply Mem.load_store_same in MSTORE. ss.
            eapply Mem.load_loadbytes in MSTORE.
            clear - MSTORE LEN_INB1. des. ss.
            (* rewrite LEN_INB1. ss. *)
            rewrite MSTORE.
            apply Mem.loadbytes_length in MSTORE.
            destruct bytes as [| x []]; ss.
            destruct x; ss.

            replace (Int.sign_ext 8 (Int.repr 1)) with Int.one in * by ss.
            hexploit decode_byte_one_inv; eauto.
            { range_stac. }
            intro R. rewrite R. ss.
          - des.
            + subst.
              rewrite MSTORE2. ss.
              destruct bs; ss.
              2: { nia. }
              apply Mem.loadbytes_empty. nia.
            + rewrite <- LEN_BS.
              eapply Mem.loadbytes_storebytes_same.

              replace (ofs_inb + Z.of_nat (mentry_nsz * tid_s) + 1)%Z with
                  (ofs_inb + Z.of_nat (mentry_nsz * tid_s + 1))%Z by nia.
              eauto.
          - nia.
        }
      + splits.
        * erewrite inbox_insert_msg_succ; ss; eauto.
          rewrite <- NUM_ENTRIES.
          rewrite INB_DIV.
          do 2 rewrite app_length. ss.
        * ii.
          des.
          { subst. eauto. }
          eapply Mem.perm_storebytes_1; eauto.
  Qed.


  Definition idx_get_inb: nat := 2.

  Lemma sim_get_cur_inbox
        m k itr idx
        cf ofsc ofsn
        inbc_t inbn_t
        (CALL_CONT: is_call_cont k)
        (MEM_MSTORE: mem_mstore ge m cf ofsc ofsn
                                inbc_t inbn_t)
        (SIM_REST:
           forall b_mst
             (FSYMB_MST: Genv.find_symbol ge _mstore =
                         Some b_mst),
             paco3 (_sim_itree prog) r idx
                   itr
                   (Returnstate
                      (Vptr b_mst (Ptrofs.repr ofsc))
                      k m))
    : paco3 (_sim_itree prog) r (idx_get_inb + idx)
            itr
            (Callstate (Internal f_get_cur_inbox)
                       [] k m).
  Proof.
    unfold idx_get_inb.
    start_func.
    { econs. }

    hexploit (in_gvar_ids _mstore); [sIn|].
    destruct 1 as [b_mst FSYMB_MST].

    fw. clear STEP_ENTRY.
    fw.
    { econs; ss. econs.
      - eval_comput. ss.
        rewrite FSYMB_MST.
        rewrite Ptrofs.add_zero_l. reflexivity.
      - eval_comput. ss.
        rewrite FSYMB_MST.
        rewrite Ptrofs.add_zero_l.
        fold Ptrofs.zero.
        rewrite Ptrofs.unsigned_zero.
        erewrite mem_mst_curflag by eauto.
        reflexivity.
      - instantiate (1:= Vptr b_mst (Ptrofs.repr ofsc)).
        ss. eval_comput.

        (* assert (1 < Ptrofs.max_unsigned)%Z by ss. *)
        hexploit mst_match_ofs_cur; eauto. intro OFSN.
        pose proof ptr_range_inb_sz.

        destruct cf; ss.
        + unfold Ptrofs.of_ints.
          rewrite Int.signed_one by ss.
          repr_tac.
          subst.
          do 3 f_equal. nia.
        + unfold Ptrofs.of_ints.
          rewrite Int.signed_zero.
          repr_tac.
          do 3 f_equal. nia.
      - ss.
    }

    apply (sim_itree_red_idx prog) with (idx_small := idx).
    { nia. }
    rewrite call_cont_is_call_cont; ss.
    eapply SIM_REST; eauto.
  Qed.


  Lemma sim_get_nxt_inbox
        m k itr idx
        cf ofsc ofsn
        inbc_t inbn_t
        (CALL_CONT: is_call_cont k)
        (MEM_MSTORE: mem_mstore ge m cf ofsc ofsn
                                inbc_t inbn_t)
        (SIM_REST:
           forall b_mst
             (FSYMB_MST: Genv.find_symbol ge _mstore =
                         Some b_mst),
             paco3 (_sim_itree prog) r idx
                   itr
                   (Returnstate
                      (Vptr b_mst (Ptrofs.repr ofsn))
                      k m))
    : paco3 (_sim_itree prog) r (idx_get_inb + idx)
            itr
            (Callstate (Internal f_get_nxt_inbox)
                       [] k m).
  Proof.
    unfold idx_get_inb.
    start_func.
    { econs. }

    hexploit (in_gvar_ids _mstore); [sIn|].
    destruct 1 as [b_mst FSYMB_MST].

    fw. clear STEP_ENTRY.
    fw.
    { econs; ss. econs.
      - eval_comput. ss.
        rewrite FSYMB_MST. cbn.
        rewrite Ptrofs.add_zero_l. reflexivity.
      - eval_comput. ss.
        rewrite FSYMB_MST. cbn.
        rewrite Ptrofs.add_zero_l.
        fold Ptrofs.zero.
        rewrite Ptrofs.unsigned_zero.
        erewrite mem_mst_curflag by eauto.

        instantiate (1:= Vint (if cf then Int.zero else Int.one)).
        desf.
      - instantiate (1:= Vptr b_mst (Ptrofs.repr ofsn)).
        ss. eval_comput.
        (* assert (1 < Ptrofs.max_unsigned)%Z by ss. *)
        hexploit mst_match_ofs_nxt; eauto. intro OFSN.
        pose proof ptr_range_inb_sz.

        destruct cf; ss.
        + unfold Ptrofs.of_ints.
          rewrite Int.signed_zero.
          repr_tac.
          subst.
          do 3 f_equal. nia.
        + unfold Ptrofs.of_ints.
          rewrite Int.signed_one by ss.
          repr_tac.
          do 3 f_equal.
          fold inb_sz in OFSN. nia.
      - ss.
    }

    apply (sim_itree_red_idx prog) with (idx_small := idx).
    { nia. }
    rewrite call_cont_is_call_cont; ss.
    eapply SIM_REST; eauto.
  Qed.

End SIM_UTILS.
