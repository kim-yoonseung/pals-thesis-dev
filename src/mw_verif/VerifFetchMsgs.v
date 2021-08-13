From ITree Require Import ITree Eq EqAxiom.
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

Require Import config_prm main_prm SystemProgs.
Require Import VerifProgBase.
Require Import VerifMainUtil.

Import Clight Clightdefs.
Import ITreeNotations.

Set Nested Proofs Allowed.


Local Transparent Archi.ptr64.
Local Opaque Int64.max_unsigned Int.max_unsigned.
Local Opaque Genv.globalenv.


Section SIM_FETCH_MSGS.
  Variable cprog: Clight.program.
  Context `{SystemEnv}.
  (* Context `{CProgSysEvent}. *)
  (* Existing Instance cprog_event_instance. *)

  Let prog: Prog.t := prog_of_clight cprog.
  Let ge := Clight.globalenv cprog.
  Variable tid: nat.
  Hypothesis RANGE_TID: (tid < num_tasks)%nat.

  Context `{genv_props ge (main_gvar_ilist tid)
                       main_gfun_ilist main_cenv_ilist}.
  (* Notation progE := (@progE extcallE). *)

  Variable r: nat -> itree progE unit -> Prog.state prog -> Prop.

  Notation sim := (paco3 _).

  Variable kp: cont.
  Hypothesis KP: is_call_cont kp.

  Inductive fm_loop_inv
            (m_linit: mem)
            (b_mst b_buf: block)
            (rxs sytm: nat)
            cf ofsc ofsn
            (k: MWITree.mstore_t -> itree progE unit)
            (i: nat) (itr: itree progE unit)
            (le: PTree.t val) (m: mem)
    : Prop :=
    FetchMsgsLoopInv
      inbc inbn
      v_sz v_t'3
      (RANGE_I: i <= num_tasks * 4)
      (ITREE: itr = mst' <- MWITree.fetch_msg_loop
                             rxs sytm (num_tasks * 4 - i)
                             (inbc, inbn);; k mst')
      (MEM_CONSTS : mem_consts ge m tid)
      (MEM_RXS : mem_rxs ge m rxs)
      (MEM_MSTORE : mem_mstore ge m cf ofsc ofsn
                               inbc inbn)
      (PERM_BUF : Mem.range_perm m b_buf 0 (Z.of_nat max_pld_size) Cur Freeable)
      (CH_BLKS: Mem.unchanged_on (fun b _ => b <> b_mst /\ b <> b_buf) m_linit m)
      (* (INBC_EQV : inbox_equiv inbc_s inbc_t) *)
      (* (INBN_EQV : inbox_equiv inbn_s inbn_t) *)
      (LENV_EQUIV:
         lenv_equiv
           le
           [(_cur_base_time, Vlong (IntNat.of_nat64 sytm));
           (_rxs__1, Vint (IntNat.of_nat rxs));
           (_nxt_base_time,
            Vlong (IntNat.of_nat64 (sytm + period)));
           (_cptr, Vptr b_mst (Ptrofs.repr ofsc));
           (_nptr, Vptr b_mst (Ptrofs.repr ofsn));
           (_pld_size, Vint (Int.repr (Z.of_nat pld_size)));
           (_i, Vint (IntNat.of_nat i));
           (_sz, v_sz); (_t'3, v_t'3);
           (_t'2, Vptr b_mst (Ptrofs.repr ofsn));
           (_t'1, Vptr b_mst (Ptrofs.repr ofsc))])
  .

  Local Opaque idx_get_inb idx_ins_msg.

  Definition idx_fch: nat :=
    idx_get_inb + idx_get_inb + 50.
    (* num_tasks * 4 * 10 (* (idx_ins_msg + 30). *). *)

  Lemma sim_fetch_msgs
        sytm m0
        k idx
        rxs cf ofsc ofsn
        inbc inbn
        (RANGE_SYTM: (0 < Z.of_nat (sytm + 2 * period) <=
                      Int64.max_unsigned)%Z)
        (RANGE_RXS: IntRange.sint rxs)
        (NEXT_BLOCK: (Genv.genv_next ge <=
                      Mem.nextblock m0)%positive)
        (MEM_CONSTS: mem_consts ge m0 tid)
        (MEM_MSTORE: mem_mstore ge m0 cf ofsc ofsn inbc inbn)
        (MEM_RXS: mem_rxs ge m0 rxs)
        (* (INBC_EQV: inbox_equiv inbc_s inbc_t) *)
        (* (INBN_EQV: inbox_equiv inbn_s inbn_t) *)
        (SIM_RET:
           forall m' inbc' inbn'
             (MEM_CH_MST: mem_changed_gvar_id
                           ge _mstore m0 m')
             (* (main_appinv_region cprog) m m') *)
             (MEM_MSTORE: mem_mstore ge m' cf
                                     ofsc ofsn inbc' inbn')
             (* (INBC_EQV: inbox_equiv inbc_s' inbc_t') *)
             (* (INBN_EQV: inbox_equiv inbn_s' inbn_t') *)
           ,
             paco3 (_sim_itree (prog_of_clight cprog))
                   r idx (k (inbc', inbn'))
                   (Clight.Returnstate Vundef kp m'))
    : paco3 (_sim_itree prog) r (idx_fch + idx)
            (mst' <- MWITree.fetch_msgs
                      rxs sytm (inbc, inbn);;
             k mst')
            (Clight.Callstate
               (Internal (f_fetch_msgs (Z.of_nat msg_size_k)
                                       (Z.of_nat max_num_tasks)))
               [Vint (IntNat.of_nat rxs);
               Vlong (IntNat.of_nat64 sytm)] kp m0)
  .
  Proof.
    guardH RANGE_SYTM.

    hexploit (in_gvar_ids _mstore); [sIn|].
    intros [b_mst FSYMB_MST].

    assert (ALLOC_OK: exists m1 b_buf e,
               alloc_variables
                 (globalenv cprog) empty_env m0
                 [(_buf, Tstruct _pals_msg_t noattr)]
                 e m1 /\
               env_equiv e [(_buf, (b_buf, Tstruct _pals_msg_t noattr))] /\
               blocks_of_env ge e = [(b_buf, 0%Z, Z.of_nat max_pld_size)] /\
               ~ Mem.valid_block m0 b_buf /\
               (* (Mem.nextblock m0 <= b_buf)%positive /\ *)

               Mem.range_perm m1 b_buf 0 (Z.of_nat max_pld_size) Cur Freeable /\
               Mem.unchanged_on (fun _ _ => True) m0 m1).
    { esplits; ss.
      - econs.
        + apply surjective_pairing.
        + econs 1.
      - ii. simpl.
        destruct (ident_eq i _buf); ss.
        + subst i. fold_cenv.
          erewrite (in_cenv_ilist _pals_msg_t) by sIn.
          rewrite PTree.gss. ss.
        + rewrite PTree.gso; ss.
          rewrite PTree.gempty.
          unfold find_ilist. ss.
          destruct (Pos.eqb_spec _buf i); ss.
          congruence.
      - ss. fold_cenv.
        erewrite (in_cenv_ilist _pals_msg_t) by sIn.
        ss. unfold blocks_of_env.
        unfold PTree.set. ss.
        fold_cenv.
        erewrite (in_cenv_ilist _pals_msg_t) by sIn.
        reflexivity.
      - eapply Mem.fresh_block_alloc.
        apply surjective_pairing.
      - ss. fold_cenv.
        erewrite (in_cenv_ilist _pals_msg_t) by sIn.
        ii. ss.
        eapply Mem.perm_alloc_2; eauto.
        apply surjective_pairing.
      - eapply Mem.alloc_unchanged_on; eauto.
        apply surjective_pairing.
    }
    destruct ALLOC_OK as
        (m1 & b_buf & e & ALLOC & ENV_EQUIV &
         BLKS_OF_ENV & B_BUF_NEW & PERM_BUF & UNCH).

    assert(B_BUF_NOT_GBLK:
             forall id_gv b_gv
               (* (IN: In id_gv main_gvar_ids) *)
               (FSYMB_GV: Genv.find_symbol ge id_gv = Some b_gv),
               b_buf <> b_gv).
    { i. eapply genv_symb_range2 in FSYMB_GV; eauto.
      ii. clarify. }

    unfold idx_fch.
    start_func.

    (* match goal with *)
    (* | |- context[Callstate (Internal ?f) ?args ?k ?m] => *)
    (*   hexploit (clight_function_entry *)
    (*               ge f args k m); ss *)
    (* end. *)
    (* { solve_norepet. } *)
    (* { solve_norepet. } *)
    (* { solve_norepet. } *)
    (* { solve_disjoint. } *)
    (* { eauto. } *)
    (* i. des. *)

    fw.
    (* consts, mstore, rxs *)
    eapply mem_consts_unch in MEM_CONSTS; cycle 1; eauto.
    { eapply Mem.unchanged_on_implies; eauto. ss. }
    eapply mem_mstore_unch in MEM_MSTORE; cycle 1; eauto.
    { eapply Mem.unchanged_on_implies; eauto. ss. }
    eapply mem_rxs_unch in MEM_RXS; cycle 1; eauto.
    { eapply Mem.unchanged_on_implies; eauto. ss. }
    clear ALLOC STEP_ENTRY.

    fw.
    (* set nxt_base_time *)
    hexploit (in_gvar_ids _PALS_PERIOD); [sIn|].
    intros [b_pprd FSYMB_PPRD].
    fw.
    { econs.
      eval_comput.
      rewrite FSYMB_PPRD. cbn.
      erewrite mem_consts_pals_period by eauto.
      repr_tac.
      rewrite <- Nat2Z.inj_add. reflexivity.
    }
    upd_lenv.

    fw. fw. fw.
    (* call *)
    hexploit (in_gfun_ilist _get_cur_inbox); [sIn|].
    i. des.
    fw.
    { econs; ss.
      - apply eval_expr_comput; ss.
        rewrite ENV_EQUIV. ss.
        rewrite FDEF_SYMB. cbn. eauto.
      - econs.
      - eauto.
      - ss.
    }
    clear dependent b_fdef.

    eapply (sim_itree_red_idx prog) with
        (idx_small:= idx_get_inb + (idx_get_inb + 40 + idx)).
    { nia. }
    eapply sim_get_cur_inbox; eauto; ss.
    intros b_mst' FSYMB_MST'.
    clarify. rename FSYMB_MST' into FSYMB_MST.

    (* ret *)
    fw. upd_lenv.
    fw.
    (* set *)
    fw.
    { econs; ss.
      apply eval_expr_comput. ss.
      rewrite LENV_EQUIV. ss.
      fold_cenv.
      erewrite (in_cenv_ilist _inbox_t) by sIn.
      simpl.
      fold_cenv.
      erewrite (in_cenv_ilist _msg_entry_t) by sIn.
      simpl.
      unfold align_attr, Coqlib.align. simpl.
      rewrite Ptrofs.add_zero. cbn. eauto.
    }
    upd_lenv.

    fw. fw. fw.
    (* call *)
    hexploit (in_gfun_ilist _get_nxt_inbox); [sIn|].
    i. des.
    fw.
    { econs; ss.
      - apply eval_expr_comput; ss.
        rewrite ENV_EQUIV. ss.
        rewrite FDEF_SYMB. cbn. eauto.
      - econs.
      - eauto.
      - ss.
    }
    clear dependent b_fdef.

    eapply (sim_itree_red_idx prog) with
        (idx_small:= idx_get_inb + (idx + 30)).
    { nia. }
    eapply sim_get_nxt_inbox; eauto; ss.
    intros b_mst2 FSYMB_MST2.
    clarify. rename FSYMB_MST2 into FSYMB_MST.

    (* ret *)
    fw. upd_lenv.
    fw.
    (* set *)
    fw.
    { econs. eval_comput.
      unfold align_attr, Coqlib.align. simpl.
      rewrite Ptrofs.add_zero. cbn. eauto. }
    upd_lenv.

    fw. fw.
    (* set pld_size *)

    pose proof range_max_pld_size as SINT_MPLD.
    pose proof range_pld_size as SINT_PLD.
    pose proof range_msg_size as SINT_MSZ.

    fw.
    { hexploit (in_gvar_ilist _MSG_SIZE); [sIn|].
      i. des. ss.
      econs. eval_comput.
      rewrite GVAR_SYMB. cbn.
      erewrite mem_consts_msg_size; eauto.
      eval_comput.
      repr_tac.
      replace (Z.of_nat msg_size + 9)%Z with (Z.of_nat pld_size).
      2: { unfold pld_size. nia. }
      reflexivity.
    }
    upd_lenv.

    fw. fw. fw.
    { econs. eval_comput. ss. }
    upd_lenv.
    fw.
    fold_for_loop _i.
    unfold MWITree.fetch_msgs.

    assert (SINT_NT4: IntRange.sint (num_tasks * 4)).
    { clear. pose proof range_num_tasks as RNT.
      assert (Byte.max_signed * 4 < Int.max_signed)%Z by ss.
      range_stac. }
    assert (SINT_NT: IntRange.sint num_tasks).
    { clear - SINT_NT4.
      range_stac. }

    hexploit (in_gvar_ilist _NUM_TASKS); [sIn|].
    intros (b_nt & FSYMB_NT & _).

    eapply (simple_for_loop cprog) with
        (idx_each := 0) (idx0 := 10)
        (id_i:= _i) (i_max := num_tasks * 4)
        (loop_inv := fm_loop_inv
                       m1 b_mst b_buf
                       rxs sytm cf ofsc ofsn k).
    { econs; eauto.
      - nia.
      - rewrite Nat.sub_0_r. ss.
      - apply Mem.unchanged_on_refl.
    }
    (* { rewrite LENV_EQUIV. ss. } *)
    { ss. }
    { nia. }
    { (* loop body *)
      clear dependent le.
      clear MEM_CONSTS MEM_MSTORE MEM_RXS PERM_BUF. i.
      rename RANGE_I into RANGE_I_T.
      clear inbc inbn.

      assert (SINT_I: IntRange.sint i).
      { clear - RANGE_I_T SINT_NT4.
        range_stac. }

      inv LINV.
      fw. fw. fw.
      { econs.
        - eval_comput.
          rewrite FSYMB_NT.
          cbn. rewrite Ptrofs.unsigned_zero.
          erewrite mem_consts_num_tasks; eauto.
          s. repr_tac.
          replace (Z.of_nat num_tasks * 4)%Z with
              (Z.of_nat (num_tasks * 4)) by nia.
          rewrite <- Nat2Z_inj_ltb.

          instantiate (1:= Vtrue).
          destruct (Nat.ltb_spec i (num_tasks * 4)); ss.
          nia.
        - ss.
      }
      rewrite Int.eq_false by ss.
      ss.
      fw. fw. fw. fw.
      { hexploit (in_gfun_ilist _pals_recvfrom); [sIn|].
        i. des. ss.
        destruct (Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero); ss.
        clear_tt.

        econs; ss.
        - eval_comput.
          rewrite FDEF_SYMB. cbn. reflexivity.
        - eval_comput.
          reflexivity.
        - ss. eauto.
        - ss.
      }

      (* event *)
      pfold. econs 3.
      { ss. econs; eauto.
        - ss.
          econs 1; eauto.
          eapply CProgOSEC_Recvfrom with
              (sid:=rxs) (sz_buf:= pld_size); eauto.
          rewrite Ptrofs.unsigned_zero. ss.
          ii. eapply Mem.perm_implies; eauto.
          { eapply PERM_BUF.
            generalize pld_size_bound. nia. }
          econs.
        - ss.
      }
      (* { econs; ss. *)
      (*   unfold pld_size. clear. range_tac. } *)
      { replace (num_tasks * 4 - i) with
            (S (num_tasks * 4 - S i)) by nia.
        (* replace (24 - i) with (S (23 - i)) by nia. *)
        simpl. econs 1. }
      { simpl_itree_goal.
        simpl_itree_goal. ss. }

      intros bs_rcv pst_r (* POSTCOND *) AFT_EVT. ss.
      (* inv POSTCOND. *)
      inv AFT_EVT.
      inv CPROG_AFTER_EVENT; ss.
      symmetry in EVENT. inv EVENT.
      existT_elim. subst.
      unf_resum. subst.
      inv OS_ESTEP. existT_elim. subst.

      guardH RETZ. list_eq_inv_tac.
      symmetry in ARGS1. inv ARGS1.
      clear ARGS ARGS0 ARGS2.

      destruct RETZ as [RETZ_NONE | RETZ_SOME].
      { (* received none *)
        des. subst.
        exists (idx + 7). left.
        simpl_itree_goal.

        fw. upd_lenv.
        fw.
        (* set *)
        fw.
        { econs; ss.
          eval_comput. ss. }
        upd_lenv.
        fw. fw. fw.
        { econs.
          - eval_comput.
            instantiate (1:= Vtrue). ss.
          - instantiate (1:= true). ss. }
        simpl.

        assert (FREE_STACK: exists m_f,
                   Mem.free_list m2 (blocks_of_env (globalenv cprog) e) = Some m_f /\
                   Mem.unchanged_on (fun b _ => b <> b_buf) m2 m_f).
        { fold ge.
          rewrite BLKS_OF_ENV. simpl.

          hexploit Mem.range_perm_free; eauto.
          destruct 1.
          esplits; desf.
          eapply Mem.free_unchanged_on; eauto.
        }
        destruct FREE_STACK as (m_f & FREE_STACK & FREE_UNCH).

        fw.
        { econs; eauto. }
        match goal with
        | |- sim _ ?idx' _ _ =>
          replace idx' with idx by nia
        end.
        ss.
        rewrite call_cont_is_call_cont by ss.

        eapply SIM_RET; eauto.
        - r. i. ss. clarify.
          eapply Mem.unchanged_on_implies with
              (fun b _ => b <> b_mst /\ b <> b_buf).
          2: { ii. split; ss.
               ii. subst b. clarify. }
          eapply Mem.unchanged_on_trans.
          { eapply Mem.unchanged_on_implies; eauto. ss. }
          eapply Mem.unchanged_on_trans; eauto.
          eapply Mem.unchanged_on_implies; eauto.
          ii. des. ss.
        - eapply mem_mstore_unch; eauto.
          eapply Mem.unchanged_on_implies; eauto.
          ii. ss. clarify.
          hexploit Genv.genv_symb_range; eauto.
          unfold Coqlib.Plt. ss.
          clear - B_BUF_NEW NEXT_BLOCK.
          unfold Mem.valid_block, Coqlib.Plt in *.
          nia.
      }

      (* received msg *)
      destruct RETZ_SOME as (bs & ? & SBYTES & ? & ? & ?). subst.
      rewrite Ptrofs.unsigned_zero in SBYTES.

      eapply mem_rxs_unch in MEM_RXS; eauto.
      2: { eapply Mem.storebytes_unchanged_on; eauto.
           ii. apply B_BUF_NEW.
           eapply genv_symb_range2; eauto. }
      eapply mem_mstore_unch in MEM_MSTORE; eauto.
      2: { eapply Mem.storebytes_unchanged_on; eauto.
           ii. apply B_BUF_NEW.
           eapply genv_symb_range2; eauto. }

      eapply Mem_range_perm_storebytes_1 in PERM_BUF; eauto.

      exists (idx_ins_msg + idx1 + idx + 30). left.
      fw. upd_lenv.
      fw. fw.
      { econs. eval_comput. ss. }
      upd_lenv.
      fw. fw.
      assert (RANGE_ZLEN: (Int.min_signed <= Zlength bs
                           <= Int.max_signed)%Z).
      { rewrite Zlength_correct.
        range_stac. }

      fw.
      { econs; ss.
        - eval_comput.
          rewrite Int_lt_repr; ss.
        - instantiate (1:= false).
          replace (Zlength bs <? 0)%Z with false.
          2: { destruct (Z.ltb_spec (Zlength bs) 0); ss.
               rewrite Zlength_correct in *. nia. }
          ss.
      }
      ss.

      fw. fw.
      fw.
      { econs; ss.
        - eval_comput.
          rewrite Zlength_correct.
          repr_tac.
          rewrite Nat2Z_inj_eqb.
          reflexivity.
        - rewrite bool_val_of_bool. ss.
      }

      destruct (Nat.eqb_spec (length bs) pld_size) as [EQ|NEQ].
      2: {
        (* neq *)
        ss.
        fw. fw.
        { econs. eauto. }
        fw.
        { econs; ss.
          eval_comput.
          repr_tac.
          replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by nia.
          reflexivity.
        }
        upd_lenv.
        fw.
        eapply (sim_itree_red_idx prog) with (idx_small:= idx1 - 0).
        { nia. }

        eapply SIM_NEXT.
        (* - eapply LENV_EQUIV. *)
        econs; eauto.
        + replace (MWITree.fetch_msg sytm bs (inbc, inbn))
            with (inbc, inbn).
          2: {
            unfold MWITree.fetch_msg.
            destruct (Nat.eqb_spec (length bs) pld_size); ss.
          }
          ss.
        + eapply mem_consts_unch_diffblk; eauto.
          { eapply Mem.storebytes_unchanged_on; eauto. }
          intros id ID_CONSTS FSYMB_ID.
          eapply B_BUF_NOT_GBLK in FSYMB_ID. ss.
        + eapply Mem.unchanged_on_trans; eauto.
          eapply Mem.storebytes_unchanged_on; eauto.
          ii. des; ss.
      }
      (* length bs = pld_size *)

      assert(BDIV: exists (sytm_to: nat) (tid_s: Z)
                     (cont: list byte),
                bs = (IntByte.to_bytes64
                        (IntNat.of_nat64 sytm_to)) ++
                     (Byte.repr tid_s)::cont /\
                IntRange.uint64 sytm_to /\
                IntRange.sintz8 tid_s /\
                length cont = msg_size).
      { rewrite <- firstn_skipn with (n:=8) (l:=bs).
        rewrite <- firstn_skipn with (n:=1) (l:=skipn 8 bs).
        pose (bs1 := firstn 8 bs).
        pose (bs2 := firstn 1 (skipn 8 bs)).
        pose (bs3 := skipn 1 (skipn 8 bs)).
        fold bs1. fold bs2. fold bs3.

        hexploit (IntByte.of_bytes_inv64 bs1).
        { apply firstn_length_le. rewrite EQ.
          unfold pld_size. nia. }
        intros TO_BYTES_TM.

        assert (LEN_SKIPN: length (skipn 8 bs) = 1 + msg_size).
        { rewrite skipn_length. rewrite EQ.
          unfold pld_size. nia. }

        assert (LEN_SID: length bs2 = 1).
        { subst bs2.
          apply firstn_length_le. nia. }

        destruct bs2 as [|b_sid []]; ss.

        exists (Z.to_nat (Int64.unsigned (IntByte.of_bytes64 bs1))),
        (Byte.signed b_sid), bs3.
        esplits.
        - f_equal.
          { unfold IntNat.of_nat64.
            rewrite Z2Nat.id.
            2: { apply Int64.unsigned_range. }
            rewrite Int64.repr_unsigned. ss. }
          f_equal.
          rewrite Byte.repr_signed; ss.
        - rr.
          rewrite Z2Nat.id.
          2: { apply Int64.unsigned_range_2. }
          apply Int64.unsigned_range_2.
        - apply (Byte.signed_range b_sid).
        - subst bs3. rewrite skipn_length. nia.
      }

      des. guardH BDIV.
      renames BDIV0 BDIV1 BDIV2 into
              RANGE_SYTM_TO RANGE_TID_S LEN_CONT.

      hexploit Mem.loadbytes_storebytes_same; eauto.
      intro LBS_ALL.
      rewrite map_length in LBS_ALL.
      rewrite EQ in LBS_ALL. ss.
      rewrite BDIV in LBS_ALL.

      replace (Z.of_nat pld_size) with
          (8 + (1 + Z.of_nat msg_size))%Z in LBS_ALL.
      2: { unfold pld_size. nia. }
      (* replace 16%Z with (8 + 8)%Z in LBS_ALL by ss. *)
      apply Mem.loadbytes_split in LBS_ALL; ss.
      2: { nia. }
      destruct LBS_ALL as (bs1 & bs' & LBS1 & LBS' & BS_EQ).
      rewrite map_app in BS_EQ.
      apply app_eqlen_inv in BS_EQ.
      2: {
        apply Mem.loadbytes_length in LBS1.
        rewrite LBS1.
        rewrite map_length.
        rewrite IntByte.to_bytes_length64. ss.
      }
      destruct BS_EQ. subst.

      (* replace 8%Z with (1 + 7)%Z in LBS' at 2 by ss. *)
      apply Mem.loadbytes_split in LBS'; ss.
      2: { nia. }
      destruct LBS' as (bs2 & bs_cont & LBS2 & LBSC & BS_EQ).

      assert (LEN_BS2: length bs2 = 1).
      { apply Mem.loadbytes_length in LBS2. ss. }

      destruct bs2 as [| b_sid []]; ss.
      inv BS_EQ.

      assert (B_BUF_SYTM:
                Mem.load Mint64 m' b_buf 0%Z =
                Some (Vlong (IntNat.of_nat64 sytm_to))).
      { erewrite Mem.loadbytes_load; cycle 1; eauto.
        - solve_divide.
        - unfold IntByte.to_bytes64.
          change (map Byte (encode_int 8 (Int64.unsigned (IntNat.of_nat64 sytm_to)))) with
              (encode_val Mint64 (Vlong (IntNat.of_nat64 sytm_to))).
          match goal with
          | |- context[ decode_val _ (encode_val _ ?v)] =>
            hexploit (decode_encode_val_general v Mint64 Mint64)
          end.
          intro DE_VAL. ss. rewrite DE_VAL. reflexivity.
      }

      assert (B_BUF_TID:
                Mem.load Mint8signed m' b_buf 8%Z =
                Some (Vint (Int.repr tid_s))).
      { erewrite Mem.loadbytes_load; eauto.
        2: { solve_divide. }
        unfold decode_val, decode_int. ss.
        rewrite rev_if_be_single.
        do 2 f_equal. ss.
        rewrite Z.add_0_r.
        apply sign_ext_byte_range_u. ss.
      }

      eapply Mem.unchanged_on_trans with (m2:=m2) in CH_BLKS.
      2: { eapply Mem.storebytes_unchanged_on; eauto.
           ii. des. ss. }
      eapply mem_consts_unch_diffblk in MEM_CONSTS; cycle 1.
      { eapply Mem.unchanged_on_implies.
        { eapply storebytes_unchanged_on'; eauto. }
        instantiate (1:= b_buf).
        unfold mem_range.
        ii. ss. des; ss.
      }
      { intros id ID_CONSTS FSYMB_ID.
        apply B_BUF_NOT_GBLK in FSYMB_ID. ss. }

      clear m2 SBYTES. rename m' into m2.

      fw. fw.
      assert(RANGE_TID_S2: IntRange.sintz tid_s).
      { range_stac. }

      fw.
      { econs.
        - eval_comput. ss.
          rewrite Ptrofs.add_zero_l.
          rewrite Ptrofs.unsigned_repr by ss.
          rewrite B_BUF_TID.
          eval_comput.
          rewrite Int_lt_repr by ss.
          reflexivity.
        - rewrite bool_val_of_bool. reflexivity.
      }

      destruct (Z.ltb_spec tid_s 0).
      { (* tid_s < 0*)
        fw. fw.
        { econs; eauto. }
        fw.
        { econs. eval_comput.
          unfold IntNat.of_nat.
          repr_tac.
          reflexivity. }
        upd_lenv.
        fw.
        eapply (sim_itree_red_idx prog) with (idx_small:= (idx1 - 0)).
        { nia. }

        eapply SIM_NEXT.
        (* - rewrite LENV_EQUIV. cbn. *)
        (*   unfold IntNat.of_nat. do 3 f_equal. *)
        (*   rewrite Nat2Z.inj_succ. ss. *)
        replace (MWITree.fetch_msg sytm bs (inbc, inbn))
          with (inbc, inbn).
        2: {
          unfold MWITree.fetch_msg.
          destruct (Nat.eqb_spec (length bs) pld_size); ss.

          cut (parse_msg bs = None).
          { intro R. rewrite R. ss. }

          unfold parse_msg.
          rewrite BDIV.
          erewrite list_divide_succ; eauto.
          rewrite Byte.signed_repr by ss.
          unfold Z_to_nat2.
          destruct (Z.ltb_spec tid_s 0); ss.
          nia.
        }

        econs; eauto.
        unfold IntNat.of_nat.
        rewrite Nat2Z.inj_succ. eauto.
      }

      (* 0 <= tid_s *)

      assert (PARSE_MSG_OK:
                parse_msg bs =
                Some (sytm_to, Z.to_nat tid_s, cont)).
      { unfold parse_msg.
        rewrite BDIV.
        erewrite list_divide_succ; eauto. ss.
        rewrite Byte.signed_repr by ss.
        unfold Z_to_nat2.
        destruct (Z.ltb_spec tid_s 0); ss.
        { nia. }
        f_equal. f_equal. f_equal.
        rewrite IntByte.to_bytes_inv64.
        unfold IntNat.of_nat64.
        rewrite Int64.unsigned_repr.
        2: { range_stac. }
        rewrite Nat2Z.id. ss.
      }

      unfold MWITree.fetch_msg.
      change pld_size with pld_size.
      rewrite EQ.
      rewrite Nat.eqb_refl. s.
      rewrite PARSE_MSG_OK.

      fw. fw.
      { econs.
        - eval_comput.
          unfold align_attr, Coqlib.align. simpl.
          rewrite Ptrofs.add_zero. cbn.
          rewrite Ptrofs.unsigned_zero.
          rewrite B_BUF_SYTM.
          eval_comput.
          unfold IntNat.of_nat64.
          rewrite Int64_eq_repr; cycle 1.
          { range_stac. }
          { rr. clear - RANGE_SYTM.
            unguard. nia. }

          rewrite Nat2Z_inj_eqb. reflexivity.
        - rewrite bool_val_of_bool. reflexivity.
      }

      hexploit (in_gfun_ilist _insert_msg); [sIn|].
      i. des.
      renames b_fdef FDEF_SYMB FDEF_FPTR into
              b_insm FSYMB_INSM FPTR_INSM.

      hexploit (in_gvar_ids _rxs); [sIn|].
      intros [b_rxs FSYMB_RXS].

      destruct (Nat.eqb_spec sytm_to sytm).
      { (* sytm_to = sytm *)
        subst sytm_to.
        fw.
        { econs; ss.
          - eval_comput.
            rewrite FSYMB_INSM. ss.
          - eval_comput.
            unfold Coqlib.align, align_attr. simpl.
            do 2 rewrite Ptrofs.add_zero_l.
            cbn.
            rewrite Ptrofs.unsigned_repr by ss.
            rewrite B_BUF_TID.
            rewrite sign_ext_byte_range by ss.
            reflexivity.
          - eauto.
          - ss.
        }

        eapply (sim_itree_red_idx prog) with
            (idx_small:= idx_ins_msg + (idx1 + idx + 10)).
        { nia. }

        replace (Int.repr tid_s) with
            (IntNat.of_nat (Z.to_nat tid_s)).
        2: { unfold IntNat.of_nat.
             rewrite Z2Nat.id; ss. }

        eapply sim_insert_msg; eauto; ss.
        { rewrite Z2Nat.id by ss. ss. }
        { apply not_eq_sym.
          eapply B_BUF_NOT_GBLK; eauto. }
        { replace (9 + Z.of_nat msg_size)%Z with (Z.of_nat pld_size).
          2: { unfold pld_size. nia. }
          range_stac.
        }
        { specialize (MEM_MSTORE _ FSYMB_MST).
          inv MEM_MSTORE.
          pose proof ptr_range_inb_sz.
          desf. nia. }
        { specialize (MEM_MSTORE _ FSYMB_MST).
          inv MEM_MSTORE.
          (* pose proof ptr_range_inb_sz. *)
          pose proof ptr_range_mstore.
          desf; nia. }
        { apply MEM_MSTORE; eauto. }

        i. guardH INB_INSERT.
        fw. fw.
        { econs; eauto. }

        (* i_inc *)
        fw.
        { econs.
          eval_comput.
          repr_tac.
          replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by nia.
          reflexivity.
        }
        upd_lenv.

        fw.
        eapply (sim_itree_red_idx prog) with (idx_small:= (idx1 - 0)).
        { nia. }

        eapply SIM_NEXT.
        (* - rewrite LENV_EQUIV. ss. *)
        rewrite INB_INSERT.
        econs; eauto.
        + eapply mem_rxs_unch_diffblk; eauto.
          { instantiate (1:= b_mst).
            eapply Mem.unchanged_on_implies; eauto.
            unfold mem_range. ii. des; ss. }
          cut (b_rxs <> b_mst).
          { ii. ss. clarify. }
          eapply Genv.global_addresses_distinct; cycle 1; eauto. ss.
        + specialize (MEM_MSTORE _ FSYMB_MST).
          ii. ss. clarify.
          inv MEM_MSTORE. econs; eauto.
          * eapply Mem.load_unchanged_on; eauto.
            unfold mem_range. unfold inbox_sz.
            ii. des; ss. desf; nia.
          * eapply Mem_range_perm_unchanged_on; eauto.
            eapply Mem.unchanged_on_implies; eauto.
            unfold mem_range, inbox_sz.
            ii. desf; nia.
          * eapply Mem_inbox_unch; eauto.
            eapply Mem.unchanged_on_implies; eauto.
            unfold mem_range, inbox_sz.
            ii. desf; nia.
        + cut (b_buf <> b_mst).
          { i. eapply Mem_range_perm_unchanged_on; eauto.
            eapply Mem.unchanged_on_implies; eauto.
            unfold mem_range, inbox_sz.
            ii. des. clarify. }
          eapply B_BUF_NOT_GBLK; eauto.
        + eapply Mem.unchanged_on_trans.
          { eauto. }
          eapply Mem.unchanged_on_implies; eauto.
          unfold mem_range.
          ii. des. ss.
      }

      fw.
      { econs; ss.
        - eval_comput.
          unfold Coqlib.align, align_attr. simpl.
          rewrite Ptrofs.add_zero. cbn.
          rewrite Ptrofs.unsigned_zero.
          rewrite B_BUF_SYTM.
          eval_comput.
          unfold IntNat.of_nat64.
          repr_tac.
          rewrite Nat2Z_inj_eqb. reflexivity.
        - rewrite bool_val_of_bool. reflexivity.
      }

      destruct (Nat.eqb_spec sytm_to (sytm + period)).
      { (* sytm_to = sytm + period *)
        subst sytm_to.
        fw.
        { econs; ss.
          - eval_comput.
            rewrite FSYMB_INSM. ss.
          - eval_comput.
            unfold Coqlib.align, align_attr. simpl.
            do 2 rewrite Ptrofs.add_zero_l.
            cbn.
            rewrite Ptrofs.unsigned_repr by ss.
            rewrite B_BUF_TID.
            rewrite sign_ext_byte_range by ss.
            reflexivity.
          - eauto.
          - ss.
        }

        eapply (sim_itree_red_idx prog) with
            (idx_small:= idx_ins_msg + (idx1 + idx + 10)).
        { nia. }

        replace (Int.repr tid_s) with
            (IntNat.of_nat (Z.to_nat tid_s)).
        2: { unfold IntNat.of_nat.
             rewrite Z2Nat.id; ss. }

        eapply sim_insert_msg; try eapply INBN_EQV;
          eauto; ss.
        { rewrite Z2Nat.id by ss. ss. }
        { apply not_eq_sym.
          eapply B_BUF_NOT_GBLK; eauto. }
        { replace (9 + Z.of_nat msg_size)%Z with (Z.of_nat pld_size).
          2: { unfold pld_size. nia. }
          clear. pose proof range_pld_size.
          range_stac. }
        { specialize (MEM_MSTORE _ FSYMB_MST).
          pose proof range_inb_sz_precise.
          inv MEM_MSTORE. desf. nia. }
        { specialize (MEM_MSTORE _ FSYMB_MST).
          pose proof range_inb_sz_precise.
          pose proof ptr_range_mstore.
          inv MEM_MSTORE. desf; nia. }
        { apply MEM_MSTORE; eauto. }

        i. guardH INB_INSERT.
        fw. fw.
        { econs; eauto. }

        (* i_inc *)
        fw.
        { econs.
          eval_comput.
          repr_tac.
          replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by nia.
          reflexivity.
        }
        upd_lenv.

        fw.
        eapply (sim_itree_red_idx prog) with (idx_small:= (idx1 - 0)).
        { nia. }

        eapply SIM_NEXT.
        (* - apply LENV_EQUIV. *)
        rewrite INB_INSERT.

        econs; eauto.
        + eapply mem_rxs_unch_diffblk; eauto.
          { instantiate (1:= b_mst).
            eapply Mem.unchanged_on_implies; eauto.
            unfold mem_range. ii. des; ss. }
          cut (b_rxs <> b_mst).
          { ii. ss. clarify. }
          eapply Genv.global_addresses_distinct; cycle 1; eauto. ss.
        + specialize (MEM_MSTORE _ FSYMB_MST).
          ii. ss. clarify.
          inv MEM_MSTORE. econs; eauto.
          * eapply Mem.load_unchanged_on; eauto.
            unfold mem_range. unfold inbox_sz.
            ii. des; ss. desf; nia.
          * eapply Mem_range_perm_unchanged_on; eauto.
            eapply Mem.unchanged_on_implies; eauto.
            unfold mem_range, inbox_sz.
            ii. desf; nia.
          * eapply Mem_inbox_unch; eauto.
            eapply Mem.unchanged_on_implies; eauto.
            unfold mem_range, inbox_sz.
            ii. desf; nia.
        + cut (b_buf <> b_mst).
          { i. eapply Mem_range_perm_unchanged_on; eauto.
            eapply Mem.unchanged_on_implies; eauto.
            unfold mem_range, inbox_sz.
            ii. des. clarify. }
          eapply B_BUF_NOT_GBLK; eauto.
        + eapply Mem.unchanged_on_trans.
          { eauto. }
          eapply Mem.unchanged_on_implies; eauto.
          unfold mem_range.
          ii. des. ss.
      }

      fw.
      { econs. eauto. }
      fw.
      { econs. eval_comput.
        repr_tac.
        reflexivity. }
      upd_lenv.
      fw.
      eapply (sim_itree_red_idx prog) with (idx_small:= (idx1 - 0)%nat).
      { nia. }

      eapply SIM_NEXT.
      (* { rewrite LENV_EQUIV. *)
      (*   unfold IntNat.of_nat. *)
      (*   rewrite Nat2Z.inj_succ. ss. } *)

      econs; eauto.
      unfold IntNat.of_nat.
      rewrite Nat2Z.inj_succ. ss.
    }

    (* after loop *)
    clear le LENV_EQUIV.
    clear MEM_CONSTS MEM_RXS MEM_MSTORE PERM_BUF.
    clear inbc inbn.
    i. inv LINV_END.
    fw. fw. fw.
    { econs.
      - eval_comput.
        rewrite FSYMB_NT.
        erewrite mem_consts_num_tasks; eauto.
        s. repr_tac.
        replace (Z.of_nat (num_tasks * 4)) with
            (Z.of_nat num_tasks * 4)%Z by nia.
        rewrite Z.ltb_irrefl. ss.
      - instantiate (1:= false). ss.
    }

    simpl.
    assert (FREE_STACK: exists m_f,
               Mem.free_list m_e (blocks_of_env (globalenv cprog) e) = Some m_f /\
               Mem.unchanged_on (fun b _ => b <> b_buf) m_e m_f).
    { fold ge.
      rewrite BLKS_OF_ENV. simpl.

      hexploit Mem.range_perm_free; eauto.
      destruct 1.
      esplits; desf.
      eapply Mem.free_unchanged_on; eauto.
    }
    des.

    fw. fw. fw.
    { econs; ss. eauto. }

    eapply (sim_itree_red_idx prog) with
        (idx_small := idx).
    { nia. }

    rewrite Nat.sub_diag. s.
    simpl_itree_goal.

    assert(UNCH_F: mem_changed_gvar_id ge _mstore m0 m_f).
    { r. i. ss. clarify.
      eapply Mem.unchanged_on_implies with
          (P:= fun b ofs => b <> b_mst /\ b <> b_buf).
      2: { ii. split; auto.
           ii. subst b. ss. }

      eapply Mem.unchanged_on_trans with (m2:=m1).
      { eapply Mem.unchanged_on_implies; eauto. ss. }
      eapply Mem.unchanged_on_trans; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      ii. subst. des; ss. }

    eapply SIM_RET; eauto.
    eapply mem_mstore_unch; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    assert (Mem.valid_block m0 b_mst).
    { eapply (genv_symb_range2 ge _mstore); eauto. }
    ii. subst b. ss. clarify.
  Qed.

End SIM_FETCH_MSGS.
