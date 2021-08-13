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


Definition ctrl_gvar_ids := map fst ctrl_gvar_ilist.
Definition ctrl_gfun_ids := map fst ctrl_gfun_ilist.
Definition ctrl_cenv_ids := map fst ctrl_cenv_ilist.


Lemma range_qrange_sanitize_prec i
  : 0 <= qrange_sanitize i < 4.
Proof.
  unfold qrange_sanitize.
  destruct (Z.leb_spec 0 i);
    destruct (Z.ltb_spec i QSIZE); ss.
Qed.


Lemma range_adv_qidx_prec i
  : 0 <= adv_qidx i < 4.
Proof.
  apply range_qrange_sanitize_prec.
Qed.


Lemma set_queue_mem
      c e q q' m m' b ofs
      (MEM_Q: Mem.loadbytes m b ofs 4 =
              Some (inj_bytes (map Byte.repr q)))
      (RANGE_C: 0 <= c < 4)
      (RANGE_E: IntRange.sintz8 e)
      (SET_Q: q' = set_queue c e q)
      (STORE: Mem.store Mint8signed m b (ofs + c)
                        (Vint (Int.repr e)) = Some m')
  : Mem.loadbytes m' b ofs 4 =
    Some (inj_bytes (map Byte.repr q')).
Proof.

  assert (LEN_Q: length q = 4%nat).
  { apply Mem.loadbytes_length in MEM_Q.
    unfold inj_bytes in MEM_Q.
    do 2 rewrite map_length in MEM_Q. nia. }

  assert (CN: exists cn, Z.of_nat cn = c).
  { exists (Z.to_nat c). nia. }
  des.

  assert (q' = firstn cn q ++ [e] ++ skipn (S cn) q).
  { unfold set_queue in *.
    generalize (replace_nth_spec _ q cn e).
    i. des.
    { exfalso. nia. }

    cut (firstn cn q = l1 /\ skipn (S cn) q = l2).
    { i. des. subst.
      rewrite firstn_app_exact by ss.
      replace (l1 ++ [p] ++ l2) with ((l1 ++ [p]) ++ l2).
      2: { rewrite app_assoc. ss. }

      rewrite skipn_app_exact.
      2: { rewrite app_length. ss. nia. }
      rewrite Nat2Z.id.
      rewrite <- app_assoc. ss.
    }
    split.
    - subst.
      rewrite firstn_app_exact; ss.
    - subst.
      replace (l1 ++ [p] ++ l2) with ((l1 ++ [p]) ++ l2).
      2: { rewrite app_assoc. ss. }
      rewrite skipn_app_exact.
      2: { rewrite app_length. ss. nia. }
      ss.
  }
  clear SET_Q.
  subst q'.

  rename MEM_Q into LBS.
  replace 4 with (c + (1 + (3 - c))) in * by nia.
  eapply Mem.loadbytes_split in LBS; try nia.
  destruct LBS as (mvs1 & mvs2 & LBS1 & LBS2 & MVS_EQ).

  assert (LEN_BS1: length mvs1 = cn).
  { apply Mem.loadbytes_length in LBS1.
    rewrite LBS1. nia. }

  rewrite <- firstn_skipn with (l:= q) (n:=cn) in MVS_EQ.
  unfold inj_bytes in MVS_EQ.
  rewrite map_app in MVS_EQ.
  rewrite map_app in MVS_EQ.
  apply app_eqlen_inv in MVS_EQ.
  2: { do 2 rewrite map_length.
       rewrite firstn_length_le by nia.
       ss. }

  destruct MVS_EQ as (MVS_EQ1 & MVS_EQ2).

  unfold inj_bytes.
  do 2 rewrite map_app.
  apply Mem.loadbytes_concat; try nia.
  { rewrite MVS_EQ1.
    eapply Mem.loadbytes_unchanged_on; eauto.
    { eapply store_unchanged_on'; eauto. }
    unfold mem_range.
    ii. des; ss. nia.
  }
  clear mvs1 LBS1 MVS_EQ1 LEN_BS1.

  (**)
  eapply Mem.loadbytes_split in LBS2; try nia.
  destruct LBS2 as (mvs3 & mvs4 & LBS3 & LBS4 & MVS_EQ').

  assert (LEN_MVSS3: length mvs3 = 1%nat).
  { apply Mem.loadbytes_length in LBS3.
    rewrite LBS3. nia. }

  subst mvs2.

  assert (DIV_SKIPN: exists x, skipn cn q = x :: skipn (S cn) q).
  { destruct (skipn cn q) as [| h t] eqn: DES.
    { exfalso.
      hexploit skipn_nil_implies; eauto.
      nia.
    }
    erewrite skipn_nth_next; eauto.
  }
  des.
  rewrite DIV_SKIPN in MVS_EQ2. ss.
  destruct mvs3 as [| mvs3_h []]; ss.
  clarify.

  rewrite rw_cons_app.
  apply Mem.loadbytes_concat; try nia.
  - apply Mem.loadbytes_store_same in STORE.
    ss. rewrite STORE.
    unfold inj_bytes, encode_int. s.
    rewrite rev_if_be_single. ss.

    cut (Byte.repr e =
         Byte.repr (Int.unsigned (Int.repr e))).
    { congruence. }
    apply signed_byte_int_unsigned_repr_eq.
  - eapply Mem.loadbytes_unchanged_on; eauto.
    { eapply store_unchanged_on'; eauto. }
    unfold mem_range. ii. des. ss. nia.
Qed.



Record mem_cst_blk (m: mem) (st: CtrlState.t) (b_cst: block): Prop :=
  MemCtrlState {
      (* mem_cst_load: *)
      (*   Mem.loadbytes m b_cst 0 8 = *)
      (*   Some (inj_bytes (CtrlState.to_bytes cst)); *)

      mem_cst_mode: (* exists md_z, *)
        (* Mem.loadbytes m b_cst 0 1 = Some [Byte (Byte.repr md_z)] /\ *)
        (* mode st = mode_of_Z md_z ; *)
        Mem.loadbytes m b_cst 0 1 =
        Some [Byte (Byte.repr (mode_to_Z (mode st)))] ;
      mem_cst_tout: Mem.loadbytes m b_cst 1 1 =
                    Some [Byte (Byte.repr (timeout st))] ;
      mem_cst_qbgn: Mem.loadbytes m b_cst 2 1 =
                    Some [Byte (Byte.repr (queue_begin st))] ;
      mem_cst_qend: Mem.loadbytes m b_cst 3 1 =
                    Some [Byte (Byte.repr (queue_end st))] ;
      mem_cst_q: Mem.loadbytes m b_cst 4 4 =
                 Some (inj_bytes (map Byte.repr (queue st))) ;

      mem_cst_perm:
        Mem.range_perm m b_cst 0 8 Cur Writable;
    }.

Lemma loadbytes_mem_cst
      m b_cst bs md st
      (PERM: Mem.range_perm m b_cst 0 8 Cur Writable)
      (LBS: Mem.loadbytes m b_cst 0 8 =
            Some (Byte (Byte.repr (mode_to_Z md))
                       :: inj_bytes (tl bs)))
      (* (STATE: st = of_bytes bs) *)
      (STATE: st = copy_state_from_hb md bs)
  : mem_cst_blk m st b_cst.
Proof.
  subst st.

  replace 8 with (1 + 7) in LBS by ss.
  eapply Mem.loadbytes_split in LBS; try nia.
  destruct LBS as (mvs1 & mvs & LBS1 & LBS & MVS_EQ). ss.
  hexploit Mem.loadbytes_length; try apply LBS1.
  intros LEN_BS1.
  destruct mvs1 as [| mv1 []]; ss. clarify.
  destruct bs as [| b1 bs].
  { exfalso. ss.
    apply Mem.loadbytes_length in LBS. ss. }
  ss.

  replace 7 with (1 + 6) in LBS by ss.
  eapply Mem.loadbytes_split in LBS; try nia.
  destruct LBS as (mvs1 & mvs & LBS2 & LBS & MVS_EQ). ss.
  hexploit Mem.loadbytes_length; try apply LBS2.
  intros LEN_BS2.
  destruct mvs1 as [| mv1 []]; ss.
  destruct bs as [| b2 bs]; ss. clarify.

  replace 6 with (1 + 5) in LBS by ss.
  eapply Mem.loadbytes_split in LBS; try nia.
  destruct LBS as (mvs1 & mvs & LBS3 & LBS & MVS_EQ). ss.
  hexploit Mem.loadbytes_length; try apply LBS3.
  intros LEN_BS3.
  destruct mvs1 as [| mv1 []]; ss.
  destruct bs as [| b3 bs]; ss. clarify.

  replace 5 with (1 + 4) in LBS by ss.
  eapply Mem.loadbytes_split in LBS; try nia.
  destruct LBS as (mvs1 & mvs & LBS4 & LBS & MVS_EQ). ss.
  hexploit Mem.loadbytes_length; try apply LBS4.
  intros LEN_BS4.
  destruct mvs1 as [| mv1 []]; ss.
  destruct bs as [| b4 bs]; ss. clarify.

  unfold of_bytes. ss.
  econs; ss.
  - rewrite Byte.repr_signed. ss.
  - rewrite Byte.repr_signed. ss.
  - rewrite Byte.repr_signed. ss.
  - repeat rewrite Byte.repr_signed.
    hexploit Mem.loadbytes_length; try apply LBS.
    intro LEN_BS.
    destruct bs as [| ? bs]; ss.
    destruct bs as [| ? bs]; ss.
    destruct bs as [| ? bs]; ss.
    destruct bs as [| ? bs]; ss.
    destruct bs as [| ? bs]; ss.
Qed.

Lemma mem_cst_loadbytes
      m b_cst bs st
      (MEM_CST: mem_cst_blk m st b_cst)
      (WF_ST: wf st)
      (TO_BYTES: bs = to_bytes st)
  : Mem.loadbytes m b_cst 0 8 = Some (inj_bytes bs).
Proof.
  subst bs.
  inv WF_ST.
  inv MEM_CST. ss. des.

  replace 8 with (1 + 7) by ss.
  rewrite rw_cons_app.
  eapply Mem.loadbytes_concat; try nia; ss.

  s. replace 7 with (1 + 6) by ss.
  rewrite rw_cons_app.
  eapply Mem.loadbytes_concat; try nia; ss.

  s. replace 6 with (1 + 5) by ss.
  rewrite rw_cons_app.
  eapply Mem.loadbytes_concat; try nia; ss.

  s. replace 5 with (1 + 4) by ss.
  rewrite rw_cons_app.
  eapply Mem.loadbytes_concat; try nia; ss.
Qed.



Lemma store_set_mode
      md m m' st b
      (MEM_CST: mem_cst_blk m st b)
      (STORE: Mem.store Mint8signed m b
                        0 (Vint (Int.repr (mode_to_Z md))) = Some m')
  : mem_cst_blk m' (set_mode md st) b.
Proof.
  destruct st as [md_p tout qb qe q].
  inv MEM_CST.
  unfold set_mode. ss.

  hexploit store_unchanged_on'; eauto.
  s. unfold mem_range. i.

  econs; s.
  - hexploit Mem.load_loadbytes.
    { eapply Mem.load_store_same in STORE.
      apply STORE. }
    clear. ss.
    intros (bs & LBS & VEQ).
    rewrite LBS. f_equal.
    apply Mem.loadbytes_length in LBS.
    destruct bs as [| mv []]; ss.
    f_equal.
    rewrite sign_ext_byte_range in VEQ.
    2: { destruct md; ss. }

    destruct mv; ss. f_equal.
    rewrite decode_val_signed_byte in VEQ.

    assert (MODE_TO_Z_EQ: mode_to_Z md = Byte.signed i).
    { apply Int_repr_eq_inv.
      { destruct md; ss. }
      { r. generalize (Byte.signed_range i).
        range_stac. }

      assert (AUX: forall x y, Vint x = Vint y -> x = y).
      { inversion 1. ss. }
      apply AUX. ss.
    }
    rewrite MODE_TO_Z_EQ.
    rewrite Byte.repr_signed. ss.
  - eapply Mem.loadbytes_unchanged_on; eauto.
    unfold mem_range.
    ii. nia.
  - eapply Mem.loadbytes_unchanged_on; eauto.
    unfold mem_range.
    ii. nia.
  - eapply Mem.loadbytes_unchanged_on; eauto.
    unfold mem_range.
    ii. nia.
  - eapply Mem.loadbytes_unchanged_on; eauto.
    unfold mem_range.
    ii. nia.
  - ii. eapply Mem.perm_store_1; eauto.
Qed.


Lemma init_zerobytes
  : of_bytes (List.repeat Byte.zero 8) = init.
Proof.
  unfold of_bytes, init. ss.
Qed.


Section MEMORY_INV.

  Variable ge: genv.

  Let fsymb (id: ident) (bpred: block -> Prop): Prop :=
    forall b (FIND_SYMB: Genv.find_symbol ge id = Some b),
      bpred b.

  Definition mem_cst (m: mem) (cst: CtrlState.t): Prop :=
    fsymb _state (mem_cst_blk m cst).

  Definition mem_grant (m: mem): Prop :=
    fsymb _grant_msg
          (fun b_gr => Mem.loadbytes m b_gr 0 8 =
                    Some (inj_bytes grant_msg)).

  Definition inv_ctrl
             (ast: CtrlState.t) (m: mem): Prop :=
    <<CST_WF: CtrlState.wf ast>> /\
    <<MEM_CST: mem_cst m ast>> /\
    <<MEM_GRANT: mem_grant m>>.

  Lemma mem_cst_unch
        ast m m'
        (MEM_CST : mem_cst m ast)
        (MEM_UNCH : Mem.unchanged_on (blocks_of ge [_state]) m m')
    : mem_cst m' ast.
  Proof.
    rr. rr in MEM_CST. i.
    hexploit MEM_CST.
    { apply FIND_SYMB. }
    inversion 1.

    assert (forall i, blocks_of ge [_state] b i).
    { unfold blocks_of. i.
      exists _state.
      split.
      * clear. ss. eauto.
      * apply FIND_SYMB.
    }

    econs;
      try by eapply Mem.loadbytes_unchanged_on; eauto.
    ii. eapply Mem.perm_unchanged_on; eauto.
  Qed.

  Lemma mem_cst_unch_diffblk
        ast m m' b
        (MEM_CST : mem_cst m ast)
        (MEM_UNCH : mem_changed_block b m m')
        (FSYMB: Genv.find_symbol ge _state <> Some b)
    : mem_cst m' ast.
  Proof.
    eapply mem_cst_unch; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    unfold blocks_of. i.
    simpl in *. des; ss.
    ii. subst. ss.
  Qed.

  Lemma mem_grant_unch
        m m'
        (MEM_GRANT : mem_grant m)
        (MEM_UNCH : Mem.unchanged_on (blocks_of ge [_grant_msg]) m m')
    : mem_grant m'.
  Proof.
    rr. rr in MEM_GRANT. i.
    hexploit MEM_GRANT.
    { apply FIND_SYMB. }
    i. eapply Mem.loadbytes_unchanged_on; eauto.
    unfold blocks_of.
    intros _ _.
    exists _grant_msg.
    splits.
    - clear. ss. eauto.
    - apply FIND_SYMB.
  Qed.

  Lemma mem_grant_unch_diffblk
        m m' b
        (MEM_CST : mem_grant m)
        (MEM_UNCH : mem_changed_block b m m')
        (FSYMB: Genv.find_symbol ge _grant_msg <> Some b)
    : mem_grant m'.
  Proof.
    eapply mem_grant_unch; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    unfold blocks_of. i.
    simpl in *. des; ss.
    ii. subst. ss.
  Qed.

  Lemma inv_ctrl_dep_app_blocks
    : forall (ast : CtrlState.t) (m m' : mem)
        (INV: inv_ctrl ast m)
        (MEM_UNCH: Mem.unchanged_on (blocks_of ge ctrl_gvar_ids) m m'),
      inv_ctrl ast m'.
  Proof.
    unfold inv_ctrl. i. des.
    splits.
    - ss.
    - eapply mem_cst_unch; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      unfold blocks_of. ss.
      i. des; ss.
      clarify. esplits; eauto.
    - eapply mem_grant_unch; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      unfold blocks_of. ss.
      i. des; ss.
      clarify.
      exists _grant_msg. esplits; eauto.
  Qed.

End MEMORY_INV.


Section MEM_INIT.

  Variable tid: nat.
  Variable cprog: Clight.program.

  (* Hypothesis CTRL_TASK_ID: (tid = 1 \/ tid = 2)%nat. *)
  Hypothesis CPROG_EQ: __guard__ (cprog = prog_ctrl (Z.of_nat tid)).
  (* Notation prog := (prog_of_clight (prog_ctrl (Z.of_nat tid))). *)
  (* Notation prog := (prog_of_clight cprog). *)
  Notation ge := (globalenv cprog).

  Let GENV_PROPS
    : genv_props (globalenv cprog)
                 (main_gvar_ilist tid ++ ctrl_gvar_ilist)
                 (main_gfun_ilist ++ ctrl_gfun_ilist)
                 (main_cenv_ilist ++ ctrl_cenv_ilist).
  Proof.
    rewrite CPROG_EQ.
    apply (genv_props_ctrl tid).
  Qed.

  Lemma inv_ctrl_init:
    forall (m_i : mem),
      Genv.init_mem cprog = Some m_i ->
      inv_ctrl ge CtrlState.init m_i.
  Proof.
    intros m_i INIT_MEM. r.
    split.
    { apply CtrlState.wf_init. }

    assert (DEFMAP: (prog_defmap cprog) ! _state = Some (Gvar v_state) /\
                    (prog_defmap cprog) ! _grant_msg = Some (Gvar v_grant_msg)).
    { rewrite CPROG_EQ.
      change (prog_defmap (prog_ctrl (Z.of_nat tid))) with
          (PTree.combine Linking.link_prog_merge
                         (prog_defmap prog_mw) (prog_defmap (ctrl.prog (Z.of_nat tid)))).
      do 2 rewrite PTree.gcombine by ss.
      split.
      - replace ((prog_defmap prog_mw) ! _state) with
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
      - replace ((prog_defmap prog_mw) ! _grant_msg) with
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
    destruct DEFMAP as [DEFMAP1 DEFMAP2].

    split.
    - (* ctrl_state *)
      intros b_cst FSYMB_CST.

      apply Genv.find_def_symbol in DEFMAP1.
      destruct DEFMAP1 as (b_cst' & FSYMB_CST' & FDEF_CST).

      replace (Genv.globalenv cprog) with
          (genv_genv (globalenv cprog)) in FSYMB_CST' by ss.
      fold fundef in FSYMB_CST'.
      rewrite FSYMB_CST in FSYMB_CST'.
      symmetry in FSYMB_CST'. inv FSYMB_CST'.

      eapply Genv.init_mem_characterization_gen in INIT_MEM.
      r in INIT_MEM.
      exploit INIT_MEM; eauto. s.
      intros (RANGE_PERM & PERM & LOAD & LOADBYTES).

      eapply loadbytes_mem_cst; cycle 2.
      + rewrite <- init_zerobytes. ss.
      + rewrite Z.max_l in RANGE_PERM by nia. ss.
      + rewrite Z.max_l in LOADBYTES by nia.
        rewrite LOADBYTES by ss.
        clear. ss.

    - intros b_gr FSYMB_GR.
      apply Genv.find_def_symbol in DEFMAP2.
      destruct DEFMAP2 as (b_gr' & FSYMB_GR' & FDEF_GR).

      replace (Genv.globalenv cprog) with
          (genv_genv (globalenv cprog)) in FSYMB_GR' by ss.
      fold fundef in FSYMB_GR'.
      rewrite FSYMB_GR in FSYMB_GR'.
      symmetry in FSYMB_GR'. clarify.

      eapply Genv.init_mem_characterization_gen in INIT_MEM.
      r in INIT_MEM.
      exploit INIT_MEM; eauto. s.
      intros (RANGE_PERM & PERM & LOAD & LOADBYTES).

      rewrite LOADBYTES by ss.
      ss.
  Qed.

End MEM_INIT.

Section SIM_FUNCS.
  Variable tid: nat.
  Variable cprog: Clight.program.
  Variable r: nat -> itree progE unit -> Clight.state -> Prop.

  (* Hypothesis CTRL_TASK_ID: (tid = 1 \/ tid = 2)%nat. *)
  (* Hypothesis CPROG_EQ: __guard__ (cprog = prog_ctrl (Z.of_nat tid)). *)
  Notation ge := (globalenv cprog).
  Notation prog := (prog_of_clight cprog).

  Hypothesis GENV_PROPS
    : genv_props ge
                 (main_gvar_ilist tid ++ ctrl_gvar_ilist)
                 (main_gfun_ilist ++ ctrl_gfun_ilist)
                 (main_cenv_ilist ++ ctrl_cenv_ilist).


  Definition idx_qs: nat := 20.

  Lemma sim_qrange_sanitize
        (itr: itree progE unit)
        (m: mem) (k: cont)
        (i: Z) (idx_ret: nat)
        (CALL_CONT: is_call_cont k)
        (RANGE_I: IntRange.sintz i)
        (SIM_RET:
           paco3 (_sim_itree prog) r
                 idx_ret itr
                 (Returnstate (Vint (Int.repr (qrange_sanitize i))) k m))
    : paco3 (_sim_itree prog) r
            (idx_ret + idx_qs)%nat itr
            (Callstate (Internal f_qrange_sanitize)
                       [Vint (Int.repr i)] k m).
  Proof.
    (* clear CPROG_EQ. *)
    unfold idx_qs.
    start_func.
    { econs. }
    ss.
    fw. fw. fw.
    { econs.
      - eval_comput.
        repr_tac. ss.
      - rewrite bool_val_of_bool. ss.
    }
    unfold qrange_sanitize in SIM_RET.

    destruct (Z.ltb_spec i 0).
    - s.
      fw.
      { econs. eval_comput. ss. }
      upd_lenv.
      fw. fw.
      { econs.
        - eval_comput. ss.
        - ss.
      }
      rewrite Int.eq_true. s.
      fw.
      { econs.
        - eval_comput. ss.
        - eval_comput. ss.
        - ss.
      }
      destruct (Z.leb_spec 0 i).
      { exfalso. nia. }
      rewrite andb_false_l in SIM_RET.

      red_idx idx_ret.
      rewrite call_cont_is_call_cont by ss.
      apply SIM_RET.
    - s.
      fw.
      { econs.
        eval_comput.
        repr_tac.
        instantiate (1:= if i <? 4 then Vtrue else Vfalse).
        destruct (Z.ltb_spec i 4); ss.
      }
      upd_lenv.
      fw. fw.
      { econs.
        - eval_comput. reflexivity.
        - instantiate (1:= (i <? 4)).
          clear. desf.
      }

      destruct (Z.leb_spec 0 i).
      2: { exfalso. nia. }

      unfold QSIZE in *.
      destruct (Z.ltb_spec i 4); ss.
      + (* safe value *)
        fw.
        { econs.
          - eval_comput. reflexivity.
          - eval_comput. reflexivity.
          - ss.
        }
        rewrite call_cont_is_call_cont by ss.
        red_idx idx_ret.
        apply SIM_RET.
      + (* return 0 *)
        fw.
        { econs.
          - eval_comput. reflexivity.
          - eval_comput. reflexivity.
          - ss.
        }
        rewrite call_cont_is_call_cont by ss.
        red_idx idx_ret.
        apply SIM_RET.
  Qed.


  Opaque idx_qs.
  Definition idx_aqi: nat := idx_qs + 20.

  Lemma sim_adv_qidx
        (itr: itree progE unit)
        (m: mem) (k: cont)
        (i: Z) (idx_ret: nat)
        (CALL_CONT: is_call_cont k)
        (RANGE_I: IntRange.sintz i)
        (SIM_RET:
           paco3 (_sim_itree prog) r
                 idx_ret itr
                 (Returnstate (Vint (Int.repr (adv_qidx i))) k m))
    : paco3 (_sim_itree prog) r
            (idx_ret + idx_aqi)%nat itr
            (Callstate (Internal f_adv_qidx)
                       [Vint (Int.repr i)] k m).
  Proof.
    (* clear CPROG_EQ. *)
    unfold idx_aqi.
    start_func.
    { econs. }
    simpl in *.

    fw. fw. fw. fw. fw.
    { econs.
      eval_comput.
      rewrite Int_add_repr_signed by range_stac.
      reflexivity. }
    upd_lenv.

    fw. fw.
    { econs.
      eval_comput.
      reflexivity. }
    upd_lenv.

    fw. fw.
    { hexploit (in_gfun_ilist _qrange_sanitize); [sIn|].
      i. des.
      econs; eauto.
      - ss.
      - eval_comput. rewrite FDEF_SYMB. ss.
      - eval_comput.
        reflexivity.
      - ss.
    }

    red_idx (idx_ret + 10 + idx_qs)%nat.
    replace (Int.repr (i + 1)) with
        (Int.repr (Int.signed (Int.repr (i + 1)))).
    2: { rewrite Int.repr_signed. ss. }

    eapply sim_qrange_sanitize; eauto.
    { ss. }
    { apply Int.signed_range. }

    fw. upd_lenv.
    fw. fw.
    { econs.
      - eval_comput.
        replace (qrange_sanitize (Int.signed (Int.repr (i + 1))))
          with (adv_qidx i).
        2: { unfold adv_qidx.
             unfold qrange_sanitize.

             destruct (Z.ltb_spec i Int.max_signed).
             - assert (IntRange.sintz (i + 1)).
               { range_stac. }
               rewrite Int.signed_repr by range_stac.
               ss.
             - assert (i = Int.max_signed).
               { r in RANGE_I.
                 nia. }
               subst i. ss.
        }
        reflexivity.
      - ss.
      - ss.
    }
    ss.

    rewrite call_cont_is_call_cont by ss.
    red_idx (idx_ret)%nat.
    apply SIM_RET.
  Qed.


  Opaque idx_aqi.

  Definition idx_chdev: nat := 30.

  Lemma sim_check_dev_id
        (itr: itree progE unit)
        (m: mem) (k: cont)
        (tid_dev: Z) (idx_ret: nat)
        (CALL_CONT: is_call_cont k)
        (RANGE_TID_DEV: IntRange.sintz tid_dev)
        (SIM_RET:
           paco3 (_sim_itree prog) r
                 idx_ret itr
                 (Returnstate (Val.of_bool (check_dev_id tid_dev)) k m))
    : paco3 (_sim_itree prog) r
            (idx_ret + idx_chdev)%nat itr
            (Callstate (Internal f_check_dev_id)
                       [Vint (Int.repr tid_dev)] k m).
  Proof.
    (* clear CPROG_EQ. *)
    unfold idx_chdev.
    start_func.
    { econs. }
    unfold check_dev_id in SIM_RET. ss.

    fw. fw. fw. fw. fw.
    { econs.
      - eval_comput.
        rewrite Int_eq_repr_signed by range_stac.
        reflexivity.
      - rewrite bool_val_of_bool. reflexivity.
    }
    change (Z.of_nat 3) with 3 in *.
    change (Z.of_nat 4) with 4 in *.
    change (Z.of_nat 5) with 5 in *.

    destruct (Z.eqb tid_dev 3).
    { (* tid_dev = 3 *)
      fw.
      { econs.
        eval_comput. reflexivity. }
      upd_lenv.
      fw. fw.
      { econs.
        { eval_comput. reflexivity. }
        ss. }
      rewrite Int.eq_false by ss.
      s.
      fw.
      { econs.
        eval_comput. reflexivity. }
      upd_lenv.
      fw. fw.
      { econs.
        eval_comput. reflexivity. }
      upd_lenv.
      fw. fw.
      { econs; ss.
        - eval_comput. ss.
        - ss. }

      ss.
      rewrite call_cont_is_call_cont by ss.

      red_idx idx_ret.
      eapply SIM_RET.
    }
    fw.
    { econs.
      eval_comput.
      rewrite Int_eq_repr_signed by range_stac.
      instantiate (1:= if tid_dev =? 4 then Vtrue else Vfalse).
      destruct (Z.eqb_spec tid_dev 4); ss.
    }
    upd_lenv.
    fw.

    destruct (Z.eqb tid_dev 4).
    { (* tid_dev = 4 *)
      fw.
      { econs.
        - eval_comput. reflexivity.
        - ss. }
      rewrite Int.eq_false by ss.
      s.
      fw.
      { econs.
        eval_comput. reflexivity. }
      upd_lenv.
      fw. fw.
      { econs.
        eval_comput. reflexivity. }
      upd_lenv.
      fw. fw.
      { econs; ss.
        - eval_comput. ss.
        - ss. }

      ss.
      rewrite call_cont_is_call_cont by ss.

      red_idx idx_ret.
      eapply SIM_RET.
    }

    fw.
    { econs.
      - eval_comput. ss.
      - ss. }
    rewrite Int.eq_true. s.

    fw.
    { econs.
      eval_comput.
      rewrite Int_eq_repr_signed by range_stac.
      instantiate (1:= if tid_dev =? 5 then Vtrue else Vfalse).
      destruct (Z.eqb_spec tid_dev 5); ss.
    }
    upd_lenv.
    fw.

    destruct (Z.eqb tid_dev 5).
    { (* tid_dev = 5 *)
      fw.
      { econs.
        eval_comput. reflexivity. }
      upd_lenv.
      fw. fw.
      { econs; ss.
        - eval_comput. ss.
        - ss. }

      ss.
      rewrite call_cont_is_call_cont by ss.
      red_idx idx_ret.
      eapply SIM_RET.
    }
    (* false *)
    fw.
    { econs. eval_comput. ss. }
    upd_lenv.
    fw. fw.
    { econs; ss.
      - eval_comput. ss.
      - ss. }
    s. rewrite call_cont_is_call_cont by ss.
    red_idx idx_ret.
    eapply SIM_RET.
  Qed.

End SIM_FUNCS.
