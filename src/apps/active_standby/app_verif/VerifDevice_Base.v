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

Import Clight Clightdefs.
Import ITreeNotations.
Import ActiveStandby.

Import DevState.

Set Nested Proofs Allowed.
(* Arguments app : simpl nomatch. *)
Local Transparent Archi.ptr64.
Local Opaque Z.of_nat Z.to_nat.

(* Arguments Nat.mul: simpl never. *)
Arguments Nat.mul: simpl never.

Opaque globalenv.

Local Open Scope Z.


Definition dev_gvar_ids := map fst dev_gvar_ilist.
Definition dev_gfun_ids := map fst dev_gfun_ilist.
Definition dev_cenv_ids := map fst dev_cenv_ilist.


Record mem_dst_blk (m: mem) (st: DevState.t) (b_cst: block): Prop :=
  MemDevState {
      mem_dst_owner_status:
        Mem.loadbytes m b_cst 0 1 =
        Some [Byte (Byte.repr (owner_status_to_Z (owner_status st)))] ;
      mem_dst_demand: Mem.loadbytes m b_cst 1 1 =
                      Some [Byte (Byte.repr (Z.of_nat (demand st)))] ;

      mem_dst_perm:
        Mem.range_perm m b_cst 0 2 Cur Writable;
    }.


Lemma store_set_owner_status
      (is_owner: bool) zown m m' st b
      (MEM_DST: mem_dst_blk m st b)
      (ZOWN: zown = if is_owner then 1 else 2)
      (STORE: Mem.store Mint8signed m b 0
                        (Vint (Int.repr zown)) = Some m')
  : mem_dst_blk m' (set_owner_status is_owner st) b.
Proof.
  destruct st as [own dmd].
  inv MEM_DST.
  unfold set_owner_status. ss.

  hexploit store_unchanged_on'; eauto.
  s. unfold mem_range. i.

  econs; s.
  - eapply Mem.loadbytes_store_same in STORE. ss.
    rewrite STORE.
    destruct is_owner; ss.
  - eapply Mem.loadbytes_unchanged_on; eauto.
    ii. nia.
  - ii. eapply Mem.perm_store_1; eauto.
Qed.

Lemma store_set_demand
      (new_dmd: nat) m m' st b
      (MEM_DST: mem_dst_blk m st b)
      (STORE: Mem.store Mint8signed m b 1
                        (Vint (Int.repr (Z.of_nat new_dmd))) = Some m')
  : mem_dst_blk m' (set_demand new_dmd st) b.
Proof.
  destruct st as [own dmd].
  inv MEM_DST.
  unfold set_owner_status. ss.

  hexploit store_unchanged_on'; eauto.
  s. unfold mem_range. i.

  econs; s.
  - eapply Mem.loadbytes_unchanged_on; eauto.
    ii. nia.
  - eapply Mem.loadbytes_store_same in STORE. ss.
    rewrite STORE.
    unfold inj_bytes, encode_int. s.
    rewrite rev_if_be_single. s.
    do 3 f_equal.

    symmetry.
    apply signed_byte_int_unsigned_repr_eq.
  - ii. eapply Mem.perm_store_1; eauto.
Qed.

Lemma reduce_demand_eq
      st
  : reduce_demand st = set_demand (pred (demand st)) st.
Proof.
  destruct st; ss.
Qed.


Section MEMORY_INV.

  Variable ge: genv.

  Let fsymb (id: ident) (bpred: block -> Prop): Prop :=
    forall b (FIND_SYMB: Genv.find_symbol ge id = Some b),
      bpred b.

  Definition mem_dst (m: mem) (dst: DevState.t): Prop :=
    fsymb _state (mem_dst_blk m dst).

  Definition mem_acq (m: mem): Prop :=
    fsymb _acq_msg
          (fun b_acq => Mem.loadbytes m b_acq 0 8 =
                     Some (inj_bytes acq_msg)).

  Definition mem_rel (m: mem): Prop :=
    fsymb _rel_msg
          (fun b_rel => Mem.loadbytes m b_rel 0 8 =
                     Some (inj_bytes rel_msg)).

  Definition inv_dev
             (ast: DevState.t) (m: mem): Prop :=
    <<DST_WF: DevState.wf ast>> /\
    <<MEM_DST: mem_dst m ast>> /\
    <<MEM_ACQ: mem_acq m>> /\
    <<MEM_REL: mem_rel m>>.

  Lemma mem_dst_unch
        ast m m'
        (MEM_DST : mem_dst m ast)
        (MEM_UNCH : Mem.unchanged_on (blocks_of ge [_state]) m m')
    : mem_dst m' ast.
  Proof.
    rr. rr in MEM_DST. i.
    hexploit MEM_DST.
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

  Lemma mem_dst_unch_diffblk
        ast m m' b
        (MEM_DST : mem_dst m ast)
        (MEM_UNCH : mem_changed_block b m m')
        (FSYMB: Genv.find_symbol ge _state <> Some b)
    : mem_dst m' ast.
  Proof.
    eapply mem_dst_unch; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    unfold blocks_of. i.
    simpl in *. des; ss.
    ii. subst. ss.
  Qed.

  Lemma mem_acq_unch
        m m'
        (MEM_ACQ : mem_acq m)
        (MEM_UNCH : Mem.unchanged_on (blocks_of ge [_acq_msg]) m m')
    : mem_acq m'.
  Proof.
    rr. rr in MEM_ACQ. i.
    hexploit MEM_ACQ.
    { apply FIND_SYMB. }
    i. eapply Mem.loadbytes_unchanged_on; eauto.
    unfold blocks_of.
    intros _ _.
    exists _acq_msg.
    splits.
    - clear. ss. eauto.
    - apply FIND_SYMB.
  Qed.

  Lemma mem_acq_unch_diffblk
        m m' b
        (MEM_DST : mem_acq m)
        (MEM_UNCH : mem_changed_block b m m')
        (FSYMB: Genv.find_symbol ge _acq_msg <> Some b)
    : mem_acq m'.
  Proof.
    eapply mem_acq_unch; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    unfold blocks_of. i.
    simpl in *. des; ss.
    ii. subst. ss.
  Qed.

  Lemma mem_rel_unch
        m m'
        (MEM_REL : mem_rel m)
        (MEM_UNCH : Mem.unchanged_on (blocks_of ge [_rel_msg]) m m')
    : mem_rel m'.
  Proof.
    rr. rr in MEM_REL. i.
    hexploit MEM_REL.
    { apply FIND_SYMB. }
    i. eapply Mem.loadbytes_unchanged_on; eauto.
    unfold blocks_of.
    intros _ _.
    exists _rel_msg.
    splits.
    - clear. ss. eauto.
    - apply FIND_SYMB.
  Qed.

  Lemma mem_rel_unch_diffblk
        m m' b
        (MEM_DST : mem_rel m)
        (MEM_UNCH : mem_changed_block b m m')
        (FSYMB: Genv.find_symbol ge _rel_msg <> Some b)
    : mem_rel m'.
  Proof.
    eapply mem_rel_unch; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    unfold blocks_of. i.
    simpl in *. des; ss.
    ii. subst. ss.
  Qed.

  Lemma inv_dev_dep_app_blocks
    : forall (ast : DevState.t) (m m' : mem)
        (INV: inv_dev ast m)
        (MEM_UNCH: Mem.unchanged_on (blocks_of ge dev_gvar_ids) m m'),
      inv_dev ast m'.
  Proof.
    unfold inv_dev. i. des.
    splits.
    - ss.
    - eapply mem_dst_unch; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      unfold blocks_of. ss.
      i. des; ss.
      clarify. esplits; eauto.
    - eapply mem_acq_unch; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      unfold blocks_of. ss.
      i. des; ss.
      clarify.
      exists _acq_msg. esplits; eauto.
    - eapply mem_rel_unch; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      unfold blocks_of. ss.
      i. des; ss.
      clarify.
      exists _rel_msg. esplits; eauto.
  Qed.

End MEMORY_INV.


Section MEM_INIT.

  Variable tid: nat.
  Variable cprog: Clight.program.

  Hypothesis CPROG_EQ: __guard__ (cprog = prog_dev (Z.of_nat tid)).
  Notation ge := (globalenv cprog).

  Let GENV_PROPS
    : genv_props (globalenv cprog)
                 (main_gvar_ilist tid ++ dev_gvar_ilist)
                 (main_gfun_ilist ++ dev_gfun_ilist)
                 (main_cenv_ilist ++ dev_cenv_ilist).
  Proof.
    rewrite CPROG_EQ.
    apply (genv_props_dev tid).
  Qed.

  Lemma inv_dev_init:
    forall (m_i : mem),
      Genv.init_mem cprog = Some m_i ->
      inv_dev ge DevState.init m_i.
  Proof.
    intros m_i INIT_MEM. r.
    split.
    { apply DevState.wf_init. }

    assert (DEFMAP: (prog_defmap cprog) ! _state = Some (Gvar v_state) /\
                    (prog_defmap cprog) ! _acq_msg = Some (Gvar v_acq_msg) /\
                    (prog_defmap cprog) ! _rel_msg = Some (Gvar v_rel_msg)).
    { rewrite CPROG_EQ.
      change (prog_defmap (prog_dev (Z.of_nat tid))) with
          (PTree.combine Linking.link_prog_merge
                         (prog_defmap prog_mw) (prog_defmap (dev.prog (Z.of_nat tid)))).
      do 3 rewrite PTree.gcombine by ss.
      splits.
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
      - replace ((prog_defmap prog_mw) ! _acq_msg) with
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
      - replace ((prog_defmap prog_mw) ! _rel_msg) with
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
    destruct DEFMAP as (DEFMAP1 & DEFMAP2 & DEFMAP3).

    splits.
    - (* dev_state *)
      intros b_dst FSYMB_DST.

      apply Genv.find_def_symbol in DEFMAP1.
      destruct DEFMAP1 as (b_dst' & FSYMB_DST' & FDEF_DST).

      replace (Genv.globalenv cprog) with
          (genv_genv (globalenv cprog)) in FSYMB_DST' by ss.
      fold fundef in FSYMB_DST'.
      rewrite FSYMB_DST in FSYMB_DST'.
      symmetry in FSYMB_DST'. inv FSYMB_DST'.

      eapply Genv.init_mem_characterization_gen in INIT_MEM.
      r in INIT_MEM.
      exploit INIT_MEM; eauto. s.
      intros (RANGE_PERM & PERM & LOAD & LOADBYTES).

      hexploit LOADBYTES; eauto.
      rewrite Z.max_l by ss.
      replace (Z.to_nat 2) with 2%nat by ss.
      rewrite app_nil_r. s.
      replace 2 with (1 + 1) by ss.

      clear LOADBYTES. intro LOADBYTES.
      apply Mem_loadbytes_split' in LOADBYTES; try nia.
      des; ss.

    - intros b FSYMB.
      apply Genv.find_def_symbol in DEFMAP2.
      destruct DEFMAP2 as (b' & FSYMB' & FDEF).

      replace (Genv.globalenv cprog) with
          (genv_genv (globalenv cprog)) in FSYMB' by ss.
      fold fundef in FSYMB'.
      rewrite FSYMB in FSYMB'.
      symmetry in FSYMB'. clarify.

      eapply Genv.init_mem_characterization_gen in INIT_MEM.
      r in INIT_MEM.
      exploit INIT_MEM; eauto. s.
      intros (RANGE_PERM & PERM & LOAD & LOADBYTES).

      rewrite LOADBYTES by ss.
      ss.
    - intros b FSYMB.
      apply Genv.find_def_symbol in DEFMAP3.
      destruct DEFMAP3 as (b' & FSYMB' & FDEF).

      replace (Genv.globalenv cprog) with
          (genv_genv (globalenv cprog)) in FSYMB' by ss.
      fold fundef in FSYMB'.
      rewrite FSYMB in FSYMB'.
      symmetry in FSYMB'. clarify.

      eapply Genv.init_mem_characterization_gen in INIT_MEM.
      r in INIT_MEM.
      exploit INIT_MEM; eauto. s.
      intros (RANGE_PERM & PERM & LOAD & LOADBYTES).

      rewrite LOADBYTES by ss.
      ss.
  Qed.

End MEM_INIT.
