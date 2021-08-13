From ITree Require Import ITree.
From compcert Require Coqlib.
From Paco Require Import paco.

Require Import List.
Require Import Arith ZArith Lia.

Require Import Relation_Operators.

Require Import sflib.
Require Import Axioms StdlibExt IntegersExt.

Require Import SysSem.
Require Import IPModel DiscreteTimeModel.
Require Import NWSysModel.
Require Import RTSysEnv.
Require Import SyncSysModel AbstAsyncSysModel.

Require Import MSteps.
Require Import FMSim.

Set Nested Proofs Allowed.


Lemma match_inbox_rowmsg
      inb_t1 inb_s1
      (MATCH_INBS: opt2list inb_s1 = inb_t1)
  : AANode.choose_inbox_rowmsg inb_t1 inb_s1.
Proof.
  destruct inb_s1; ss; clarify.
  - econs. ss. eauto.
  - econs.
Qed.

Lemma match_inbox_rowmsg_det
      inb_t1 inb_s1 inb_s2
      (MATCH_INBS: opt2list inb_s1 = inb_t1)
      (ROWMSG: AANode.choose_inbox_rowmsg inb_t1 inb_s2)
  : inb_s1 = inb_s2.
Proof.
  destruct inb_s1, inb_s2; ss; clarify.
  - inv ROWMSG. ss.
    des; clarify.
  - inv ROWMSG.
  - inv ROWMSG. ss.
Qed.

Lemma match_inbox_rowmsgs
      inb_t inb_s
      (MATCH_INBS: map opt2list inb_s = inb_t)
  : Forall2 AANode.choose_inbox_rowmsg inb_t inb_s.
Proof.
  rewrite Forall2_nth. i.
  destruct (nth_error inb_s n) as [omsg|] eqn: INB_S_N.
  2: {
    rewrite nth_error_None2.
    2: { subst inb_t. rewrite map_length.
         apply nth_error_None. ss. }
    econs.
  }
  subst inb_t.
  rewrite Coqlib.list_map_nth.
  rewrite INB_S_N. ss.
  econs.
  destruct omsg as [msg|]; ss.
  - econs. ss. eauto.
  - econs.
Qed.

Lemma match_inbox_rowmsgs_det
      inb_t inb_s inb_s'
      (MATCH_INBS: map opt2list inb_s = inb_t)
      (ROWMSGS: Forall2 AANode.choose_inbox_rowmsg inb_t inb_s')
  : inb_s' = inb_s.
Proof.
  apply nth_eq_list_eq. i.
  rewrite Forall2_nth in ROWMSGS.
  specialize (ROWMSGS n).
  inv ROWMSGS.
  - rewrite Coqlib.list_map_nth in *.
    rewrite nth_error_None2; ss.
    apply nth_error_None.
    destruct (nth_error inb_s n); ss.
  - rewrite Coqlib.list_map_nth in *.
    destruct (nth_error inb_s n); ss.
    f_equal. symmetry.
    eapply match_inbox_rowmsg_det; eauto.
    clarify.
Qed.





Section PROOF.
  Context {sysE: Type -> Type}.
  (* Context `{rnws_params}. *)
  Context `{SystemEnv}.

  Variable nodes: list (@SNode.t sysE bytes).
  Let num_nodes: nat := length nodes.

  Variable mcasts_src: list (list Tid).
  Variable tm_init: nat.
  Hypothesis TM_INIT_COND: period <= tm_init.

  Hypothesis NUM_TASKS_EQ: num_nodes = num_tasks.
  Hypothesis MCASTS_EQ: map snd mcasts = mcasts_src.

  Definition rsz_bmsg (bs: bytes): bytes? :=
    Some (resize_bytes msg_size bs).

  Let sync_sys: SyncSys.t :=
    SyncSys.mk period nodes mcasts_src rsz_bmsg.

  Let sys_src := SyncSys.as_dsys
                   sync_sys (* (tm_init + max_clock_skew). *)
                   tm_init.
  Let sys_tgt := AASys.as_dsys nodes tm_init.

  Inductive match_ist
            (node: @SNode.t sysE bytes)
    : (SNode.app_state node)? ->
      (nat * AANode.stage_t * SNode.app_state node)? -> Prop :=
  | MatchIst_None
    : match_ist node None None
  | MatchIst_SomeIst
      oast ocnt stg ast
      (OCNT_UB: ocnt <= num_tasks)
      (MATCH: oast = match stg with
                     | AANode.Done => Some ast
                     | _ => None
                     end)
    : match_ist node oast (Some (ocnt, stg, ast))
  .

  Inductive match_lst
    : @SNode.state sysE bytes -> @AANode.state sysE -> Prop :=
  | MatchLst
      tid node inb_s inb_t
      oast oist
      (TID_UB: tid < num_tasks)
      (LEN_INB: length inb_s = num_tasks)
      (MATCH_INBS: map opt2list inb_s = inb_t)
      (MATCH_IST: match_ist node oast oist)
    : match_lst (SNode.State tid node inb_s oast)
                (AANode.State tid node inb_t oist).

  Inductive interm_ist {node: @SNode.t sysE bytes}
            (sytm: nat) (outb: list bytes?) (ticks: nat)
    : SNode.app_state node -> AANode.istate_t node -> Prop :=
  | IntermIst_Running
      ast' ocnt' sh
      (OCNT_UB': ocnt' <= num_tasks)
      (* (TICKS_UB: ticks < period * DTime.units_per_ns) *)
      (SEND_HIST: map (fun (omsg: bytes?) => (omsg: bool)) outb = sh)
    : interm_ist sytm outb ticks
                 ast' (ocnt', AANode.Running sytm sh, ast')
  | IntermIst_Done
      ast' ocnt'
      (OCNT_UB': ocnt' <= num_tasks)
      (* (TAU_STEPS: clos_refl_trans *)
      (*               _ node.(SNode.app_step) ast' ast_f) *)
      (PERIOD_END: SNode.period_end node ast')
    : interm_ist sytm outb ticks
                 ast' (ocnt', AANode.Done, ast')
  .

  Inductive sync_steps
            (sytm: nat) (node: @SNode.t sysE bytes)
            (* (inb: list bytes?) *)
            (inbc: list (list bytes)) (ticks: nat)
    : (AANode.istate_t node)? -> events sysE -> list bytes? ->
      (AANode.istate_t node)? -> Prop :=
  | SyncSteps_OffBeforeBegin
      oist (* outb *)
      (* (OUTB: Forall (fun x => x = None) outb) *)
      (* (OUTB: outb = repeat None num_tasks) *)
    : sync_steps sytm node inbc ticks
                 oist [] [] None

  | SyncSteps_TurnOn
      ocnt ast
      (OCNT_UB: ocnt <= num_tasks)
      (INIT_AST: SNode.init_app_state node ast)
    : sync_steps sytm node inbc ticks
                 None [] [] (Some (ocnt, AANode.Done, ast))
  | SyncSteps_Ready
      ocnt ast (* outb *)
      (* (OUTB: outb = repeat None num_tasks); *)
      (OCNT_UB: ocnt <= num_tasks)
      (* (TICKS_UB: ticks < period * DTime.units_per_ns) *)
    : sync_steps sytm node inbc ticks
                 (Some (ocnt, AANode.Done, ast)) [] []
                 (Some (ocnt, AANode.Ready sytm inbc, ast))
  | SyncSteps_Running
      ocnt ast es outb oist' inb
      ast_pi outb_i es_r oast'
      (OCNT_UB: ocnt <= num_tasks)
      (CHOOSE_MSG: Forall2 AANode.choose_inbox_rowmsg inbc inb)
      (AST_PINIT: SNode.period_begin node (Z.of_nat sytm) inb ast ast_pi)
      (OUTB_INIT: outb_i = repeat None num_tasks)
      (OUTB_LEN: length outb = num_tasks)
      (SNODE_ISTAR: SNode.istar
                      rsz_bmsg num_tasks mcasts_src node
                      (ast_pi, outb_i) es_r (oast', outb))
      (FILTER_NBS: deopt_list (map DSys.filter_nb1 es_r) =
                   Some es)
      (OPT_IST: option_rel2 (interm_ist sytm outb ticks)
                            oast' oist')
    : sync_steps sytm node inbc ticks
                 (Some (ocnt, AANode.Done, ast)) es outb oist'
  .

  Inductive tgtstep_inv
            (sytm: nat) (ticks: nat)
            (* (inb_s: list bytes?) *)
            (outbs: list (list bytes?))
    : @AANode.state sysE -> events sysE ->
      list bytes? -> @AANode.state sysE -> Prop :=
  | TgtstepInv_Init
      tid node inbn oist (* outb_i *)
      (TID_UB: tid < num_tasks)
      (INBN_LEN_UB: length inbn = num_tasks)
      (INBN_ROW_LEN_UB: Forall (fun row => length row <= 1) inbn)
      (TICKS_ZERO: ticks = 0)
      (* (OUTBS_I: outbs = repeat (repeat None num_tasks) num_tasks) *)
      (OUTBS_I: outbs = repeat [] num_tasks)
      (OCNT_UB_IF_EXISTS: option_rel1
                            (fun ist =>
                               let '(ocnt, _, _) := ist in
                               ocnt <= num_tasks) oist)
      (* (OUTB_I: outb_i = repeat None num_tasks) *)
      (* (MATCH_IST: match_ist node ( *)
      (*    option_rel1 (fun ist => exists ast', *)
    (*                              match_ist node ast' ist) oist) *)
    : tgtstep_inv sytm ticks (* inb_s *) outbs
                  (AANode.State tid node inbn oist)
                  [] (* outb_i *) []
                  (AANode.State tid node inbn oist)

  | TgtstepInv_Step
      tid node inbc inbn oist oist'
      es outb (* outb_s *)
      (TICKS_POS: 0 < ticks)
      (TID_UB: tid < num_tasks)
      (INBC_LEN_UB: length inbc = num_tasks)
      (INBC_ROW_LEN_UB: Forall (fun row => length row <= 1) inbc)
      (INBN: map (fun (bs1: list bytes?) =>
                    opt2list (nth tid bs1 None)) outbs = inbn)
      (SYNC_STEPS: sync_steps sytm node (* inb_s *) inbc
                              ticks oist es outb oist')
      (* (MATCH_OUTB: match_outb outb_s outb) *)
    : tgtstep_inv sytm ticks (* inb_s *) outbs
                  (AANode.State tid node inbc oist)
                  es outb
                  (AANode.State tid node inbn oist')
  .

  Inductive tgtstep_inv1
            (sytm: nat) (ticks: nat)
            (outbs: list (list bytes?))
    : @AANode.state sysE -> events sysE ->
      list bytes? -> @AANode.state sysE -> Prop :=
    TgtstepInv1
      tid node inbc inbn oist oist'
      es outb (* outb_s *)
      (TID_UB: tid < num_tasks)
      (INBC_LEN_UB: length inbc = num_tasks)
      (INBC_ROW_LEN_UB: Forall (fun row => length row <= 1) inbc)
      (INBN_TZERO: ticks = 0 -> outbs = repeat [] num_tasks)
      (INBN_TPOS: 0 < ticks ->
             map (fun (bs1: list bytes?) =>
                    opt2list (nth tid bs1 None)) outbs = inbn)
      (SYNC_STEPS: sync_steps sytm node inbc
                              ticks oist es outb oist')
      (* (MATCH_OUTB: match_outb outb_s outb) *)
    : tgtstep_inv1 sytm ticks outbs
                   (AANode.State tid node inbc oist) es outb
                   (AANode.State tid node inbn oist')
  .

  Lemma match_lst_tgtstep
        sytm
        (* tid snode inb_s oast *)
        st_src st_tgt
        (MATCH_LST: match_lst
                      (* (SNode.State tid snode inb_s oast) *)
                      st_src
                      st_tgt)
    : tgtstep_inv
        sytm 0
        (List.repeat
           (* (List.repeat None num_tasks) *) []
           num_tasks)
        st_tgt [] (* (List.repeat None num_tasks) *)
        [] st_tgt.
  Proof.
    inv MATCH_LST.
    econs 1; eauto.
    { rewrite map_length. ss. }
    { apply Forall_forall.
      intros bs IN_INB_S.
      rewrite in_map_iff in IN_INB_S. des.
      destruct x; ss; clarify; ss.
      nia.
    }

    inv MATCH_IST.
    - econs.
    - ss.
  Qed.

  Lemma get_outbox_eq
        tid outbs
    : map opt2list (map (SNode.get_outbox_msg_by_dest tid) outbs) =
      map (fun bs1 : list bytes ? => opt2list (nth tid bs1 None)) outbs.
  Proof.
    apply nth_eq_list_eq. i.
    repeat rewrite Coqlib.list_map_nth.
    unfold SNode.get_outbox_msg_by_dest.
    destruct (nth_error outbs n) as [outb|] eqn:OUTB.
    * ss.
      destruct (nth_error outb tid) eqn: OUTB_N.
      { erewrite nth_error_nth; eauto. }
      ss.
      rewrite nth_overflow; ss.
      apply nth_error_None. ss.
    * ss.
  Qed.



  Lemma tgtstep_nxt_match_lst
        sytm outbs zsytm
        st_i_src st_i_tgt es outb st_f_tgt
        (* tid node inb_s oast *)
        (OUTBS_LEN: length outbs = num_tasks)
        (MATCH_LST: match_lst st_i_src st_i_tgt)
        (* (ST_I_SRC: st_i_src = SNode.State tid node inb_s oast) *)
        (TGTSTEPS: tgtstep_inv
                     sytm (period * DTime.units_per_ns) outbs
                     st_i_tgt es outb st_f_tgt)
        (TIMESTAMP: zsytm = Z.of_nat sytm)
    : exists ess_src st_f_src (* outb_s *),
      <<STEP_SRC: SNode.step
                    rsz_bmsg num_tasks mcasts_src sytm
                    st_i_src ess_src outb st_f_src>> /\
      (* <<MATCH_OUTB: match_outb outb_s outb>> /\ *)
      <<NOT_NB: DSys.filter_nb_localstep (zsytm, ess_src) =
                Some (zsytm, es)>> /\
      <<MATCH_LST': match_lst (SNode.accept_msgs outbs st_f_src)
                              st_f_tgt>>.
  Proof.
    guardH NUM_TASKS_EQ. guardH MCASTS_EQ.
    inv MATCH_LST. existT_elim. clarify.
    inv TGTSTEPS.
    { exfalso.
      pose proof period_cond.
      pose proof DTime.units_per_ns_pos. nia. }
    existT_elim. clarify.

    inv SYNC_STEPS.
    - (* Off before begin *)
      exists [].
      esplits; eauto.
      + destruct oast.
        * econs 3; eauto. econs 1.
        * econs 1. eauto.
      + ss.
        econs; ss.
        * rewrite map_length. ss.
        * apply get_outbox_eq.
        * econs.

    - destruct oast as [?|]; ss.
      { inv MATCH_IST. }
      esplits; eauto.
      + econs 2; eauto.
      + ss.
      + econs; eauto.
        * rewrite map_length. ss.
        * apply get_outbox_eq.
        * econs; ss.

    - (* ready -> fail *)
      destruct oast as [ast'|]; inv MATCH_IST.
      clarify.

      esplits; ss.
      + econs 3; eauto. econs 1.
      + ss.
      + econs; ss.
        * rewrite map_length. ss.
        * apply get_outbox_eq.
        * econs; ss.
      + ss.

    - destruct oast as [ast'|]; inv MATCH_IST; ss.
      clarify.

      assert (inb = inb_s).
      { eapply match_inbox_rowmsgs_det; eauto. }
      subst inb.

      inv OPT_IST.
      + (* failed in the middle *)
        esplits; eauto.
        * econs 3; eauto. econs; eauto. econs.
        * unfold DSys.filter_nb_localstep. ss.
          rewrite FILTER_NBS. ss.
        * econs; eauto.
          { rewrite map_length. ss. }
          { apply get_outbox_eq. }
          { econs. }
      + (* Done successfully *)
        match goal with
        | H: interm_ist _ _ _ _ _ |- _ => inv H
        end.
        * (* running *)
          esplits; eauto.
          { econs 3; eauto.
            econs 2.
            - eauto.
            - eapply SNode.istar_snoc_fail; eauto.
            - econs.
          }
          { unfold DSys.filter_nb_localstep. ss.
            rewrite FILTER_NBS. ss. }
          { econs; ss.
            - rewrite map_length; ss.
            - apply get_outbox_eq.
            - econs; ss. }
        * (* done *)
          esplits; eauto.
          { econs; eauto.
            econs; eauto. }
          { unfold DSys.filter_nb_localstep. ss.
            rewrite FILTER_NBS. ss. }
          { econs; eauto.
            - rewrite map_length. ss.
            - apply get_outbox_eq.
            - econs; ss. }
  Qed.

  Definition rsz_dmsg (dmsg: Tid * bytes): Tid * bytes :=
    (fst dmsg, resize_bytes msg_size (snd dmsg)).

  Lemma inbox_size_bound
        inbn n
        (INB_LEN_UB: length inbn <= n)
        (ROW: Forall (fun r => length r <= 1) inbn)
    : AANode.inbox_sz inbn <= n.
  Proof.
    depgen n.
    induction inbn as [| h t IH]; i; ss.
    destruct n as [|n]; ss.
    { nia. }
    inv ROW.
    hexploit IH; eauto. i.
    unfold AANode.inbox_sz in *. ss.
    rewrite app_length. nia.
  Qed.


  Definition conv_tgtmsg (outb: list bytes?)
             (odm_src: (Tid * bytes)?)
    : (Tid * bytes)? :=
    match odm_src with
    | None => None
    | Some (tid_d, bs) =>
      if tid_d <? num_tasks + num_mcasts then
        let tids_ad := SNode.get_actual_dest num_tasks mcasts_src tid_d in
        if SNode.check_available tids_ad outb then
          Some (tid_d, resize_bytes msg_size bs)
        else None
      else None
    end.


  Lemma get_actual_dest_if_mcast
        mid midx mems
        (MID_EQ: mid = num_tasks + midx)
        (MEM: nth_error mcasts_src midx = Some mems)
    : SNode.get_actual_dest
        num_tasks mcasts_src mid = mems.
  Proof.
    unfold SNode.get_actual_dest.
    destruct (Nat.ltb_spec mid num_tasks).
    { nia. }
    subst mid.
    rewrite minus_plus. rewrite MEM. ss.
  Qed.


  Definition insert_sanitized_msg
             (outb: list bytes?)
             (odm_s: (Tid * bytes)?)
    : list bytes? :=
    match odm_s with
    | None => outb
    | Some (tid_d, bs) =>
      let tids_ad := SNode.get_actual_dest
                       num_tasks mcasts_src tid_d in
      SNode.insert_msg tids_ad bs outb
    end.

  Lemma check_available_spec
        (M: Set)
        adest (outb: list M?)
    : SNode.check_available adest outb = true <->
      Forall (fun tid => nth_error outb tid = Some None) adest.
  Proof.
    split.
    - unfold SNode.check_available.
      induction adest as [| h t IH].
      { i. ss. }
      intro CH.
      rewrite andb_all_true_iff in CH.
      econs.
      { ss.
        hexploit CH.
        { left. eauto. }
        unfold SNode.check_available1. desf.
      }
      apply IH.
      apply andb_all_true_iff. ss. eauto.

    - intro FA.
      unfold SNode.check_available.
      apply andb_all_true_iff.

      induction FA.
      { i. ss. }

      unfold SNode.check_available1 in *. ss.
      intros b IN. des.
      + desf.
      + eauto.
  Qed.

  Lemma get_msg_by_dest_cases
        tid adest tid_d msg
        (VALID_TID: tid < num_tasks)
        (ACTUAL_DEST: adest = SNode.get_actual_dest
                                num_tasks mcasts_src tid_d)
    : (SNode.is_in_tids tid adest = true /\
       AANode.get_msg_by_dest tid (Some (tid_d, msg)) = [msg]) \/
      (SNode.is_in_tids tid adest = false /\
       AANode.get_msg_by_dest tid (Some (tid_d, msg)) = []).
  Proof.
    unfold SNode.get_actual_dest in ACTUAL_DEST.
    destruct (Nat.ltb_spec tid_d num_tasks).
    { (* tid_d is a task id *)
      subst adest. ss.
      destruct (Nat.eqb_spec tid tid_d); ss.
      - (* eq *)
        subst tid. rewrite Nat.eqb_refl. ss.
        left. eauto.
      - (* neq *)
        right.
        destruct (Nat.eqb_spec tid_d tid); ss.
        { congruence. }
        split; ss.

        cut (existsb (Nat.eqb tid_d) (get_mcast_of tid) = false).
        { intro R. rewrite R. ss. }

        apply existsb_false_iff.
        eapply Forall_forall. intros mid MID_IN.
        eapply get_mcast_of_spec in MID_IN. des.
        destruct (Nat.eqb_spec tid_d mid); ss.
        nia.
    }
    (* tid_d may be an mcast_id *)
    destruct (nth_error mcasts_src (tid_d - num_tasks))
      as [mems|] eqn: MEMS.
    { subst adest.
      unfold SNode.is_in_tids.

      rewrite <- MCASTS_EQ in MEMS.
      rewrite map_nth_error_iff in MEMS. des.
      destruct a as [mip mems']. ss. subst.

      destruct (existsb (Nat.eqb tid) mems) eqn:TID_MEM.
      - left. ss.

        hexploit (member_impl_get_mcast_of tid_d); eauto.
        { nia. }
        { apply existsb_exists in TID_MEM. des.
          hexploit beq_nat_true; eauto.
          i. subst. eauto. }
        intro TID_D_IN.
        cut (existsb (Nat.eqb tid_d) (get_mcast_of tid) = true).
        { intro R. rewrite R.
          split; eauto. rewrite Bool.orb_true_r. ss. }

        apply existsb_exists.
        esplits.
        { eauto. }
        apply Nat.eqb_refl.
      - (* tid not member *)
        right. ss.
        cut (existsb (Nat.eqb tid_d) (get_mcast_of tid) = false).
        { intro R. rewrite R.
          split; eauto.
          destruct (Nat.eqb_spec tid_d tid); ss.
          nia. }
        apply existsb_false_iff.
        apply Forall_forall.
        intros mid MID_IN.
        eapply get_mcast_of_spec in MID_IN. des.
        destruct (Nat.eqb_spec tid_d mid); ss.
        subst tid_d. clarify.
        rewrite minus_plus in MEMS. clarify.
        rewrite <- TID_MEM.
        symmetry. eapply existsb_exists.
        esplits.
        { eauto. }
        eapply Nat.eqb_refl.
    }
    { (* invalid tid_d *)
      right.
      rewrite ACTUAL_DEST.
      split; ss.
      destruct (Nat.eqb_spec tid_d tid); ss.
      { subst. nia. }
      destruct (existsb (Nat.eqb tid_d) (get_mcast_of tid)) eqn: TID_D_IN_MCAST_OF; ss.
      eapply existsb_exists in TID_D_IN_MCAST_OF. des.
      hexploit beq_nat_true; eauto. i. subst.
      hexploit get_mcast_of_spec; eauto.
      i. des.
      subst.
      rewrite minus_plus in MEMS.
      rewrite Coqlib.list_map_nth in MEMS.
      rewrite MCAST_MEMBER in MEMS. ss.
    }
  Qed.


  Lemma insert_sanitized_msg_aux
        tid outb odm odm_t
        (TID_UB: tid < num_tasks)
        (CONV: odm_t = conv_tgtmsg outb odm)
        (OUTB_LEN: length outb = num_tasks)
    : opt2list (nth tid (insert_sanitized_msg outb odm_t) None) =
      opt2list (nth tid outb None) ++
               AANode.get_msg_by_dest tid odm_t.
  Proof.
    guardH NUM_TASKS_EQ. guardH MCASTS_EQ.
    hexploit (nth_error_Some2 _ outb tid).
    { nia. }
    i. des.
    renames e1 NTH_EX into outb_n OUTB_N.
    erewrite (nth_error_nth outb); eauto.

    destruct odm as [[tid_d msg]| ]; ss.
    2: { clarify. rewrite app_nil_r. ss.
         erewrite (nth_error_nth outb); eauto. }

    pose (adest := SNode.get_actual_dest
                     num_tasks mcasts_src tid_d).
    fold adest in CONV.

    destruct (Nat.ltb_spec tid_d (num_tasks + num_mcasts)) as [LT|GE].
    2: { subst odm_t. ss.
         rewrite app_nil_r.
         erewrite (nth_error_nth outb); eauto.
    }

    destruct (SNode.check_available adest outb) eqn: AVAILABLE.
    2: { clarify.
         rewrite app_nil_r. ss.
         erewrite (nth_error_nth outb); eauto. }

    pose (msg' := resize_bytes msg_size msg).
    subst odm_t.
    apply check_available_spec in AVAILABLE.

    hexploit (get_msg_by_dest_cases tid adest tid_d msg'); eauto.
    intros [[IN_ADEST GET_MSG_ONE] | [NOT_IN_ADEST GET_MSG_NIL]].
    - (* In *)
      fold msg'.
      rewrite GET_MSG_ONE. clear GET_MSG_ONE. ss.
      fold adest.
      rewrite Forall_forall in AVAILABLE.

      assert (IN_ADEST': In tid adest).
      { unfold SNode.is_in_tids in IN_ADEST.
        apply existsb_exists in IN_ADEST. des.
        hexploit beq_nat_true; eauto. i. subst.
        eauto. }

      assert (outb_n = None).
      { hexploit AVAILABLE; eauto.
        i. clarify. }
      subst outb_n.

      assert (INSERT_N: nth_error (SNode.insert_msg adest msg' outb) tid = Some (Some msg')).
      { unfold SNode.insert_msg.
        rewrite imap_nth_error_iff. ss.
        rewrite OUTB_N. ss. f_equal.
        unfold SNode.insert_msg1.
        rewrite IN_ADEST. ss.
      }
      erewrite nth_error_nth; eauto. ss.
    - (* not_in *)
      fold msg'.
      rewrite GET_MSG_NIL. clear GET_MSG_NIL.

      assert (INSERT_N: nth_error (SNode.insert_msg adest msg' outb) tid = Some outb_n).
      { unfold SNode.insert_msg.
        rewrite imap_nth_error_iff. ss.
        rewrite OUTB_N. ss. f_equal.
        unfold SNode.insert_msg1.
        rewrite NOT_IN_ADEST. ss.
      }

      erewrite nth_error_nth; eauto.
      rewrite app_nil_r. ss.
  Qed.

  Inductive upd_outbox_rel
    : list bytes? -> (Tid * bytes)? -> (Tid * bytes)? ->
      list bytes? -> Prop :=
  | UpdOutbox_Init
      outb_i
      (OUTB_I: outb_i = repeat None num_tasks)
    : upd_outbox_rel [] None None outb_i
  | UpdOutbox_Empty
    : upd_outbox_rel [] None None []
  | UpdOutbox_Cont
      outb odm_src odm_tgt outb'
      (OUTB_NONNIL: length outb = num_tasks)
      (CONV: conv_tgtmsg outb odm_src = odm_tgt)
      (INSERT: insert_sanitized_msg outb odm_tgt = outb')
      (* (UPDATE: SNode.update_outbox *)
      (*            rsz_bmsg num_tasks mcasts_src *)
      (*            outb odm = outb') *)
    : upd_outbox_rel outb odm_src odm_tgt outb'
  .


  Lemma conv_tgtmsg_spec
        outb odm odm_p
        (CONV: conv_tgtmsg outb odm = odm_p)
    : SNode.update_outbox
        rsz_bmsg num_tasks mcasts_src outb odm =
      insert_sanitized_msg outb odm_p.
  Proof.
    destruct odm as [[tid msg]|]; ss.
    2: { subst. ss. }
    pose (adest := SNode.get_actual_dest num_tasks mcasts_src tid).
    fold adest in CONV. fold adest.

    destruct (Nat.ltb_spec tid (num_tasks + num_mcasts)).
    2: {
      assert (ADEST_NIL: adest = []).
      { subst adest.
        unfold SNode.get_actual_dest.
        destruct (Nat.ltb_spec tid num_tasks).
        { nia. }
        rewrite nth_error_None2; eauto.
        rewrite <- MCASTS_EQ.
        rewrite map_length.
        rewrite <- num_mcasts_eq. nia.
      }
      rewrite ADEST_NIL.
      desf. ss.
      unfold SNode.insert_msg.

      apply nth_eq_list_eq. i.
      rewrite imap_nth_error_iff. ss.
      unfold SNode.insert_msg1. ss.
      destruct (nth_error outb n); ss.
    }

    destruct (SNode.check_available adest outb) eqn:CH_AV.
    2: { subst. ss. }
    subst odm_p. ss.
  Qed.


  Lemma process_outmsg_spec
        outb sh sh' odm odm_p
        (OUTB_LEN: length outb = num_tasks)
        (SEND_HIST: sh = map (fun omsg: bytes? => (omsg: bool)) outb)
        (PROC_OUTMSG: AANode.process_outmsg sh odm = (sh', odm_p))
    : conv_tgtmsg outb odm = odm_p /\
      sh' = map (fun omsg: bytes? => (omsg:bool))
                (insert_sanitized_msg outb odm_p).
  Proof.
    guardH NUM_TASKS_EQ. guardH MCASTS_EQ.

    destruct odm as [[tid msg]|]; ss.
    2: { inv PROC_OUTMSG.
         splits; eauto. }

    pose (adest := SNode.get_actual_dest num_tasks mcasts_src tid).
    fold adest.

    destruct (check_send_hist sh tid) as [sh''|] eqn:CH_SH.
    2: {
      inv PROC_OUTMSG.
      apply check_send_hist_None in CH_SH.
      2: { rewrite map_length. ss. }
      des.
      - (* invalid tid *)
        destruct (Nat.ltb_spec tid (num_tasks + num_mcasts)).
        { unfold valid_dest_id in *. nia. }
        ss.

      - (* unicast *)
        unfold valid_task_id in *.
        destruct (Nat.ltb_spec tid (num_tasks + num_mcasts)).
        2: { nia. }

        destruct (SNode.check_available adest outb) eqn:CH_AV.
        2: { esplits; ss. }

        exfalso.
        apply check_available_spec in CH_AV.
        rewrite Forall_forall in CH_AV.

        apply map_nth_error_iff in SEND_DONE. des.
        hexploit CH_AV.
        { subst adest.
          unfold SNode.get_actual_dest.
          destruct (Nat.ltb_spec tid num_tasks).
          2: { nia. }
          ss. eauto. }
        i. clarify.
        (* { eauto. } *)
        (* { i. subst. ss. } *)

      - (* multicast, invalid tid *)
        unfold valid_mcast_id in *. des.
        destruct (Nat.ltb_spec tid (num_tasks + num_mcasts)).
        2: { exfalso. nia. }
        ss. split; ss.

        destruct (SNode.check_available adest outb) eqn:CH_AV; ss.
        exfalso.
        apply check_available_spec in CH_AV.
        rewrite Forall_forall in CH_AV.

        hexploit (CH_AV tid_sent).
        { subst adest.
          unfold mcast_member in MEMBER.
          hexploit get_mcast_of_spec; eauto. i. des.
          erewrite get_actual_dest_if_mcast; eauto.
          rewrite <- MCASTS_EQ.
          rewrite map_nth_error_iff. esplits; eauto.
        }
        rewrite nth_error_None2.
        2: { rewrite OUTB_LEN.
             r in TID_INVALID.
             unfold valid_task_id in TID_INVALID. nia. }
        i. congruence.

      - (* multicast *)
        unfold valid_mcast_id in *.
        destruct (Nat.ltb_spec tid (num_tasks + num_mcasts)).
        2: { exfalso. des. nia. }
        clear DEST_MCAST_ID.

        destruct (SNode.check_available adest outb) eqn:CH_AV.
        2: { esplits; ss. }

        exfalso.
        apply check_available_spec in CH_AV.
        rewrite Forall_forall in CH_AV.

        apply map_nth_error_iff in SEND_DONE.
        unfold mcast_member in MEMBER. des.
        hexploit get_mcast_of_spec; eauto. i. des.

        hexploit CH_AV; eauto.
        { subst adest.
          unfold SNode.get_actual_dest.
          destruct (Nat.ltb_spec tid num_tasks).
          { exfalso. nia. }
          subst tid.
          rewrite minus_plus.
          rewrite <- MCASTS_EQ.
          erewrite map_nth_error; eauto. ss.
          eauto.
        }
        { i. clarify. }
    }

    eapply check_send_hist_Some in CH_SH.
    2: { subst sh.
         rewrite map_length. ss. }
    des.
    - (* valid task_id *)
      unfold valid_task_id in DEST_TASK_ID.
      destruct (Nat.ltb_spec tid (num_tasks + num_mcasts)).
      2: { nia. }

      inv PROC_OUTMSG.
      assert (ADEST: adest = [tid]).
      { subst adest.
        unfold SNode.get_actual_dest.
        destruct (Nat.ltb_spec tid num_tasks); ss.
        nia. }
      unfold insert_sanitized_msg.
      fold adest.
      rewrite ADEST in *.
      clear adest ADEST.

      apply map_nth_error_iff in SEND_AVAILABLE. des.
      assert (CH_AV: SNode.check_available [tid] outb = true).
      { apply check_available_spec.
        econs.
        2: { econs. }
        i. clarify.
        destruct a; ss.
      }
      rewrite CH_AV.
      split; ss.

      apply nth_eq_list_eq. i.
      destruct (lt_ge_dec n num_tasks).
      2: {
        rewrite Coqlib.list_map_nth.
        rewrite nth_error_None2 by nia.
        unfold SNode.insert_msg.
        rewrite imap_nth_error_iff. ss.
        rewrite nth_error_None2 by nia.
        ss.
      }
      unfold SNode.insert_msg.
      rewrite Coqlib.list_map_nth.
      rewrite imap_nth_error_iff. ss.

      destruct (Nat.eq_dec n tid).
      + subst n.
        rewrite SEND_AVAILABLE.
        rewrite UPD_HIST. ss.
        unfold SNode.insert_msg1. ss.
        rewrite Nat.eqb_refl. ss.
      + hexploit UPD_HIST_OTHERS; eauto.
        rewrite Coqlib.list_map_nth.
        intro SH'_N.
        unfold SNode.insert_msg1. ss.
        destruct (Nat.eqb_spec n tid); ss.
        rewrite SH'_N.
        destruct (nth_error outb n); ss.

    - (* valid mcast_id *)
      rename tid into mid.
      unfold valid_mcast_id in DEST_MCAST_ID.
      destruct (Nat.ltb_spec mid (num_tasks + num_mcasts)).
      2: { des. nia. }

      inv PROC_OUTMSG.
      des.
      assert (exists mems,
                 <<MEMBERS: nth_error mcasts_src midx = Some mems>> /\
                 <<ADEST_EQ: adest = mems>>).
      { assert (MEMS: exists mems, nth_error mcasts_src midx = Some mems).
        { eapply Some_not_None.
          apply nth_error_Some.
          rewrite <- MCASTS_EQ.
          rewrite map_length.
          rewrite <- num_mcasts_eq. ss. }
        des. esplits; eauto.
        subst adest.

        erewrite get_actual_dest_if_mcast; eauto.
      }
      des.
      unfold insert_sanitized_msg.
      fold adest.
      rewrite ADEST_EQ in *.
      clear adest ADEST_EQ.

      rewrite <- MCASTS_EQ in MEMBERS.
      apply map_nth_error_iff in MEMBERS. des.
      destruct a as [mip mems']. ss. subst.

      assert (CH_AV: SNode.check_available mems outb = true).
      { apply check_available_spec.
        apply Forall_forall.
        intros tid1 IN1.

        hexploit (UPD_HIST tid1).
        (* { r. rewrite <- OUTB_LEN. *)
        (*   apply nth_error_Some. congruence. } *)
        { r. eapply member_impl_get_mcast_of; eauto. }
        intros (VALID_TID & OUTB_TID1 & SH'_TID1).
        rewrite map_nth_error_iff in OUTB_TID1. des.
        (* clarify. *)
        (* destruct outb1; ss. *)
        destruct a; ss.
      }
      rewrite CH_AV.
      split; ss.

      apply nth_eq_list_eq. i.
      destruct (lt_ge_dec n num_tasks).
      2: {
        rewrite Coqlib.list_map_nth.
        rewrite nth_error_None2 by nia.
        unfold SNode.insert_msg.
        rewrite imap_nth_error_iff. ss.
        rewrite nth_error_None2 by nia.
        ss.
      }
      unfold SNode.insert_msg.
      rewrite Coqlib.list_map_nth.
      rewrite imap_nth_error_iff. ss.
      unfold SNode.insert_msg1.

      destruct (SNode.is_in_tids n mems) eqn:N_MEMS.
      + hexploit UPD_HIST; eauto.
        { r. eapply member_impl_get_mcast_of; eauto.
          unfold SNode.is_in_tids in N_MEMS.
          eapply existsb_exists in N_MEMS. des.
          hexploit beq_nat_true; eauto.
          i. clarify. eauto. }
        intros (VALID_N & OUTB_N & SH'_N).
        apply map_nth_error_iff in OUTB_N. des.
        destruct (nth_error outb n); ss.
      + hexploit (UPD_HIST_OTHERS n); eauto.
        { unfold mcast_member.
          intro IN.
          eapply get_mcast_of_spec in IN. des.
          assert (midx0 = midx) by nia.
          subst midx0.
          clarify.

          unfold SNode.is_in_tids in N_MEMS.
          eapply existsb_false_iff in N_MEMS.
          rewrite Forall_forall in N_MEMS.
          hexploit N_MEMS; eauto.
          rewrite Nat.eqb_refl. ss.
        }
        intro SH'_N.
        rewrite Coqlib.list_map_nth in SH'_N.
        rewrite SH'_N.
        destruct (nth_error outb n); ss.
  Qed.


  Lemma actual_dest_mcast_member
        tid_ad mid
        (MCAST_ID : valid_mcast_id mid)
    : In tid_ad (SNode.get_actual_dest
                   num_tasks mcasts_src mid) <->
      mcast_member tid_ad mid.
  Proof.
    unfold SNode.get_actual_dest.
    r in MCAST_ID. des.
    destruct (Nat.ltb_spec mid num_tasks); ss.
    { nia. }
    unfold mcast_member.
    split.
    - destruct (nth_error mcasts_src (mid - num_tasks))
        as [mems|] eqn: MEMS; ss.
      intro TID_AD_IN_MEMS.

      rewrite <- MCASTS_EQ in MEMS.
      rewrite map_nth_error_iff in MEMS. des; ss.
      destruct a as [mip mems']. ss. clarify.
      replace midx with (num_tasks + midx - num_tasks) by nia.
      eapply member_impl_get_mcast_of; eauto.
    - intro IN_MCAST_OF.
      apply get_mcast_of_spec in IN_MCAST_OF.
      i. des.

      assert (midx0 = midx) by nia.
      subst midx0.
      replace (mid - num_tasks) with midx by nia.
      rewrite <- MCASTS_EQ.
      rewrite Coqlib.list_map_nth.
      rewrite MCAST_MEMBER. ss.
  Qed.

  Lemma actual_dest_tid
        tid
        (TASK_ID : valid_task_id tid)
    : SNode.get_actual_dest
        num_tasks mcasts_src tid = [tid].
  Proof.
    unfold SNode.get_actual_dest.
    r in TASK_ID.
    destruct (Nat.ltb_spec tid num_tasks); ss.
    nia.
  Qed.

  Lemma actual_dest_invalid
        tid
        (INVALID_DEST: ~ valid_dest_id tid)
    : SNode.get_actual_dest
        num_tasks mcasts_src tid = [].
  Proof.
    unfold SNode.get_actual_dest.
    unfold valid_dest_id in *.
    destruct (Nat.ltb_spec tid num_tasks); ss.
    { nia. }
    rewrite nth_error_None2.
    2: { rewrite <- MCASTS_EQ.
         rewrite map_length.
         rewrite <- num_mcasts_eq. nia. }
    ss.
  Qed.


  Lemma check_send_hist_iff_check_available
        sh tid outb
        (LEN_OUTB: length outb = num_tasks)
        (VALID_DEST: valid_dest_id tid)
        (SEND_HIST: map (fun (omsg: bytes?) => (omsg: bool)) outb = sh)
    : (check_send_hist sh tid: bool) =
      SNode.check_available
        (SNode.get_actual_dest
           num_tasks (map snd mcasts) tid) outb.
  Proof.
    destruct (check_send_hist sh tid) as [sh'|]eqn: CHK_SH.
    - s. symmetry.
      apply check_available_spec.

      hexploit check_send_hist_Some; eauto.
      { subst sh. rewrite map_length. ss. }
      i. des.
      + unfold SNode.get_actual_dest.
        destruct (Nat.ltb_spec tid num_tasks); ss.
        2: { exfalso.
             eapply nth_error_Some1' in SEND_AVAILABLE.
             subst sh. rewrite map_length in *. nia. }
        econs.
        2: { econs. }
        subst sh.
        rewrite map_nth_error_iff in SEND_AVAILABLE.
        des; ss.
        destruct a; ss.
      + s. rewrite MCASTS_EQ.

        apply Forall_forall. intros x IN.
        eapply actual_dest_mcast_member in IN; eauto.
        hexploit UPD_HIST; eauto.
        intros (VALID_TID_AD & SH_AD & SH'_AD).
        subst sh.
        apply map_nth_error_iff in SH_AD. des.
        destruct a; ss.

    - s. symmetry.
      match goal with
      | |- ?x = _ => destruct x eqn: CHK_AVL; ss
      end.

      apply check_available_spec in CHK_AVL.
      rewrite MCASTS_EQ in CHK_AVL.

      hexploit check_send_hist_None; eauto.
      { subst sh. rewrite map_length. nia. }
      i. des.
      + ss.
      + rewrite actual_dest_tid in CHK_AVL by ss.
        inv CHK_AVL.
        apply map_nth_error_iff in SEND_DONE. des; ss.
        destruct a; ss; clarify.
      + rewrite Forall_forall in CHK_AVL.
        apply actual_dest_mcast_member in MEMBER; ss.
        hexploit CHK_AVL; eauto.
        intro NTH_SOME.
        apply nth_error_Some1' in NTH_SOME.
        r in TID_INVALID.
        hexploit TID_INVALID.
        { r. nia. }
        ss.
      + rewrite Forall_forall in CHK_AVL.
        apply actual_dest_mcast_member in MEMBER; ss.
        hexploit CHK_AVL; eauto.
        intro NTH_SOME.
        subst sh.
        apply map_nth_error_iff in SEND_DONE. des.
        destruct a; ss. clarify.
  Qed.

  Lemma SNode_insert_msg_no_dest (msgT: Set)
        ms (outb: list msgT?)
    : SNode.insert_msg [] ms outb = outb.
  Proof.
    unfold SNode.insert_msg.
    unfold SNode.insert_msg1. ss.
    generalize 0.
    induction outb; i; ss.
    rewrite IHoutb. ss.
  Qed.

  Lemma tau_steps_istar
        (node: @SNode.t sysE bytes) sntz
        sh outb1 ast1 ast2
        (* oe om *) (* ast' outb' *)
        (SH_LEN: length sh = num_tasks)
        (SEND_HIST: map (fun (omsg: bytes?) => (omsg: bool)) outb1 = sh)
        (TAU_STEPS: AANode.sh_tau_steps sh node ast1 ast2)
        (* (STEP: SNode.istep node ast2 oe om ast') *)
        (* (OUTB': outb' = SNode.update_outbox *)
        (*                   sntz num_tasks mcasts_src outb1 om) *)
    : SNode.istar sntz num_tasks mcasts_src node
            (ast1, outb1) (* (opt2list oe) *) []
            (* (Some ast', outb'). *)
            (Some ast2, outb1).
  Proof.
    (* apply Operators_Properties.clos_rt_rt1n in TAU_STEPS. *)
    induction TAU_STEPS.
    - econs 2.
    - econs 3.
      { econs 1; eauto. }
      { eauto. }
      { eauto. }
      { ss. }
    - econs 3.
      { econs 3; eauto. }
      { eauto. }
      { s. rewrite <- MCASTS_EQ.
        destruct (lt_ge_dec tid (num_tasks + num_mcasts)).
        - erewrite <- check_send_hist_iff_check_available; cycle 1.
          { subst sh. rewrite map_length in SH_LEN. ss. }
          { ss. }
          { eauto. }
          rewrite OUTMSGS. s.
          rewrite MCASTS_EQ.
          destruct (sntz msg); eauto.
        - rewrite MCASTS_EQ.
          rewrite actual_dest_invalid. ss.
          destruct (sntz msg).
          + rewrite SNode_insert_msg_no_dest.
            eauto.
          + eauto.
          + unfold valid_dest_id. nia.
      }
      ss.
  Qed.


  Lemma tgtstep_inv_localstep
        sytm ticks outbs
        st_i es_acc outb st
        tes1 odm_tgt st1
        tsp1 es1
        (SYTM_SYNC: Nat.divide period sytm)
        (SYTM_LB: period <= sytm)
        (TICKS_UB: ticks < period * DTime.units_per_ns)
        (INV: tgtstep_inv sytm ticks outbs
                          st_i es_acc outb st)
        (STEP: AANode.step (DTime.uadd (DTime.of_ns (sytm - max_clock_skew)) ticks)
                           st tes1 odm_tgt st1)
        (NOT_NB: DSys.filter_nb_localstep tes1 = Some (tsp1, es1))
    : <<TIMESTAMP_EQ: es1 = [] \/ tsp1 = Z.of_nat sytm>> /\
      exists odm_src outb',
        (* <<MATCH_OUTMSGS: conv_tgtmsg outb odm_src = odm_tgt>> /\ *)
        <<UPDATE_OUTBOX: upd_outbox_rel outb odm_src odm_tgt outb'>> /\
        <<INV_ADV: tgtstep_inv1
                     sytm ticks outbs
                     st_i (es_acc ++ es1) outb' st1>>.
  Proof.
    guardH NUM_TASKS_EQ. guardH MCASTS_EQ.
    inv INV.
    - (* first tick *)
      assert (EXACT: exact_skwd_base_time period (DTime.of_ns (sytm - max_clock_skew)) = Some sytm).
      { apply exact_skwd_base_time_iff.
        splits; ss.
        clear - SYTM_LB.
        pose proof period_cond.
        unfold DELTA in *. nia. }
      rewrite DTime_uadd_zero in STEP.
      destruct oist as [[[ocnt stg] ast]|]; ss.
      + (* On *)
        inv STEP; ss.
        * (* Fail *)
          existT_elim. subst.
          unfold DSys.filter_nb_localstep in NOT_NB. ss.
          clarify.
          esplits; eauto.
          { econs 2; eauto. }
          ss.
          econs; eauto.
          { inversion 1. }
          { ss. econs 1. }
        * (* Sync *)
          existT_elim. subst.
          assert (sytm0 = sytm) by clarify.
          subst sytm0.
          unfold DSys.filter_nb_localstep in NOT_NB. ss.
          clarify.

          esplits; eauto.
          { econs 2; eauto. }
          econs; eauto.
          { inversion 1. }
          { econs; ss. }

        * (* OnStay *)
          exfalso. clarify.
        * (* StartRun *)
          exfalso. clarify.
        * (* Running_Go *)
          exfalso. clarify.
        * (* Running_Done *)
          exfalso. clarify.

      + (* Off *)
        inv STEP.
        * (* Stay off *)
          unfold DSys.filter_nb_localstep in NOT_NB. ss.
          clarify.
          esplits; eauto.
          { econs 2; eauto. }
          econs; eauto.
          { inversion 1. }
          { econs. }

        * (* TurnOn *)
          assert (sytm0 = sytm) by clarify.
          subst sytm0.
          unfold DSys.filter_nb_localstep in NOT_NB. ss.
          clarify.

          esplits; eauto.
          { econs 2; eauto. }
          econs; eauto.
          { inversion 1. }
          { econs; eauto.
            hexploit inbox_size_bound; eauto.
            i. nia. }

    - (* not first tick *)

      assert (NOT_EXACT: exact_skwd_base_time
                           period (DTime.uadd (DTime.of_ns (sytm - max_clock_skew))
                                              ticks) = None).
      { apply exact_skwd_base_time_None_iff.
        { ss. nia. }
        exists sytm.
        ss. splits; eauto.
        - nia.
        - eapply lt_le_trans.
          { instantiate (1:= (sytm - max_clock_skew + period) * DTime.units_per_ns).
            nia. }
          cut (sytm - max_clock_skew + period =
               sytm + period - max_clock_skew).
          { i. nia. }
          pose proof period_cond.
          unfold DELTA in *. nia.
      }

      inv SYNC_STEPS; ss.
      + (* Off before begin *)
        inv STEP; ss.
        2: { exfalso. clarify. }
        unfold DSys.filter_nb_localstep in NOT_NB. ss.
        clarify.
        esplits; eauto.
        { econs 2; eauto. }
        econs; ss.
        { nia. }
        econs.
      + (* turned on at this period *)
        inv STEP; ss.
        * (* fail *)
          existT_elim. subst.
          unfold DSys.filter_nb_localstep in NOT_NB. ss.
          clarify.
          esplits; eauto.
          { econs 2; eauto. }
          econs; ss.
          { nia. }
          econs.
        * exfalso. clarify.
        * (* stay done *)
          existT_elim. subst.
          unfold DSys.filter_nb_localstep in NOT_NB. ss.
          clarify.
          esplits; eauto.
          { econs 2; eauto. }
          econs; ss.
          { nia. }
          econs; eauto.
      + (* ready *)
        inv STEP; ss.
        * (* fail *)
          existT_elim. subst.
          unfold DSys.filter_nb_localstep in NOT_NB. ss.
          clarify.
          esplits; eauto.
          { econs 2; eauto. }
          econs; ss.
          { nia. }
          econs; eauto.
        * (* stay ready *)
          existT_elim. subst.
          unfold DSys.filter_nb_localstep in NOT_NB. ss.
          clarify.
          esplits; eauto.
          { econs 2; eauto. }
          econs; ss.
          { nia. }
          econs; eauto.
        * (* start running *)
          existT_elim. subst.
          unfold DSys.filter_nb_localstep in NOT_NB. ss.
          clarify.
          esplits.
          { eauto. }
          { econs 1; eauto. }

          econs; ss.
          { nia. }
          econs; eauto.
          { inv INBOX; ss.
            exfalso.
            hexploit inbox_size_bound; eauto.
            unfold AANode.inbox_sz. i.
            cut (ocnt + length (concat inbc) < 2 * length inbc).
            { i. nia. }
            nia.
          }
          { apply repeat_length. }
          { eapply SNode.IStar_Base. }
          { ss. }
          { econs.
            econs; ss.
            2: {
              apply nth_eq_list_eq. i.
              rewrite Coqlib.list_map_nth.
              destruct (lt_ge_dec n num_tasks).
              - rewrite repeat_nth_error_Some by ss.
                rewrite repeat_nth_error_Some by ss.
                ss.
              - rewrite repeat_nth_error_None by ss.
                rewrite repeat_nth_error_None by ss.
                ss.
            }
            inv INBOX.
            { nia. }
            hexploit inbox_size_bound; eauto.
            unfold AANode.inbox_sz. i.
            cut (ocnt + length (concat inbc) < 2 * length inbc).
            { i. nia. }
            nia.
          }
      + (* running *)
        inv STEP; ss; existT_elim; subst; ss.
        * (* stay off *)
          unfold DSys.filter_nb_localstep in NOT_NB. ss.
          clarify.
          esplits; eauto.
          { econs 3; eauto.
            instantiate (1:= None). ss. }
          econs; ss.
          { nia. }
          rewrite app_nil_r.
          econs; eauto.
        * exfalso. congruence.
        * (* fail *)
          unfold DSys.filter_nb_localstep in NOT_NB. ss.
          clarify.
          esplits; eauto.
          { econs 3; eauto.
            instantiate (1:= None). ss. }
          econs; ss.
          { nia. }
          rewrite app_nil_r.

          assert (ISTAR':
                    SNode.istar
                      rsz_bmsg num_tasks mcasts_src node
                      (ast_pi, repeat None num_tasks) es_r
                      (None, outb)).
          { eapply SNode.istar_snoc_fail; eauto. }

          econs; try apply ISTAR'; eauto.
          econs.
        * exfalso. congruence.
        * (* stay on *)
          unfold DSys.filter_nb_localstep in NOT_NB. ss.
          clarify.
          esplits; eauto.
          { econs 3; eauto.
            instantiate (1:= None). ss. }
          econs; ss.
          { nia. }
          rewrite app_nil_r.
          econs; eauto.
        * exfalso.
          inv OPT_IST.
          match goal with
          | H: interm_ist _ _ _ _ _ |- _ => inv H
          end.
        * (* running go *)
          inv OPT_IST.
          match goal with
          | H: interm_ist _ _ _ _ _ |- _ => inv H
          end.
          renames sytm0 ocnt0 into sytm ocnt_cur.

          unfold DSys.filter_nb_localstep in NOT_NB. ss.
          destruct (deopt_list (map DSys.filter_nb1 (opt2list oe)))
            as [es_f|] eqn: FILTER_NB_SOME; ss.
          clarify.
          apply deopt_list_Some_iff in FILTER_NB_SOME.

          assert (ISTAR': SNode.istar
                            rsz_bmsg num_tasks mcasts_src node
                            (ast_pi, repeat None num_tasks) (es_r ++ opt2list oe) (Some ast',
                                                                                   SNode.update_outbox rsz_bmsg num_tasks mcasts_src outb om)).
          { eapply SNode.istar_app; eauto.
            replace (opt2list oe) with ([] ++ opt2list oe) by ss.
            eapply SNode.istar_app; eauto.
            { eapply tau_steps_istar; eauto.
              rewrite map_length. ss. }
            econs 3; eauto.
            { econs 2. }
            rewrite app_nil_r. ss.
          }

          hexploit process_outmsg_spec; eauto.
          intros (CONV_TGT_EQ & SH').
          guardH CONV_TGT_EQ. guardH SH'.
          hexploit conv_tgtmsg_spec; eauto.
          intros UPD_OUTB_EQ.

          esplits.
          { right. eauto. }
          { econs 3; eauto.
            (* conv_tgtmsg outb om = odm_tgt *)
            (* OUTMSGS : (sh', odm_tgt) = AANode.process_outmsg (map (fun omsg : bytes ? => omsg) outb) om *)
          }
          econs; eauto.
          { nia. }
          econs; eauto.
          { unfold insert_sanitized_msg.
            desf.
            (* length SNode.insert_msg ? b outb = length outb *)
            unfold SNode.insert_msg.
            rewrite imap_length. ss.
          }
          { replace (insert_sanitized_msg outb odm_tgt)
              with (SNode.update_outbox rsz_bmsg num_tasks mcasts_src outb om).
            eauto. }
          { apply deopt_list_Some_iff.
            do 2 rewrite map_app.
            f_equal.
            - apply deopt_list_Some_iff in FILTER_NBS. eauto.
            - eauto.
          }
          econs.
          econs 1; eauto.

        * (* running done *)
          unfold DSys.filter_nb_localstep in NOT_NB. ss.
          clarify.
          esplits; eauto.
          { econs 3; eauto.
            instantiate (1:= None). ss. }
          econs; ss.
          { nia. }
          rewrite app_nil_r.

          inv OPT_IST.

          match goal with
          | H: interm_ist _ _ _ _ _ |- _ => inv H
          end.

          assert (SNode.istar rsz_bmsg num_tasks mcasts_src node
                              (ast_pi, repeat None num_tasks)
                              es_r (Some ast_f, outb)).
          { replace es_r with (es_r ++ []).
            2: { rewrite app_nil_r. ss. }
            eapply SNode.istar_app; eauto.
            eapply tau_steps_istar; eauto.
            rewrite map_length. ss.
          }

          econs; eauto.
          econs.
          econs 2; eauto.
  Qed.


  Lemma tgtstep_inv1_adv
        sytm ticks outbs
        st_i es_acc outb' st1
        outbs' tm st'
        outs_src outs_tgt
        (INV: tgtstep_inv1 sytm ticks outbs
                           st_i es_acc outb' st1)
        (SYTM_LB: period <= sytm)
        (SYTM_SYTM: Nat.divide period sytm)
        (TIME: tm = DTime.uadd (DTime.of_ns (sytm - max_clock_skew)) ticks)
        (TICKS_UB: ticks < period * DTime.units_per_ns)
        (UPD_OUTB_EACH: Forall4 upd_outbox_rel
 (* (fun outb1 out_src outb2 => *)
 (*                                   SNode.update_outbox *)
 (*                                     rsz_bmsg num_tasks mcasts_src *)
 (*                                     outb1 out_src = outb2) *)
                                outbs outs_src outs_tgt outbs')
        (* (MATCH_OUTS: Forall3 (fun conv_tgtmsg) *)
        (*                      outbs outs_src  *)
        (*                      outs_src = outs_tgt) *)
        (ACCEPT_MSGS: AANode.accept_msgs tm outs_tgt st1 = st')
    : tgtstep_inv sytm (S ticks) outbs'
                  st_i es_acc outb' st'.
  Proof.
    guardH MCASTS_EQ. guardH NUM_TASKS_EQ.
    inv INV. ss.
    econs; ss.
    - nia.
    - destruct ticks as [|ticks'].
      + rewrite DTime_uadd_zero.
        assert (EXACT: exact_skwd_base_time period (DTime.of_ns (sytm - max_clock_skew)) = Some sytm).
        { apply exact_skwd_base_time_iff.
          splits; ss.
          clear - SYTM_LB.
          pose proof period_cond.
          unfold DELTA in *. nia. }
        rewrite EXACT.
        hexploit INBN_TZERO; eauto. i. subst outbs.
        apply nth_eq_list_eq. i.

        destruct (lt_ge_dec n num_tasks) as [LT|GE].
        * erewrite AANode.merge_inbox_nth.
          2: { unfold AANode.init_inbox.
               rewrite repeat_nth_error_Some; eauto. }
          do 2 rewrite Coqlib.list_map_nth.
          hexploit Forall4_nth1; eauto.
          { apply repeat_nth_error_Some; eauto. }
          i. des.
          renames e2 e3 e4 into out_src out_tgt outb''.
          renames NTH2 NTH3 NTH4 into
                  OUT_SRC OUT_TGT OUTB''.
          inv P_FA.
          { rewrite OUT_TGT, OUTB''. ss.
            match goal with
            | |- context[opt2list ?o] =>
              replace o with (@None bytes)
            end.
            2: {
              destruct (lt_ge_dec tid num_tasks).
              - erewrite nth_error_nth; eauto.
                apply repeat_nth_error_Some. ss.
              - rewrite nth_overflow; ss.
                rewrite repeat_length. ss.
            }
            ss.
          }
          { rewrite OUTB'', OUT_TGT. ss.
            destruct tid; ss. }
          { exfalso.
            ss. nia. }
        * hexploit Forall4_length; eauto.
          rewrite repeat_length. i. des.
          rewrite nth_error_None2.
          2: { rewrite map_length. nia. }
          rewrite nth_error_None2.
          2: { rewrite AANode.merge_inbox_length.
               unfold AANode.init_inbox.
               rewrite repeat_length. ss. }
          ss.
      + assert (NEXACT: exact_skwd_base_time period
                          (DTime.uadd (DTime.of_ns (sytm - max_clock_skew))
                                      (S ticks')) = None).
        { apply exact_skwd_base_time_None_iff.
          { ss. nia. }
          exists sytm.
          ss. splits; eauto.
          - nia.
          - eapply lt_le_trans.
            { instantiate (1:= (sytm - max_clock_skew + period) * DTime.units_per_ns).
              nia. }
            cut (sytm - max_clock_skew + period =
                 sytm + period - max_clock_skew).
            { i. nia. }
            pose proof period_cond.
            unfold DELTA in *. nia.
        }
        rewrite NEXACT.

        hexploit INBN_TPOS.
        { nia. }
        i. subst inbn.
        apply nth_eq_list_eq. i.
        (* rewrite Forall4_nth in UPD_OUTB_EACH. *)
        (* specialize (UPD_OUTB_EACH n). *)
        rewrite Coqlib.list_map_nth.

        destruct (lt_ge_dec n (length outbs)).
        * hexploit (nth_error_Some2 _ outbs n); ss.
          i. des. renames e1 NTH_EX into outb OUTB.
          hexploit Forall4_nth1; eauto. i. des.
          renames e2 e3 e4 into out_s out_t outb''.
          renames NTH2 NTH3 NTH4 into OUT_S OUT_T OUTB''.
          rewrite OUTB''. ss.
          erewrite AANode.merge_inbox_nth.
          2: { apply map_nth_error; eauto. }
          erewrite map_nth_error; eauto.
          f_equal.
          inv P_FA.
          { ss.
            rewrite repeat_nth_default.
            destruct tid; ss.
          }
          { ss. destruct tid; ss. }
          { eapply insert_sanitized_msg_aux; eauto. }

        * hexploit Forall4_length; eauto. i. des.
          rewrite nth_error_None2.
          2: { nia. }
          rewrite nth_error_None2.
          2: { rewrite AANode.merge_inbox_length.
               rewrite map_length. ss. }
          ss.

    - inv SYNC_STEPS.
      + econs; eauto.
      + econs; eauto.
      + econs; eauto.
      + econs; eauto.
        inv OPT_IST.
        { econs. }
        econs.
        inv H1.
        { econs; eauto. }
        { econs; eauto. }
  Qed.

  Inductive acc_events (sytm: nat)
    : events sysE -> tsp * events sysE -> events sysE -> Prop :=
  | AccEvents_Nil tsp es
    : acc_events sytm es (tsp, []) es
  | AccEvents_NotNil
      es es1 zsytm
      (TIMESTAMP: zsytm = Z.of_nat sytm)
    : acc_events sytm es (zsytm, es1) (es ++ es1)
  .

  Inductive acc_trace (sytm: nat)
    : events sysE -> list (tsp * events sysE) -> events sysE -> Prop :=
    AccTrace
      es tr es'
      (TIMESTAMPS_OK: Forall (fun tes => fst tes = Z.of_nat sytm \/ snd tes = []) tr)
      (CONCAT_EVENTS: es ++ concat (map snd tr) = es')
    : acc_trace sytm es tr es'.


  Lemma cons_acc_trace
        tm x y z w a
        (AE1: acc_events tm x y z)
        (AE2: acc_trace tm z w a)
    : acc_trace tm x (y::w) a.
  Proof.
    inv AE2.
    inv AE1.
    - econs.
      + econs; ss. eauto.
      + ss.
    - econs.
      + econs; ss. eauto.
      + ss. rewrite <- app_assoc. ss.
  Qed.


  Lemma tgtstep_lemma
        lsts_i tm lsts tm' lsts'
        es1_r es1
        sytm ticks outbs
        es_acc
        (STEP: DSys.step sys_tgt (AASys.State tm lsts)
                         es1_r (AASys.State tm' lsts'))
        (NOT_NBS: DSys.filter_nb_sysstep es1_r = Some es1)
        (INV: Forall4 (tgtstep_inv sytm ticks outbs)
                      lsts_i es_acc outbs lsts)
        (SYTM_LB: period <= sytm)
        (SYTM_SYNC: Nat.divide period sytm)
        (TICKS_UB: ticks < period * DTime.units_per_ns)
        (TIME: tm = DTime.uadd (DTime.of_ns (sytm - max_clock_skew)) ticks)
    : exists outbs' es_acc',
      <<INV': Forall4 (tgtstep_inv sytm (S ticks) outbs')
                      lsts_i es_acc' outbs' lsts'>> /\
      <<TIME': tm' = DTime.uadd (DTime.of_ns (sytm - max_clock_skew)) (S ticks)>> /\
      <<ES_ACC_APP: Forall3 (acc_events sytm) es_acc es1 es_acc'>>
  .
  Proof.
    guardH NUM_TASKS_EQ. guardH MCASTS_EQ.
    guardH TIME.
    inv STEP.
    rename nsts1 into lsts1.

    assert (STEP_EX: forall n (N_UB: n < length lsts_i),
               exists (x: events sysE * (Tid * bytes) ? * list bytes?),
                 (fun n x =>
                    ((* <<N_SMALL: n < num_tasks>> /\ *)
                      exists lst_i lst1 es_acc_n es1_r_n es1_n
                        outb out_tgt,
                       <<LSTS_I_N: nth_error lsts_i n = Some lst_i>> /\
                       <<LSTS1_N: nth_error lsts1 n = Some lst1>> /\
                       <<ES_ACC_N: nth_error es_acc n = Some es_acc_n>> /\
                       <<ES1_R_N: nth_error es1_r n = Some es1_r_n>> /\
                       <<ES1_N: nth_error es1 n = Some es1_n>> /\
                       <<OUTB_N: nth_error outbs n = Some outb>> /\
                       <<OUT_TGT: nth_error outs n = Some out_tgt>> /\
                       let '(es_acc_n', odm, outb') := x in
                       <<INV1: tgtstep_inv1 sytm ticks outbs
                                            lst_i es_acc_n' outb' lst1>> /\
                       <<ACC_EVENTS': acc_events sytm es_acc_n es1_n es_acc_n'>> /\
                       <<UPD_OUTB: upd_outbox_rel outb odm out_tgt outb'>>)
                 )
                   n x).
    {
      i.
      hexploit Forall4_length; try apply INV; eauto. i. des.
      hexploit Forall4_length; try apply STEP; eauto. i. des.

      assert (length es1_r = length es1).
      { unfold DSys.filter_nb_sysstep in NOT_NBS.
        rewrite deopt_list_Some_iff in NOT_NBS.
        assert (length es1 = length es1_r).
        { erewrite <- map_length.
          rewrite NOT_NBS.
          rewrite map_length. ss. }
        nia.
      }

      hexploit (nth_error_Some2 _ lsts n).
      { nia. }
      i. des. renames e1 NTH_EX into lst LST.
      hexploit Forall4_nth4; try apply INV; eauto.
      i. des.
      renames e1 e2 e3 into lst_i es_acc_n outb_n.
      renames NTH1 NTH2 NTH3 into LST_I ES_ACC_N OUTB_N.
      rename P_FA into INV_N.
      hexploit Forall4_nth1; try apply STEPS; eauto.
      i. des.
      renames e2 e3 e4 into es1_r_n outs_n nsts1_n.
      renames NTH2 NTH3 NTH4 into ES1_R_N OUTS_N NSTS1_N.
      rename P_FA into STEP_N.

      unfold DSys.filter_nb_sysstep in NOT_NBS.
      apply deopt_list_Some_iff in NOT_NBS.

      assert (NTH_AUX: nth_error (map (fun x => Some x) es1) n =
                       Some (DSys.filter_nb_localstep es1_r_n)).
      { rewrite NOT_NBS.
        apply map_nth_error. eauto. }
      rewrite map_nth_error_iff in NTH_AUX.
      destruct NTH_AUX as [[tsp1_n es1_n] [ES1_N FILTER_LOCAL]].

      hexploit tgtstep_inv_localstep; eauto.
      { rewrite <- TIME. eauto. }
      i. nbdes.
      guardH TIMESTAMP_EQ.

      exists (es_acc_n ++ es1_n, odm_src, outb').
      esplits; eauto.
      destruct TIMESTAMP_EQ.
      - clarify.
        rewrite app_nil_r. econs.
      - clarify.
        econs. ss.
    }

    apply exists_list in STEP_EX. des.
    rename l into xs.
    pose (es_xs := map fst (map fst xs)).
    pose (outbs_xs := map snd xs).
    pose (odms_xs := map snd (map fst xs)).

    exists outbs_xs, es_xs.
    assert (UPD_OUTB_EACH: Forall4 upd_outbox_rel
                                   outbs odms_xs outs outbs_xs).
    { apply Forall4_nth. i.
      destruct (lt_ge_dec n (length lsts_i)).
      - hexploit (nth_error_Some2 _ xs n); [nia|].
        i. des.
        destruct e1 as [[es' odm'] outb'].
        exploit (NTH_PROP n); eauto. i. nbdes.
        guardH UPD_OUTB.

        subst odms_xs outbs_xs.
        do 3 rewrite Coqlib.list_map_nth.
        rewrite NTH_EX. ss.
        rewrite OUTB_N, OUT_TGT.
        econs. eauto.

      - subst odms_xs outbs_xs.
        hexploit Forall4_length; try eapply INV; eauto.
        i. des.
        hexploit Forall4_length; try eapply STEPS; eauto.
        i. des.
        rewrite nth_error_None2 by nia.
        rewrite nth_error_None2.
        2: { do 2 rewrite map_length. nia. }
        rewrite nth_error_None2 by nia.
        rewrite nth_error_None2.
        2: { rewrite map_length. nia. }
        econs.
    }

    splits.
    - apply Forall4_nth. i.
      destruct (lt_ge_dec n (length lsts_i)) as [LT|GE].
      + hexploit (nth_error_Some2 _ xs n).
        { nia. }
        i. des. rename NTH_EX into XS_N.
        destruct e1 as [[es odm] outb].
        exploit (NTH_PROP n); eauto. i. des.

        hexploit tgtstep_inv1_adv; eauto. intro INV_NXT.

        subst es_xs outbs_xs.
        erewrite map_nth_error; eauto.
        2: { apply map_nth_error. eauto. }
        erewrite map_nth_error; eauto. ss.
        erewrite map_nth_error; eauto.
        rewrite LSTS_I_N.
        econs. ss.
      + hexploit Forall4_length; try apply INV; eauto. i. des.
        hexploit Forall4_length; try apply STEPS; eauto. i. des.
        rewrite nth_error_None2 by nia.
        rewrite nth_error_None2.
        2: { subst es_xs.
             do 2 rewrite map_length. nia. }
        rewrite nth_error_None2.
        2: { subst outbs_xs.
             rewrite map_length. nia. }
        rewrite nth_error_None2.
        2: { rewrite map_length. nia. }
        econs.

    - rewrite <- DTime_uadd_one.
      unfold DTime.uadd. ss.
      f_equal.
      rewrite TIME. ss. nia.

    - apply Forall3_nth. i.
      destruct (lt_ge_dec n (length lsts_i)) as [LT|GE].
      + hexploit (nth_error_Some2 _ xs n).
        { nia. }
        i. des. rename NTH_EX into XS_N.
        destruct e1 as [es outb].
        exploit (NTH_PROP n); eauto. i. des.
        destruct es as [es_acc_n' odm]. des.

        subst es_xs.
        do 2 rewrite Coqlib.list_map_nth.
        rewrite ES1_N, ES_ACC_N, XS_N. ss.
        econs. ss.
      + hexploit Forall4_length; try apply INV; eauto. i. des.
        hexploit Forall4_length; try apply STEPS; eauto. i. des.
        rewrite nth_error_None2 by nia.
        rewrite nth_error_None2.
        2: {
          unfold DSys.filter_nb_sysstep in NOT_NBS.
          rewrite deopt_list_Some_iff in NOT_NBS.
          assert (length es1 = length es1_r).
          { erewrite <- map_length.
            rewrite NOT_NBS.
            rewrite map_length. ss. }
          nia.
        }
        rewrite nth_error_None2.
        2: { subst es_xs.
             do 2 rewrite map_length. nia. }
        econs.
  Qed.



  Lemma tgtsteps_lemma
        ticks' tm lsts trs tm' lsts'
        sytm ticks outbs
        lsts_i es_acc
        (MSTEPS: msteps sys_tgt ticks'
                        (AASys.State tm lsts) trs
                        (AASys.State tm' lsts'))
        (INV: Forall4 (tgtstep_inv sytm ticks outbs)
                      lsts_i es_acc outbs lsts)
        (SYTM_LB: period <= sytm)
        (SYTM_SYNC: Nat.divide period sytm)
        (TICKS_UB: ticks + ticks' <= period * DTime.units_per_ns)
        (TIME: tm = DTime.uadd (DTime.of_ns (sytm - max_clock_skew)) ticks)
    : exists outbs' es_acc',
      <<INV': Forall4 (tgtstep_inv sytm (ticks + ticks') outbs')
                      lsts_i es_acc' outbs' lsts'>> /\
      <<TIME': tm' = DTime.uadd (DTime.of_ns (sytm - max_clock_skew)) (ticks + ticks')>> /\
      <<ES_ACC_APP: Forall3 (acc_trace sytm) es_acc trs es_acc'>>
  .
  Proof.
    guardH MCASTS_EQ. guardH NUM_TASKS_EQ.
    depgen trs. depgen tm'. depgen lsts'. depgen tm.
    depgen ticks. depgen lsts. depgen outbs.
    depgen es_acc.
    induction ticks' as [| ticks' IH]; i; ss.
    { inv MSTEPS.
      esplits; ss.
      - rewrite plus_0_r. eauto.
      - rewrite plus_0_r. eauto.
      - unfold AASys.num_sites. ss.
        apply Forall3_nth. i.
        hexploit Forall4_length; eauto. i. des.
        destruct (lt_ge_dec n (length lsts')).
        + hexploit (nth_error_Some2 _ es_acc n).
          { nia. }
          i. des.
          rewrite repeat_nth_error_Some by ss.
          rewrite NTH_EX. econs.
          econs; ss.
          rewrite app_nil_r. ss.
        + rewrite nth_error_None2 by nia.
          rewrite nth_error_None2.
          2: { rewrite repeat_length. ss. }
          econs.
    }

    inv MSTEPS.
    destruct st1 as [tm1 lsts1].
    hexploit tgtstep_lemma; eauto.
    { nia. }
    i. des.

    hexploit IH; eauto.
    { nia. }
    i. des.
    clarify.
    esplits; ss.
    - rewrite <- plus_n_Sm. eauto.
    - rewrite <- plus_n_Sm. eauto.
    - apply Forall3_nth. i.
      (* clear - CONS_EVENTS ES_ACC_APP ES_ACC_APP0. *)
      r in CONS_EVENTS.
      rewrite Forall3_nth in
          CONS_EVENTS, ES_ACC_APP, ES_ACC_APP0.
      specialize (CONS_EVENTS n).
      specialize (ES_ACC_APP n).
      specialize (ES_ACC_APP0 n).
      inv CONS_EVENTS; inv ES_ACC_APP; inv ES_ACC_APP0;
        try congruence.
      + econs.
      + econs.
        repeat match goal with
               | H: Some _ = nth_error _ _ |- _ =>
                 symmetry in H
               end.
        clarify.
        eapply cons_acc_trace; eauto.
  Qed.

  Lemma srcstep_not_sync
        n tm_src lsts
        (TIME_NOT_SYNC: forall k (LT_N: k < n),
            ~ Nat.divide period (tm_src + k))
    : exists tr tm_src',
      <<STEP_SRC: msteps sys_src n
                         (SyncSys.State tm_src lsts) tr
                         (SyncSys.State tm_src' lsts)>> /\
      <<TIME': tm_src' = tm_src + n>> /\
      <<TRACE_NILS: Forall (Forall (fun tes => snd tes = [])) tr>> /\
      <<TR_LENGTH: length tr = length lsts>>
  .
  Proof.
    depgen tm_src.
    induction n as [| n' IH]; i; ss.
    { esplits.
      - econs. eauto.
      - rewrite plus_0_r. ss.
      - apply Forall_forall.
        intros a IN.
        apply repeat_spec in IN.
        subst. econs.
      - rewrite repeat_length. ss.
    }
    hexploit (IH (S tm_src)); eauto.
    { i. hexploit (TIME_NOT_SYNC (S k)); eauto.
      { nia. }
      rewrite <- plus_n_Sm. ss. }
    i. des.

    exists (map (fun a => (Z.of_nat tm_src, [])::a) tr).
    subst.
    esplits; eauto.
    - econs; eauto.
      + ss. econs 1; eauto.
        hexploit (TIME_NOT_SYNC 0).
        { nia. }
        rewrite plus_0_r. ss.
      + unfold DSys.filter_nb_sysstep.
        apply deopt_list_Some_iff.
        instantiate (1 := repeat (Z.of_nat tm_src, ([]: events sysE)) (length lsts)).
        eapply nth_eq_list_eq. i.
        do 2 rewrite Coqlib.list_map_nth.

        destruct (lt_ge_dec n (length lsts)).
        2: {
          rewrite repeat_nth_error_None by ss.
          rewrite repeat_nth_error_None by ss. ss.
        }

        rewrite repeat_nth_error_Some by ss.
        rewrite repeat_nth_error_Some by ss.
        ss.
      + r. apply Forall3_nth. i.
        change (list (event sysE)) with (events sysE).
        destruct (lt_ge_dec n (length lsts)).
        * rewrite repeat_nth_error_Some by ss.
          rewrite Coqlib.list_map_nth.
          hexploit (nth_error_Some2 _ tr n); eauto.
          { nia. }
          i. des.
          rewrite NTH_EX. econs. ss.
        * rewrite repeat_nth_error_None by ss.
          rewrite Coqlib.list_map_nth.
          rewrite nth_error_None2 by nia.
          ss. econs.
    - apply Forall_forall.
      intros row IN. ss.
      apply in_map_iff in IN. des. clarify.
      econs; ss.
      rewrite Forall_forall in TRACE_NILS.
      apply TRACE_NILS. eauto.
    - rewrite map_length. ss.
  Qed.


  Section PERIOD_SIM.
    Variable sytm: nat.
    Hypothesis SYTM_LB: period <= sytm.
    Hypothesis SYTM_BASE_TIME: Nat.divide period sytm.

    Lemma period_sim
          lsts_src tm_tgt lsts_tgt
          tr_tgt tm_tgt' lsts_tgt'
          (NUM_LSTS: length lsts_tgt = num_tasks)
          (TM_TGT: tm_tgt = DTime.of_ns (sytm - max_clock_skew))
          (INV: Forall2 match_lst lsts_src lsts_tgt)
          (STEPS_TGT: msteps sys_tgt
                             (period * DTime.units_per_ns)
                             (AASys.State tm_tgt lsts_tgt) tr_tgt
                             (AASys.State tm_tgt' lsts_tgt'))
      : <<TM_TGT': tm_tgt' = DTime.of_ns (sytm + period - max_clock_skew) >> /\
        exists tr_src lsts_src',
               <<STEPS_SRC: msteps sys_src
                                   period
                                   (SyncSys.State sytm lsts_src) tr_src
                                   (SyncSys.State (sytm + period) lsts_src')>> /\
               <<FA: Forall2 tes_equiv tr_src tr_tgt>> /\
               <<INV': Forall2 match_lst
                               lsts_src' lsts_tgt'>>
    .
    Proof.
      guardH NUM_TASKS_EQ. guardH MCASTS_EQ.
      pose (outb_i:=
              List.repeat
                (* (List.repeat (@None bytes) num_tasks) *)
                ([]: list bytes?) num_tasks).
      assert (INVS_TGT: Forall4 (tgtstep_inv sytm 0 outb_i)
                                lsts_tgt
                                (List.repeat [] num_tasks)
                                outb_i
                                lsts_tgt).
      { apply Forall4_nth. i.
        rewrite Forall2_nth in INV.
        specialize (INV n).
        destruct (lt_ge_dec n num_tasks) as [LT|GE].
        2: {
          rewrite nth_error_None2 by nia.
          rewrite nth_error_None2.
          2: { rewrite repeat_length. ss. }
          rewrite nth_error_None2.
          2: { subst outb_i.
               rewrite repeat_length. ss. }
          econs.
        }

        hexploit (nth_error_Some2 _ lsts_tgt n); [nia|].
        i. des. renames e1 NTH_EX into lst_tgt LST_TGT.
        rewrite LST_TGT.
        subst outb_i.
        rewrite repeat_nth_error_Some by ss.
        rewrite repeat_nth_error_Some by ss.
        econs.
        rewrite LST_TGT in INV. inv INV.
        eapply match_lst_tgtstep; eauto.
      }

      hexploit tgtsteps_lemma; eauto.
      { rewrite DTime_uadd_zero. ss. }
      i. des.

      assert(ST_SRC_EX:
               (forall n (N_UB: n < num_tasks),
                   exists (xs: events (nbE +' sysE) *
                          (* list (bytes?) * *)
                          SNode.state),
                     (fun n x =>
                        let '(es_r, (* outb_s, *) lst_src') := xs in
                        option_rel2
                          (fun lst_src (* es *) outb =>
                             <<STEP_SRC:
                               SNode.step
                                 rsz_bmsg num_tasks mcasts_src sytm
                                 lst_src es_r outb lst_src'>>)
                          (nth_error lsts_src n)
                          (nth_error outbs' n) /\
                        option_rel1
                          (fun es =>
                             <<NOT_NB: DSys.filter_nb_localstep (Z.of_nat sytm, es_r) =
                                       Some (Z.of_nat sytm, es)>>)
                          (nth_error es_acc' n) /\
                        option_rel1
                          (fun lst_tgt' =>
                             <<MATCH': match_lst
                                         (SNode.accept_msgs outbs' lst_src') lst_tgt'>>)
                          (nth_error lsts_tgt' n)
                     )
                       n xs)).
      { i.
        hexploit (nth_error_Some2 _ lsts_tgt n); [nia|].
        i. des. renames e1 NTH_EX into lst_tgt LST_TGT.
        hexploit Forall2_nth2; eauto. i. des.
        renames e1 NTH1 P_FA into lst_src LST_SRC MATCH_LST.
        hexploit Forall4_nth1; eauto. i. des.
        renames e2 e3 e4 into es outb lst_tgt'.
        renames NTH2 NTH3 NTH4 into ES_N OUTB_N LST_TGT'.
        hexploit tgtstep_nxt_match_lst; eauto.
        { hexploit Forall4_length; eauto. i. des.
          nia. }
        i. des.
        clear P_FA.
        rewrite ES_N, OUTB_N, LST_SRC, LST_TGT'.

        exists (ess_src, st_f_src).
        esplits; eauto.
        econs; eauto.
      }

      eapply exists_list in ST_SRC_EX. des.
      renames l LIST_LEN into xs XS_LEN.
      split.
      { r. rewrite TIME'. ss.
        unfold DTime.uadd, DTime.of_ns. ss.
        f_equal.
        rewrite <- Nat.mul_add_distr_r.
        f_equal.
        clear - SYTM_LB.
        pose proof period_cond as PRD_COND.
        unfold DELTA in PRD_COND.
        nia.
      }

      pose (tes_src := map fst xs).
      (* pose (outbs_src := map snd (map fst xs)). *)
      pose (lsts_src1 := map snd xs).
      pose (lsts_src' := map (SNode.accept_msgs outbs') lsts_src1).

      hexploit (srcstep_not_sync (pred period) (S sytm) lsts_src').
      { clear - SYTM_BASE_TIME.
        i. intro DIV_K.
        unfold Nat.divide in *.
        destruct SYTM_BASE_TIME as [z1 SYTM_EQ].
        des. subst.
        assert (LTS: z1 * period < S (z1 * period) + k < (S z1) * period) by nia.
        rewrite DIV_K in LTS.
        assert (CONTRA: z1 < z < S z1) by nia.
        nia.
      }
      i. des.

      assert (exists tr_src_tot,
                 <<CONS_EACH: cons_each_rel
                                (map (fun es : events sysE => (Z.of_nat sytm, es)) es_acc')
                                tr tr_src_tot>> /\
                <<FLATTEN:
                   Forall2 (fun tr es =>
                              flatten_tes tr =
                              map (fun e => (Z.of_nat sytm, e)) es)
                           tr_src_tot es_acc'>>).
      {
        cut (forall n (N_UB: n < num_tasks),
                exists (tot_n: list (tsp * events sysE)),
                  (fun n tot_n =>
                     option_rel2
                       (fun h t => (Z.of_nat sytm, h) :: t = tot_n)
                       (nth_error es_acc' n)
                       (nth_error tr n) /\
                     option_rel1
                       (fun es =>
                          flatten_tes tot_n =
                          (map (fun e => (Z.of_nat sytm, e)) es))
                       (nth_error es_acc' n))
                    n tot_n).
        { clear NTH_PROP.
          intro EX.
          eapply exists_list in EX.  des.
          exists l.

          cut (forall n, (exists es_n tr_n tot_n,
                        <<ES_N: nth_error es_acc' n = Some es_n>> /\
                        <<TR_N: nth_error tr n = Some tr_n>> /\
                        <<TOT_N: nth_error l n = Some tot_n>>) \/
                    (<<ES_N: nth_error es_acc' n = None>> /\
                     <<TR_N: nth_error tr n = None>> /\
                     <<TOT_N: nth_error l n = None>>)).
          { intro CASES.
            splits.
            - r. apply Forall3_nth. i.
              rewrite Coqlib.list_map_nth.
              specialize (CASES n). des.
              + exploit NTH_PROP; eauto.
                rewrite TR_N, TOT_N, ES_N.
                intros [CONS _]. inv CONS.
                econs; ss.
              + rewrite TR_N, TOT_N, ES_N.
                ss. econs.
            - apply Forall2_nth. i.
              change (list (event sysE))
                with (events sysE) in *.
              specialize (CASES n). des.
              + exploit NTH_PROP; eauto.
                rewrite TR_N, TOT_N, ES_N.
                intros [_ FLTN]. r in FLTN.
                econs. eauto.
              + rewrite TOT_N, ES_N.
                econs.
          }
          i.
          destruct (lt_ge_dec n num_tasks) as [LT|GE].
          - hexploit (nth_error_Some2 _ lsts_tgt n).
            { nia. }
            i. des. renames e1 NTH_EX into lst_tgt LST_TGT.
            hexploit Forall4_nth1; eauto. i. des.
            renames e2 e3 e4 into es_n out_n lst_tgt'.
            renames NTH2 NTH3 NTH4 into ES_N OUT_N LST_TGT'.
            clear P_FA.

            hexploit (nth_error_Some2 _ l n).
            { nia. }
            i. des. renames e1 NTH_EX into tot_n TOT_N.
            hexploit (nth_error_Some2 _ tr n).
            { rewrite TR_LENGTH.
              subst lsts_src' lsts_src1.
              do 2 rewrite map_length. nia. }
            i. des. renames e1 NTH_EX into tr_n TR_N.
            rewrite ES_N, TOT_N, TR_N.
            left. esplits; eauto.
          - hexploit Forall4_length; eauto. i. des.
            rewrite nth_error_None2 by nia.
            rewrite nth_error_None2.
            2: { rewrite TR_LENGTH.
                 subst lsts_src' lsts_src1.
                 do 2 rewrite map_length.
                 nia. }
            rewrite nth_error_None2 by nia.
            right. esplits; eauto.
        }

        i.
        hexploit (nth_error_Some2 _ lsts_tgt n).
        { nia. }
        i. des. renames e1 NTH_EX into lst_tgt LST_TGT.
        hexploit Forall4_nth1; eauto. i. des.
        renames NTH2 NTH3 NTH4 into ES_N OUTBS_N LST_TGT'.
        rewrite ES_N.
        hexploit (nth_error_Some2 _ tr n).
        { rewrite TR_LENGTH.
          subst lsts_src' lsts_src1.
          do 2 rewrite map_length. nia. }
        i. des. rename NTH_EX into TR_N.
        rewrite TR_N.
        esplits; eauto.
        - econs. ss.
        - r. ss.
          unfold flatten_tes. ss.
          rewrite <- flat_map_concat_map.

          cut (flat_map flatten_te e1 = []).
          { intro R. rewrite R.
            rewrite app_nil_r.
            ss. }

          apply not_in_nil.
          intros [t es] IN.
          apply in_flat_map in IN. des.
          rewrite Forall_nth in TRACE_NILS.
          specialize (TRACE_NILS n). r in TRACE_NILS.
          change (list (event sysE))
            with (events sysE) in *.
          rewrite TR_N in TRACE_NILS.
          rewrite Forall_forall in TRACE_NILS.
          hexploit TRACE_NILS; eauto. i.
          destruct x as [t' es']; ss.
          clarify.
      }

      des.

      exists tr_src_tot, lsts_src'.
      splits.
      - assert (PRD_POS: 0 < period).
        { pose proof period_cond. nia. }

        destruct period as [|prd'].
        { exfalso. nia. }
        econs.
        { ss.
          cut (Forall4
                 (SNode.step rsz_bmsg (length lsts_src) mcasts_src sytm)
                 lsts_src tes_src outbs' lsts_src1).
          { econs 2; eauto. }
          apply Forall4_nth. i.
          destruct (lt_ge_dec n num_tasks) as [LT|GE].
          2: {
            hexploit Forall2_length; try apply INV; eauto. i.
            hexploit Forall4_length; eauto. i. des.
            rewrite nth_error_None2 by nia.
            rewrite nth_error_None2.
            2: { subst tes_src.
                 rewrite map_length. nia. }
            rewrite nth_error_None2 by nia.
            rewrite nth_error_None2.
            2: { subst lsts_src1.
                 rewrite map_length. nia. }
            econs.
          }

          hexploit (nth_error_Some2 _ xs n); [nia|].
          i. des. rename NTH_EX into XS_N.
          (* destruct e1 as [[tes outb_s] lst_src1]. *)
          destruct e1 as [es_r lst_src1].
          exploit NTH_PROP; eauto. ss.
          intro PROP_N.

          hexploit (nth_error_Some2 _ lsts_tgt n); [nia|].
          i. des. renames e1 NTH_EX into lst_tgt LST_TGT.
          hexploit Forall2_nth2; try apply INV; eauto. i. des.
          renames e1 NTH1 P_FA into lst_src LST_SRC MATCH_LST.
          hexploit Forall4_nth1; eauto. i. des.
          renames e2 e3 e4 into es outb lst_tgt'.
          renames NTH2 NTH3 NTH4 into ES_N OUTB_N LST_TGT'.
          rewrite LST_SRC.
          rewrite OUTB_N, LST_SRC in PROP_N.
          inv PROP_N. des.
          subst tes_src lsts_src1.
          repeat rewrite Coqlib.list_map_nth.
          rewrite XS_N, OUTB_N. ss. econs.
          replace (length lsts_src) with num_tasks.
          2: { hexploit Forall2_length; try apply INV; eauto.
               i. nia. }
          eauto.
        }
        { unfold DSys.filter_nb_sysstep.
          instantiate (1:= (map (fun es => (Z.of_nat sytm, es)) es_acc')).
          apply deopt_list_Some_iff.
          apply nth_eq_list_eq. i.
          do 3 rewrite Coqlib.list_map_nth.

          destruct (lt_ge_dec n num_tasks) as [LT|GE].
          2: {
            rewrite nth_error_None2.
            2: { hexploit Forall4_length; eauto. i. des.
                 congruence. }
            rewrite nth_error_None2.
            2: { subst tes_src.
                 do 2 rewrite map_length. nia. }
            ss.
          }

          hexploit (nth_error_Some2 _ xs n); [nia|].
          i. des. rename NTH_EX into XS_N.
          destruct e1 as [(* [tes_t tes_es] *) es_r lst_src1].
          exploit NTH_PROP; eauto. ss.
          intros (STEP_SRC_EX & NOT_NB_OK & MATCH').

          subst tes_src.
          erewrite map_nth_error; eauto.
          2: { erewrite map_nth_error; eauto. }
          s. hexploit (nth_error_Some2 _ es_acc' n).
          { hexploit Forall4_length; eauto. i. des.
            congruence. }
          i. des. renames e1 NTH_EX into es1 ES1.
          rewrite ES1 in *. ss.
          rewrite NOT_NB_OK. eauto.
        }
        { fold lsts_src'.
          subst tm_src'.
          rewrite <- pred_Sn in STEP_SRC. ss.
          rewrite <- plus_n_Sm. eauto. }
        { eauto. }
      - apply Forall2_nth. i.
        rewrite Forall2_nth in FLATTEN.
        specialize (FLATTEN n).

        destruct (nth_error tr_src_tot n) as [tr_src_n|] eqn: TR_SRC_N.
        + change (list (event sysE))
                 with (events sysE) in FLATTEN.
          destruct (nth_error es_acc' n) as [es_n|] eqn:ES_N.
          2: { inv FLATTEN. }
          hexploit Forall3_nth3; try apply ES_ACC_APP; eauto. i. des.
          apply nth_error_In in NTH1.
          apply repeat_spec in NTH1. subst e1.
          renames e2 NTH2 into tr_tgt_n TR_TGT_N.
          inv P_FA. ss.
          rewrite TR_TGT_N. econs.

          cut (flatten_tes tr_tgt_n =
               map (fun e => (Z.of_nat sytm, e)) (concat (map snd tr_tgt_n))).
          { intro FLTN_TGT.
            inv FLATTEN.
            r. rewrite FLTN_TGT. ss. }

          apply tes_when_eff_tstamp_identical. eauto.
        + inv FLATTEN.
          rewrite Forall3_nth in ES_ACC_APP.
          specialize (ES_ACC_APP n). inv ES_ACC_APP.
          * econs.
          * change (list (event sysE)) with (events sysE) in *.
            congruence.
      - apply Forall2_nth. intro n.
        destruct (lt_ge_dec n num_tasks).
        + hexploit (nth_error_Some2 _ xs n); [nia|].
          i. des. rename NTH_EX into XS_N.
          (* destruct e1 as [[tes_t tes_es] lst_src1]. *)
          destruct e1 as [es_r lst_src1].
          exploit NTH_PROP; eauto. ss.
          intros (STEP_SRC_EX & NOT_NB_OK & MATCH').

          subst lsts_src' lsts_src1.
          erewrite map_nth_error; eauto.
          2: { erewrite map_nth_error; eauto. }
          ss.

          destruct (nth_error lsts_tgt' n)
            as [lst_tgt'|] eqn:LST_TGT'.
          2: { exfalso.
               hexploit (nth_error_Some2 _ lsts_tgt' n).
               { hexploit Forall4_length; eauto. i. des.
                 nia. }
               i. des. congruence.
          }
          ss. econs. eauto.
        + subst lsts_src' lsts_src1.
          do 2 rewrite Coqlib.list_map_nth.
          rewrite nth_error_None2 by nia.
          rewrite nth_error_None2.
          2: { hexploit Forall4_length; eauto. i. des.
               nia. }
          econs.
    Qed.

  End PERIOD_SIM.

  Lemma period_fmsim_states
    : forall (sytm: nat)
        (SYTM_LB: period <= sytm)
        (SYTM_BASE_TIME: Nat.divide period sytm)
        lsts_src tm_tgt lsts_tgt
        (NUM_LSTS: length lsts_tgt = num_tasks)
        (TM_TGT: tm_tgt = DTime.of_ns (sytm - max_clock_skew))
        (INV: Forall2 match_lst lsts_src lsts_tgt),
      fmsim_states _ sys_src sys_tgt
                   (SyncSys.State sytm lsts_src)
                   (AASys.State tm_tgt lsts_tgt).
  Proof.
    pcofix CIH. i.
    pfold. econs.
    { instantiate (1:= period * DTime.units_per_ns).
      pose proof period_cond.
      pose proof DTime.units_per_ns_pos.
      nia. }

    i. destruct st_tgt'.
    hexploit period_sim; eauto. i. des.
    exists period.
    esplits; eauto.
    { pose proof period_cond. nia. }
    right. apply CIH; eauto.
    - nia.
    - apply Nat.divide_add_r; ss.
      apply Nat.divide_refl.
    - hexploit msteps_num_sites_eq; try apply STEPS; eauto.
      i. des.
      ss. unfold AASys.num_sites in NUM_SITES_EQ. ss.
      nia.
  Qed.

  Lemma safe_sys_tgt: DSys.safe sys_tgt.
  Proof. apply AASys.safe. Qed.

  Lemma match_init_states
        lsts_src lsts_tgt
        (LSTS_SRC: lsts_src = imap (SNode.init_state num_tasks) 0 nodes)
        (LSTS_TGT: lsts_tgt = imap AANode.init_state 0 nodes)
    : Forall2 match_lst lsts_src lsts_tgt.
  Proof.
    subst.
    apply Forall2_nth. i.
    rewrite imap_nth_error_iff.
    rewrite imap_nth_error_iff. ss.

    destruct (lt_ge_dec n (length nodes)).
    2: {
      hexploit (nth_error_None2 _ nodes n); eauto.
      intro R. rewrite R in *. ss.
      econs.
      (* inv LSTS_SRC. inv LSTS_TGT. *)
    }

    hexploit (nth_error_Some2 _ nodes n); eauto.
    i. des. renames e1 NTH_EX into nd NODE_N.
    rewrite NODE_N in *.

    econs.
    econs.
    - nia.
    - rewrite repeat_length. ss.
    - apply nth_eq_list_eq.
      intro k.
      rewrite Coqlib.list_map_nth.
      unfold AANode.init_inbox.

      destruct (lt_ge_dec k num_nodes).
      + rewrite repeat_nth_error_Some by nia.
        rewrite repeat_nth_error_Some by nia.
        ss.
      + rewrite repeat_nth_error_None by nia.
        rewrite repeat_nth_error_None by nia.
        ss.
    - econs.
  Qed.

  Lemma AASys_step_pre_aux
        tm tid
        (nd: @SNode.t sysE bytes)
        es_r out nst
        (STEP: AANode.step tm (AANode.init_state tid nd)
                           es_r out nst)
        (NOT_EXACT: exact_skwd_base_time period tm = None)
    : snd es_r = [] /\ out = None /\
      nst = AANode.init_state tid nd.
  Proof.
    inv STEP; ss.
    esplits; ss.
    exfalso.
    congruence.
  Qed.

  Lemma AASys_msteps_pre_silent
        n st es st'
        tm lsts
        (MSTEPS: msteps sys_tgt n st es st')
        (STATE: st = AASys.State tm lsts)
        (LSTS_INIT: lsts = imap AANode.init_state 0 nodes)
        (NOT_EXACT_SKWD_BASE: forall m (M_RANGE: m < n),
            exact_skwd_base_time
              period (DTime.uadd tm m) = None)
    : Forall (silent_local_trace sysE) es /\
      st' = AASys.State (DTime.uadd tm n) lsts.
  Proof.
    depgen tm.
    induction MSTEPS; i; ss.
    - subst.
      esplits; ss.
      + apply Forall_forall.
        intros es IN.
        apply repeat_spec in IN. subst. ss.
      + rewrite DTime_uadd_zero. ss.
    - subst.
      assert (<<ES1_R_SILENT: Forall (fun x => snd x = []) es1_r>> /\
              <<ST1: st1 = AASys.State (DTime.succ tm)
                                       (imap AANode.init_state 0 nodes)>>).
      { clear - STEP NOT_EXACT_SKWD_BASE.
        inv STEP.

        assert (<<ES_NIL: Forall (fun x => snd x = []) es1_r>> /\
                <<OUTS: Forall (fun x => x = None) outs>> /\
                <<NSTS1: nsts1 = imap AANode.init_state 0 nodes>>).
        { rewrite Forall4_nth in STEPS.
          cut (forall n,
                  option_rel1 (fun x => snd x = [])
                              (nth_error es1_r n) /\
                  option_rel1 (fun x => x = None)
                              (nth_error outs n) /\
                  option_rel2
                    (fun nd x => x = AANode.init_state n nd)
                    (nth_error nodes n) (nth_error nsts1 n)).
          { intros AUX.
            splits.
            - apply Forall_nth. intro m.
              specialize (AUX m). des.
              eauto.
            - apply Forall_nth. intro m.
              specialize (AUX m). des.
              eauto.
            - subst.
              apply nth_eq_list_eq.
              intro m.
              rewrite imap_nth_error_iff. ss.

              specialize (AUX m). des.
              inv AUX1; ss.
          }

          intro m.
          specialize (STEPS m).
          inv STEPS.
          - esplits; ss.
            rewrite imap_nth_error_iff in *. ss.
            destruct (nth_error nodes m); ss. econs.
          - fold (events (nbE +' sysE)) in *.
            destruct (nth_error es1_r m); ss. clarify.
            match goal with
            | H: Some ?x = nth_error (imap _ _ _) m |- _ =>
              rewrite imap_nth_error_iff in H
            end.
            ss.
            destruct (nth_error nodes m); ss. clarify.
            match goal with
            | H: AANode.step tm _ _ _ _ |- _ => inv H; ss
            end.
            2: {
              exfalso.
              hexploit (NOT_EXACT_SKWD_BASE 0); eauto.
              { nia. }
              rewrite DTime_uadd_zero.
              i. congruence.
            }
            splits; ss.
            econs. ss.
        }

        des.
        esplits; eauto.
        subst.

        rewrite map_id_ext; eauto.
        intros st _.

        unfold AANode.accept_msgs.
        destruct st.
        hexploit (NOT_EXACT_SKWD_BASE 0).
        { nia. }
        rewrite DTime_uadd_zero.
        intro EX_NONE. rewrite EX_NONE.

        replace (map (AANode.get_msg_by_dest task_id) outs) with
            (repeat (@nil bytes) (length outs)).
        2: { apply nth_eq_list_eq.
             intro k.
             destruct (lt_ge_dec k (length outs)).
             2: {
               rewrite nth_error_None2.
               2: { rewrite repeat_length. ss. }
               rewrite nth_error_None2.
               2: { rewrite map_length. ss. }
               ss.
             }

             rewrite repeat_nth_error_Some by ss.
             rewrite Coqlib.list_map_nth.
             rewrite Forall_nth in OUTS.
             specialize (OUTS k).
             hexploit (nth_error_Some2 _ outs k); ss.
             i. des.
             rewrite NTH_EX in *. ss. clarify.
        }

        rewrite AANode.merge_inbox_nils. ss.
      }
      des.

      assert (ES1_SILENT: Forall (fun x => snd x = []) es1).
      { unfold DSys.filter_nb_sysstep in FILTER_NB.
        apply deopt_list_Some_iff in FILTER_NB.
        apply Forall_nth. intro k.
        rewrite Forall_nth in ES1_R_SILENT.

        specialize (ES1_R_SILENT k).
        destruct (nth_error es1 k) eqn: ES1_N.
        2: { fold (events sysE).
             rewrite ES1_N. ss. }
        fold (events sysE).
        rewrite ES1_N.

        assert (MAP_ES1_K:
                  nth_error (map (fun x => Some x) es1) k = (Some (Some p))).
        { rewrite map_nth_error_iff.
          esplits; eauto. }
        rewrite FILTER_NB in MAP_ES1_K.

        erewrite map_nth_error_iff in MAP_ES1_K; eauto.
        des.
        fold (events (nbE +' sysE)) in ES1_R_SILENT.
        rewrite MAP_ES1_K in ES1_R_SILENT.
        ss.
        destruct a; clarify. ss.
        destruct p; clarify. ss.

        unfold DSys.filter_nb_localstep in *.
        ss. clarify.
      }

      hexploit (IHMSTEPS (DTime.uadd tm 1)).
      { rewrite DTime_uadd_one. des; ss. }
      { i. rewrite DTime_uadd_assoc.
        apply NOT_EXACT_SKWD_BASE. nia. }
      rewrite DTime_uadd_assoc. ss.

      intros (TR2 & ST2).
      split; ss.
      apply Forall_nth. intro k.
      unfold cons_each_rel in CONS_EVENTS.
      rewrite Forall3_nth in CONS_EVENTS.
      specialize (CONS_EVENTS k).
      rewrite Forall_nth in TR2.
      specialize (TR2 k).
      rewrite Forall_nth in ES1_SILENT.
      specialize (ES1_SILENT k).

      fold (events sysE) in *.
      destruct (nth_error tr k); ss.
      destruct (nth_error es1 k).
      2: { inv CONS_EVENTS. }
      destruct (nth_error tr2 k).
      2: { inv CONS_EVENTS. }
      inv CONS_EVENTS.

      ss. econs; ss.
  Qed.

  Lemma SSys_ex_step_pre_silent
        tm (lsts: list (@SNode.state sysE bytes))
        mcs sntz
        (* (NO_SYNC: ~ Nat.divide period tm) *)
        (LSTS_INIT: lsts = imap (SNode.init_state num_tasks)
                                0 nodes)
    : SyncSys.step mcs period sntz
                   (SyncSys.State tm lsts)
                   (repeat (Z.of_nat tm, []) (length lsts))

                   (SyncSys.State (S tm) lsts).
  Proof.
    destruct (Nat_divide_dec period tm) as [DIV | NDIV].
    2: { econs 1; eauto. }
    econs 2; eauto.
    3: { instantiate (1:= repeat [] (length lsts)).
         rewrite map_repeat. ss. }
    { instantiate (1:= lsts).
      instantiate (1:= repeat [] (length lsts)).
      apply Forall4_nth. i.

      destruct (lt_ge_dec n (length lsts)).
      - hexploit (nth_error_Some2 _ lsts n); eauto.
        i. des.

        rewrite NTH_EX.
        rewrite repeat_nth_error_Some by ss.
        rewrite repeat_nth_error_Some by ss.
        econs.
        subst lsts.
        rewrite imap_length.
        rewrite imap_nth_error_iff in NTH_EX. ss.

        destruct (nth_error nodes n) as [nd|]; ss.
        clarify.
        econs 1.
        unfold SNode.init_box.
        rewrite <- NUM_TASKS_EQ. ss.
      - rewrite nth_error_None2 by ss.
        rewrite nth_error_None2.
        2: { rewrite repeat_length. ss. }
        rewrite nth_error_None2.
        2: { rewrite repeat_length. ss. }
        econs.
    }
    apply map_id_ext.
    intros nd IN. subst.
    rewrite imap_length.

    unfold SNode.accept_msgs.
    destruct nd; ss.
    rewrite map_repeat.
    unfold SNode.get_outbox_msg_by_dest.
    rewrite Coqlib.nth_error_nil.

    cut (inbox = repeat None (length nodes)).
    { congruence. }

    apply In_nth_error in IN. des.
    rewrite imap_nth_error_iff in IN. ss.
    destruct (nth_error nodes n); ss.
    clarify.
    rewrite <- NUM_TASKS_EQ. ss.
  Qed.

  Lemma SSys_ex_msteps_pre_silent
        tm lsts n st
        (* (NO_SYNC: forall m (RANGE_M: m < n), *)
        (*     ~ Nat.divide period (tm + m)) *)
        (STATE: st = SyncSys.State tm lsts)
        (LSTS: lsts = imap (SNode.init_state num_tasks) 0 nodes)
    : exists es,
      msteps sys_src n st es
             (SyncSys.State (tm + n) lsts) /\
      Forall (silent_local_trace _) es.
  Proof.
    guardH NUM_TASKS_EQ. guardH MCASTS_EQ.

    depgen st. depgen tm.
    induction n as [| n IH]; i; ss.
    { esplits.
      - rewrite plus_0_r. subst. econs; eauto.
      - apply Forall_forall.
        intros x IN.
        apply repeat_spec in IN.
        clarify.
    }
    subst.
    hexploit (IH (S tm)); eauto.
    (* { intros m RANGE_M. *)
    (*   replace (S tm + m) with (tm + S m) by nia. *)
    (*   apply NO_SYNC. nia. } *)
    (* { eauto. } *)
    intros (es & MSTEPS & ES_SILENT).

    esplits.
    - econs.
      + ss. apply SSys_ex_step_pre_silent. ss.
      + (* instantiate (1:= repeat (tm, []) (length lsts)). *)
        unfold DSys.filter_nb_sysstep.
        rewrite deopt_list_Some_iff.
        do 2 rewrite map_repeat. ss.
      + rewrite <- plus_n_Sm. ss. eauto.
      + instantiate (1:= map (fun x => (Z.of_nat tm, []) :: x) es).
        r. apply Forall3_nth.
        intro k.
        rewrite Coqlib.list_map_nth. ss.

        assert (length nodes = length es).
        { hexploit msteps_num_sites_eq; eauto. ss.
          unfold SyncSys.num_sites. ss.
          rewrite imap_length.
          i. des. ss. }

        fold (events sysE).
        destruct (nth_error es k) eqn: ES_K; ss.
        * rewrite repeat_nth_error_Some.
          2: { rewrite imap_length.
               apply nth_error_Some1' in ES_K. nia. }
          econs. ss.
        * rewrite nth_error_None2.
          2: { rewrite repeat_length.
               rewrite imap_length.
               apply nth_error_None in ES_K. nia. }
          econs.

    - apply Forall_forall.
      intros es1 ES1_IN.
      rewrite in_map_iff in ES1_IN. des. clarify.
      econs; ss.
      rewrite Forall_forall in ES_SILENT.
      eapply ES_SILENT. ss.
  Qed.


  Lemma async_sync_fmsim_states
        (tm_ns: nat)
        (SYTM_LB: period <= tm_ns)
        (* (SYTM_BASE_TIME: Nat.divide period sytm) *)
        lsts_src tm_tgt lsts_tgt
        (NUM_LSTS: length lsts_tgt = num_tasks)
        (TM_TGT: tm_tgt = DTime.of_ns tm_ns)
        (* (INV: Forall2 match_lst lsts_src lsts_tgt) *)
        (LSTS_SRC: lsts_src = imap (SNode.init_state num_tasks) 0 nodes)
        (LSTS_TGT: lsts_tgt = imap AANode.init_state 0 nodes)
    : fmsim_states _ sys_src sys_tgt
                   (SyncSys.State tm_ns lsts_src)
                   (AASys.State tm_tgt lsts_tgt).
  Proof.
    i. guardH LSTS_SRC. guardH LSTS_TGT.
    guardH NUM_LSTS. guardH TM_TGT. guardH MCASTS_EQ.

    assert (exists (tm1: nat),
               <<DIV: Nat.divide period (tm1 + max_clock_skew)>> /\
               <<FIRST_SYNC_TIME: tm1 - period < tm_ns <= tm1>>).
    {
      assert (BT_EQ: exists bt, bt = base_time period (tm_ns + max_clock_skew)).
      { esplits; eauto. }
      des.

      pose proof period_cond.
      eapply base_time_spec in BT_EQ; try nia.
      des.

      destruct (Nat.eq_dec bt (tm_ns + max_clock_skew)) as [EQ|NEQ].
      - subst bt.
        (* exists (bt - max_clock_skew). *)
        exists tm_ns.
        subst. esplits; eauto. nia.
      - exists (bt + period - max_clock_skew).
        esplits.
        + replace (bt + period - max_clock_skew + max_clock_skew)
            with (bt + period) by nia.
          apply Nat.divide_add_r; ss.
          apply Nat.divide_refl.
        + nia.
        + nia.
    }
    des.

    pose (sytm1 := tm1 + max_clock_skew).
    fold sytm1 in DIV.
    hexploit (period_fmsim_states sytm1); eauto.
    { nia. }
    { apply match_init_states; eauto. }
    intro FMSIM1.

    punfold FMSIM1. inv FMSIM1.

    pfold.
    2: { apply fmsim_states_monotone. }
    econs.
    { instantiate (1:= (tm1 - tm_ns) *
                       DTime.units_per_ns + n_tgt).
      nia. }

    i. eapply msteps_split in STEPS. des.
    assert (<<ES1_SILENT: Forall (silent_local_trace _) es1>> /\
            <<ST1: st1 = AASys.State (DTime.of_ns tm1) lsts_tgt>>).
    { hexploit AASys_msteps_pre_silent; try apply MSTEPS1; eauto.
      { i.
        eapply exact_skwd_base_time_None_iff.
        { rewrite TM_TGT. ss.
          clear - FIRST_SYNC_TIME.
          pose proof DTime.units_per_ns_pos.
          nia. }
        exists (sytm1 - period).
        rewrite TM_TGT. ss.
        split.
        2: { apply Nat.divide_sub_r; eauto.
             apply Nat.divide_refl. }
        subst sytm1.
        clear - M_RANGE FIRST_SYNC_TIME FIRST_SYNC_TIME0.
        pose proof DTime.units_per_ns_pos as DTIME_UNITS_POS.
        nia.
      }
      ss.
      rewrite TM_TGT. ss.
      replace (DTime.uadd (DTime.of_ns tm_ns)
                          ((tm1 - tm_ns) * DTime.units_per_ns))
        with (DTime.of_ns tm1).
      2: { unfold DTime.of_ns.
           unfold DTime.uadd. ss.
           f_equal. nia. }
      eauto.
    }

    assert (exists es_src_p,
               <<MSTEPS_SRC_P:
                 msteps sys_src (tm1 - tm_ns + max_clock_skew)
                        (SyncSys.State tm_ns lsts_src) es_src_p
                        (SyncSys.State sytm1 lsts_src)>> /\
               <<ES_SRC_P_SILENT:
                   Forall (silent_local_trace _) es_src_p>>).
    { hexploit (SSys_ex_msteps_pre_silent tm_ns lsts_src); eauto.
      i. des. subst.

      esplits; eauto.
      replace sytm1 with (tm_ns + (tm1 - tm_ns + max_clock_skew)).
      2: { subst sytm1. nia. }
      eauto.
    }

    des.
    hexploit STEPS_SIM; eauto.
    { subst sytm1.
      rewrite Nat.add_sub.
      subst st1. eauto. }
    i. des.

    hexploit msteps_concat.
    { apply MSTEPS_SRC_P. }
    { apply STEPS_SRC. }
    i. des.

    esplits; try apply MSTEPS_CONCAT.
    { nia. }
    { (* Forall2 tes_equiv *)
      apply Forall2_nth. i.
      destruct (nth_error es n) as [es_n|] eqn: ES_N.
      2: {
        rewrite nth_error_None2.
        2: {
          eapply nth_error_None in ES_N.
          apply Forall3_length in ES_CONCAT.
          apply Forall2_length in TRACE_EQUIV.
          apply Forall3_length in ES_DIV.
          des. nia.
        }
        econs.
      }

      rewrite Forall3_nth in ES_CONCAT.
      specialize (ES_CONCAT n).
      rewrite ES_N in ES_CONCAT.

      destruct (nth_error tr_src n) as [tr_src_n|] eqn: TR_SRC_N.
      2: { inv ES_CONCAT. }
      destruct (nth_error es_src_p n) as [es_src_p_n|] eqn: ES_SRC_P_N.
      2: { inv ES_CONCAT. }
      inv ES_CONCAT.

      rewrite Forall2_nth in TRACE_EQUIV.
      specialize (TRACE_EQUIV n).
      rewrite TR_SRC_N in TRACE_EQUIV.
      destruct (nth_error es2 n) as [es2_n|] eqn: ES2_N;
        inv TRACE_EQUIV.

      rewrite Forall3_nth in ES_DIV.
      specialize (ES_DIV n).
      rewrite ES2_N in ES_DIV.
      destruct (nth_error es1 n) as [es1_n|] eqn: ES1_N.
      2: { inv ES_DIV. }
      destruct (nth_error tr_tgt n) as [tr_tgt_n|] eqn: TR_TGT_N.
      2: { inv ES_DIV. }
      inv ES_DIV.

      rewrite Forall_nth in ES_SRC_P_SILENT.
      specialize (ES_SRC_P_SILENT n).
      rewrite ES_SRC_P_N in ES_SRC_P_SILENT. ss.

      rewrite Forall_nth in ES1_SILENT.
      specialize (ES1_SILENT n).
      rewrite ES1_N in ES1_SILENT. ss.
      econs.

      rewrite flatten_silent_local_trace_iff in *.
      unfold tes_equiv in *.
      unfold flatten_tes in *.
      do 2 rewrite map_app.
      do 2 rewrite concat_app.
      congruence.
    }
    eauto.
  Qed.

End PROOF.
