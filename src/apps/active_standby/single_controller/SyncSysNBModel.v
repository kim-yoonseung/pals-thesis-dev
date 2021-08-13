From ITree Require Import ITree.
From compcert Require Coqlib.
From Paco Require Import paco.

Require Import sflib.
Require Import Axioms StdlibExt IntegersExt.

Require Import SysSem.
Require Import IPModel DiscreteTimeModel.
Require Import RTSysEnv.
Require Import SyncSysModel.

Require Import List.
Require Import Arith ZArith Lia.


Module SyncSysNB.
  Section SYS.
    Context {sysE: Type -> Type}.
    Context {msgT: Set}.
    Variable is_nb_step: list (@SNode.state sysE msgT) -> list (@SNode.state sysE msgT) -> bool.

    Record t: Type :=
      mk { period: nat ;
           nodes: list (@SNode.t sysE msgT) ;
           mcasts: list (list Tid) ;

           sanitize_msg: msgT -> msgT? ;
         }.

    Inductive wf: t -> Prop :=
      Wf prd nds mcs sntz (* imcasts *)
         (PERIOD_POS: 0 < prd)
      : wf (mk prd nds mcs sntz).

    Record state: Type :=
      State { time: nat ;
              node_states: list (@SNode.state sysE msgT) ;
            }.

    Inductive state_wf (num_tasks: nat)
      : state -> Prop :=
      StateWf
        tm nsts
        (WF_NSTS: iForall (SNode.state_wf num_tasks) 0 nsts)
        (NUM_TASKS: length nsts = num_tasks)
      : state_wf num_tasks (State tm nsts).

    Definition init_state (tm_init: nat) (sys: t): state :=
      let nds := nodes sys in
      let nsts := imap (SNode.init_state (length nds)) 0 nds in
      State tm_init nsts.

    Lemma wf_init_state
          tm sys
          (* (WF_SYS: wf sys) *)
      : state_wf (length (nodes sys))
                 (init_state tm sys).
    Proof.
      econs; eauto.
      2: { rewrite imap_length. ss. }
      (* inv WF_SYS. ss. *)
      destruct sys as [period nodes mcasts]. ss.
      apply iForall_nth. ss.
      i. rewrite imap_nth_error_iff.
      destruct (nth_error nodes n); ss.
      econs. rewrite repeat_length; ss.
    Qed.

    Inductive step
              (mcasts: list (list Tid)) (period: nat)
              (sntz: msgT -> msgT?)
      : state -> list (tsp * events (nbE +' sysE)) ->
        state -> Prop :=
    | Step_Wait
        tm nsts tes
        (WAIT: ~ Nat.divide period tm)
        (EMPTY_EVTS: tes = List.repeat (Z.of_nat tm, []) (length nsts))
      : step mcasts period sntz
             (State tm nsts) tes (State (S tm) nsts)

    | Step_Run
        tm nsts ess tes outs nsts1 nsts'
        (WAIT: Nat.divide period tm)
        (STEPS: Forall4 (SNode.step sntz (length nsts) mcasts tm) nsts ess outs nsts1)
        (ACCEPT_MSGS: List.map (SNode.accept_msgs outs) nsts1 = nsts')
        (ATTACH_TIMESTAMP:
           tes = if is_nb_step nsts nsts'
                 then map (fun es => (Z.of_nat tm, [embed (Event NobehEvent tt)])) ess
                 else map (fun es => (Z.of_nat tm, es)) ess)
      : step mcasts period sntz
             (State tm nsts) tes (State (S tm) nsts')
    .

    Lemma wf_prsv
          nt mcs sntz prd
          st es st'
          (STEP: step mcs prd sntz
                      st es st')
          (WF_STATE: state_wf nt st)
      : state_wf nt st'.
    Proof.
      inv WF_STATE. inv STEP.
      - econs; eauto.
      - econs; eauto.
        2: { rewrite map_length.
             hexploit Forall4_length; eauto.
             i. des. eauto. }
        apply iForall_nth. i.
        rewrite iForall_nth in WF_NSTS.
        specialize (WF_NSTS n). ss.

        rewrite Coqlib.list_map_nth.
        destruct (nth_error nsts n) as [nst_n|] eqn: NST_N.
        2: {
          rewrite nth_error_None2.
          { econs. }
          apply Forall4_length in STEPS.
          des.
          rewrite <- LEN14.
          apply nth_error_None. ss.
        }

        hexploit Forall4_nth1; eauto. i. des.
        rewrite NTH4. ss.
        eapply SNode.wf_accept_msgs_prsv; eauto.
        { hexploit Forall4_length; eauto. i. des. ss. }
        eapply SNode.wf_prsv; eauto.
    Qed.

    Lemma wf_progress
          mcs prd sntz
          nt st
          (WF_STATE: state_wf nt st)
      : exists es st',
        step mcs prd sntz st es st'.
    Proof.
      destruct st as [tm nsts].

      destruct (Nat_divide_dec prd tm).
      2: { esplits. econs 1; eauto. }

      assert (exists l2 l3 l4,
                 Forall4 (SNode.step sntz (length nsts) mcs tm)
                         nsts l2 l3 l4).
      { eapply Forall4_exists_list.
        i. apply SNode.step_progress. }
      des. esplits. econs 2; eauto.
    Qed.

    Definition num_sites (st: state): nat :=
      length st.(node_states).

    Program Definition as_dsys (sys: t) (tm_init: nat): DSys.t :=
      DSys.mk state num_sites
              (step (mcasts sys) (period sys) (sanitize_msg sys))
              (fun st => st = init_state tm_init sys) _.
    Next Obligation.
      splits.
      - unfold num_sites.
        inv STEP; ss.
        + rewrite repeat_length. ss.
        + hexploit Forall4_length; eauto. i. des.
          des_ifs; rewrite map_length; ss.
      - unfold num_sites.
        inv STEP; ss.
        rewrite map_length.
        hexploit Forall4_length; eauto. i. des. ss.
    Qed.

    Lemma safe
          tm
          (sys: t)
          (WF: wf sys)
      : DSys.safe (as_dsys sys tm).
    Proof.
      econs.
      { esplits; ss. }
      i.
      pose (num_tasks := length (nodes sys)).

      assert (WF_STATE: state_wf num_tasks st_i).
      { subst num_tasks.
        inv INIT.
        apply wf_init_state. }
      rename st_i into st.
      clear INIT.
      depgen st.

      pcofix CIH. i.
      pfold. econs.
      { eapply wf_progress. eauto. }
      i. right. ss.
      hexploit wf_prsv; eauto.
    Qed.

  End SYS.
End SyncSysNB.
