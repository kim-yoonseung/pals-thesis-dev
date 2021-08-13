From ITree Require Import ITree.
From compcert Require Coqlib.
From Paco Require Import paco.

Require Import sflib.
Require Import Axioms StdlibExt IntegersExt.

Require Import SysSem.
Require Import IPModel DiscreteTimeModel.
Require Import RTSysEnv.

Require Import List.
Require Import Arith ZArith Lia.


Module SNode.
  Section SNODE.
    Context {sysE: Type -> Type}.
    Context {msgT: Set}.
    Variable sanitize_msg: msgT -> msgT?.

    Notation appE := (sysE +' @abst_sendE msgT).

    Record t : Type :=
      mk { (* mcast_groups: list Tid ; *)
           app_state: Type ;
           init_app_state: app_state -> Prop ;

           period_begin: Z(*sytm*) -> list (msgT?) ->
                         app_state -> app_state -> Prop ;
           app_step: app_state -> app_state -> Prop ;
           at_event: app_state -> event_call appE -> Prop ;
           after_event: app_state -> event appE -> app_state -> Prop ;
           period_end: app_state -> bool ;
         }.

    (** ** ITree as SNode *)
    Section RUN_PERIOD.
      Variable num_tasks: nat.
      Variable mcasts: list (list Tid).

      Variable node: t.
      Notation app_state := node.(app_state).

      Inductive istep
        : app_state -> (event (nbE +' sysE))? ->
          (Tid * msgT)? -> app_state -> Prop :=
      | IStep_Tau
          ast ast'
          (TAU_STEP: node.(app_step) ast ast')
        : istep ast None None ast'
      | IStep_SysEvent
          R (syse: sysE R) (r: R)
          ast (evt: event (nbE +' sysE)) ast'
          (AT_EVENT: node.(at_event) ast (EventCall (inl1 syse)))
          (AFT_EVENT: node.(after_event)
                             ast (Event (inl1 syse) r) ast')
          (VIS_EVENT: evt = Event (subevent _ syse) r)
        : istep ast (Some evt) None ast'
      | IStep_Msg
          tid msg snde
          ast ast'
          (SEND_EVENT: snde = AbstSendEvent tid msg)
          (AT_EVENT: node.(at_event) ast (EventCall (inr1 snde)))
          (AFT_EVENT: node.(after_event)
                             ast (Event (inr1 snde) tt) ast')
        : istep ast None (Some (tid, msg)) ast'
      .

      Definition is_in_tids (tid: Tid) (tids: list Tid): bool :=
        existsb (Nat.eqb tid) tids.

      Definition check_available1
                 (outbox: list msgT?)
                 (tid_ad: Tid)
        : bool :=
        match nth_error outbox tid_ad with
        | None => false
        | Some entry =>
          match entry with
          | None => true
          | Some _ => false
          end
        end.

      Definition check_available
                 (tids_ad: list Tid)
                 (outbox: list msgT?) : bool :=
        andb_all (map (check_available1 outbox) tids_ad).

      Definition get_actual_dest (tid: Tid): list Tid :=
        if tid <? num_tasks then [tid]
        else
          match nth_error mcasts (tid - num_tasks) with
          | None => []
          | Some member_tids => member_tids
          end.

      Definition insert_msg1
                 (tids_ad: list Tid) (msg: msgT)
                 (tid_entry: Tid) (entry: msgT?)
        : msgT? :=
        if is_in_tids tid_entry tids_ad then
          Some msg
        else entry.

      Definition insert_msg
                 (tids_ad: list Tid) (msg: msgT)
                 (outbox: list msgT?)
        : list msgT? :=
        imap (insert_msg1 tids_ad msg) 0 outbox.

      Definition update_outbox
                 (outb: list msgT?)
                 (oms: (Tid * msgT)?)
        : list msgT? :=
        match oms with
        | None => outb
        | Some (tid_d, msg) =>
          match sanitize_msg msg with
          | None => outb
          | Some msg_s =>
            let tids_ad := get_actual_dest tid_d in
            if check_available tids_ad outb then
              insert_msg tids_ad msg_s outb
            else outb
          end
        end.

      Lemma update_outbox_None outb:
        update_outbox outb None = outb.
      Proof. ss. Qed.

      Lemma update_outbox_not_in
            outb tid1 tid2 msg
            (IN: ~ List.In tid1 (get_actual_dest tid2)):
        nth tid1 (update_outbox outb (Some (tid2, msg))) None =
        nth tid1 outb None.
      Proof.
        ss. des_ifs.
        unfold insert_msg.
        destruct (classic (tid1 < length outb)); cycle 1.
        { repeat rewrite nth_overflow; ss; try nia.
          rewrite imap_length. nia.
        }
        specialize (imap_nth_error_iff
                      _ _ (insert_msg1 (get_actual_dest tid2) m) 0 outb tid1). i.
        erewrite nth_error_nth' in H0; cycle 1.
        { rewrite imap_length. ss. }
        erewrite nth_error_nth' in H0; ss.
        inv H0. rewrite H2.
        instantiate (1:=None).
        unfold insert_msg1. des_ifs.
        unfold is_in_tids in *.
        erewrite existsb_exists in Heq1. des.
        rewrite Nat.eqb_eq in Heq2. subst. ss.
      Qed.

      Lemma update_outbox_in
            outb tid1 tid2 msg msg_s
            (LENGTH: length outb = num_tasks)
            (MSG: sanitize_msg msg = Some msg_s)
            (IN: In tid1 (get_actual_dest tid2))
            (TID: tid1 < length outb)
            (AVAILABLE: check_available (get_actual_dest tid2) outb = true):
        nth tid1 (update_outbox outb (Some (tid2, msg))) None = Some msg_s.
      Proof.
        ss. rewrite MSG, AVAILABLE.
        unfold insert_msg.
        specialize (imap_nth_error_iff
                      _ _ (insert_msg1 (get_actual_dest tid2) msg_s) 0 outb tid1). i.
        erewrite nth_error_nth' in H; cycle 1.
        { rewrite imap_length. ss. }
        erewrite nth_error_nth' in H; ss.
        inv H. rewrite H1. instantiate (1:=None).
        unfold insert_msg1. des_ifs.
        unfold is_in_tids in *.
        exploit existsb_exists. i. des.
        exploit x1; cycle 1.
        { i. rewrite x in Heq. ss. }
        { esplits; try eapply IN. apply Nat.eqb_eq. ss. }
      Qed.

      Lemma update_outbox_length outb msg:
        length (update_outbox outb msg) = length outb.
      Proof.
        unfold update_outbox. des_ifs.
        unfold insert_msg. apply imap_length.
      Qed.

      Lemma update_outbox_empty msg:
        update_outbox [] msg = [].
      Proof.
        unfold update_outbox. des_ifs.
      Qed.

      Lemma update_outbox_check_available
            tid1 tid2 outb msg
            (IN: ~ In tid1 (get_actual_dest tid2)):
        check_available1 (update_outbox outb (Some (tid2, msg))) tid1 =
        check_available1 outb tid1.
      Proof.
        unfold update_outbox. des_ifs.
        unfold insert_msg, check_available1.
        rewrite imap_nth_error_iff.
        unfold insert_msg1. ss.
        destruct (nth_error outb tid1) eqn:NTH; ss.
        des_ifs.
        unfold is_in_tids in *.
        rewrite existsb_exists in Heq2. des.
        rewrite Nat.eqb_eq in Heq1. subst. ss.
      Qed.

      Inductive istar
        : app_state * list msgT? ->
          events (nbE +' sysE) ->
          app_state? * list msgT? -> Prop :=
      | IStar_Fail
          ast outb
        : istar (ast, outb) [] (None, outb)
      | IStar_Base
          ast outb
        : istar (ast, outb) [] (Some ast, outb)
      | IStar_step
          ast es1 oms1 ast1
          outb outb1
          es2 oast' outb' es
          (ASTEP: istep ast es1 oms1 ast1)
          (INSERT_OUTB: outb1 = update_outbox outb oms1)
          (ASTAR': istar (ast1, outb1) es2
                         (oast', outb'))
          (EVENTS_APP: es = opt2list es1 ++ es2)
          (* (OUTMSGS_APP: oms = opt2list oms1 ++ oms2) *)
        : istar (ast, outb) es (oast', outb')
      .

      Definition init_box: list msgT? :=
        repeat None num_tasks.

      Inductive run_period
                (sytm: nat) (inb: list msgT?)
        : app_state -> events (nbE +' sysE) ->
          list msgT? -> app_state? -> Prop :=
      | RunPeriod_PrdInitFailed
          ast (* outb_i *)
          (* (OUT B_I: outb_i = repeat None num_tasks) *)
        : run_period sytm inb
                     ast [] (* outb_i *) [] None
      | RunPeriod_PrdInitOK
          ast ast1 es oast' outb'
          (PERIOD_BEGIN: node.(period_begin) (Z.of_nat sytm) inb ast ast1)
          (STAR: istar (ast1, init_box) es (oast', outb'))
          (FINAL: option_rel1 node.(period_end) oast')
        : run_period sytm inb
                     ast es outb' oast'.

    End RUN_PERIOD.

    Inductive state: Type :=
      State (tid: Tid) (node: t)
            (* (mids: list Tid) *)
            (inbox: list msgT?)
            (oast: node.(app_state)?).

    Inductive state_wf (num_tasks: nat) (tid: Tid)
      : state -> Prop :=
      StateWf
        node inb oast
        (LEN_INB: length inb = num_tasks)
      : state_wf num_tasks tid (State tid node inb oast).

    Definition init_state (num_tasks: nat)
               (tid: Tid) (node: t) : state :=
      (* let mids := i_get_mcast_of tid imcasts in *)
      State tid node (repeat None num_tasks) None.

    Lemma wf_init_state nts tid node
      : state_wf nts tid (init_state nts tid node).
    Proof.
      econs; eauto.
      rewrite repeat_length. ss.
    Qed.

    Inductive step
              (num_tasks: nat)
              (mcasts: list (list Tid))
              (sytm: nat)
      : state -> (events (nbE +' sysE)) ->
        (list msgT?) -> state -> Prop :=
    | Step_InactInact
        tid node inb inb_i
        (INB_I: inb_i = init_box num_tasks)
      : step num_tasks mcasts sytm
             (State tid node inb None) ([]) []
             (State tid node inb_i None)

    | Step_Activate
        tid node inb ast inb_i
        (INB_I: inb_i = init_box num_tasks)
        (INIT_APP_STATE: node.(init_app_state) ast)
      : step num_tasks mcasts sytm
             (State tid node inb None) ([]) []
             (State tid node inb_i (Some ast))

    | Step_Run
        tid node inb ast
        es outb oast' inb_i
        (RUN_PERIOD: run_period
                       num_tasks mcasts
                       node sytm inb ast es outb oast')
        (* (OUTBOX_DEST: outb_d = make_outbox outb) *)
        (INB_I: inb_i = init_box num_tasks)
      : step num_tasks mcasts sytm
             (State tid node inb (Some ast))
             (es) outb
             (State tid node inb_i oast')
    .

    Lemma wf_prsv
          nt mcs sytm
          st te oms st' tid
          (STEP: step nt mcs sytm
                      st te oms st')
          (WF: state_wf nt tid st)
      : state_wf nt tid st'.
    Proof.
      inv WF.
      inv STEP.
      - econs.
        unfold init_box.
        rewrite repeat_length. ss.
      - econs.
        unfold init_box.
        rewrite repeat_length. ss.
      - econs.
        unfold init_box.
        rewrite repeat_length. ss.
    Qed.

    Definition get_outbox_msg_by_dest
               (tid: Tid)
               (outb: list msgT?): msgT? :=
      match nth_error outb tid with
      | None => None
      | Some om => om
      end.

    Lemma get_outbox_msg_nth tid outb:
      get_outbox_msg_by_dest tid outb = nth tid outb None.
    Proof.
      unfold get_outbox_msg_by_dest. des_ifs.
      - eapply nth_error_nth in Heq. eauto.
      - rewrite nth_error_None in Heq.
        symmetry. apply nth_overflow. ss.
    Qed.

    Definition accept_msgs
               (in_msgs_sys: list (list msgT?))
               (st: state)
      : state :=
      match st with
      | State tid node _ oast =>
        let inb: list msgT? :=
            map (get_outbox_msg_by_dest tid) in_msgs_sys in
        State tid node inb oast
      end.

    Lemma wf_accept_msgs_prsv
          nts tid ins
          st st'
          (ACCEPT: accept_msgs ins st = st')
          (LEN_INS: length ins = nts)
          (WF: state_wf nts tid st)
      : state_wf nts tid st'.
    Proof.
      inv WF. ss.
      econs.
      rewrite map_length. ss.
    Qed.

    Lemma step_progress
          nts mcs sytm st
      : exists es outb st',
        step nts mcs sytm
             st es outb st'.
    Proof.
      destruct st as [tid node inb []].
      - esplits. econs; eauto.
        econs 1; eauto.
      - esplits. econs 1. eauto.
    Qed.

    (** istar lemmas *)

    Lemma istar_snoc_fail
          n mcs (node: t)
          ast outb es oast1 outb1
          (ISTAR: istar n mcs node (ast, outb) es (oast1, outb1))
      : istar n mcs node (ast, outb) es (None, outb1).
    Proof.
      remember (ast, outb) as st.
      remember (oast1, outb1) as st1.
      depgen ast. depgen oast1.
      revert outb outb1.
      induction ISTAR; i; ss.
      - clarify. econs.
      - clarify. econs.
      - clarify.
        hexploit IHISTAR; eauto.
        intro ISTAR'.
        econs; eauto.
    Qed.

    Lemma istar_app
          n mcs (node: t)
          ast0 outb0 es1
          ast1 outb1 es2
          oast' outb'
          (ISTAR1: istar n mcs node (ast0, outb0) es1
                         (Some ast1, outb1))
          (ISTAR2: istar n mcs node (ast1, outb1) es2
                         (oast', outb'))
      : istar n mcs node (ast0, outb0) (es1 ++ es2)
              (oast', outb').
    Proof.
      remember (ast0, outb0) as st0 eqn:ST0.
      remember (Some ast1, outb1) as st1 eqn:ST1.
      clear ast0 outb0 ST0.

      induction ISTAR1; i; ss.
      - clarify.
      - clarify.
        econs 3; eauto.
        rewrite app_assoc. ss.
    Qed.

  End SNODE.

End SNode.



Module SyncSys.
  Section SYS.
    Context {sysE: Type -> Type}.
    Context {msgT: Set}.

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
        (ATTACH_TIMESTAMP: map (fun es => (Z.of_nat tm, es)) ess = tes)
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
      des.
      esplits. econs 2; eauto.
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
          rewrite map_length. ss.
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
End SyncSys.



Module AppMod.
  Record t {sysE: Type -> Type} {msgT: Set}: Type :=
    mk { abst_state_t: Type;
         job_itree: Z (*sync_time*) -> list msgT? ->
                    abst_state_t ->
                    itree (sysE +' (* bsendE *) @abst_sendE msgT) abst_state_t ;

         init_abst_state: abst_state_t ;
       }.
End AppMod.


Module ITrSNode.
  Section SNODE.
    Context {sysE: Type -> Type}.
    Context {msgT: Set}.

    Variable app_mod: @AppMod.t sysE msgT.

    Let sendE: Type -> Type := @abst_sendE msgT.
    Let appE: Type -> Type := sysE +' sendE.

    Let astate_t: Type := AppMod.abst_state_t app_mod.
    Let t : Type := itree appE astate_t.

    Inductive init_app_state : t -> Prop :=
      InitAppState
        ast itr
        (INIT_ASTATE: AppMod.init_abst_state app_mod = ast)
        (INIT_ITREE: itr = Ret ast)
      : init_app_state itr.

    Inductive period_begin (zsytm: Z) (inb: list msgT?)
      : t -> t -> Prop :=
      PeriodBegin
        itr0 ast0 itr1
        (RET: observe itr0 = RetF ast0)
        (PERIOD_INIT_ITREE:
           itr1 = AppMod.job_itree app_mod zsytm inb ast0)
      : period_begin zsytm inb itr0 itr1.

    Inductive app_step: t -> t -> Prop :=
    | AppStep
        itr itr'
        (OBS_TAU: observe itr = TauF itr')
      : app_step itr itr'
    .

    Inductive at_event: t -> event_call appE -> Prop :=
      AtEvent
        R itr (e: appE R) k
        (OBS: observe itr = VisF e k)
      : at_event itr (EventCall e)
    .

    Inductive after_event: t -> event appE -> t -> Prop :=
      AfterEvent
        R itr (e: appE R) k (r: R) itr'
        (OBS: observe itr = VisF e k)
        (AFTER_EVENT: k r = itr')
      : after_event itr (Event e r) itr'.

    Definition period_end (itr: t): bool :=
      match observe itr with
      | RetF _ => true
      | _ => false
      end.

    Definition to_snode: SNode.t :=
      SNode.mk t
               init_app_state period_begin
               app_step at_event after_event period_end.

  End SNODE.
End ITrSNode.
