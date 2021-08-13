From ITree Require Import ITree.
From compcert Require Coqlib.
From Paco Require Import paco.

Require Import sflib.
Require Import Axioms StdlibExt IntegersExt.

Require Import SysSem.
Require Import IPModel DiscreteTimeModel.
Require Import RTSysEnv.
Require Import NWSysModel SyncSysModel.
Require Import ProgSem.

Require Import List.
Require Import Arith ZArith Lia.

Require Import Relation_Operators.

(* Definition filter_by_dest {A} *)
(*            (tids_dest: list Tid) *)
(*            (smsgs: list (Tid * A?)) *)
(*   : list A? := *)
(*   (* let (tid_s, dmsgs) := smsgs in *) *)
(*   filtermap (chget_by_dest tids_dest) smsgs. *)




Module AANode.

  Section ABST_ASYNC_NODE.
    Import SNode.

    Context {sysE: Type -> Type}.
    Context `{SystemEnv}.
    (* Context {msgT: Set}. *)
    (* Context `{rnws_params}. *)
    Let msgT: Set := bytes.
    Notation appE := (sysE +' bsendE).
    Notation t := (@SNode.t sysE msgT).

    (* Definition istate (node: @SNode.t sysE msgT): Type := *)
    (*   nat(*sytm*) * nat(*ocnt*) * *)
    (*   list (list msgT)(*inbc*) * node.(app_state). *)
    (*   (* IState (sytm: nat) (old_msg_cnt: nat) *) *)
    (*   (*        (ast: node.(app_state)). *) *)
    Inductive stage_t: Type :=
    | Ready (sytm: nat) (inbc: list (list msgT))
    | Running (sytm: nat) (sh: list bool)
    | Done
    .

    Definition istate_t (node: @SNode.t sysE msgT): Type :=
      nat(*ocnt*) * stage_t * node.(app_state).

    Inductive istate_wf (node: @SNode.t sysE msgT)
      : istate_t node -> Prop :=
      IStateWf
        ocnt stg ast
        (WF_SEND_HIST:
           forall sytm sh
             (STAGE_RUNNING: stg = Running sytm sh),
             length sh = num_tasks)
      : istate_wf node (ocnt, stg, ast).

    Record state: Type :=
      State { task_id: Tid;
              node: @SNode.t sysE msgT;
              (* mcast_ids: list Tid; *)
              (* num_nodes: nat; *)

              inbox_n: list (list msgT);
              istate: (istate_t node)?;
            }.

    Inductive state_wf (tid: Tid)
      : state -> Prop :=
      StateWf
        nd (* mids *) inbn oist
        (* (WF_NODE: SNode.wf mcasts' nd) *)
        (* (MCAST_IDS: SysEnv.get_mcast_of tid = mids) *)
        (INBN_LENGTH: length inbn = num_tasks)
        (ISTATE_WF: option_rel1 (istate_wf nd) oist)
      : state_wf tid (State tid nd inbn oist).

    Definition init_inbox: list (list msgT) :=
      List.repeat [] num_tasks.

    Definition inbox_sz (inb: list (list msgT)): nat :=
      length (concat inb).

    Definition init_state (tid: Tid) (node: t) : state :=
      State tid node (* (SysEnv.get_mcast_of tid) *)
            init_inbox None.

    Lemma wf_init_state
          tid nd
      : state_wf tid (init_state tid nd).
    Proof.
      econs; eauto.
      - unfold init_inbox.
        rewrite repeat_length. ss.
      - econs.
    Qed.

    Fixpoint merge_inbox
             (inbn inbn_arr: list (list msgT))
      : list (list msgT) :=
      match inbn with
      | [] => []
      | ent1 :: ents1 =>
        match inbn_arr with
        | [] => inbn
        | ent2 :: ents2 =>
          (ent1 ++ ent2) :: merge_inbox ents1 ents2
        end
      end.

    Lemma merge_inbox_nils
          (inb: list (list msgT)) n
      : merge_inbox inb (repeat [] n) = inb.
    Proof.
      depgen n.
      induction inb as [| h t IH]; i; ss.
      destruct n; ss.
      rewrite IH. rewrite app_nil_r. ss.
    Qed.

    Lemma merge_inbox_length
          inb inb'
      : length (merge_inbox inb inb') =
        length inb.
    Proof.
      depgen inb'.
      induction inb as [| h t IH]; i; ss.
      destruct inb'; ss.
      f_equal. eauto.
    Qed.

    Lemma merge_inbox_size
          inb1 inb2
          (INBS_LEN_EQ: length inb1 = length inb2)
      : inbox_sz (merge_inbox inb1 inb2) =
        inbox_sz inb1 + inbox_sz inb2.
    Proof.
      unfold inbox_sz.
      remember (length inb1) as n eqn: INB_LEN1.
      rename INBS_LEN_EQ into INB_LEN2.
      depgen inb2. depgen inb1.

      induction n as [| n' IH]; i; ss.
      { destruct inb1; destruct inb2; ss. }
      destruct inb1 as [| h1 t1]; ss.
      destruct inb2 as [| h2 t2]; ss.

      repeat rewrite app_length.
      rewrite IH; eauto. nia.
    Qed.

    Lemma inbox_size_empty
      : inbox_sz init_inbox = 0.
    Proof.
      unfold init_inbox.
      generalize num_tasks as k.
      induction k as [|k' IH]; ss.
    Qed.

    Lemma merge_inbox_nth
          inb inb' n r
          (NTH: nth_error inb n = Some r)
      : nth_error (merge_inbox inb inb') n =
        Some (r ++ match nth_error inb' n with
                   | None => []
                   | Some r' => r'
                   end).
    Proof.
      revert inb inb' r NTH.
      induction n as [| n' IH]; i; ss.
      { destruct inb, inb'; clarify. ss.
        rewrite app_nil_r. ss. }
      destruct inb, inb'; ss.
      { rewrite app_nil_r. ss. }
      apply IH; eauto.
    Qed.

    Lemma merge_inbox_nth_None
          inb inb' n
          (NTH: nth_error inb n = None)
      : nth_error (merge_inbox inb inb') n = None.
    Proof.
      depgen inb. depgen inb'.
      induction n as [| n' IH]; i; ss.
      { desf. }
      desf.
      destruct inb'; ss; clarify.
      eauto.
    Qed.



    (* Definition istate_update_inbox *)
    (*            {node: @SNode.t sysE msgT} *)
    (*            (nsytm: nat) *)
    (*            (inbn: list (list msgT)) *)
    (*            (ist: istate_t node) *)
    (*   : (istate_t node)? := *)
    (*   let '(ocnt, stg, ast) := ist in *)
    (*   match stg with *)
    (*   | Done => Some (ocnt, Ready nsytm _, ast) *)
    (*   | _ => None *)
    (*   end. *)

    (* Definition filter_by_dest *)
    (*            (tid: Tid) (mids: list Tid) *)
    (*            (in_msgs: list (list (Tid * msgT))) *)
    (*   : list (list msgT) := *)
    (*   map (filtermap (check_dest tid mids)) *)



    (* Definition inbox_accept_msgs *)
    (*            (in_msgs: list (list (Tid * msgT))) *)
    (*            (inb: list (list msgT)) *)
    (*   : list (list msgT) := *)
    (*   let ms_new: list (list msgT) := *)
    (*       map (filter_by_dest tid  *)
    (*       map (filtermap (check_dest tid (mcast_groups node))) in_msgs in *)

    (* Definition filter_by_dest_opt *)
    (*            (ids_to_me: list Tid) *)
    (*            (om: (Tid * msgT)?) *)
    (*   : list msgT *)

    Definition get_msg_by_dest
               (tid: Tid)
               (om: (Tid * msgT)?)
      : list msgT :=
      match om with
      | None => []
      | Some (id_dest, msg) =>
        if orb (id_dest =? tid)
               (existsb (Nat.eqb id_dest) (get_mcast_of tid))
        then [msg] else []
      end.

    Definition accept_msgs (tm: DTime.t)
               (in_msgs: list (Tid * msgT)?)
               (st: state)
      : state :=
      match st with
      | State tid node inbn oist =>
        let inbn1 :=
            match exact_skwd_base_time period tm with
            | None => inbn
            | Some _ => init_inbox
            end
        in
        let ms_new := map (get_msg_by_dest tid) in_msgs in
        State tid node (merge_inbox inbn1 ms_new) oist
      end.

    Inductive choose_inbox_rowmsg
      : list msgT -> msgT? -> Prop :=
    | ChooseInboxRowmsg_Nil
      : choose_inbox_rowmsg [] None
    | ChooseInboxRowmsg_Nonnil
        ms msg
        (MSG_IN_ROW: In msg ms)
      : choose_inbox_rowmsg ms (Some msg)
    .

    Inductive abst_inbox
              (ocnt: nat) (inbc: list (list msgT))
              (* (inbc_a: list msgT?) *)
      : list msgT? -> nat -> Prop :=
    | AbstInbox_OK
        inbc_a
        (INBC_A: Forall2 choose_inbox_rowmsg inbc inbc_a)
      : abst_inbox ocnt inbc inbc_a O
    | AbstInbox_Error
        inbc_a ocnt'
        (TOO_MANY_MSGS: ocnt + length (concat inbc) > length inbc * 4)
      : abst_inbox ocnt inbc inbc_a ocnt'
    .

    Inductive sh_tau_steps (sh: list bool)
              (node: @SNode.t sysE msgT)
      : SNode.app_state node -> SNode.app_state node -> Prop :=
    | SHTau_Refl
        ast
      : sh_tau_steps sh node ast ast
    | SHTau_AppStep
        ast ast1 ast'
        (APP_STEP: node.(app_step) ast ast1)
        (TAU_REST: sh_tau_steps sh node ast1 ast')
      : sh_tau_steps sh node ast ast'
    | SHTau_SendHistBlocks
        tid msg snde
        ast ast1 ast'
        (SEND_EVENT: snde = AbstSendEvent tid msg)
        (AT_EVENT: node.(at_event) ast (EventCall (inr1 snde)))
        (AFT_EVENT: node.(after_event)
                           ast (Event (inr1 snde) tt) ast1)
        (OUTMSGS: check_send_hist sh tid = None)
        (TAU_REST: sh_tau_steps sh node ast1 ast')
      : sh_tau_steps sh node ast ast'
    .

    Definition process_outmsg (sh: list bool)
               (om: (Tid * msgT)?)
      : list bool * (Tid * msgT)? :=
      match om with
      | None => (sh, None)
      | Some (tid_d, msg) =>
        match check_send_hist sh tid_d with
        | None => (sh, None)
        | Some sh' => (sh', Some (tid_d, resize_bytes msg_size msg))
        end
      end.

    Inductive step (tm: DTime.t)
      : state -> tsp * events (nbE +' sysE) ->
        (Tid * msgT)? -> state -> Prop :=
    (* Off *)
    | Step_StayOff
        tid node inbn
      : step tm
             (State tid node inbn None)
             (0%Z, []) None
             (State tid node inbn None)

    | Step_TurnOn
        tid node inbn sytm
        ocnt ast
        (BASE_TIME: exact_skwd_base_time period tm = Some sytm)
        (OLD_CNT: ocnt <= inbox_sz inbn)
        (INIT_APP_STATE: node.(init_app_state) ast)
      : step tm
             (State tid node inbn None)
             (0%Z, []) None
             (State tid node inbn
                    (Some (ocnt, Done, ast)))
    (* On *)
    | Step_Fail
        tid node inbn ist
      : step tm
             (State tid node inbn (Some ist))
             (0%Z, []) None
             (State tid node inbn None)

    | Step_Sync
        tid node inbn
        ocnt sytm ast
        (SYNC_TIME: exact_skwd_base_time period tm = Some sytm)
      : step tm
             (State tid node inbn
                    (Some (ocnt, Done, ast)))
             (0%Z, []) None
             (State tid node inbn
                    (Some (ocnt, Ready sytm inbn, ast)))

    | Step_On_Stay
        tid node inbn
        ocnt stg ast
        (SYNC_TIME: exact_skwd_base_time period tm = None)
      : step tm
             (State tid node inbn
                    (Some (ocnt, stg, ast)))
             (0%Z, []) None
             (State tid node inbn
                    (Some (ocnt, stg, ast)))

    | Step_StartRun
        tid node inbn
        ocnt sytm inbc ast
        inbc_a ocnt' ast' sh
        (SYNC_TIME: exact_skwd_base_time period tm = None)
        (INBOX: abst_inbox ocnt inbc inbc_a ocnt')
        (PERIOD_BEGIN: node.(period_begin)
                              (Z.of_nat sytm) inbc_a ast ast')
        (SEND_HIST: sh = List.repeat false num_tasks)
      : step tm
             (State tid node inbn
                    (Some (ocnt, Ready sytm inbc, ast)))
             (0%Z, []) None
             (State tid node inbn
                    (Some (ocnt', Running sytm sh, ast')))

    | Step_Running_Go
        tid node inbn
        ocnt sytm sh ast
        ast1 oe om sh' ast'
        es oms zsytm
        (SYNC_TIME: exact_skwd_base_time period tm = None)
        (TAU_STEPS: sh_tau_steps sh node ast ast1)
        (ISTEP: SNode.istep node ast1 oe om ast')
        (EVTS: es = opt2list oe)
        (OUTMSGS: (sh', oms) = process_outmsg sh om)
        (TIMESTAMP: zsytm = Z.of_nat sytm)
      : step tm
             (State tid node inbn
                    (Some (ocnt, Running sytm sh, ast)))
             (zsytm, es) oms
             (State tid node inbn
                    (Some (ocnt, Running sytm sh', ast')))

    | Step_Running_Done
        tid node inbn
        ocnt sytm sh ast ast_f
        (SYNC_TIME: exact_skwd_base_time period tm = None)
        (* (TAU_STEPS: clos_refl_trans *)
        (*           _ node.(app_step) ast ast_f) *)
        (TAU_STEPS: sh_tau_steps sh node ast ast_f)
        (PERIOD_END: node.(SNode.period_end) ast_f)
      : step tm
             (State tid node inbn
                    (Some (ocnt, Running sytm sh, ast)))
             (0%Z, []) None
             (State tid node inbn
                    (Some (ocnt, Done, ast_f)))
    .

    Lemma wf_prsv
          tm tid
          st es oms st'
          (STEP: step tm st es oms st')
          (WF_STATE: state_wf tid st)
      : state_wf tid st'.
    Proof.
      inv WF_STATE.
      destruct oist as [ist|].
      2: { inv STEP; ss. }
      inv STEP; ss.
      - existT_elim. clarify.
      - existT_elim. clarify.
        econs; eauto. ss.
        econs. i. clarify.
        apply repeat_length.
      - existT_elim. clarify.
        unfold process_outmsg in *.
        inv ISTATE_WF.
        destruct om as [[tid_d msg]|]; ss.
        2: { clarify. }
        destruct (check_send_hist sh tid_d) as [sh_nxt|] eqn: SH'.
        2: { clarify. }

        clarify.
        econs; eauto. ss.
        econs. i. clarify.
        apply check_send_hist_Some in SH'; eauto.
        nbdes. eauto.
    Qed.

    Lemma step_progress
          tm st
      : exists es oms st',
        step tm st es oms st'.
    Proof.
      destruct st as [tid nd inbn oist].
      destruct oist.
      - esplits. eapply Step_Fail.
      - esplits. econs 1.
    Qed.

    Lemma wf_accept_msgs_prsv
          tid st
          tm in_msgs
          (WF_STATE: state_wf tid st)
      : state_wf tid (accept_msgs tm in_msgs st).
    Proof.
      inv WF_STATE. ss.
      econs; ss.
      rewrite merge_inbox_length.
      desf; ss.
      unfold init_inbox.
      apply repeat_length.
    Qed.

    (* Inductive star (period: nat) (tm: DTime.t) *)
    (*   : state -> nat * events (nbE +' sysE) -> *)
    (*     list (Tid * msgT) -> state -> Prop := *)
    (* | Star_Base *)
    (*     st sytm *)
    (*   : star period tm *)
    (*          st (sytm, []) [] st *)
    (* | Star_Step *)
    (*     sytm st es1 oms1 st1 *)
    (*     es2 oms2 st' es oms *)
    (*     (STEP: step tm *)
    (*                 st (sytm, es1) oms1 st1) *)
    (*     (STAR_REST: star period (DTime.succ tm) *)
    (*                      st1 (sytm, es2) oms2 st') *)
    (*     (ES: es = es1 ++ es2) *)
    (*     (OMS: oms = oms1 ++ oms2) *)
    (*   : star period tm *)
    (*          st (sytm, es) oms st'. *)

  End ABST_ASYNC_NODE.
End AANode.


Module AASys.
  Section SYS.
    Import SyncSys.
    Context {sysE: Type -> Type}.
    (* Context {msgT: Set}. *)
    Context `{SystemEnv}.
    (* Let msgT: Set := bytes. *)

    Record state: Type :=
      State { time: DTime.t ;
              node_states: list (@AANode.state sysE) ;
            }.

    Inductive state_wf
      : state -> Prop :=
      StateWf
        tm nsts
        (WF_NSTS: iForall AANode.state_wf 0 nsts)
      : state_wf (State tm nsts).

    Definition init_state (tm_init: nat)
               (sys: list SNode.t): state :=
      let num_nodes := length sys in
      let nsts := imap AANode.init_state 0 sys in
      State (DTime.of_ns tm_init) nsts.

    Lemma wf_init_state
          tm sys
      : state_wf (init_state tm sys).
    Proof.
      econs.
      apply iForall_nth. i. ss. r.
      rewrite imap_nth_error_iff. ss.
      destruct (nth_error sys n); ss.
      apply AANode.wf_init_state.
    Qed.

    Inductive step
      : state -> list (tsp * events (nbE +' sysE)) ->
        state -> Prop :=
      Step_Run
        tm nsts tes outs nsts1 nsts' tm'
        (STEPS: Forall4 (AANode.step tm)
                        nsts tes outs nsts1)
        (ACCEPT_MSGS: List.map (AANode.accept_msgs tm outs)
                               nsts1 = nsts')
        (TIME: tm' = DTime.succ tm)
      : step (State tm nsts) tes (State tm' nsts').

    Lemma wf_prsv
          st tes st'
          (STEP: step st tes st')
          (WF: state_wf st)
      : state_wf st'.
    Proof.
      inv WF. inv STEP.
      econs.
      apply iForall_nth. i. ss. r.
      rewrite Coqlib.list_map_nth.
      destruct (nth_error nsts1 n) as [nst_n|] eqn:NST_N; ss.
      hexploit Forall4_nth4; eauto. i. des.
      eapply AANode.wf_accept_msgs_prsv.
      eapply AANode.wf_prsv; eauto.
      rewrite iForall_nth in WF_NSTS. ss.
      specialize (WF_NSTS n).
      rewrite NTH1 in WF_NSTS. ss.
    Qed.

    Lemma step_progress
          st
      : exists tes st', step st tes st'.
    Proof.
      destruct st as [tm nsts].
      assert (STEP_EX: forall n (N_UB: n < length nsts),
                 exists x,
                   option_rel4 (AANode.step tm)
                               (nth_error nsts n)
                               (Some (fst (fst x)))
                               (Some (snd (fst x)))
                               (Some (snd x))).
      { i. eapply nth_error_Some in N_UB.
        eapply Some_not_None in N_UB. des.
        hexploit (AANode.step_progress tm a).
        i. des.
        rewrite N_UB.
        exists (es, oms, st'). ss.
        econs. ss.
      }
      apply exists_list in STEP_EX. des.
      exists (map (fun x => fst (fst x)) l).
      esplits.
      econs; eauto.
      instantiate (1:= map (fun x => snd x) l).
      instantiate (1:= map (fun x => snd (fst x)) l).

      apply Forall4_nth. intro i.
      destruct (le_lt_dec (length nsts) i).
      - rewrite nth_error_None2; eauto.
        rewrite nth_error_None2.
        2: { rewrite map_length. nia. }
        rewrite nth_error_None2.
        2: { rewrite map_length. nia. }
        rewrite nth_error_None2.
        2: { rewrite map_length. nia. }
        econs.
      - assert (exists a, nth_error nsts i = Some a).
        { apply Some_not_None.
          eapply nth_error_Some. ss. }
        assert (X_EQ: exists x, nth_error l i = Some x).
        { apply Some_not_None.
          eapply nth_error_Some. rewrite LIST_LEN. ss. }
        des.

        hexploit NTH_PROP; eauto.
        repeat rewrite Coqlib.list_map_nth.
        rewrite X_EQ. ss.
    Qed.


    Definition num_sites (st: state): nat :=
      length st.(node_states).

    Program Definition as_dsys (sys: list SNode.t) (tm_init: nat): DSys.t :=
      DSys.mk state num_sites step
              (fun st => st = init_state tm_init sys) _.
    Next Obligation.
      splits.
      - unfold num_sites.
        inv STEP; ss.
        hexploit Forall4_length; eauto. i. des. ss.
        (* + rewrite repeat_length. ss. *)
        (* + hexploit Forall4_length; eauto. i. des. ss. *)
      - unfold num_sites.
        inv STEP; ss.
        rewrite map_length.
        hexploit Forall4_length; eauto. i. des. ss.
    Qed.

    Lemma safe
          tm nodes
      : DSys.safe (as_dsys nodes tm).
    Proof.
      econs.
      { exists (init_state tm nodes). ss. }
      i. ss.
      hexploit (wf_init_state tm nodes); eauto.
      rewrite <- INIT.
      clear INIT.
      revert st_i.

      pcofix CIH.
      intros st WF.
      pfold.
      econs.
      { eapply step_progress. }
      i. ss.
      right.
      hexploit wf_prsv; eauto.
    Qed.

  End SYS.
End AASys.
