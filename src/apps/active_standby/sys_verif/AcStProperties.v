From Paco Require Import paco.
From ITree Require Import ITree.
Require Import sflib.

Require Import StdlibExt IntegersExt.
Require Import SysSem.
Require Import SyncSysModel.

Require Import FMSim FMSim_Switch.
Require Import PALSSystem.

Require console ctrl dev.

Require Import AcStSystem.
Require Import SpecConsole SpecController SpecDevice.
Require Import VerifConsole VerifController VerifDevice.

Require Import AcStRefinement.

Require Import ZArith Streams List Lia.

Local Opaque Z.of_nat Z.to_nat.

Import ActiveStandby.

Set Nested Proofs Allowed.

Require Import MSteps.
Require Import CProgEventSem.
(* Require Import AsyncSyncRef. *)

Require Import BehavUtils.

Local Opaque Nat.add Nat.mul.
Local Opaque MAX_TIMEOUT.
Local Opaque period.
Arguments Nat.min: simpl nomatch.
Arguments nth_error: simpl nomatch.



Definition dev_tids: list nat :=
  [tid_dev1; tid_dev2; tid_dev3].

Definition is_dev_tid (tid: nat): Prop :=
  In tid dev_tids.

Definition is_ctrl_tid (tid: nat): Prop :=
  tid = tid_ctrl1 \/ tid = tid_ctrl2.

Definition compl_event (logv: Z): event obsE :=
  Event (inl1 (WriteLog logv)) tt.


Module AcStInv.

  Definition num_tasks: nat := 6.

  Definition valid_abst_queue (aq: list nat): Prop :=
    <<ELEMS_NODUP: NoDup aq>> /\
    <<EACH_DEV_TID: Forall is_dev_tid aq>>.

  Inductive match_queue
  : list nat -> Z * Z * list Z -> Prop :=
  | MatchQueue_Empty
      csr qe q
      (LEN_Q: Zlength q = QSIZE)
      (VALID_CURSOR: (0 <= csr < QSIZE)%Z)
      (CURSOR_END: csr = qe)
    : match_queue [] (csr, qe, q)
  | MatchQueue_Cons
      csr qe q
      h t
      (LEN_Q: Zlength q = QSIZE)
      (VALID_CURSOR: (0 <= csr < QSIZE)%Z)
      (CURSOR_NOT_END: csr <> qe)
      (HEAD_EQ: nth_error q (Z.to_nat csr) = Some (Z.of_nat h))
      (MATCH_REST: match_queue t (adv_qidx csr, qe, q))
    : match_queue (h :: t) (csr, qe, q)
  .

  Definition queue_of_ctrl (cst: CtrlState.t)
    : Z * Z * list Z :=
    (CtrlState.queue_begin cst,
     CtrlState.queue_end cst,
     CtrlState.queue cst).

  Definition try_add_abst_queue
             (tid: nat)
             (aq: list nat)
    : list nat :=
    if existsb (Nat.eqb tid) aq then aq else snoc aq tid.

  Lemma match_try_add_queue
        tid_add
        aq (st st': CtrlState.t)
        (* (VALID_AQ: valid_abst_queue aq) *)
        (TID_ADD_DEV: is_dev_tid tid_add)
        (MATCH_Q: match_queue aq (queue_of_ctrl st))
        (ST': st' = try_add_queue st (Z.of_nat tid_add))
    : match_queue aq (queue_of_ctrl st').
  Proof.
  Admitted.

  Lemma match_try_release
        tid_add
        aq (st st': CtrlState.t)
        (* (VALID_AQ: valid_abst_queue aq) *)
        (TID_ADD_DEV: is_dev_tid tid_add)
        (MATCH_Q: match_queue aq (queue_of_ctrl st))
        (ST': st' = try_release st (Z.of_nat tid_add))
    : match_queue aq (queue_of_ctrl st').
  Proof.
  Admitted.

  Record abst_ctrl_t: Type :=
    AbstCtrl {
        inbox_ctrl: list bytes? ;
        active_flag: bool ;
        abst_queue: list nat ;
        head_timeout: nat ;
      }.

  Definition cur_owner (ac: abst_ctrl_t): nat? :=
    (* let '(_, (_, aq, tout)) := ac in *)
    match abst_queue ac with
    | [] => None
    | h::_ =>
      if 0 <? head_timeout ac then Some h else None
    end.

  (* Definition abst_dev_t: Type := *)
  (*   nat (*owner*) * nat? (*demand?*). *)

  Definition abst_sys_t: Type :=
    abst_ctrl_t * (nat? * nat? * nat?).

  Inductive abst_ctrl_wf
    : abst_ctrl_t -> Prop :=
    AbstCtrlStateWf
      actv_flag inb_ctrl aq tout
      (WF_INBOX: length inb_ctrl = 6)
      (MSGS_LENGTH: Forall (option_rel1 (fun msg => length msg = 8)) inb_ctrl)
      (VALID_ABST_QUEUE: valid_abst_queue aq)
      (VALID_OWNER_TIMEOUT: tout <= MAX_TIMEOUT)
    : abst_ctrl_wf
        (AbstCtrl inb_ctrl actv_flag aq tout).

  Inductive get_abst_dev
    : nat? * nat? * nat? -> nat -> nat? -> Prop :=
  | GetAbstDev1
      d1 d2 d3
    : get_abst_dev (d1, d2, d3) 3 d1
  | GetAbstDev2
      d1 d2 d3
    : get_abst_dev (d1, d2, d3) 4 d2
  | GetAbstDev3
      d1 d2 d3
    : get_abst_dev (d1, d2, d3) 5 d3
  .

  Inductive abst_sys_wf: abst_sys_t -> Prop :=
    AbstSysWf
      actrl ad1 ad2 ad3
      (WF_ACTRL: abst_ctrl_wf actrl)
      (WF_AD1: option_rel1 (fun dmd => dmd <= MAX_TIMEOUT) ad1)
      (WF_AD2: option_rel1 (fun dmd => dmd <= MAX_TIMEOUT) ad2)
      (WF_AD3: option_rel1 (fun dmd => dmd <= MAX_TIMEOUT) ad3)
      (* (CURRENT_OWNER_TIMEOUT: *)
      (*    option_rel1 (fun tid_owner => *)
      (*                   forall dmd_owner *)
      (*                     (GET_OWNER: get_abst_dev *)
      (*                                   (ad1, ad2, ad3) *)
      (*                                   tid_owner (Some dmd_owner)), *)
      (*                     dmd_owner = head_timeout actrl) *)
      (*                (cur_owner actrl)) *)
    : abst_sys_wf (actrl, (ad1, ad2, ad3)).


  Inductive match_ctrl_ast (actrl: abst_ctrl_t) (b: bool)
    : forall (amod: @AppMod.t obsE bytes),
        itree appE (AppMod.abst_state_t amod) -> Prop :=
  | MatchCtrl_Active
      (* aq tout *)
      tid_z
      tout_z qb qe q
      (ACTIVE_FLAG: b = active_flag actrl)
      (TOUT_ACTIVE: tout_z = Z.of_nat (head_timeout actrl))
      (MATCH_QUEUE: match_queue (abst_queue actrl) (qb, qe, q))
    : match_ctrl_ast actrl b
                     (ctrl_mod tid_z)
                     (Ret (CtrlState.mk CtrlState.Active
                                        tout_z qb qe q))
  | MatchCtrl_Standby
      tid_z tout_z qb qe q
      (STANDBY_FLAG: b = negb (active_flag actrl))
      (TOUT_STANDBY:
         tout_z = Z.of_nat
                    (let tout' := head_timeout actrl in
                     if tout' =? MAX_TIMEOUT then 0
                     else tout'))
      (* (tout = MAX_TIMEOUT /\ tout_z = 0%Z) \/ *)
      (* (tout < MAX_TIMEOUT /\ tout_z = Z.of_nat tout)) *)
      (MATCH_QUEUE: match_queue (abst_queue actrl) (qb, qe, q))
    : match_ctrl_ast actrl b
                     (ctrl_mod tid_z)
                     (Ret (CtrlState.mk CtrlState.Active
                                        tout_z qb qe q))
  .

  Definition drop_self_entry (b: bool) (inb_c: list bytes?)
    : list bytes? :=
    replace_nth inb_c (if b then 1 else 2) None.

  Inductive match_ctrl
    : abst_sys_t ->
      bool -> @SNode.state obsE bytes -> Prop :=
  | MatchCtrl
      actrl adevs (b: bool)
      (* inb_c ac2 (b: bool) adevs *)
      amod tid inb ast
      (TASK_ID: tid = if b then tid_ctrl1 else tid_ctrl2)
      (CTRL_APP_MOD: amod = ctrl_mod (Z.of_nat tid))
      (MATCH_CTRL_AST: option_rel1 (match_ctrl_ast actrl b amod) ast)
      (DROP_ENTRY: drop_self_entry b (inbox_ctrl actrl) = inb)
    : match_ctrl (actrl, adevs) b
                 (SNode.State tid (ITrSNode.to_snode
                                     amod) inb ast).


  Inductive dev_wait (asys: abst_sys_t)
            (tid: nat) (dmd: nat)
    : nat -> Prop :=
  | DevWait_SentAcq
      actrl adevs
      (RANGE_DEMAND: 0 < dmd <= MAX_TIMEOUT)
      (ABST_SYS: asys = (actrl, adevs))
      (* (ABST_CTRL: actrl = (inb_c, ac')) *)
      (GET_ABST_DEV: get_abst_dev adevs tid (Some dmd))
      (INB_CTRL_ACQ: nth_error (inbox_ctrl actrl) tid =
                     Some (Some acq_msg))
    : dev_wait asys tid dmd ((MAX_TIMEOUT + 1) * 2 + 2)

  | DevWait_WaitInQueue
      actrl adevs w i
      (ABST_SYS: asys = ( actrl, adevs ))
      (GET_ABST_DEV: get_abst_dev adevs tid (Some dmd))
      (I_NONZERO: i <> 0)
      (IN_QUEUE: nth_error (abst_queue actrl) i = Some tid)
      (W_VAL: w = let tout := head_timeout actrl in
                  if tout =? 0 then MAX_TIMEOUT + 1 else tout)
    : dev_wait asys tid dmd (w + (MAX_TIMEOUT + 1) * (i - 1) + 1)
  | DevWait_WaitLast
      actrl adevs w
      (ABST_SYS: asys = ( actrl, adevs ))
      (GET_ABST_DEV: get_abst_dev adevs tid (Some dmd))
      (IN_QUEUE_HEAD: nth_error (abst_queue actrl) 0 = Some tid)
      (W_VAL: w = if head_timeout actrl =? 0 then 1 else 0)
    : dev_wait asys tid dmd w
  .

  Inductive dev_owner (asys: abst_sys_t)
            (tid: nat) (dmd: nat)
    : Prop :=
  | DevOwner
      actrl adevs
      (ABST_SYS: asys = ( actrl, adevs ))
      (GET_ABST_DEV: get_abst_dev adevs tid (Some dmd))
      (IN_QUEUE_HEAD: nth_error (abst_queue actrl) 0 = Some tid)
      (TIMTOUT_NONZERO: head_timeout actrl <> 0)
    : dev_owner asys tid dmd.

  Inductive match_dev_ast
            (tout: nat) (is_owner: bool) (dmd: nat?)
    : forall (amod: @AppMod.t obsE bytes),
      itree appE (AppMod.abst_state_t amod) -> Prop :=
  .

  Inductive match_dev
            (asys: abst_sys_t) (tid: nat)
    : @SNode.state obsE bytes -> Prop :=.
  (*   MatchDev *)
  (*     actrl adevs st_dmd *)
  (*     inb ast *)
  (*     (ABST_SYS: asys = ( actrl, adevs )) *)
  (*     (GET_ABST_DEV: get_abst_dev adevs tid st_dmd) *)
  (*     (MATCH_DEV_AST: match_dev_ast (head_timeout actrl) *)
  (*                                   (cur_owner *)
  (*                                   st_dmd ast) *)
  (*   : match_dev asys tid *)
  (*               (SNode.State tid (ITrSNode.to_snode dev_mod) *)
  (*                            inb ast). *)

  (* st_dmd / ast *)
  (*  None / None *)
  (*  None / Some (None, 0) *)
  (*  Some d / Some (Some (tid =? head), d) *)
  (* None *)


(* (TASK_ID: tid = if b then tid_ctrl1 else tid_ctrl2) *)
(*       (CTRL_APP_MOD: amod = ctrl_mod (Z.of_nat tid)) *)
(*       (MATCH_CTRL_AST: option_rel1 (match_ctrl_ast ac2 b amod) ast) *)
(*       (DROP_ENTRY: drop_self_entry b inb_c = inb) *)
(*     : match_ctrl ((inb_c, ac2), devs) b *)
(*                  (SNode.State tid (ITrSNode.to_snode *)
(*                                      amod) inb ast). *)


(*   Inductive match_ctrl_ast *)
(*     : bool * list nat * nat -> bool -> *)
(*       forall (amod: @AppMod.t obsE bytes), *)
(*         itree appE (AppMod.abst_state_t amod) -> Prop := *)
(*   | MatchCtrl_Active *)
(*       b aq tout *)
(*       tid_z *)
(*       tout_z qb qe q *)
(*       (TOUT_ACTIVE: tout_z = Z.of_nat tout) *)
(*       (MATCH_QUEUE: match_queue aq (qb, qe, q)) *)
(*     : match_ctrl_ast (b, aq, tout) b *)
(*                      (ctrl_mod tid_z) *)
(*                      (Ret (CtrlState.mk CtrlState.Active *)
(*                                         tout_z qb qe q)) *)
(*   | MatchCtrl_Standby *)
(*       b aq tout b' *)
(*       tid_z *)
(*       tout_z qb qe q *)
(*       (STANDBY_FLAG: b' = negb b) *)
(*       (TOUT_STANDBY: *)
(*          (tout = MAX_TIMEOUT /\ tout_z = 0%Z) \/ *)
(*          (tout < MAX_TIMEOUT /\ tout_z = Z.of_nat tout)) *)
(*       (MATCH_QUEUE: match_queue aq (qb, qe, q)) *)
(*     : match_ctrl_ast (b, aq, tout) b' *)
(*                      (ctrl_mod tid_z) *)
(*                      (Ret (CtrlState.mk CtrlState.Active *)
(*                                         tout_z qb qe q)) *)
(*   . *)

(*   Definition drop_self_entry (b: bool) (inb_c: list bytes?) *)
(*     : list bytes? := *)
(*     replace_nth inb_c (if b then 1 else 2) None. *)

(*   Inductive match_ctrl *)
(*     : abst_sys_t -> *)
(*       bool -> @SNode.state obsE bytes -> Prop := *)
(*   | MatchCtrl *)
(*       inb_c ac2 (b: bool) devs *)
(*       amod tid inb ast *)
(*       (TASK_ID: tid = if b then tid_ctrl1 else tid_ctrl2) *)
(*       (CTRL_APP_MOD: amod = ctrl_mod (Z.of_nat tid)) *)
(*       (MATCH_CTRL_AST: option_rel1 (match_ctrl_ast ac2 b amod) ast) *)
(*       (DROP_ENTRY: drop_self_entry b inb_c = inb) *)
(*     : match_ctrl ((inb_c, ac2), devs) b *)
(*                  (SNode.State tid (ITrSNode.to_snode *)
(*                                      amod) inb ast). *)

  Inductive match_con
    : @SNode.state obsE bytes -> Prop :=
  | MatchConsole
      nd inb st tid
      (CTRL_TID: tid = tid_con)
      (NODE: nd = ITrSNode.to_snode con_mod)
    : match_con (SNode.State tid nd inb st).

  Inductive match_ctrl_pre (tid: nat)
    : @SNode.state obsE bytes -> Prop :=
  | MatchCtrlPre
      nd inb st
      (CTRL_TID: is_ctrl_tid tid)
      (NODE: nd = ITrSNode.to_snode (ctrl_mod (Z.of_nat tid)))
      (STATE: option_rel1 (SNode.init_app_state nd) st)
    : match_ctrl_pre tid (SNode.State tid nd inb st).

  Inductive match_dev_pre (tid: nat)
    : @SNode.state obsE bytes -> Prop :=
  | MatchDevicePre
      nd inb st
      (CTRL_TID: is_dev_tid tid)
      (NODE: nd = ITrSNode.to_snode dev_mod)
      (STATE: option_rel1 (SNode.init_app_state nd) st)
    : match_dev_pre tid (SNode.State tid nd inb st).


  Inductive sys_pre: @SyncSys.state obsE bytes -> Prop :=
    SystemInvPre
      tm
      nst_con nst_c1 nst_c2
      nst_d1 nst_d2 nst_d3

      (MATCH_CON: match_con nst_con)
      (MATCH_CTRL1: match_ctrl_pre tid_ctrl1 nst_c1)
      (MATCH_CTRL2: match_ctrl_pre tid_ctrl2 nst_c2)
      (MATCH_DEV1: match_dev_pre tid_dev1 nst_d1)
      (MATCH_DEV2: match_dev_pre tid_dev2 nst_d2)
      (MATCH_DEV3: match_dev_pre tid_dev3 nst_d3)

      (WF_CON: SNode.state_wf num_tasks tid_con nst_con)
      (WF_CTRL1: SNode.state_wf num_tasks tid_ctrl1 nst_c1)
      (WF_CTRL2: SNode.state_wf num_tasks tid_ctrl2 nst_c2)
      (WF_DEV1: SNode.state_wf num_tasks tid_dev1 nst_d1)
      (WF_DEV2: SNode.state_wf num_tasks tid_dev2 nst_d2)
      (WF_DEV3: SNode.state_wf num_tasks tid_dev3 nst_d3)

    : sys_pre (SyncSys.State
                 tm [nst_con; nst_c1; nst_c2;
                    nst_d1; nst_d2; nst_d3]).

  Inductive sys: abst_sys_t -> @SyncSys.state obsE bytes -> Prop :=
    SystemInv
      tm
      nst_con nst_c1 nst_c2
      nst_d1 nst_d2 nst_d3
      (* (controller_id, inbox, abst_queue, owner_timeout) *)
      (asys: abst_sys_t)

      (* (VALID_ABST_CTRL_STATE: valid_abst_ctrl (fst asys)) *)
      (MATCH_CON: match_con nst_con)
      (MATCH_CTRL1: match_ctrl asys true nst_c1)
      (MATCH_CTRL2: match_ctrl asys false nst_c2)
      (MATCH_DEV1: match_dev asys tid_dev1 nst_d1)
      (MATCH_DEV2: match_dev asys tid_dev2 nst_d2)
      (MATCH_DEV3: match_dev asys tid_dev3 nst_d3)

      (WF_CON: SNode.state_wf num_tasks tid_con nst_con)
      (WF_CTRL1: SNode.state_wf num_tasks tid_ctrl1 nst_c1)
      (WF_CTRL2: SNode.state_wf num_tasks tid_ctrl2 nst_c2)
      (WF_DEV1: SNode.state_wf num_tasks tid_dev1 nst_d1)
      (WF_DEV2: SNode.state_wf num_tasks tid_dev2 nst_d2)
      (WF_DEV3: SNode.state_wf num_tasks tid_dev3 nst_d3)

    : sys asys
          (SyncSys.State
             tm [nst_con; nst_c1; nst_c2;
                nst_d1; nst_d2; nst_d3]).

End AcStInv.



(* behavior in which a controller starts earlier than
   (or, at the same time with) any of the devices. *)
Definition service_start (start_tsp: nat)
           (beh: behav_t obsE): Prop :=
  exists tid_ctrl logv,
    is_ctrl_tid tid_ctrl /\
    event_in_beh tid_ctrl (Z.of_nat start_tsp, compl_event logv) beh /\
    (forall tid, is_ctrl_tid tid \/ is_dev_tid tid ->
            ~ exists tsp evt, tsp < start_tsp /\
                         event_in_beh tid (Z.of_nat tsp, evt) beh).

Definition service_time (start_tsp cur_tsp: nat)
           (beh: behav_t obsE): Prop :=
  forall tsp: nat,
    Nat.divide (Z.to_nat period) tsp ->
    start_tsp <= tsp < cur_tsp ->
    exists tid_ctrl logv,
      is_ctrl_tid tid_ctrl /\
      event_in_beh tid_ctrl (Z.of_nat tsp, compl_event logv) beh.


Definition service_start_exec (t_s: nat) (exec: exec_t obsE): Prop :=
  exists tid_ctrl logv,
    <<CTRL_TID: is_ctrl_tid tid_ctrl>> /\
    <<COMPL_IN_EXEC: event_in_exec tid_ctrl (Z.of_nat t_s)
                                   (compl_event logv) exec>> /\
    <<COMPL_AFTER_START:
      forall tid' t'
        (CTRL_OR_DEV: (is_ctrl_tid \1/ is_dev_tid) tid')
        (BEFORE_START: t' < t_s),
        ~ event_in_exec tid' (Z.of_nat t')
          (compl_event logv) exec >>
.


Section LEMMAS.
  Variable sys: @SyncSys.t obsE bytes.
  Variable tm_init: nat.
  Hypothesis PERIOD_POS: SyncSys.period sys <> 0.
  Let dsys: DSys.t := SyncSys.as_dsys sys tm_init.
  Let period: nat := SyncSys.period sys.


  Definition service_time_exec (t_s t_serv: nat)
             (exec: exec_t obsE): Prop :=
    forall (t: nat),
      Nat.divide period t ->
      t_s <= t < t_serv ->
      exists tid_ctrl logv,
        is_ctrl_tid tid_ctrl /\
        event_in_exec tid_ctrl (Z.of_nat t)
                      (compl_event logv) exec.

  Definition service_time_tr (t_s t_serv: nat)
             (tr: list (list (Z * events obsE))): Prop :=
    forall (t: nat),
      Nat.divide period t ->
      t_s <= t < t_serv ->
      exists tid_ctrl logv,
        is_ctrl_tid tid_ctrl /\
        event_in_tr tid_ctrl (Z.of_nat t)
                    (compl_event logv) tr.

  Definition dev_event (e: event obsE): Prop :=
    (exists n, e = Event (inl1 CheckDemand) n) \/
    (e = Event (inl1 UseResource) tt).


  Lemma inv_prsv_pre
        st tm
        (INV_PRE: AcStInv.sys_pre st)
        (SYS_TIME: tm = SyncSys.time st)
        (SYNC_TIME: Nat.divide period tm)
    : forall tr st'
        (MSTEPS: msteps dsys period st tr st')
    ,
      (<<INV_PRE': AcStInv.sys_pre st'>> /\
       <<ONLY_CONSOLE_ALIVE:
         forall tid' t' e'
           (EVENT: event_in_tr tid' t' e' tr),
           tid' = tid_con /\ (exists b, e' = Event (inl1 GetUserInput) b)>>) \/
      (exists actrl,
          <<INV_ST': AcStInv.sys actrl st'>> /\
          <<CTRL_STARTS:
            exists tid_c logv,
              <<CTRL: is_ctrl_tid tid_c>> /\
              <<START_EVENT_IN_TRACE:
                event_in_tr tid_c (Z.of_nat tm)
                            (compl_event logv)
                            tr>> >> /\
          <<NO_DEV_EVENTS:
            forall tid' t' e'
              (EVENT: event_in_tr tid' t' e' tr),
              ~ dev_event e'>>).
  Proof.
  Admitted.

  Lemma inv_prsv_sys
        actrl st tm
        (INV_ST: AcStInv.sys actrl st)
        (SYS_TIME: tm = SyncSys.time st)
        (SYNC_TIME: Nat.divide period tm)
    : forall tr st'
        (MSTEPS: msteps dsys period st tr st')
    ,
      <<SERVICE_END: ~ exists logv, event_in_tr tid_ctrl1 (Z.of_nat tm)
                       (compl_event logv) tr /\
                     ~ exists logv, event_in_tr tid_ctrl2 (Z.of_nat tm)
                       (compl_event logv) tr>> \/
      exists actrl',
        <<INV_ST': AcStInv.sys actrl' st'>>.
  Proof.
  Admitted.

  Lemma inv_prsv_sys_wait
        actrl st tm
        tid_d wtm dmd
        (INV_ST: AcStInv.sys actrl st)
        (INV_DWAIT: AcStInv.dev_wait actrl tid_d dmd wtm)
        (SYS_TIME: tm = SyncSys.time st)
        (SYNC_TIME: Nat.divide period tm)
    : forall tr st'
        (MSTEPS: msteps dsys period st tr st')
    ,
      <<SERVICE_END: ~ exists logv, event_in_tr tid_ctrl1 (Z.of_nat tm)
                       (compl_event logv) tr /\
                     ~ exists logv, event_in_tr tid_ctrl2 (Z.of_nat tm)
                       (compl_event logv) tr>>\/
      <<DEV_FAIL: ~ exists logv, event_in_tr tid_d (Z.of_nat tm)
                    (compl_event logv) tr>> \/
      exists actrl' wtm',
        <<INV_ST': AcStInv.sys actrl' st'>> /\
        <<INV_DWAIT': AcStInv.dev_wait actrl' tid_d dmd wtm'>> /\
        <<WAITING_TIME_DECR: wtm' < wtm>>
  .
  Proof.
  Admitted.

  Lemma dev_wait_zero_impl_owner
        actrl tid dmd
        (INV_DWAIT_ZERO: AcStInv.dev_wait actrl tid dmd 0)
    : AcStInv.dev_owner actrl tid dmd.
  Proof.
  Admitted.

  Lemma inv_prsv_sys_owner
        actrl st tm
        tid_d dmd
        (INV_ST: AcStInv.sys actrl st)
        (INV_DOWN: AcStInv.dev_owner actrl tid_d dmd)
        (SYS_TIME: tm = SyncSys.time st)
        (SYNC_TIME: Nat.divide period tm)
    : forall tr st'
        (MSTEPS: msteps dsys period st tr st')
    ,
      <<SERVICE_END: ~ exists logv, event_in_tr tid_ctrl1 (Z.of_nat tm)
                       (compl_event logv) tr /\
                     ~ exists logv, event_in_tr tid_ctrl2 (Z.of_nat tm)
                       (compl_event logv) tr>> \/
      <<DEV_FAIL: ~ exists logv, event_in_tr tid_d (Z.of_nat tm)
                    (compl_event logv) tr>> \/
      exists actrl',
        <<INV_ST': AcStInv.sys actrl' st'>> /\
        <<OWNER_EVT: event_in_tr tid_d (Z.of_nat tm)
                                 (Event (inl1 UseResource) tt) tr>> /\
        <<INV_DOWN': AcStInv.dev_owner actrl' tid_d (pred dmd)>>
  .
  Proof.
  Admitted.


  Lemma inv_use_res_exclusive
        actrl st tm tr st'
        tid1 tid2
        (INV_ST: AcStInv.sys actrl st)
        (SYS_TIME: tm = SyncSys.time st)
        (SYNC_TIME: Nat.divide period tm)
        (MSTEPS: msteps dsys period st tr st')
        (USE_IN_TR1: event_in_tr
                       tid1 (Z.of_nat tm) (Event (inl1 UseResource) tt) tr)
        (USE_IN_TR2: event_in_tr
                       tid2 (Z.of_nat tm) (Event (inl1 UseResource) tt) tr)
    : tid1 = tid2.
  Proof.
  Admitted.

  Lemma inv_pre_time_indep
        st st'
        (NODE_EQ: SyncSys.node_states st =
                  SyncSys.node_states st')
        (PRE: AcStInv.sys_pre st)
    : AcStInv.sys_pre st'.
  Proof.
  Admitted.


  Lemma msteps_pre_first_sync
        st exec
        (SAFE_ST: DSys.safe_state st)
        (EXEC_ST: DSys.exec_state dsys st exec)
        (INV_PRE: AcStInv.sys_pre st)
    : exists n_fst tr_fst st_fst exec_fst tm_fst,
      <<EXEC_DIV_FST: sapp_each_rel tr_fst exec_fst exec>> /\
      <<MSTEPS_FST: msteps dsys n_fst st tr_fst st_fst>> /\
      <<INV_PRE_FST: AcStInv.sys_pre st_fst>> /\
      <<FIRST_SYNC_TIME: Nat.divide period tm_fst>> /\
      <<SYS_TIME_FST: SyncSys.time st_fst = tm_fst>> /\
      <<SYS_TIME_FST_ADV: SyncSys.time st_fst = SyncSys.time st + n_fst>> /\
      <<EMPTY_TRACE_FST: Forall (Forall (fun x => snd x = [])) tr_fst>> /\
      <<SAFE_ST_FST: DSys.safe_state st_fst>> /\
      <<EXEC_ST_FST: DSys.exec_state dsys st_fst exec_fst>>
  .
  Proof.
    pose (nst := nsteps_to_sync period (SyncSys.time st)).
    exists nst.

    hexploit (sync_nonsync_msteps_det
                _ _ sys tm_init PERIOD_POS st); eauto.
    fold dsys. fold period. fold nst.
    i. des.

    hexploit safe_exec_impl_msteps; eauto.
    instantiate (1:= nst).
    i. des.
    hexploit DET; eauto. i. des. subst.

    esplits; eauto.
    - eapply inv_pre_time_indep.
      2: { eauto. }
      destruct st; ss.
    - ss.
      hexploit (nsteps_to_sync_spec
                  period (SyncSys.time st) nst); eauto.
      i. des. ss.
    - apply empty_trace_empty.
  Qed.


  Lemma service_start_msteps_pre
        st (exec: exec_t obsE) t t_s
        (EXEC_STATE: DSys.exec_state dsys st exec)
        (SAFE_ST: DSys.safe_state st)
        (INV_PRE: AcStInv.sys_pre st)
        (SYS_TIME: t = SyncSys.time st)
        (SYNC_TIME: Nat.divide period t)
        (SERVICE_START: service_start_exec t_s exec)
    : exists k_pre tr_pre st_pre exec_pre,
      <<MSTEPS_PRE: msteps dsys (k_pre * period)
                           st tr_pre st_pre>> /\
      <<START_TIME_EQ: SyncSys.time st_pre = t_s>> /\
      <<INV_PRE: AcStInv.sys_pre st_pre>> /\
      <<SAFE_ST_PRE: DSys.safe_state st_pre>> /\
      <<EXEC_STATE_PRE: DSys.exec_state dsys st_pre exec_pre>> /\
      <<EXEC_DIV_PRE: sapp_each_rel tr_pre exec_pre exec>> /\
      <<ONLY_CONSOLE_ALIVE:
        forall tid t' e'
          (EVENT: event_in_tr tid t' e' tr_pre),
          tid = tid_con /\ (exists b, e' = Event (inl1 GetUserInput) b)>>
          (* exists b, tid = tid_con /\ e' = Event GetUserInput b>> *)
  .
  Proof.
    assert (<<SYNC_T_S: Nat.divide period t_s>> /\
            <<T_LT: t <= t_s>>).
    { hexploit sync_exec_time_props; eauto.
      intro FA.
      r in SERVICE_START. des.
      inv COMPL_IN_EXEC.
      eapply Forall_nth1 in FA; eauto.
      eapply Forall_stream_forall in FA; eauto.
      ss. des.
      - subst. ss.
      - (* esplits; eauto. *)
        admit.
    }
    des.

    assert (T_S: exists z, t + period * z = t_s).
    { r in SYNC_TIME. des. rename z into z_t.
      r in SYNC_T_S. des. rename z into z_s.
      exists (z_s - z_t). nia. }
    des.

    clear T_LT SYNC_T_S.
    subst t_s.
    r in SERVICE_START. des.
    clear tid_ctrl CTRL_TID COMPL_IN_EXEC.
    revert st t exec EXEC_STATE SAFE_ST
           INV_PRE SYS_TIME SYNC_TIME COMPL_AFTER_START.
    induction z as [| z IH]; i; ss.
    { exists 0. esplits; eauto.
      - rewrite Nat.mul_0_l. econs; eauto.
      - nia.
      - eapply sapp_each_rel_base.
        apply exec_state_len. eauto.
      - i. ss. exfalso.
        inv EVENT.
        eapply nth_error_In in LOCAL_EXEC.
        eapply repeat_spec in LOCAL_EXEC. subst. ss.
    }

    hexploit safe_exec_impl_msteps; eauto.
    instantiate (1:= period).
    i. des.

    hexploit inv_prsv_pre; eauto. i. des.
    2: {
      exfalso.
      eapply (COMPL_AFTER_START tid_c).
      { eauto. }
      { instantiate (1:= t). nia. }
      eapply event_in_tr_exec; eauto.
      admit.
    }

    hexploit sync_msteps_system_time_adv; eauto.
    intro TIME'. des.
    hexploit IH; eauto.
    { rewrite TIME'.
      eauto with app_pf. }
    { ii. hexploit (COMPL_AFTER_START tid' t'); eauto.
      { nia. }
      intro C. apply C.
      eapply event_in_later_exec; eauto. }
    i. des.

    hexploit msteps_concat.
    { eapply MSTEPS. }
    { eapply MSTEPS_PRE. }
    i. des.
    replace (period + k_pre * period) with
        (S k_pre * period) in MSTEPS_CONCAT by nia.

    esplits; eauto.
    - nia.
    - hexploit (sapp_each_rel_assoc _ exec exec' exec_pre); eauto.
    - i.
      cut (event_in_tr tid t' e' tr \/
           event_in_tr tid t' e' tr_pre).
      { i. des; eauto. }
      clear - EVENT ES_CONCAT.
      inv EVENT.
      eapply Forall3_nth3 in ES_CONCAT; eauto.
      des. subst.
      apply in_app_or in EVTS_AT_T. des.
      + left. econs; eauto.
      + right. econs; eauto.
  (* Qed. *)
  Admitted.

  Lemma service_start_msteps_start
        st (exec: exec_t obsE) t_s
        (EXEC_STATE: DSys.exec_state dsys st exec)
        (SAFE_ST: DSys.safe_state st)
        (INV_PRE: AcStInv.sys_pre st)
        (SYS_TIME: t_s = SyncSys.time st)
        (SYNC_TIME: Nat.divide period t_s)
        (SERVICE_START: service_start_exec t_s exec)
    : exists tr_s st_s exec_s actrl,
      <<MSTEPS_S: msteps dsys period st tr_s st_s>> /\
      <<INV_ST_S: AcStInv.sys actrl st_s>> /\
      <<SAFE_ST: DSys.safe_state st_s>> /\
      <<EXEC_STATE_S: DSys.exec_state dsys st_s exec_s>> /\
      <<EXEC_DIV_S: sapp_each_rel tr_s exec_s exec>> /\
      <<CTRL_STARTS:
        exists tid_c logv,
          <<CTRL: is_ctrl_tid tid_c>> /\
          <<START_EVENT_IN_TRACE:
            event_in_tr tid_c (Z.of_nat t_s) (compl_event logv)
                        tr_s>> >> /\
      <<NO_DEV_EVENTS:
        forall tid t' e'
          (EVENT: event_in_tr tid t' e' tr_s),
          ~ dev_event e'>>
  .
  Proof.
    subst.
    hexploit safe_exec_impl_msteps; eauto.
    instantiate (1:= period). i. des.
    hexploit sync_msteps_system_time_adv; eauto.
    intro TIME_ST'. des.

    hexploit inv_prsv_pre; eauto. i. des.
    { exfalso.
      r in SERVICE_START. des.
      hexploit event_in_exec_must_in_tr; eauto.
      { nia. }
      i. hexploit ONLY_CONSOLE_ALIVE; eauto.
      i. des. ss.
    }

    esplits; eauto.
  Qed.

  Lemma service_start_msteps
        st (exec: exec_t obsE) t t_s
        (EXEC_STATE: DSys.exec_state dsys st exec)
        (SAFE_ST: DSys.safe_state st)
        (INV_PRE: AcStInv.sys_pre st)
        (SYS_TIME: t = SyncSys.time st)
        (SERVICE_START: service_start_exec t_s exec)
    : exists tintv_s tr_s st_s actrl_s exec_s,
      <<MSTEPS_START: msteps dsys tintv_s st tr_s st_s>> /\
      <<SYS_TIME_SYNC: Nat.divide period (SyncSys.time st_s)>> /\
      <<TIME_ST_S2: SyncSys.time st_s = t_s + period>> /\
      <<INV_ST_S: AcStInv.sys actrl_s st_s>> /\
      <<SAFE_ST_S: DSys.safe_state st_s>> /\
      <<EXEC_STATE_S: DSys.exec_state dsys st_s exec_s>> /\
      <<EXEC_DIV_S: sapp_each_rel tr_s exec_s exec>> /\
      <<CTRL_STARTS:
        exists tid_c logv,
          <<CTRL: is_ctrl_tid tid_c>> /\
          <<START_EVENT_IN_TRACE:
            event_in_tr tid_c (Z.of_nat t_s) (compl_event logv)
                        tr_s>> >> /\
      <<NO_DEV_EVENTS_BEFORE_START:
        forall tid t' e'
          (EVENT: event_in_tr tid t' e' tr_s),
          ~ dev_event e'>>
  .
  Proof.
    hexploit msteps_pre_first_sync; eauto. i. des.
    assert (SERVICE_START_FST:
              service_start_exec t_s exec_fst).
    { r in SERVICE_START. des.
      r. esplits; eauto.
      { eapply event_in_exec_not_in_tr; eauto.
        intro IN_TR_FST.
        inv IN_TR_FST.
        eapply Forall_nth1 in EMPTY_TRACE_FST; eauto.
        rewrite Forall_forall in EMPTY_TRACE_FST.
        hexploit EMPTY_TRACE_FST; eauto. s. i. clarify.
      }
      i.
      hexploit COMPL_AFTER_START; eauto.
      intros C IN_FST. apply C.
      eapply event_in_later_exec; eauto.
    }

    guardH SYS_TIME_FST.
    hexploit (service_start_msteps_pre st_fst); eauto.
    { rewrite SYS_TIME_FST. ss. }
    i. des.

    hexploit msteps_concat.
    { eapply MSTEPS_FST. }
    { eapply MSTEPS_PRE. }
    i. des.
    renames MSTEPS_CONCAT ES_CONCAT into
            MSTEPS_CONCAT1 TR_CONCAT1.

    hexploit sync_msteps_system_time_adv;
      try apply MSTEPS_PRE; eauto.
    intro TIME_ST_PRE. r in TIME_ST_PRE.

    hexploit service_start_msteps_start; eauto.
    { rewrite TIME_ST_PRE.
      rewrite SYS_TIME_FST.
      eauto with app_pf. }
    { r in SERVICE_START_FST. des.
      r. esplits; eauto.
      { rewrite START_TIME_EQ.
        eapply event_in_exec_not_in_tr; eauto.
        intro IN_TR_PRE.
        hexploit ONLY_CONSOLE_ALIVE; eauto.
        clear - CTRL_TID.
        i. des. subst. ss.
      }
      rewrite START_TIME_EQ.
      i. hexploit COMPL_AFTER_START; eauto.
      intros C IN_FST. apply C.
      eapply event_in_later_exec; eauto.
    }
    i. des.

    hexploit sync_msteps_system_time_adv;
      try apply MSTEPS_S; eauto.
    intro TIME_ST_S. r in TIME_ST_S.

    hexploit msteps_concat.
    { eapply MSTEPS_CONCAT1. }
    { eapply MSTEPS_S. }
    intros (tr_tot & MSTEPS_TOT & TR_TOT). des.

    exists (n_fst + k_pre * period + period),
    tr_tot, st_s, actrl, exec_s.

    splits; eauto.
    - rewrite TIME_ST_S. rewrite TIME_ST_PRE.
      rewrite SYS_TIME_FST.
      eauto with app_pf.
    - nia.
    - hexploit (sapp_each_rel_assoc
                  _ exec exec_fst exec_pre); eauto.
      i.
      hexploit (sapp_each_rel_assoc
                  _ exec exec_pre exec_s); eauto.
    - esplits; eauto.
      rewrite START_TIME_EQ in *.
      clear - START_EVENT_IN_TRACE TR_TOT.
      inv START_EVENT_IN_TRACE.
      eapply Forall3_nth2 in TR_TOT; eauto. des.
      clarify.
      econs; eauto.
      apply in_or_app. eauto.
    - i.
      cut (event_in_tr tid t' e' tr_fst \/
           event_in_tr tid t' e' tr_pre \/
              event_in_tr tid t' e' tr_s).
      { intro IN_TR. des; eauto.
        - clear - EMPTY_TRACE_FST IN_TR.
          inv IN_TR.
          eapply Forall_nth1 in EMPTY_TRACE_FST; eauto.
          rewrite Forall_forall in EMPTY_TRACE_FST.
          hexploit EMPTY_TRACE_FST; eauto. i. ss. clarify.
        - clear - ONLY_CONSOLE_ALIVE IN_TR.
          hexploit ONLY_CONSOLE_ALIVE; eauto.
          clear.
          i. des. subst.
          intro DEV. r in DEV.
          des; ss.
      }
      clear - EVENT TR_TOT TR_CONCAT1.
      inv EVENT.
      eapply Forall3_nth3 in TR_TOT; eauto. des. subst.
      eapply Forall3_nth3 in TR_CONCAT1; eauto. des. subst.
      eapply in_app_or in EVTS_AT_T. des.
      2: { right. right. econs; eauto. }
      eapply in_app_or in EVTS_AT_T. des.
      { left. econs; eauto. }
      { right. left. econs; eauto. }
  Qed.


  Lemma event_in_exec_msteps
        actrl st (exec: exec_t obsE) tm
        tid t e
        (EXEC_STATE: DSys.exec_state dsys st exec)
        (SAFE_ST: DSys.safe_state st)
        (INV_ST: AcStInv.sys actrl st)
        (SYS_TIME: tm = SyncSys.time st)
        (SYNC_TIME: Nat.divide period tm)
        (EVT_IN_EXEC: event_in_exec tid (Z.of_nat t) e exec)
    : exists k tr1 st1 exec1,
      <<MSTEPS1: msteps dsys (k * period) st tr1 st1>> /\
      <<SAFE_ST1: DSys.safe_state st1>> /\
      <<EXEC_STATE1: DSys.exec_state dsys st1 exec1>> /\
      <<EXEC_DIV1: sapp_each_rel tr1 exec1 exec>> /\
      <<EVT_TIME_EQ: SyncSys.time st1 = t >> /\
      (<<SERVICE_FAILED: ~ service_time_tr tm t tr1>> \/
       exists actrl1 tr2 st2 exec2,
         <<INV_ST1: AcStInv.sys actrl1 st1>> /\
         <<MSTEPS2: msteps dsys period st1 tr2 st2>> /\
         <<SAFE_ST2: DSys.safe_state st2>> /\
         <<EXEC_STATE2: DSys.exec_state dsys st2 exec2>> /\
         <<EXEC_DIV2: sapp_each_rel tr2 exec2 exec1>> /\
         <<EVENT_IN_TR2: event_in_tr tid (Z.of_nat t) e tr2>>).
  Proof.
    assert (<<SYNC_T_S: Nat.divide period t>> /\
            <<T_LT: tm <= t>>).
    { hexploit sync_exec_time_props; eauto.
      intro FA.
      inv EVT_IN_EXEC.
      eapply Forall_nth1 in FA; eauto.
      eapply Forall_stream_forall in FA; eauto.
      ss. des.
      - subst. ss.
      - (* esplits; eauto. *)
        admit.
    }
    des.

    assert (T_S: exists z, tm + z * period = t).
    { r in SYNC_TIME. des. rename z into z_t.
      r in SYNC_T_S. des. rename z into z_s.
      exists (z_s - z_t). nia. }
    des.

    subst t.
    clear T_LT SYNC_T_S.
    revert actrl st tm exec EXEC_STATE SAFE_ST
           INV_ST SYS_TIME SYNC_TIME EVT_IN_EXEC.
    induction z as [| z IH]; i; ss.
    { exists 0.
      esplits; eauto.
      { rewrite Nat.mul_0_l. econs; eauto. }
      { eapply sapp_each_rel_base.
        apply exec_state_len. eauto. }
      { nia. }

      right.
      hexploit safe_exec_impl_msteps; eauto.
      instantiate (1:= period).
      i. des.
      hexploit sync_msteps_system_time_adv; eauto.
      intro TIME_ST'. des.

      esplits; eauto.
      eapply event_in_exec_must_in_tr; eauto.
      nia.
    }

    replace (tm + S z * period) with
        (tm + period + z * period) in EVT_IN_EXEC by nia.

    hexploit safe_exec_impl_msteps; eauto.
    instantiate (1:= period).
    i. des.
    rename MSTEPS into MSTEPS1.
    renames tr st' exec' into tr1 st1 exec1.
    hexploit sync_msteps_system_time_adv; eauto.
    intro TIME_ST1. des.

    hexploit inv_prsv_sys; eauto. i. des.
    { hexploit safe_exec_impl_msteps; eauto.
      instantiate (1:= z * period).
      i. des.

      hexploit sync_msteps_system_time_adv; try apply MSTEPS; eauto.
      intro TIME_ST'. des.

      hexploit msteps_concat.
      { apply MSTEPS1. }
      { apply MSTEPS. }
      i. des.

      exists (S z). esplits; eauto.
      { hexploit (sapp_each_rel_assoc _ exec exec1 exec'); eauto. }
      { nia. }

      left.
      intro SVTM. r in SVTM.
      hexploit (SVTM tm); eauto.
      { nia. }
      intros [tid_c [logv [CTRL_TID IN_TR]]].

      eapply event_in_tr_div in IN_TR; eauto. des.
      - (* inv CTRL_TID; ss. *)
        admit.
      - inv IN_TR.
        hexploit sync_msteps_trace_time_range;
          try apply MSTEPS; eauto.
        nia.
    }

    hexploit IH; try apply INV_ST'; eauto.
    { rewrite TIME_ST1.
      eauto with app_pf. }
    { rewrite TIME_ST1.
      eapply event_in_exec_not_in_tr; eauto.
      intro C. inv C.
      hexploit sync_msteps_trace_time_range; eauto.
      nia.
    }
    i. nbdes.
    rename MSTEPS0 into MSTEPS2.

    hexploit msteps_concat.
    { apply MSTEPS1. }
    { apply MSTEPS2. }
    i. nbdes.

    exists (S k). esplits; eauto.
    { eapply sapp_each_rel_assoc; eauto. }
    { nia. }
    des.
    - left.
      rewrite TIME_ST1 in SERVICE_FAILED.
      intro SV_TR.
      r in SV_TR.
      apply SERVICE_FAILED. r.
      i.
      hexploit SV_TR; eauto.
      { nia. }
      i. des.
      esplits; eauto.
      hexploit event_in_tr_div; eauto.
      intro IN_TR.
      (* des; ss. *)
      (* exfalso. *)
      (* inv IN_TR. *)
      (* hexploit sync_msteps_trace_time_range; try apply MSTEPS1; eauto. *)
    (* nia. *)
      admit.
    - right.
      esplits; eauto.
      replace (tm + S z * period) with
          (SyncSys.time st1 + z * period) by nia.
      ss.
      (* Qed. *)
  Admitted.

  Lemma dev_wait_intro
        actrl st (* (exec: exec_t obsE) *) tm
        tr actrl' st' tid dmd dmd_n
        (* (EXEC_STATE: DSys.exec_state dsys st exec) *)
        (MSTEPS_DMD: msteps dsys period st tr st')
        (* (SAFE_ST: DSys.safe_state st) *)
        (INV_ST: AcStInv.sys actrl st)
        (INV_ST': AcStInv.sys actrl' st')
        (SYS_TIME: tm = SyncSys.time st)
        (SYNC_TIME: Nat.divide period tm)
        (DMD_NAT: Z_to_nat2 (Int.signed dmd) = Some dmd_n)
        (DMD_POS: 0 < dmd_n)
        (EVT_IN_EXEC: event_in_tr
                        tid (Z.of_nat tm)
                        (Event (inl1 CheckDemand) dmd) tr)
    : AcStInv.dev_wait actrl' tid
                       (Nat.min MAX_TIMEOUT dmd_n)
                       ((MAX_TIMEOUT + 2) * 2).
  Proof.
  Admitted.

  Lemma dev_wait_msteps
        actrl st (exec: exec_t obsE) tm
        tid wtm dmd
        (EXEC_STATE: DSys.exec_state dsys st exec)
        (SAFE_ST: DSys.safe_state st)
        (INV_ST: AcStInv.sys actrl st)
        (SYS_TIME: tm = SyncSys.time st)
        (SYNC_TIME: Nat.divide period tm)
        (INV_DWAIT: AcStInv.dev_wait actrl tid dmd wtm)
    : exists k tr_w st_w' exec_w',
      (* k_pre tr_pre st_s actrl_s exec_s, *)
      <<MSTEPS_W: msteps dsys (k * period) st tr_w st_w'>> /\
      <<SAFE_ST_W': DSys.safe_state st_w'>> /\
      <<EXEC_STATE_W': DSys.exec_state dsys st_w' exec_w'>> /\
      <<EXEC_DIV_W': sapp_each_rel tr_w exec_w' exec>> /\
      <<K_BOUND: k <= wtm>> /\

      (<<SERVICE_FAILED: ~ service_time_tr tm (tm + k * period) tr_w>> \/
       <<DEV_FAILED: exists k_fail logv,
           <<K_FAIL_BOUND: k_fail < k>> /\
           <<DEV_NOT_COMPL:
             ~ event_in_tr tid (Z.of_nat (tm + k_fail * period))
               (compl_event logv) tr_w>> >> \/
       exists actrl_o,
         <<INV_ST_W': AcStInv.sys actrl_o st_w'>> /\
         <<INV_DOWN: AcStInv.dev_owner actrl_o tid dmd>>).
  Proof.
    subst.
    revert actrl st exec tid dmd
           EXEC_STATE SAFE_ST INV_ST
           SYNC_TIME INV_DWAIT.

    pattern wtm. revert wtm.
    apply nat_strong_ind.
    intros wtm IH. i. ss.
    destruct (Nat.eq_dec wtm 0).
    - subst wtm.
      esplits; eauto.
      + rewrite Nat.mul_0_l. econs; eauto.
      + eapply sapp_each_rel_base.
        apply exec_state_len; eauto.
      + right. right. esplits; eauto.
        eapply dev_wait_zero_impl_owner; eauto.
    - hexploit safe_exec_impl_msteps; eauto.
      instantiate (1:= period).
      i. des.

      hexploit sync_msteps_system_time_adv; eauto.
      intros TIME_ST'. des.

      hexploit inv_prsv_sys_wait; eauto. i. des.
      + (* service_fail *)
        exists 1.
        esplits; eauto.
        { rewrite Nat.mul_1_l. ss. }
        { nia. }
        left.
        rewrite Nat.mul_1_l.

        intro SV_TR.
        r in SV_TR.
        hexploit (SV_TR (SyncSys.time st)); eauto.
        { nia. }

        intros (tid_c & CTRL & IN_TR).
        (* r in CTRL. *)
      (* des; subst; eauto. *)
        admit.

      + (* device_fail *)
        exists 1.
        esplits; eauto.
        { rewrite Nat.mul_1_l. ss. }
        { nia. }
        right. left.
        exists 0. splits; ss.
        rewrite Nat.mul_0_l.
        rewrite Nat.add_0_r. ss.
        admit.

      + (* success *)
        hexploit IH; eauto.
        { rewrite TIME_ST'.
          eauto with app_pf. }
        i. nbdes.
        hexploit msteps_concat.
        { apply MSTEPS. }
        { eauto. }
        replace (period + k * period) with
            (S k * period) by nia.
        i. nbdes.

        esplits; eauto.
        { eapply sapp_each_rel_assoc; eauto. }
        { nia. }

        des.
        * left.
          intro SV_TR. r in SV_TR.
          apply SERVICE_FAILED. r.
          i. hexploit SV_TR; eauto.
          { nia. }
          i. des.
          esplits; eauto.
          hexploit event_in_tr_div; eauto.
          intro IN_TR. des; ss.
          exfalso.
          inv IN_TR.
          hexploit sync_msteps_trace_time_range;
            try eapply MSTEPS; eauto.
          nia.
          admit.
        * right. left.
          exists (S k_fail).
          esplits.
          { nia. }

          replace (SyncSys.time st + S k_fail * period)
            with (SyncSys.time st' + k_fail * period) by nia.
          intro IN_TR. apply DEV_NOT_COMPL.
          hexploit event_in_tr_div; eauto.
          intro IN_TR2. des; ss.
          exfalso.
          inv IN_TR2.
          hexploit sync_msteps_trace_time_range;
            try eapply MSTEPS; eauto.
          nia.
          admit.
        * right. right.
          esplits; eauto.
          (* Qed. *)
  Admitted.

  Lemma dev_owner_msteps
        actrl st (exec: exec_t obsE) tm
        tid dmd
        (EXEC_STATE: DSys.exec_state dsys st exec)
        (SAFE_ST: DSys.safe_state st)
        (INV_ST: AcStInv.sys actrl st)
        (SYS_TIME: tm = SyncSys.time st)
        (SYNC_TIME: Nat.divide period tm)
        (INV_DOWNER: AcStInv.dev_owner actrl tid dmd)
    : exists tr_o st_o' exec_o',
      <<MSTEPS_O: msteps dsys (dmd * period) st tr_o st_o'>> /\
      <<SAFE_ST_O': DSys.safe_state st_o'>> /\
      <<EXEC_STATE_O': DSys.exec_state dsys st_o' exec_o'>> /\
      <<EXEC_DIV_O': sapp_each_rel tr_o exec_o' exec>> /\

      (<<SERVICE_FAILED: ~ service_time_tr tm (tm + dmd * period) tr_o>> \/
       <<DEV_FAILED: exists k_fail logv,
           <<K_FAIL_BOUND: k_fail < dmd>> /\
           <<DEV_NOT_COMPL:
             ~ event_in_tr tid (Z.of_nat (tm + k_fail * period))
               (compl_event logv) tr_o>> >> \/
       exists actrl_o',
         <<INV_ST_O': AcStInv.sys actrl_o' st_o'>> /\
         <<USE_RES: forall k (K_UBND: k < dmd),
             event_in_tr tid (Z.of_nat (tm + k * period))
                         (Event (inl1 UseResource) tt) tr_o>>).
  Proof.
    subst.
    revert actrl st exec tid
           EXEC_STATE SAFE_ST INV_ST
           SYNC_TIME INV_DOWNER.

    induction dmd as [| dmd IH]; i; ss.
    - esplits; eauto.
      + rewrite Nat.mul_0_l. econs; eauto.
      + eapply sapp_each_rel_base.
        apply exec_state_len; eauto.
      + right. right.
        esplits; eauto.
        i. nia.
    - hexploit safe_exec_impl_msteps; eauto.
      instantiate (1:= period).
      i. des.
      renames tr st' MSTEPS into tr1 st1 MSTEPS1.

      hexploit sync_msteps_system_time_adv; eauto.
      intros TIME_ST1. des.

      hexploit inv_prsv_sys_owner; eauto. i. des.
      + (* service_fail *)
        hexploit safe_exec_impl_msteps; eauto.
        instantiate (1:= dmd * period).
        i. des.
        renames tr st' MSTEPS into tr2 st2 MSTEPS2.

        hexploit sync_msteps_system_time_adv; eauto.
        intro TIME_ST2. des.

        hexploit msteps_concat.
        { eapply MSTEPS1. }
        { eauto. }
        i. des.

        esplits; eauto.
        { eapply sapp_each_rel_assoc; eauto. }
        left.
        intro SVTM. r in SVTM.
        hexploit (SVTM (SyncSys.time st)); eauto.
        { nia. }
        intros [tid_c [CTRL_TID IN_TR]].

        (* eapply event_in_tr_div in IN_TR; eauto. des. *)
        (* * inv CTRL_TID; ss. *)
        (* * inv IN_TR. *)
        (*   hexploit sync_msteps_trace_time_range; *)
        (*     try apply MSTEPS2; eauto. *)
      (*   nia. *)
        admit.
      + (* device_fail *)
        hexploit safe_exec_impl_msteps; eauto.
        instantiate (1:= dmd * period).
        i. des.
        renames tr st' MSTEPS into tr2 st2 MSTEPS2.

        hexploit sync_msteps_system_time_adv; eauto.
        intro TIME_ST2. des.

        hexploit msteps_concat.
        { eapply MSTEPS1. }
        { eauto. }
        i. des.

        esplits; eauto.
        { eapply sapp_each_rel_assoc; eauto. }
        right. left.

        exists 0.
        (* splits. *)
        (* { nia. } *)

        (* rewrite Nat.mul_0_l, Nat.add_0_r. *)
        (* intro IN_TR. *)
        (* eapply DEV_FAIL. *)

        (* eapply event_in_tr_div in IN_TR; eauto. *)
        (* des; ss. *)
        (* exfalso. *)
        (* inv IN_TR. *)
        (* hexploit sync_msteps_trace_time_range; *)
        (*   try apply MSTEPS2; eauto. *)
      (* nia. *)
        admit.

      + (* success *)
        hexploit IH; eauto.
        { rewrite TIME_ST1.
          eauto with app_pf. }
        i. nbdes.
        hexploit msteps_concat.
        { apply MSTEPS1. }
        { eauto. }
        replace (period + dmd * period) with
            (S dmd * period) by nia.
        i. nbdes.

        esplits; eauto.
        { eapply sapp_each_rel_assoc; eauto. }

        des.
        * left.
          intro SV_TR. r in SV_TR.
          apply SERVICE_FAILED. r.
          i. hexploit SV_TR; eauto.
          { nia. }
          i. des.
          esplits; eauto.
          hexploit event_in_tr_div; eauto.
          intro IN_TR. des; ss.
          exfalso.
          inv IN_TR.
          hexploit sync_msteps_trace_time_range;
            try eapply MSTEPS1; eauto.
          nia.
          admit.
        * right. left.
          exists (S k_fail).
          esplits.
          { nia. }

          replace (SyncSys.time st + S k_fail * period)
            with (SyncSys.time st1 + k_fail * period) by nia.
          intro IN_TR. apply DEV_NOT_COMPL.
          hexploit event_in_tr_div; eauto.
          intro IN_TR2. des; ss.
          exfalso.
          inv IN_TR2.
          hexploit sync_msteps_trace_time_range;
            try eapply MSTEPS1; eauto.
          nia.
          admit.
        * right. right.
          esplits; eauto.
          i.
          destruct k as [| k'].
          2: {
            replace (SyncSys.time st + S k' * period)
              with (SyncSys.time st1 + k' * period) by nia.
            hexploit (USE_RES k').
            { nia. }
            clear - ES_CONCAT.
            intro IN_TR. inv IN_TR.
            eapply Forall3_nth2 in ES_CONCAT; eauto. des.
            subst.
            econs; eauto.
            apply in_or_app; eauto.
          }
          rewrite Nat.mul_0_l, Nat.add_0_r.
          clear - OWNER_EVT ES_CONCAT.
          inv OWNER_EVT.
          eapply Forall3_nth1 in ES_CONCAT; eauto. des.
          subst.
          econs; eauto.
          eapply in_or_app; eauto.
  (* Qed. *)
  Admitted.

  Let max_prds_each_owner: nat := MAX_TIMEOUT + 2.
  Let max_prds_tot: nat := 1 + max_prds_each_owner * 3.


  (* exec version of final theorems *)


  (* Lemma service_time_failed_after_start *)
  (*       t_s t *)
  (*       (* tid_st *) *)
  (*       scnt tr (st st': DSys.state dsys) exec' exec *)
  (*       (* (SYS_TIME: SyncSys.time st' = t_s + period) *) *)
  (*       (EXEC_DIV: sapp_each_rel tr exec' exec) *)
  (*       (* (EXEC_ST: DSys.exec_state dsys st exec) *) *)
  (*       (TIME_LE: t_s <= SyncSys.time st') *)
  (*       (MSTEPS: msteps dsys scnt st tr st') *)
  (*       (* (EVENT_IN_TR: event_in_tr *) *)
  (*       (*                 tid_st t_s *) *)
  (*       (*                 (Event (MarkComplete t_s) tt) tr) *) *)
  (*       (* (TR_ST: nth_error tr tid_st = Some tr_st) *) *)
  (*       (* (COMPL: In (compl_event t_s) (flatten_tes tr_st)) *) *)
  (*       (FAIL_AFTER_START: *)
  (*          ~ service_time_exec (SyncSys.time st') t exec') *)
  (*   : ~ service_time_exec t_s t exec. *)
  (* Proof. *)
  (*   intro SERV_EXEC. *)
  (*   apply FAIL_AFTER_START. clear FAIL_AFTER_START. *)
  (*   r in SERV_EXEC. r. *)
  (*   intros t' SYNC_T' RANGE_T'. *)
  (*   hexploit SERV_EXEC; eauto. *)
  (*   { nia. } *)

  (*   intros (tid_c & CTRL & IN_EXEC). *)
  (*   hexploit sync_msteps_time; eauto. i. des. *)

  (*   inv IN_EXEC. *)
  (*   eapply Forall3_nth3 in EXEC_DIV; eauto. des. subst. *)
  (*   renames e1 e2 into tr_n exec'_n. *)
  (*   renames NTH1 NTH2 into TR_N EXEC'_N. *)

  (*   esplits; eauto. *)
  (*   econs; eauto. *)

  (*   apply stream_In_app_or in EVTS_AT_T. des; ss. *)
  (*   exfalso. *)
  (*   eapply Forall_nth1 in TRACE_TIME; eauto. *)
  (*   rewrite Forall_forall in TRACE_TIME. *)
  (*   hexploit TRACE_TIME; eauto. s. nia. *)
  (* Qed. *)

  Lemma service_time_failed_tr_exec
        scnt st tr st'
        exec' exec
        t_s t' t
        (SAFE_ST': DSys.safe_state st')
        (EXEC_ST': DSys.exec_state dsys st' exec')
        (MSTEPS: msteps dsys scnt st tr st')
        (EXEC_DIV: sapp_each_rel tr exec' exec)
        (SYS_TIME: SyncSys.time st = t_s)
        (SYS_TIME': t' <= SyncSys.time st')
        (TIME_LE: t' <= t)
        (SERV_FAIL_TR: ~ service_time_tr t_s t' tr)
    : ~ service_time_exec t_s t exec.
  Proof.
    intro SV_EXEC.
    apply SERV_FAIL_TR. clear SERV_FAIL_TR.
    r in SV_EXEC.
    r. i.
    hexploit SV_EXEC; eauto.
    { nia. }
    i. des.
    esplits; eauto.

    eapply event_in_exec_must_in_tr; eauto.
    nia.
  Qed.

  Lemma service_time_failed_later_exec
        scnt st st'
        t' t_s t tr exec exec'
        (* (SAFE_ST': DSys.safe_state st') *)
        (* (EXEC_ST': DSys.exec_state dsys st' exec') *)
        (MSTEPS: msteps dsys scnt st tr st')
        (SYS_TIME': SyncSys.time st' = t')
        (EXEC_DIV: sapp_each_rel tr exec' exec)
        (TIME_LE: t_s <= t')
        (SERV_FAIL_LATER: ~ service_time_exec t' t exec')
    : ~ service_time_exec t_s t exec.
  Proof.
    intro SV_EXEC.
    apply SERV_FAIL_LATER. clear SERV_FAIL_LATER.
    r in SV_EXEC.
    r. i.
    hexploit SV_EXEC; eauto.
    { nia. }
    i. des.
    esplits; eauto.
    eapply event_in_exec_not_in_tr; eauto.

    intro IN_TR. inv IN_TR.
    hexploit sync_msteps_trace_time_range; eauto.
    nia.
  Qed.

  Lemma safety_exec
        (st_i: DSys.state dsys) exec t_s
        (INV_PRE: AcStInv.sys_pre st_i)
        (SAFE_ST: DSys.safe_state st_i)
        (EXEC_ST: DSys.exec_state dsys st_i exec)
        (SERV_START: service_start_exec t_s exec)
    : forall tid t_u
        (DEV: is_dev_tid tid)
        (USE: event_in_exec tid (Z.of_nat t_u)
                            (Event (inl1 UseResource) tt) exec),
      ((* service_fail *)
        ~ service_time_exec t_s t_u exec) \/
      ((* exclusive *)
        forall tid',
          tid' <> tid ->
          ~ event_in_exec tid' (Z.of_nat t_u)
            (Event (inl1 UseResource) tt) exec).
  Proof.
    hexploit service_start_msteps; eauto.
    renames SAFE_ST EXEC_ST SERV_START into
            SAFE_ST_I EXEC_ST_I SERV_START_I.
    i. des.

    hexploit sync_msteps_system_time_adv; eauto.
    (* rewrite Nat.add_assoc. *)
    (* rewrite START_TIME_EQ. *)
    intros TIME_ST_S. r in TIME_ST_S.
    eapply event_in_exec_not_in_tr in USE; eauto.
    2: { ii. hexploit NO_DEV_EVENTS_BEFORE_START; eauto.
         unfold dev_event.
         intro C. apply C. right. ss. }

    eapply update_goal_lor.
    { eapply service_time_failed_later_exec; eauto.
      nia. }

    eapply update_goal_ror with
        (Q:= forall tid' : nat,
            tid' <> tid ->
            ~ event_in_exec tid' (Z.of_nat t_u)
              (Event (inl1 UseResource) tt) exec_s).
    { intro NOT_IN_EXEC_S.
      i. hexploit NOT_IN_EXEC_S; eauto.
      intros C IN_EXEC. apply C. clear C.
      eapply event_in_exec_not_in_tr; eauto.

      intro IN_TR.
      hexploit NO_DEV_EVENTS_BEFORE_START; eauto.
      intro C. apply C. r.
      right. ss.
    }

    hexploit event_in_exec_msteps; eauto. i. nbdes.
    hexploit sync_msteps_system_time_adv; eauto.
    intro TIME_ST1. r in TIME_ST1.

    des.
    { (* serv_fail1 *)
      left.
      eapply service_time_failed_tr_exec; eauto.
      { nia. }
      rewrite EVT_TIME_EQ.
      rewrite <- TIME_ST_S. ss.
    }
    right.

    intros tid' TID_EQ USE_EXEC.
    eapply event_in_exec_not_in_tr in USE_EXEC; eauto.
    2: {
      intro C. inv C.
      hexploit sync_msteps_trace_time_range;
        try apply MSTEPS1; eauto.
      nia.
    }

    eapply TID_EQ.
    eapply inv_use_res_exclusive; try apply MSTEPS2; eauto.
    - rewrite TIME_ST1.
      apply Nat.divide_add_r; ss.
      apply Nat.divide_mul_r.
      apply Nat.divide_refl.
    - rewrite EVT_TIME_EQ. ss.
      eapply event_in_exec_must_in_tr in USE_EXEC; eauto.
      rewrite <- EVT_TIME_EQ.
      hexploit sync_msteps_system_time_adv; eauto.
      i. des. nia.
    - rewrite EVT_TIME_EQ. ss.
  Qed.

  Lemma liveness_exec
        (st_i: DSys.state dsys) exec t_s
        (INV_PRE: AcStInv.sys_pre st_i)
        (SAFE_ST: DSys.safe_state st_i)
        (EXEC_ST: DSys.exec_state dsys st_i exec)
        (SERV_START: service_start_exec t_s exec)
    : forall tid t_dmd dmd dmd_n
      (DEV_TID: is_dev_tid tid)
      (DMD_POS: 0 < dmd_n)
      (DMD_NAT: Z_to_nat2 (Int.signed dmd) = Some dmd_n)
      (DMD_IN_EXEC: event_in_exec tid (Z.of_nat t_dmd)
                                  (Event (inl1 CheckDemand) dmd) exec),
      ((* service_fail *)
        ~ service_time_exec t_s (t_dmd + max_prds_tot * period) exec) \/
      ((* device_fail *)
        exists tm_dfail logv,
          t_dmd <= tm_dfail < t_dmd + max_prds_tot * period /\
          Nat.divide period tm_dfail /\
          ~ event_in_exec tid (Z.of_nat tm_dfail)
            (compl_event logv) exec) \/
            (* (Event (MarkComplete tm_dfail) tt) exec) \/ *)
      ((* success *)
        exists t_own,
          t_dmd <= t_own < t_dmd + max_prds_tot * period /\
          forall k (K_BND: k < Nat.min MAX_TIMEOUT dmd_n),
            event_in_exec tid (Z.of_nat (t_own + k * period))
                          (Event (inl1 UseResource) tt) exec)
  .
  Proof.
    hexploit service_start_msteps; eauto.
    renames SAFE_ST EXEC_ST SERV_START into
            SAFE_ST_I EXEC_ST_I SERV_START_I.
    i. des.

    hexploit sync_msteps_system_time_adv; eauto.
    (* rewrite Nat.add_assoc. *)
    (* rewrite START_TIME_EQ. *)
    intros TIME_ST_S. r in TIME_ST_S.
    eapply event_in_exec_not_in_tr in DMD_IN_EXEC; eauto.
    2: { ii. hexploit NO_DEV_EVENTS_BEFORE_START; eauto.
         intro C. apply C.
         r. left. esplits; eauto. }

    eapply update_goal_lor.
    { eapply service_time_failed_later_exec; eauto. nia. }

    assert (EXEC_S_AUX:
              forall tm e
                (* (EVT_DEV: dev_event e) *)
                (TM_LBND: SyncSys.time st_s <= tm)
                (IN_EXEC: event_in_exec tid (Z.of_nat tm) e exec),
                event_in_exec tid (Z.of_nat tm) e exec_s).
    { i. eapply event_in_exec_not_in_tr; eauto.
      intro IN_TR. inv IN_TR.
      hexploit sync_msteps_trace_time_range; eauto.
      nia. }

    hexploit event_in_exec_msteps; eauto. i. nbdes.
    hexploit sync_msteps_system_time_adv; eauto.
    intro TIME_ST1. r in TIME_ST1.

    assert (EXEC_1_AUX:
              forall tm e
                (TM_LBND: t_dmd <= tm)
                (IN_EXEC: event_in_exec tid (Z.of_nat tm) e exec_s),
                event_in_exec tid (Z.of_nat tm) e exec1).
    { i. eapply event_in_exec_not_in_tr; eauto.
      intro IN_TR. inv IN_TR.
      hexploit sync_msteps_trace_time_range; eauto.
      nia. }

    des.
    { (* serv_fail1 *)
      left.
      eapply service_time_failed_tr_exec; eauto.
      { nia. }
      rewrite EVT_TIME_EQ.
      rewrite <- TIME_ST_S. ss.
    }

    eapply update_goal_lor.
    { eapply service_time_failed_later_exec;
        try apply MSTEPS1; try apply EXEC_STATE1; eauto.
      nia.
    }

    hexploit sync_msteps_system_time_adv; eauto.
    intro TIME_ST2. r in TIME_ST2.

    assert (SYNC_TIME_ST1: Nat.divide period (SyncSys.time st1)).
    { rewrite TIME_ST1.
      apply Nat.divide_add_r.
      - ss.
      - apply Nat.divide_mul_r.
        apply Nat.divide_refl. }

    hexploit inv_prsv_sys; eauto. i. des.
    { left.
      eapply service_time_failed_tr_exec; eauto.
      { nia. }
      intro SV_TR. r in SV_TR.
      hexploit (SV_TR t_dmd).
      { rewrite <- EVT_TIME_EQ. ss. }
      { nia. }
      intros (tid_x & CTRL_X & EVT_IN_TR).
      (* r in CTRL_X. desH CTRL_X. *)
      (* - subst tid_x. *)
      (*   rewrite EVT_TIME_EQ in *. ss. *)
      (* - subst tid_x. *)
      (*   rewrite EVT_TIME_EQ in *. ss. *)
      admit.
    }

    hexploit dev_wait_intro; eauto.
    { rewrite EVT_TIME_EQ. eauto. }
    intro INV_DWAIT.

    eapply update_goal_lor.
    { eapply service_time_failed_later_exec;
        try apply MSTEPS2; try apply EXEC_STATE2; eauto.
      nia.
      (* { eauto. } *)
      (* (* instantiate (1:= t_dmd + period). *) *)
      (* nia. *)
    }
    rename k into k_until_dmd.

    assert (EXEC_2_AUX:
              forall tm e
                (TM_LBND: t_dmd + period <= tm)
                (IN_EXEC: event_in_exec tid (Z.of_nat tm) e exec1),
                event_in_exec tid (Z.of_nat tm) e exec2).
    { i. eapply event_in_exec_not_in_tr; eauto.
      intro IN_TR. inv IN_TR.
      hexploit sync_msteps_trace_time_range; eauto.
      nia. }

    hexploit dev_wait_msteps; eauto.
    { rewrite TIME_ST2.
      apply Nat.divide_add_r; eauto.
      apply Nat.divide_refl. }
    i. nbdes.
    rename k into k_dwait.

    hexploit sync_msteps_system_time_adv; eauto.
    intro TIME_W'. r in TIME_W'.

    assert (EXEC_W'_AUX:
              forall tm e
                (TM_LBND: SyncSys.time st_w' <= tm)
                (IN_EXEC: event_in_exec tid (Z.of_nat tm) e exec2),
                event_in_exec tid (Z.of_nat tm) e exec_w').
    { i. eapply event_in_exec_not_in_tr; eauto.
      intro IN_TR. inv IN_TR.
      hexploit sync_msteps_trace_time_range; eauto.
      nia. }

    des.
    { (* service_failed *)
      left.
      eapply service_time_failed_tr_exec; eauto.
      { nia. }
      (* { rewrite TIME_W'. *)
      (*   unfold max_prds_tot, max_prds_each_owner. *)
      (*   rewrite TIME_ST2. *)
      (*   rewrite EVT_TIME_EQ. *)

      (*   cut (k_dwait + 1 <= (MAX_TIMEOUT + 2) * 3). *)
      (*   { clear. nia. } *)
      (*   nia. } *)
      (* rewrite <- EVT_TIME_EQ. *)
      rewrite <- TIME_ST2.
      rewrite <- TIME_W' in SERVICE_FAILED.
      ss.
    }
    { (* device_failed *)
      right. left.
      exists (t_dmd + period + k_fail * period).
      (* splits; eauto. *)
      (* { admit. (* nia. } *) } *)
      (* { unfold max_prds_tot. nia. } *)
      (* { rewrite <- EVT_TIME_EQ. *)
      (*   eauto with acst. } *)

      (* intro EXEC. *)
      (* apply EXEC_S_AUX in EXEC. *)
      (* 2: { nia. } *)
      (* apply EXEC_1_AUX in EXEC. *)
      (* 2: { nia. } *)
      (* apply EXEC_2_AUX in EXEC. *)
      (* 2: { nia. } *)
      (* revert EXEC. *)

      (* rewrite <- EVT_TIME_EQ. *)
      (* rewrite <- TIME_ST2. *)
      (* intro IN_EXEC. *)
      (* apply DEV_NOT_COMPL. *)
      (* eapply event_in_exec_must_in_tr; *)
      (*   try apply EXEC_DIV_W'; eauto. *)
      (* rewrite TIME_W'. nia. *)
      admit.
    }

    (* got ownership *)

    hexploit dev_owner_msteps; eauto.
    { rewrite TIME_W'.
      rewrite TIME_ST2. eauto with app_pf. }
    i. nbdes.

    hexploit sync_msteps_system_time_adv; eauto.
    intro TIME_O'. r in TIME_O'.

    (* assert (EXEC_W'_AUX: *)
    (*           forall tm e *)
    (*             (TM_LBND: SyncSys.time st_w' <= tm) *)
    (*             (NOT_IN_EXEC: ~ event_in_exec tid tm e exec_w'), *)
    (*             ~ event_in_exec tid tm e exec2). *)
    (* { i. intro IN_EXEC. *)
    (*   apply NOT_IN_EXEC. clear NOT_IN_EXEC. *)
    (*   eapply event_in_exec_not_in_tr; eauto. *)
    (*   intro IN_TR. inv IN_TR. *)
    (*   hexploit sync_msteps_trace_time_range; eauto. *)
    (*   nia. } *)

    eapply update_goal_lor.
    { eapply service_time_failed_later_exec;
        try apply MSTEPS_W; eauto.
      (* try apply EXEC_DIV_W'; eauto. *)
      (* { eauto. } *)
      (* instantiate (1:= SyncSys.time st_w'). *)
      nia.
    }

    des.
    { (* fail *)
      left.
      eapply service_time_failed_tr_exec; eauto.
      { unfold max_prds_tot, max_prds_each_owner.
        rewrite TIME_O'. rewrite TIME_W'.
        rewrite TIME_ST2. rewrite EVT_TIME_EQ.
        transitivity (t_dmd + (1 + k_dwait + MAX_TIMEOUT) * period).
        { nia. }
        ss.
        cut (k_dwait + MAX_TIMEOUT <= (MAX_TIMEOUT + 2) * 3).
        { clear. nia. }
        nia.
      }
      rewrite <- TIME_O' in SERVICE_FAILED.
      rewrite <- TIME_W'.
      ss.
    }
    { (* device_failed *)
      right. left.
      exists (SyncSys.time st_w' + k_fail * period).
      (* splits; eauto. *)
      (* { nia. } *)
      (* { unfold max_prds_tot, max_prds_each_owner. *)
      (*   clear - K_FAIL_BOUND TIME_W' TIME_ST2 *)
      (*                        EVT_TIME_EQ K_BOUND *)
      (*                        DMD_POS PERIOD_POS. *)
      (*   nia. } *)
      (* { rewrite TIME_W', TIME_ST2. *)
      (*   apply Nat.divide_add_r. (* why eauto with acst didn't work?*) *)
      (*   - eauto with acst. *)
      (*   - eauto with acst. *)
      (* } *)

      (* intro EXEC. *)
      (* apply EXEC_S_AUX in EXEC. *)
      (* 2: { nia. } *)
      (* apply EXEC_1_AUX in EXEC. *)
      (* 2: { nia. } *)
      (* apply EXEC_2_AUX in EXEC. *)
      (* 2: { nia. } *)
      (* apply EXEC_W'_AUX in EXEC. *)
      (* 2: { nia. } *)
      (* revert EXEC. *)

      (* intro IN_EXEC. *)
      (* apply DEV_NOT_COMPL. *)
      (* eapply event_in_exec_must_in_tr; eauto. *)
      (* rewrite TIME_O'. nia. *)
      admit.
    }
    (* success *)
    right. right.
    exists (SyncSys.time st_w').
    splits.
    - nia.
    - nia.
    - i. hexploit USE_RES; eauto.
      intro TR_EX.
      eapply event_in_later_exec; eauto.
      eapply event_in_later_exec; eauto.
      eapply event_in_later_exec; eauto.
      eapply event_in_later_exec; eauto.
      eapply event_in_tr_exec; eauto.
  Admitted.
  (* Qed. *)

End LEMMAS.




Definition acst_sync_sys: SyncSys.t :=
  PALSSys.as_sync active_standby_system.

Definition acst_sync_dsys (tm_init: nat): DSys.t :=
  PALSSys.dsys_sync active_standby_system tm_init.
  (* SyncSys.as_dsys acst_sync_sys tm_init. *)


Section ACST_LEMMAS.
  Variable tm_init: nat.
  Let dsys: DSys.t := acst_sync_dsys tm_init.

  Lemma init_inv_pre
        st
        (INIT_STATE: st = SyncSys.init_state tm_init acst_sync_sys)
    : AcStInv.sys_pre st.
  Proof.
  Admitted.

End ACST_LEMMAS.


Local Transparent period.

Lemma period_nonzero
  : period <> 0%Z.
Proof.
  unfold period. ss.
Qed.

Local Opaque period.



Theorem active_standby_synchronous_timestamps
        beh tm_init
        (BEH: DSys.behav_sys
                (PALSSys.dsys_sync
                   active_standby_system tm_init) beh)
  : forall tid tsp evt,
    event_in_beh tid (Z.of_nat tsp, evt) beh ->
    (Nat.divide (Z.to_nat period) tsp).
Proof.
  pose (sys := PALSSys.as_sync active_standby_system).
  pose (dsys := PALSSys.dsys_sync active_standby_system tm_init).
  hexploit (SyncSys.safe tm_init sys).
  { econs; eauto. s.
    generalize period_nonzero.
    admit.
    (* nia. } *)
  }
  intro SAFE_DSYS.
  inv SAFE_DSYS.
  clear INIT_EXISTS.

  r in BEH. des.
  { exfalso. apply BEH.
    esplits; ss. }
  ss.

  hexploit ALL_INIT_SAFE; eauto.
  intro SAFE_STATE.
  clear ALL_INIT_SAFE.
  clear INIT_STATE.

  r in BEH_ST. des. i.

  hexploit event_in_beh_exec; eauto. i.
  hexploit sync_event_in_exec_synchronous; eauto.
(* Qed. *)
Admitted.

Theorem active_standby_safety_sync
        beh tm_init t_start
        (BEH: DSys.behav_sys (PALSSys.dsys_sync
                                active_standby_system tm_init)
                             beh)
        (SERVICE_START: service_start t_start beh)
  : forall tid t_u,
    service_time t_start t_u beh ->
    is_dev_tid tid ->
    event_in_beh tid (Z.of_nat t_u, Event (inl1 UseResource) tt) beh ->
    forall tid',
      tid' <> tid ->
      ~ event_in_beh tid' (Z.of_nat t_u, Event (inl1 UseResource) tt) beh.
Proof.
  intros tid t_u SERVICE_TIME DEV_TID
         E_IN_BEH tid' TID_NEQ E_IN_BEH'.
  pose (sys := PALSSys.as_sync active_standby_system).
  pose (dsys := PALSSys.dsys_sync active_standby_system tm_init).
  hexploit (SyncSys.safe tm_init sys).
  { econs; eauto. s.
    generalize period_nonzero.
    (* nia. } *)
    admit.
  }
  intro SAFE_DSYS.
  inv SAFE_DSYS.
  clear INIT_EXISTS.

  r in BEH. des.
  { exfalso. apply BEH.
    esplits; ss. }
  ss.

  hexploit ALL_INIT_SAFE; eauto.
  intro SAFE_STATE.

  assert (INV_PRE: AcStInv.sys_pre st_i).
  { eapply init_inv_pre. eauto. }
  clear INIT_STATE.

  r in BEH_ST. des.

  assert (service_start_exec t_start exec).
  { (* service_start -> service_start_exec *)
    r in SERVICE_START. r.
    des.
    esplits; eauto.
    - eapply event_in_beh_exec; eauto.
    - intro tid_x. ii. hexploit (SERVICE_START1 tid_x); eauto.
      intro C. apply C.
      esplits; eauto.
      eapply event_in_exec_beh; eauto.
  }

  hexploit safety_exec; eauto.
  { admit. (* eapply period_nonzero. } *) }
  { eapply event_in_beh_exec; eauto. }
  intros [SERV_TM | EXCL].
  - apply SERV_TM.
    clear - SERVICE_TIME EXEC_BEH.
    r in SERVICE_TIME.
    r.
    i.
    hexploit SERVICE_TIME; eauto. i. des.
    esplits; eauto.
    eapply event_in_beh_exec; eauto.
  - eapply event_in_beh_exec in E_IN_BEH'; eauto.
    clear - E_IN_BEH' EXCL TID_NEQ.
    hexploit (EXCL tid'); eauto.
(* Qed. *)
Admitted.


(* Lemma update_goal_lor (P P' Q: Prop) *)
(*       (PROP_IMPL: P -> P') *)
(*       (OR: P \/ Q) *)
(*   : P' \/ Q. *)
(* Proof. *)
(*   des; eauto. *)
(* Qed. *)

(* Lemma service_time_fin_later *)
(*       t1 t2 fbeh beh' beh *)
(*       (NSERV: ~ service_time t1 t2 beh') *)
(*       (BEH_DIV: capp_each_rel fbeh beh' beh) *)
(*   : ~ service_time t1 t2 beh. *)
(* Proof. *)
(*   intro SV. *)
(*   apply NSERV. clear NSERV. *)
(*   unfold service_time in *. ii. *)

(*   hexploit SV; eauto. *)
(*   intros (tid_ctrl & CTRL_TID & EINB). *)
(*   inv EINB. *)
(*   esplits; eauto. *)
(*   eapply Forall3_nth3 in BEH_DIV; eauto. des. *)
(*   econs; eauto. *)
(*   subst. *)
(*   apply colist_In_app_or in IN_LBEH. *)
(*   eauto. *)
(* Qed. *)





Theorem active_standby_liveness_sync
        beh tm_init t_start
        (* (TM_INIT: period <= tm_init) *)
        (BEH: DSys.behav_sys
                (PALSSys.dsys_sync
                   active_standby_system tm_init) beh)
        (SERVICE_START: service_start t_start beh)
  : exists t_max: nat,
  forall tid t_dmd dmd dmd_n,
    is_dev_tid tid /\
    (* service_time  tsp beh /\ *)
    Z_to_nat2 (Int.signed dmd) = Some dmd_n /\
    0 < dmd_n /\
    event_in_beh tid (Z.of_nat t_dmd, Event (inl1 CheckDemand) dmd) beh ->
    ((* service_fail *)
      ~ service_time t_start (t_dmd + t_max) beh) \/
    ((* device_fail *)
      exists t_fail,
        t_dmd <= t_fail < t_dmd + t_max /\
        Nat.divide (Z.to_nat period) t_fail /\
        ~ exists logv, event_in_beh tid (Z.of_nat t_fail, compl_event logv) beh) \/
    ((* success *)
      exists t_own,
        t_dmd <= t_own < t_dmd + t_max /\
        forall k, k < Nat.min MAX_TIMEOUT dmd_n ->
             event_in_beh tid (Z.of_nat (t_own + k * Z.to_nat period),
                               Event (inl1 UseResource) tt) beh).
Proof.
  pose (t_max := (1 + (MAX_TIMEOUT + 2) * 3) * (Z.to_nat period)).
  exists t_max.

  pose (sys := PALSSys.as_sync active_standby_system).
  pose (dsys := PALSSys.dsys_sync active_standby_system tm_init).

  (* initial state *)
  hexploit (SyncSys.safe tm_init sys).
  { econs; eauto. s.
    generalize period_nonzero.
    admit.
    (* nia. } *)
  }
  intro SAFE_DSYS.
  inv SAFE_DSYS.
  clear INIT_EXISTS.

  r in BEH. des.
  { exfalso. apply BEH.
    esplits; ss. }
  ss.

  hexploit ALL_INIT_SAFE; eauto.
  intro SAFE_ST. clear ALL_INIT_SAFE.

  assert (INV_PRE: AcStInv.sys_pre st_i).
  { eapply init_inv_pre. eauto. }
  clear INIT_STATE.

  r in BEH_ST. des.

  i. des.

  assert (service_start_exec t_start exec).
  { (* service_start -> service_start_exec *)
    r in SERVICE_START. r.
    des.
    esplits; eauto.
    - eapply event_in_beh_exec; eauto.
    - ii. hexploit (SERVICE_START1 tid'); eauto.
      intro C. apply C.
      esplits; eauto.
      eapply event_in_exec_beh; eauto.
  }

  assert (event_in_exec tid (Z.of_nat t_dmd)
                        (Event (inl1 CheckDemand) dmd) exec).
  { (* event_in_beh -> event_in_exec *)
    eapply event_in_beh_exec; eauto. }

  hexploit liveness_exec; eauto.
  { (* eapply period_nonzero. } *)
    admit. }
  i. des.
  - left.
    intro SVTM.
    match goal with
    | H: ~ service_time_exec _ _ _ _ |- _ => apply H
    end.
    s. fold t_max.
    r in SVTM. r. s. i.
    hexploit SVTM.
    { eassumption. }
    { assumption. }
    intro CC. des.
    esplits; eauto.
    eapply event_in_beh_exec; eauto.
  - right. left.
    esplits; eauto.
    intro EINB.
  (* eapply event_in_beh_exec in EINB; eauto. *)
    admit.
  - right. right.
    esplits; eauto. i.
    eapply event_in_exec_beh; eauto.
(* Qed. *)
Admitted.
