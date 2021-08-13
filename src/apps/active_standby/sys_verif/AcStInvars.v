From Paco Require Import paco.
From ITree Require Import ITree.
Require Import sflib.

Require Import StdlibExt IntegersExt.
Require Import SysSem.
Require Import SyncSysModel.

Require Import MSteps FMSim FMSim_Switch.
Require Import PALSSystem.

Require console ctrl dev.

Require Import AcStSystem.
Require Import SpecConsole SpecController SpecDevice.
Require Import VerifConsole VerifController VerifDevice.

Require Import AcStRefinement.

Require Import ZArith Streams List Lia.

(* Local Opaque Z.of_nat Z.to_nat. *)

Import ActiveStandby.

Set Nested Proofs Allowed.

Require Import CProgEventSem.
(* Require Import AsyncSyncRef. *)

Require Import BehavUtils.
Require Import ITreeTac.

Require Import RTSysEnv.

Require Import Bool.
Require Import VerifController_Base VerifController_Updq.
Require Import CompcertLemmas.


Lemma if_both_eq A
      (x: bool) (a: A)
  : (if x then a else a) = a.
Proof.
  destruct x; ss.
Qed.



Definition dev_tids: list nat :=
  [tid_dev1; tid_dev2; tid_dev3].

Definition is_dev_tid (tid: nat): Prop :=
  In tid dev_tids.

Definition is_ctrl_tid (tid: nat): Prop :=
  tid = tid_ctrl1 \/ tid = tid_ctrl2.

(* Definition compl_event (tm:nat): nat * event obsE := *)
(*   (tm, Event (MarkComplete tm) tt). *)

Definition num_tasks: nat := 6.

Definition abst_queue_wf (aq: list nat): Prop :=
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

Definition aq_add
           (tid: nat)
           (st: list nat * nat)
  : (list nat) * nat :=
  let (aq, tout) := st in
  (* (snoc aq tid, tout). *)
  (if existsb (Nat.eqb tid) aq then aq else snoc aq tid,
   tout).

Definition aq_remove
           (tid: nat)
           (st: list nat * nat)
  : (list nat) * nat :=
  let (aq, tout) := st in
  ((* filter (fun tid' => tid' =? tid) aq, *)
    aq,
    match aq with
    | h :: _ =>
      if (h =? tid) && (0 <? tout) && (tout <? MAX_TIMEOUT)
      then 1 else tout
    | _ => tout
    end).

(* The two controller nodes simulates
   a (more reliable) single abstract controller *)

Definition snode_con := ITrSNode.to_snode con_mod.
Definition snode_c1 := ITrSNode.to_snode (ctrl_mod 1).
Definition snode_c2 := ITrSNode.to_snode (ctrl_mod 2).
Definition snode_dev := ITrSNode.to_snode dev_mod.

(* pervious execution result *)
Inductive pexec_t: Set :=
  Nothing | Update | SendHB | Compl.

Definition is_hb_sent (pex: pexec_t): bool :=
  match pex with
  | Nothing | Update => false
  | _ => true
  end.

Definition is_updated (pex: pexec_t): bool :=
  match pex with
  | Nothing => false
  | _ => true
  end.

Definition is_compl (pex: pexec_t): bool :=
  match pex with
  | Compl => true
  | _ => false
  end.

Definition is_active_side (actv_flag side: bool): bool :=
  bool_eq actv_flag side.

Definition side2tid (side: bool): nat :=
  if side then tid_ctrl1 else tid_ctrl2.


Module AbstCtrl.
  Record t: Type :=
    mk { (* controllers *)
        inbox: list bytes? ;
        failed_controller: pexec_t * pexec_t ;

        active_side: bool ; (* true => first is active *)
        abst_queue: list nat ;
        owner_timeout: nat ;
      }.

  Definition cur_owner (aq: list nat) (tout: nat): nat? :=
    match aq with
    | [] => None
    | h :: _ => if andb (0 <? tout) (tout <? MAX_TIMEOUT) then Some h else None
    end.

  Definition grant_msg_loc (aq: list nat) (tout: nat): nat? :=
    match aq with
    | [] => None
    | h :: _ => if MAX_TIMEOUT =? tout then Some h else None
    end.

  Lemma wf_grant_msg_loc_dev_tid
        aq tout
        (WF: abst_queue_wf aq)
    : option_rel1 is_dev_tid (grant_msg_loc aq tout).
  Proof.
    unfold grant_msg_loc.
    destruct aq; ss.
    r in WF. des.
    inv EACH_DEV_TID.
    desf; ss.
  Qed.

  Definition pex_prev_active (ac: t): pexec_t :=
    if (active_side ac) then
      fst (failed_controller ac)
    else
      snd (failed_controller ac).

  Definition aq_process_dev_msg
             (st: list nat * nat)
             (tid_md: nat * bytes?)
    : list nat * nat :=
    (* let (aq, tout) := st in *)
    let (tid, md) := tid_md in
    match md with
    | None => st
    | Some bs =>
      if Byte.eq (nth O bs Byte.zero) Byte.one then
        aq_add tid st
      else
        aq_remove tid st
    end.

  Definition aq_process_dev_msgs
             (aq: list nat) (tout: nat)
             (mds: list (nat * bytes?))
    : list nat * nat :=
    fold_left (aq_process_dev_msg) mds (aq, tout).

  Definition aq_update_queue
             (aq: list nat) (tout: nat)
             (mds: list (nat * bytes?))
    : list nat * nat :=
    let (aq1, tout1) := aq_process_dev_msgs aq tout mds in
    match tout1 with
    | O => (aq1, 0)
    | S O => (tl aq1, 0)
    | S tout' => (aq1, tout')
    end.

  Definition aq_new_owner
             (aq: list nat) (tout: nat)
    :  nat * nat? :=
    if (tout =? 0) then
      match hd_error aq with
      | Some nown => (MAX_TIMEOUT, Some nown)
      | None => (0, None) (* unreachable *)
      end
    else (tout, None).

  Lemma aq_new_owner_grant_msg_loc
        aq tout
        tout' nown
        (TIMEOUT_LT_MAX: tout < MAX_TIMEOUT)
        (AQ_NEW_OWNER: aq_new_owner aq tout =
                       (tout', nown))
    : grant_msg_loc aq tout' = nown.
  Proof.
    unfold aq_new_owner, grant_msg_loc in *.
    ss. desf.
    unfold MAX_TIMEOUT in *. nia.
  Qed.

  Definition next_active_side
             (mcon mc1 mc2: bytes?) (asd: bool): bool :=
    let tgl: bool := mcon in
    let alive1: bool := mc1 in
    let alive2: bool := mc2 in
    if asd then
      if tgl then
        andb alive1 (negb alive2)
      else alive1
    else
      if tgl then
        negb (andb (negb alive1) alive2)
      else negb alive2.

  Definition next
             (pex1 pex2: pexec_t)
             (inb: list bytes?) (asd: bool)
             (aq: list nat) (tout: nat)
    : bool * list nat * nat * nat? :=
    match inb with
    | mcon :: mc1 :: mc2 :: md1 :: md2 :: md3 :: nil =>
      let asd': bool := next_active_side mcon mc1 mc2 asd in
      let tout_ug :=
          let pex_pa := if asd then pex1 else pex2 in
          if andb (negb (is_hb_sent pex_pa))
                  (tout =? MAX_TIMEOUT)
          then 0 else tout
      in
      let (aq', tout1) :=
          aq_update_queue aq tout_ug
            [(tid_dev1, md1); (tid_dev2, md2); (tid_dev3, md3)] in
      let '(tout', nown) := aq_new_owner aq' tout1 in
      (asd', aq', tout', nown)

    | _ => (true, [], 0, None) (* unreachable *)
    end.

  Inductive hb_of_abst_ctrl (is_active: bool)
            (aq: list nat) (tout: nat)
    : pexec_t -> bytes? -> Prop :=
  | HBOfAbstCtrl_None
      pex
      (HB_NOT_SENT: is_hb_sent pex = false)
    : hb_of_abst_ctrl is_active aq tout pex None
  | HBOfAbstCtrl_Some
      pex msg
      cst_m md_m tout_m qb_m qe_m q_m
      (HB_SENT: is_hb_sent pex = true)
      (CTRL_OF_BYTES: CtrlState.of_bytes msg = cst_m)
      (CTRL_EQ: cst_m = CtrlState.mk md_m tout_m
                                     qb_m qe_m q_m)
      (MATCH_QUEUE: match_queue aq (qb_m, qe_m, q_m))
      (MATCH_MODE:
         if is_active then
           md_m = CtrlState.Active
         else
           md_m = CtrlState.Standby)
      (TOUT_M: tout_m = Z.of_nat tout)
    : hb_of_abst_ctrl is_active aq tout pex (Some msg)
  .

  (* Inductive abst_dev_wf *)
  (*           (aq: list nat) (tout: nat) *)
  (*           (ment_c: bytes?) (tid_d: nat) *)
  (*   : DevState.t -> Prop := *)
  (* | AbstDevWf_Uninit *)
  (*     (NO_MSG_TO_C: ment_c = None) *)
  (*   : abst_dev_wf aq tout ment_c tid_d *)
  (*                 (DevState.mk None 0) *)
  (* | AbstDevWf_Owner *)
  (*     dmd *)
  (*     (CUR_OWNER_THIS: cur_owner aq tout = Some tid_d) *)
  (*     (RANGE_TOUT: 0 < tout < MAX_TIMEOUT) *)
  (*     (RANGE_DEMAND: 0 < dmd <= tout) *)
  (*     (NO_MSG_TO_C: ment_c = None) *)
  (*   : abst_dev_wf aq tout ment_c tid_d *)
  (*                 (DevState.mk (Some true) dmd) *)
  (* | AbstDevWf_NotOwnerWithDemand *)
  (*     dmd *)
  (*     (DMD_POS: 0 < dmd) *)
  (*     (CTRL_AWARE_DMD: In tid_d aq \/ ment_c = Some acq_msg) *)
  (*     (GRANT_EX_IF_OWNER: *)
  (*        cur_owner aq tout = Some tid_d -> *)
  (*        tout = MAX_TIMEOUT) *)
  (*   : abst_dev_wf aq tout ment_c tid_d *)
  (*                 (DevState.mk (Some false) dmd) *)
  (* | AbstDevWf_NotOwnerWithoutDemand *)
  (*     (MSG_MAYBE_REL: option_rel1 (fun m => m = rel_msg) ment_c) *)
  (*     (REL_IF_IN_Q: In tid_d aq -> ment_c = Some rel_msg) *)
  (*   : abst_dev_wf aq tout ment_c tid_d *)
  (*                 (DevState.mk (Some false) 0) *)
  (* . *)

  Inductive wf: t -> Prop :=
    Wf inb (pex1 pex2: pexec_t) asd aq tout
       me_con me_c1 me_c2
       me_d1 me_d2 me_d3
       (WF_AQ: abst_queue_wf aq)
       (RANGE_TIMEOUT: tout <= MAX_TIMEOUT)
       (EMPTY_QUEUE_TOUT_ZERO: length aq = 0 <-> tout = 0)
       (INBOX_EQ: inb = [me_con; me_c1; me_c2;
                        me_d1; me_d2; me_d3])
       (AT_LEAST_ONE_COMPL: pex1 = Compl \/ pex2 = Compl)
       (ENTRY_CON: option_rel1 (fun m => m = toggle_msg) me_con)
       (ENTRY_C1: hb_of_abst_ctrl (is_active_side asd true)
                                  aq tout pex1 me_c1)
       (ENTRY_C2: hb_of_abst_ctrl (is_active_side asd false)
                                  aq tout pex2 me_c2)
       (* (ENTRY_C2: option_rel1 (hb_of_abst_ctrl (bool_eq asd false) aq tout) me_c2) *)
       (* (ENTRY_C1_EX_IF_COMPL: *)
       (*    (fc <> Some true) -> me_c1 <> None) *)
       (* (ENTRY_C2_EX_IF_COMPL: *)
       (*    (fc <> Some false) -> me_c2 <> None) *)

       (ENTRY_D1: option_rel1 (fun m => m = rel_msg \/ m = acq_msg) me_d1)
       (ENTRY_D2: option_rel1 (fun m => m = rel_msg \/ m = acq_msg) me_d2)
       (ENTRY_D3: option_rel1 (fun m => m = rel_msg \/ m = acq_msg) me_d3)

       (* (WF_DEV1: option_rel1 (abst_dev_wf aq tout me_d1 tid_dev1) ad1) *)
       (* (WF_DEV2: option_rel1 (abst_dev_wf aq tout me_d2 tid_dev2) ad2) *)
       (* (WF_DEV3: option_rel1 (abst_dev_wf aq tout me_d3 tid_dev3) ad3) *)
    : wf (mk inb (pex1, pex2) asd aq tout).

  Inductive match_ctrl_state
            (q: list nat) (tout: nat) (is_active: bool)
    : pexec_t -> CtrlState.t -> Prop :=
  | MatchCtrlState_Uninit
      cst
      (INIT_STATE: cst = CtrlState.init)
    : match_ctrl_state q tout is_active Nothing cst
  | MatchCtrlState
      md_c tout_c qb_c qe_c q_c
      (MODE: md_c = if is_active then
                      CtrlState.Active
                    else CtrlState.Standby)
      (TIMEOUT: tout_c = Z.of_nat tout)
      (MATCH_QUEUE: match_queue q (qb_c, qe_c, q_c))
    : match_ctrl_state q tout is_active
                       Compl
                       (CtrlState.mk md_c tout_c qb_c qe_c q_c).

  (* match_state that timeout invariant becomes temporarily relaxed. *)
  Inductive match_ctrl_state_temp
            (is_prev_active_sent_hb: bool)
            (q: list nat) (tout: nat) (is_active: bool)
    : CtrlState.t -> Prop :=
  | MatchCtrlStateTemp
      md_c tout_c qb_c qe_c q_c
      (* (WF_CST: CtrlState.wf (CtrlState.mk md_c tout_c *)
      (*                                     qb_c qe_c q_c)) *)
      (MODE: md_c = if is_active then
                      CtrlState.Active
                    else CtrlState.Standby)
      (TIMEOUT_EQ: tout_c =
                   if andb (negb is_prev_active_sent_hb)
                           (tout =? MAX_TIMEOUT)
                   then 0%Z
                   else Z.of_nat tout)
      (MATCH_QUEUE: match_queue q (qb_c, qe_c, q_c))
    : match_ctrl_state_temp
        is_prev_active_sent_hb
        q tout is_active
        (CtrlState.mk md_c tout_c qb_c qe_c q_c).


  (* Definition det_send_grant *)
  (*            (is_active: bool) *)
  (*            (aq: list nat) (tout: nat) *)
  (*   : nat? := *)
  (*   if is_active then *)
  (*     grant_msg_loc aq tout *)
  (*   else None. *)

  Definition msg_c2d
             (is_active: bool) (pex: pexec_t)
             (aq: list nat) (tout: nat)
             (tid_d: nat)
    : bytes? :=
    if andb (is_updated pex) is_active then
      match grant_msg_loc aq tout with
      | None => None
      | Some tid_g =>
        if tid_g =? tid_d then
          Some grant_msg
        else None
      end
    else None.

  Definition msg_pair_c2d
             (fc: pexec_t * pexec_t)
             (asd: bool) aq tout (tid_d: nat)
    : bytes? * bytes? :=
    (msg_c2d (is_active_side asd true) (fst fc) aq tout tid_d,
     msg_c2d (is_active_side asd false) (snd fc) aq tout tid_d).

  Definition inb_dev (fc: pexec_t * pexec_t)
             asd aq tout (tid_d: nat)
    : list bytes? :=
    let (m1, m2) := msg_pair_c2d fc asd aq tout tid_d in
    [None; m1; m2; None; None; None].

  Definition drop_self_entry (b: bool) (inb_c: list bytes?)
    : list bytes? :=
    replace_nth inb_c (if b then 1 else 2) None.

  (* { owner_status : bool ?;  demand : nat } *)
  (* 1. uninit (None, 0) -> no (acq \/ rel)  *)
  (* 2. NotOwnerWithoutDemand -> (Some false, 0), not in q or rel  *)
  (* 3. NotOwnerWithDemand -> (Some false, d>0), in q \/ acq *)
  (* 4. Owner -> (Some true, d>0), cur_owner *)

  Inductive match_dev_state
            (q: list nat) (tout: nat)
            (tid_d: nat)
            (m_d2c: bytes?)
    : (* bytes? (* d2c *) -> bytes? (* c2d *) -> *)
      DevState.t -> Prop :=
  | MatchDevState_Uninit
      cst
      (INIT_STATE: cst = DevState.init)
    : match_dev_state q tout tid_d m_d2c cst
  | MatchDevState_NotOwnerNoDemand
      (NO_DMD_CASES: m_d2c = Some rel_msg \/
                     (m_d2c = None /\ ~ In tid_d q))
    : match_dev_state q tout tid_d m_d2c
                      (DevState.mk (Some false) 0)
  | MatchDevState_NotOwnerWithDemand
      dmd
      (DMD_POS: 0 < dmd)
      (DMD_CASES: (m_d2c = Some acq_msg /\ ~ In tid_d q) \/
                  (m_d2c = None /\ In tid_d q))
    : match_dev_state q tout tid_d m_d2c
                      (DevState.mk (Some false) dmd)
  | MatchDevState_Owner
      dmd
      (DMD_POS: 0 < dmd <= tout)
      (NO_MSG_TO_CTRL: m_d2c = None)
      (CUR_OWNER_THIS: cur_owner q tout = Some tid_d)
    : match_dev_state q tout tid_d m_d2c
                      (DevState.mk (Some true) dmd)
  .

  Inductive dev_wait_cnt (q: list nat) (tout: nat) (pex_act: pexec_t)
            (tid_d: nat) (* (dmd: nat) *)
    : bytes? (*d2c*) -> (* DevState.t -> *) nat (*wcnt*) -> Prop :=
  | DevWaitCount_Acq
      wcnt
      (WAIT_MAX: wcnt = (2 + (MAX_TIMEOUT + 1) * 2))
    : dev_wait_cnt q tout pex_act tid_d (* dmd *)
                   (Some acq_msg)
                   (* (DevState.mk (Some false) dmd) *)
                   wcnt

  | DevWaitCount_InQueue
      i wcnt
      (WAITING_IN_QUEUE: nth_error q (S i) = Some tid_d)
      (WCNT_EQ: wcnt = if andb (tout =? MAX_TIMEOUT)
                               (negb (is_hb_sent pex_act))
                       then (1 + (MAX_TIMEOUT + 1) * i +
                             (MAX_TIMEOUT + 1))
                       else (1 + (MAX_TIMEOUT + 1) * i + tout))
    : dev_wait_cnt q tout pex_act tid_d
                   None wcnt

  | DevWaitCount_Owner
      wcnt
      (QUEUE_HEAD: nth_error q 0 = Some tid_d)
      (TIMEOUT_MAX: tout = MAX_TIMEOUT)
      (WCNT_EQ: wcnt = if is_updated pex_act then 0 else 1)
    : dev_wait_cnt q tout pex_act tid_d
                   None wcnt
  .

  Inductive dev_wait
            (q: list nat) (tout: nat) (pex_act: pexec_t)
            (tid_d: nat) (dmd: nat)
    : bytes? (*d2c*) -> DevState.t -> nat (*wcnt*) -> Prop :=
    DevWait
      m_d2c dst wcnt
      (DMD_POS: 0 < dmd)
      (DEV_WAIT_CNT: dev_wait_cnt q tout pex_act tid_d
                                  m_d2c wcnt)
      (DEV_STATE: dst = DevState.mk (Some false) dmd)
    : dev_wait q tout pex_act tid_d dmd
               m_d2c dst wcnt.

  Inductive dev_owner
            (aq: list nat) (tout: nat)
            (pex_act: pexec_t) (tid_d: nat)
    : (* bytes? * bytes? -> *) DevState.t -> nat -> Prop :=
  | DevOwner_RcvGrant
      m_c2d dmd
      (M_C2D: m_c2d = msg_c2d true pex_act aq tout tid_d)
      (DMD_POS: 0 < dmd)
      (GRANT_IN_INBOX: m_c2d = Some grant_msg)
    : dev_owner aq tout pex_act tid_d
                (DevState.mk (Some false) dmd) dmd
  | DevOwner_KeepOwnership
      dmd
      (DMD_POS: 0 < dmd)
    : dev_owner aq tout pex_act tid_d
                (DevState.mk (Some true) dmd) dmd
  .

  Lemma grant_msg_cond
        aq tout tid_d
        pex_act
        (* (PEX_ACTIVE: pex_act = if asd then pex1 else pex2) *)
    : (grant_msg_loc aq tout = Some tid_d /\
       is_updated pex_act) <->
      msg_c2d true pex_act aq tout tid_d = Some grant_msg.
  Proof.
    split.
    - intros (GR_LOC & IS_UPD).
      unfold msg_c2d.
      rewrite IS_UPD. s.
      rewrite GR_LOC.
      rewrite Nat.eqb_refl. ss.
    - s. unfold msg_c2d.
      rewrite andb_comm. s.
      destruct (is_updated pex_act) eqn: IS_UPD; ss.
      destruct (grant_msg_loc aq tout) eqn: GR_LOC; ss.
      destruct (Nat.eqb_spec n tid_d); ss.
      subst. ss.
  Qed.


  Lemma dev_wait_to_owner
        aq tout pex tid_d dmd dst m_d2c
        (DEV_WAIT_ZERO: dev_wait aq tout pex tid_d dmd
                                 m_d2c dst 0)
    : dev_owner aq tout pex tid_d dst dmd.
  Proof.
    inv DEV_WAIT_ZERO.
    econs; eauto.
    inv DEV_WAIT_CNT.
    - ss.
    - desf.
    - apply grant_msg_cond.
      split.
      + unfold grant_msg_loc.
        destruct aq; ss.
      + desf.
  Qed.

  (* Definition match_dev_owner (owner: nat?) (tid_d: nat) *)
  (*            (dst: DevState.t): Prop := *)
  (*   DevState.owner_status dst = Some true -> *)
  (*   owner = Some tid_d. *)

  Inductive match_state (* (actrl: t) *)
    : t -> @SyncSys.state obsE bytes -> Prop :=
    MatchState
      inb_c asd aq tout
      pex1 pex2
      tm nst_con nst_c1 nst_c2 nst_d1 nst_d2 nst_d3
      ast_con ast_c1 ast_c2 ast_d1 ast_d2 ast_d3
      inb_c1 inb_c2 inb_d1 inb_d2 inb_d3
      me_con me_c1 me_c2 me_d1 me_d2 me_d3
      (INBOX_EQ: inb_c = [me_con; me_c1; me_c2;
                         me_d1; me_d2; me_d3])
      (NST_CON: nst_con = SNode.State
                            tid_con snode_con
                            [None; None; None; None; None; None]
                            ast_con)

      (MATCH_C1: option_rel1
                   (match_ctrl_state
                      aq tout (is_active_side asd true) pex1)
                   ast_c1)
      (MATCH_C2: option_rel1
                   (match_ctrl_state
                      aq tout (is_active_side asd false) pex2)
                   ast_c2)
      (INB_C1_EQ: inb_c1 = drop_self_entry true inb_c)
      (INB_C2_EQ: inb_c2 = drop_self_entry false inb_c)

      (NST_C1: nst_c1 = SNode.State
                          tid_ctrl1 (ITrSNode.to_snode
                                       (ctrl_mod (Z.of_nat tid_ctrl1)))
                          inb_c1
                          (option_map (fun cst => Ret cst) ast_c1))
      (NST_C2: nst_c2 = SNode.State
                          tid_ctrl2 (ITrSNode.to_snode
                                       (ctrl_mod (Z.of_nat tid_ctrl2)))
                          inb_c2
                          (option_map (fun cst => Ret cst) ast_c2))

      (NST_D1: nst_d1 = SNode.State
                          tid_dev1 snode_dev inb_d1
                          (option_map (fun dst => Ret dst) ast_d1))
      (NST_D2: nst_d2 = SNode.State
                          tid_dev2 snode_dev inb_d2
                          (option_map (fun dst => Ret dst) ast_d2))
      (NST_D3: nst_d3 = SNode.State
                          tid_dev3 snode_dev inb_d3
                          (option_map (fun dst => Ret dst) ast_d3))

      (DEV1: option_rel1
               ((* DevState.wf \1/ *) match_dev_state
                  aq tout tid_dev1 me_d1) ast_d1)
      (DEV2: option_rel1
               ((* DevState.wf \1/ *) match_dev_state
                  aq tout tid_dev2 me_d2) ast_d2)
      (DEV3: option_rel1
               ((* DevState.wf \1/ *) match_dev_state
                  aq tout tid_dev3 me_d3) ast_d3)

      (INB_D1_EQ: inb_dev (pex1, pex2) asd
                          aq tout tid_dev1 = inb_d1)
      (INB_D2_EQ: inb_dev (pex1, pex2) asd
                          aq tout tid_dev2 = inb_d2)
      (INB_D3_EQ: inb_dev (pex1, pex2) asd
                          aq tout tid_dev3 = inb_d3)
    : match_state (mk inb_c (pex1, pex2) asd aq tout)
                  (SyncSys.State
                     tm [nst_con; nst_c1; nst_c2;
                        nst_d1; nst_d2; nst_d3]).

  Inductive pre: @SyncSys.state obsE bytes -> Prop :=
    InvPre
      tm
      nst_con nst_c1 nst_c2
      nst_d1 nst_d2 nst_d3

      (ast_con: unit?) ment_con
      ment_d1 ment_d2 ment_d3
      ast_c1 ast_c2 hb1 hb2
      ast_d1 ast_d2 ast_d3
      (NST_CON: nst_con = SNode.State
                            tid_con snode_con
                            [None; None; None;
                            None; None; None]
                            (option_map (fun x => Ret x) ast_con))
      (MENT_CON: option_rel1 (fun m => m = toggle_msg) ment_con)
      (NST_C1: nst_c1 = SNode.State
                          tid_ctrl1 snode_c1
                          [ment_con; None; hb2;
                          ment_d1; ment_d2; ment_d3]
                          (option_map (fun cst => Ret cst) ast_c1))
                          (* ast_c1_tr) *)
      (NST_C1: nst_c2 = SNode.State
                          tid_ctrl2 snode_c2
                          [ment_con; hb1; None;
                          ment_d1; ment_d2; ment_d3]
                          (option_map (fun cst => Ret cst) ast_c2))
      (AST_C1_INIT: option_rel1 (fun cst => cst = CtrlState.init) ast_c1)
      (AST_C2_INIT: option_rel1 (fun cst => cst = CtrlState.init) ast_c2)
      (HB_IMPL_FAIL1: hb1 <> None -> ast_c1 = None)
      (HB_IMPL_FAIL2: hb2 <> None -> ast_c2 = None)

      (HB_INIT1: option_rel1 (fun hb => exists md',
                                  CtrlState.of_bytes hb =
                                  CtrlState.set_mode
                                    md' CtrlState.init) hb1)
      (HB_INIT2: option_rel1 (fun hb => exists md',
                                  CtrlState.of_bytes hb =
                                  CtrlState.set_mode
                                    md' CtrlState.init) hb2)


      (MENT_D1_REL: option_rel1 (fun m => m = rel_msg) ment_d1)
      (MENT_D2_REL: option_rel1 (fun m => m = rel_msg) ment_d2)
      (MENT_D3_REL: option_rel1 (fun m => m = rel_msg) ment_d3)

      (NST_D1: nst_d1 = SNode.State
                          tid_dev1 snode_dev
                          [None; None; None;
                          None; None; None]
                          (option_map (fun dst => Ret dst) ast_d1))
      (NST_D2: nst_d2 = SNode.State
                          tid_dev2 snode_dev
                          [None; None; None;
                          None; None; None]
                          (option_map (fun dst => Ret dst) ast_d2))
      (NST_D3: nst_d3 = SNode.State
                          tid_dev3 snode_dev
                          [None; None; None;
                          None; None; None]
                          (option_map (fun dst => Ret dst) ast_d3))
      (AST_D1_INIT: option_rel1 (fun dst => dst = DevState.init) ast_d1)
      (AST_D2_INIT: option_rel1 (fun dst => dst = DevState.init) ast_d2)
      (AST_D3_INIT: option_rel1 (fun dst => dst = DevState.init) ast_d3)

    : pre (SyncSys.State
             tm [nst_con; nst_c1; nst_c2;
                nst_d1; nst_d2; nst_d3]).

End AbstCtrl.


Definition dev_event e: Prop :=
  (exists n, e = Event CheckDemand n) \/
  (e = Event UseResource tt).

Definition cevt (logv: Z): event obsE :=
  Event (inl1 (WriteLog logv)) tt.

Lemma copy_state_from_hb_spec
      bs md cst
      (CST_OF_BYTES: CtrlState.of_bytes bs = cst)
  : CtrlState.copy_state_from_hb md bs =
    CtrlState.set_mode md cst.
Proof.
  unfold CtrlState.copy_state_from_hb in *.
  rewrite CST_OF_BYTES. ss.
Qed.


Definition opt_eqb {A} (f: A -> A -> bool)
           (a b: A?): bool :=
  match a, b with
  | Some x, Some y => f x y
  | _, _ => false
  end.

Arguments nth_error: simpl nomatch.


Import AbstCtrl.

Lemma byte_one_equiv b
  : Byte.eq b Byte.one = (Byte.signed b =? 1)%Z.
Proof.
  rewrite Byte.eq_signed.
  replace (Byte.signed Byte.one) with 1%Z by ss.
  destruct (Z.eqb_spec (Byte.signed b) 1) as [EQ | NEQ]; ss.
  - rewrite EQ. ss.
  - destruct (Coqlib.zeq (Byte.signed b) 1); ss.
Qed.



Lemma NoDup_app A
      (l1 l2: list A)
      (NODUP1: NoDup l1)
      (NODUP2: NoDup l2)
      (DISJOINT: Coqlib.list_disjoint l1 l2)
  : NoDup (l1 ++ l2).
Proof.
  induction l1 as [| h t IH]; ss.
  econs.
  { intro IN.
    apply in_app_or in IN. des.
    - inv NODUP1. ss.
    - r in DISJOINT.
      hexploit (DISJOINT h); eauto.
      ss. eauto.
  }
  apply IH.
  { inv NODUP1. ss. }
  r in DISJOINT. r.

  intros x y INX INY.
  hexploit DISJOINT; eauto. ss. eauto.
Qed.



Lemma NoDup_app_inv A
      (l1 l2: list A)
      (NODUP: NoDup (l1 ++ l2))
  : <<NODUP1: NoDup l1>> /\
    <<NODUP2: NoDup l2>> /\
    <<DISJOINT: Coqlib.list_disjoint l1 l2>>.
Proof.
  induction l1 as [| h1 t1 IH]; ss.
  { splits; ss. econs. }

  inv NODUP.
  match goal with
  | H1: ~ In _ _, H2: NoDup _ |- _ =>
    renames H1 H2 into NOT_IN NODUP_APP
  end.
  hexploit IH; eauto. i. des.
  esplits; eauto.
  - econs; eauto.
    intro IN.
    apply NOT_IN. apply in_or_app. eauto.
  - r. intros x y IN1 IN2.
    ss. des.
    + subst x.
      intro Y_EQ. subst y.
      apply NOT_IN. apply in_or_app. eauto.
    + apply DISJOINT; eauto.
Qed.


Lemma wf_aq_len_bound
      q
      (WF_Q: abst_queue_wf q)
  : length q <= 3 /\
    (3 <= length q -> forall tid, is_dev_tid tid -> In tid q).
Proof.
  r in WF_Q. des.

  destruct q as [| q1 [| q2 [| q3 q']]];
    try by ss; nia.

  assert (DEV_TIDS: is_dev_tid q1 /\ is_dev_tid q2 /\
                    is_dev_tid q3 /\ Forall is_dev_tid q').
  { do 3 match goal with
         | H: Forall _ _ |- _ => inv H; split; ss
         end.
  }

  destruct DEV_TIDS as (DEV1 & DEV2 & DEV3 & DEV_TIDS).
  clear EACH_DEV_TID.

  destruct q' as [| q4 q'].
  { clear DEV_TIDS.
    split; ss.
    intros _ tid DEV_TID.
    r in DEV_TID. ss.

    des; subst; ss.
    - unfold is_dev_tid in *. ss.
      (desH DEV1; subst; eauto);
        (desH DEV2; subst; eauto);
        (desH DEV3; subst; eauto);
        eapply (nodup_fixed_point Nat.eq_dec) in ELEMS_NODUP; ss.
    - unfold is_dev_tid in *. ss.
      (desH DEV1; subst; eauto);
        (desH DEV2; subst; eauto);
        (desH DEV3; subst; eauto);
        eapply (nodup_fixed_point Nat.eq_dec) in ELEMS_NODUP; ss.
    - unfold is_dev_tid in *. ss.
      (desH DEV1; subst; eauto);
        (desH DEV2; subst; eauto);
        (desH DEV3; subst; eauto);
        eapply (nodup_fixed_point Nat.eq_dec) in ELEMS_NODUP; ss.
  }

  exfalso.

  assert (DEV4: is_dev_tid q4).
  { inv DEV_TIDS. ss. }
  clear DEV_TIDS.
  replace (q1 :: q2 :: q3 :: q4 :: q') with
      ([q1; q2; q3; q4] ++ q') in * by ss.

  apply NoDup_app_inv in ELEMS_NODUP. des.
  clear dependent q'.

  unfold is_dev_tid in *. ss.
  des; ss; subst;
    (eapply (nodup_fixed_point Nat.eq_dec) in NODUP1; ss).
Qed.



Lemma qrange_sanitize_id x
      (RANGE_OK: (0 <= x < QSIZE)%Z)
  :qrange_sanitize x = x.
Proof.
  unfold qrange_sanitize.
  destruct (Z.leb_spec 0 x).
  2: { nia. }
  destruct (Z.ltb_spec x QSIZE).
  2: { nia. }
  ss.
Qed.



Lemma adv_qidx_n_neq
      n x
      (RANGE_X: (0 <= x < QSIZE)%Z)
      (N_RANGE: 0 < n < 4)
  : adv_qidx_n n x <> x.
Proof.
  destruct n as [| n].
  { nia. }
  destruct n as [| n].
  { ss.
    unfold adv_qidx.
    unfold qrange_sanitize.
    destruct (Z.leb_spec 0 (x + 1)); ss.
    2: { nia. }
    destruct (Z.ltb_spec (x + 1) QSIZE); ss.
    { nia. }
    unfold QSIZE in *. nia.
  }
  destruct n as [| n].
  { ss.
    unfold adv_qidx.
    unfold qrange_sanitize.
    destruct (Z.leb_spec 0 (x + 1)); ss.
    2: { nia. }
    destruct (Z.ltb_spec (x + 1) QSIZE); ss.
    2: { unfold QSIZE in *. nia. }

    destruct (Z.leb_spec 0 (x + 1 + 1)); ss.
    2: { nia. }
    destruct (Z.ltb_spec (x + 1 + 1) QSIZE); ss.
    2: { unfold QSIZE in *. nia. }
    unfold QSIZE in *. nia.
  }
  destruct n as [| n].
  { ss.
    unfold adv_qidx.
    unfold qrange_sanitize.
    destruct (Z.leb_spec 0 (x + 1)); ss.
    2: { nia. }
    destruct (Z.ltb_spec (x + 1) QSIZE); ss.
    2: { unfold QSIZE in *. nia. }

    destruct (Z.leb_spec 0 (x + 1 + 1)); ss.
    2: { nia. }
    destruct (Z.ltb_spec (x + 1 + 1) QSIZE); ss.
    2: { unfold QSIZE in *. nia. }

    destruct (Z.leb_spec 0 (x + 1 + 1 + 1)); ss.
    2: { nia. }
    destruct (Z.ltb_spec (x + 1 + 1 + 1) QSIZE); ss.
    2: { unfold QSIZE in *. nia. }
    unfold QSIZE in *. nia.
  }
  nia.
Qed.

Lemma adv_qidx_n_1_comm
      qb
  : forall n : nat, adv_qidx_n n (adv_qidx qb) =
             adv_qidx (adv_qidx_n n qb).
Proof.
  induction n; ss.
  rewrite IHn; ss.
Qed.

Lemma match_queue_adv_qb_qe
      aq qb qe q
      (MATCH_Q: match_queue aq (qb, qe, q))
  : adv_qidx_n (length aq) qb = qe.
Proof.
  depgen qb.
  induction aq as [| hd tl IH]; i; ss.
  { inv MATCH_Q. ss. }
  inv MATCH_Q.
  rewrite <- adv_qidx_n_1_comm.
  eauto.
Qed.


Lemma match_try_add_queue
      cst md tout_z qb qe q
      tid_d tid_d_z
      (RANGE_QB: (0 <= qb < QSIZE)%Z)
      (CST: cst = CtrlState.mk md tout_z qb qe q)
  : forall n aq csr tids_q_prev
      (ADV_N: adv_qidx_n (3 - n) qb = csr)
      (N_LBND: length tids_q_prev + n = 3)
      (* length aq <= n) *)
      (* (length tids_q_prev + n = 3) *)
      (NOT_IN_PREV: ~ In tid_d tids_q_prev)
      (* (nodup (tids_q_prev ++ aq)) *)
      (* (Forall is_dev_tid (tids_q_prev ++ aq)) *)
      (WF_AQ: abst_queue_wf (tids_q_prev ++ aq))
      (MATCH: match_queue aq (csr, qe, q))
      (DEV_TID: is_dev_tid tid_d)
      (TID_Z: tid_d_z = Z.of_nat tid_d)
      ,
    exists aq' qe' q',
      <<AQ': aq' = if (existsb (Nat.eqb tid_d) aq) then aq
                   else snoc aq tid_d>> /\
      <<TRY_ADD: try_add_queue_loop cst tid_d_z n csr =
                 CtrlState.mk md tout_z qb qe' q'>> /\
      <<MATCH_Q': match_queue aq' (csr, qe', q')>> /\
      <<WF_Q': abst_queue_wf aq'>> /\
      <<UNCHANGED_UNLESS_QE:
        forall (n: nat)
          (N_NOT_QE: Z.of_nat n <> qe),
          nth_error q' n = nth_error q n>>.
Proof.
  intro n.
  induction n as [| n' IH]; i; ss.
  { exfalso.
    hexploit wf_aq_len_bound; eauto.
    intros [LEN_APP HAVE_ALL].

    destruct aq; ss.
    2: { rewrite app_length in LEN_APP. ss. nia. }
    rewrite app_nil_r in *.

    hexploit HAVE_ALL; eauto. nia.
  }
  guardH ADV_N.

  inv MATCH; ss.
  { rewrite Z.eqb_refl.
    unfold snoc. s.
    esplits; eauto.
    econs; eauto.
    - rewrite Zlength_correct.
      unfold set_queue.
      rewrite replace_nth_length.
      rewrite <- Zlength_correct. ss.

    - (* clear - VALID_CURSOR RANGE_QB. *)
      clear.
      unfold adv_qidx.
      unfold qrange_sanitize.
      desf.
      + clear. nia.
      + destruct (Z.leb_spec 0 (qe + 1)); ss.
        2: { nia. }
        destruct (Z.ltb_spec (qe + 1) QSIZE); ss.
        unfold QSIZE in *. nia.

    - unfold set_queue.
      rewrite replace_nth_gss; eauto.
      cut (qe < Zlength q)%Z.
      { rewrite Zlength_correct. nia. }
      nia.

    - econs; ss.
      + rewrite Zlength_correct.
        unfold set_queue.
        rewrite replace_nth_length.
        rewrite <- Zlength_correct. ss.
      + apply range_adv_qidx_prec.
    - r. esplits.
      + econs; ss. econs.
      + econs; ss.
    - i.
      unfold set_queue.
      rewrite replace_nth_gso; eauto.
      nia.
  }
  (* inductive case *)

  destruct (Z.eqb_spec csr qe).
  { exfalso. congruence. }
  match goal with
  | H: abst_queue_wf (_ ++ ?h :: ?t) |- _ =>
    renames h t into h tl
  end.

  unfold get_queue.
  erewrite nth_error_nth; eauto.
  rewrite Nat2Z_inj_eqb.

  destruct (Nat.eqb_spec h tid_d).
  { subst h.
    ss. rewrite Nat.eqb_refl. s.
    esplits; eauto.
    - econs; eauto.
    - clear - WF_AQ.
      r in WF_AQ. des.
      r. splits.
      + apply NoDup_app_inv in ELEMS_NODUP. des. ss.
      + apply Forall_app_inv in EACH_DEV_TID. des. ss.
  }

  destruct (Nat.eqb_spec tid_d h).
  { exfalso. congruence. }

  s.
  hexploit (IH tl (adv_qidx csr)
               (snoc tids_q_prev h)); eauto.
  { rewrite <- ADV_N.
    replace (3 - n') with (S (2 - n')) by nia.
    ss. }
  { rewrite snoc_length. nia. }
  { unfold snoc.
    intro IN. eapply in_app_or in IN.
    destruct IN; ss.
    ss. des; ss. }
  { unfold snoc. rewrite <- app_assoc. ss. }
  i. des.

  esplits; eauto.
  match goal with
  | |- context [match_queue ?q _] =>
    replace q with (h :: aq') by desf
  end.

  econs; eauto.
  - inv MATCH_Q'; ss.
  - (* by using (aq' not having h) => length < 3 *)
    intro CSR_EQ.

    assert (adv_qidx_n (length aq') (adv_qidx csr) = qe').
    { (* from MATCH_Q' *)

      eapply match_queue_adv_qb_qe; eauto.
    }
    assert (ADV': adv_qidx_n (S (length aq')) csr = qe').
    { s. rewrite <- adv_qidx_n_1_comm. ss. }

    assert (S_LEN_LE: S (length aq') <= 3).
    { cut (length aq' < 3).
      { clear. nia. }
      hexploit (wf_aq_len_bound aq'); eauto.
      intros [LEN1 IF_HAVE_ALL].
      destruct (lt_ge_dec (length aq') 3); ss.
      exfalso.
      hexploit (IF_HAVE_ALL).
      { eauto. }
      { instantiate (1:= h).
        clear - WF_AQ.
        r in WF_AQ. des.
        rewrite Forall_forall in EACH_DEV_TID.
        apply EACH_DEV_TID; eauto.
        apply in_or_app. right. ss. eauto.
      }
      assert (~ In h tl).
      { clear - WF_AQ.
        intro H_IN_TL.
        r in WF_AQ. des.
        apply NoDup_app_inv in ELEMS_NODUP. des.
        inv NODUP2. eauto.
      }
      destruct (existsb (Nat.eqb tid_d) tl).
      - subst aq'. ss.
      - subst aq'.
        unfold snoc.
        intro IN.
        apply in_app_or in IN.
        destruct IN; ss.
        des; eauto.
    }

    subst csr.
    hexploit adv_qidx_n_neq; eauto. nia.

  - rewrite UNCHANGED_UNLESS_QE; eauto.
    rewrite Z2Nat.id; ss.
  - destruct (existsb (Nat.eqb tid_d) tl) eqn: D_IN_TL.
    + clear - WF_AQ.
      r in WF_AQ. des.
      r. splits.
      * apply NoDup_app_inv in ELEMS_NODUP. des. ss.
      * apply Forall_app_inv in EACH_DEV_TID. des. ss.
    + eapply existsb_false_iff in D_IN_TL.
      move WF_AQ at bottom.
      r in WF_AQ. des.
      apply NoDup_app_inv in ELEMS_NODUP. des.

      unfold snoc.
      r. esplits.
      * apply NoDup_app; eauto.
        { econs; ss. econs. }
        intros x y XIN YIN. ss.
        des; subst; ss.
        ii. subst.
        rewrite Forall_forall in D_IN_TL.
        hexploit D_IN_TL; eauto.
        rewrite Nat.eqb_refl. ss.
      * apply Forall_app.
        { apply Forall_app_inv in EACH_DEV_TID.
          des; ss. }
        { econs; ss. }
Qed.


Lemma match_try_release
      cst md tout tout_z qb qe q
      tid_d tid_d_z
      aq
      (CST: cst = CtrlState.mk md tout_z qb qe q)
      (EMPTY_QUEUE_TOUT_ZERO: length aq = 0 -> tout = 0)
      (TIMEOUT_Z: tout_z = Z.of_nat tout)
      (WF_TOUT: tout <= MAX_TIMEOUT)
      (WF_AQ: abst_queue_wf aq)
      (MATCH: match_queue aq (qb, qe, q))
      (DEV_TID: is_dev_tid tid_d)
      (TID_Z: tid_d_z = Z.of_nat tid_d)
: exists tout',
  <<WF_TOUT': tout' <= MAX_TIMEOUT>> /\
  <<AQ_REM: aq_remove tid_d (aq, tout) = (aq, tout') >> /\
  <<TRY_ADD: try_release cst tid_d_z =
             CtrlState.mk md (Z.of_nat tout') qb qe q>> /\
  <<EMPTY_QUEUE_TOUT_ZERO': length aq = 0 -> tout' = 0>>
.
Proof.
  unfold aq_remove.
  unfold try_release.
  subst cst. ss.
  inv MATCH.
  { exists tout. ss.
    esplits; eauto.
    hexploit EMPTY_QUEUE_TOUT_ZERO; eauto.
    i. subst.
    ss.
    rewrite Z.eqb_refl. ss.
  }

  renames h t0 into hd tl.
  apply Z.eqb_neq in CURSOR_NOT_END.
  rewrite CURSOR_NOT_END. s.

  (* exists (if hd =? tid_d then 1 else tout). *)
  exists (if (hd =? tid_d) && (0 <? tout) && (tout <? MAX_TIMEOUT)
     then 1 else tout).
  esplits; ss.
  - desf. unfold MAX_TIMEOUT. nia.
  - rewrite qrange_sanitize_id by ss.
    unfold get_queue.
    erewrite nth_error_nth by eauto.
    rewrite Nat2Z_inj_eqb.

    replace (0 <? Z.of_nat tout)%Z with
        (0 <? tout).
    2: { rewrite Nat2Z_inj_ltb. ss. }
    replace (Z.of_nat tout <? SpecController.MAX_TIMEOUT)%Z
      with (tout <? MAX_TIMEOUT).
    2: { replace SpecController.MAX_TIMEOUT with
             (Z.of_nat MAX_TIMEOUT) by ss.
         rewrite Nat2Z_inj_ltb. ss. }
    rewrite andb_assoc.
    desf.
Qed.

Lemma match_proc_dev_msg
      aq tout
      tid_d me_d cst tid_d_z
      md tout_z qb qe q
      (WF_TIMEOUT: tout <= MAX_TIMEOUT)
      (WF_Q: abst_queue_wf aq)
      (EMPTY_QUEUE_TOUT_ZERO: length aq = 0 -> tout = 0)
      (MATCH_Q: match_queue aq (qb, qe, q))
      (* (APP_DEV:  = cst1) *)
      (CST: cst = CtrlState.mk md tout_z qb qe q)
      (MATCH_TIMEOUT: tout_z = Z.of_nat tout)
      (DEV_TID: is_dev_tid tid_d)
      (MATCH_TID: tid_d_z = Z.of_nat tid_d)
  : exists aq1 tout1
      qb1 qe1 q1,
    <<WF_TIMEOUT1: tout1 <= MAX_TIMEOUT>> /\
    <<PROC1: aq_process_dev_msg (aq, tout) (tid_d, me_d) =
              (aq1, tout1)>> /\
    <<CST1: apply_devmsg cst tid_d_z me_d =
            CtrlState.mk md (Z.of_nat tout1) qb1 qe1 q1>> /\
    <<MATCH_Q1: match_queue aq1 (qb1, qe1, q1)>> /\
    <<WF_Q1: abst_queue_wf aq1>> /\
    <<EMPTY_QUEUE_TOUT_ZERO': length aq1 = 0 -> tout1 = 0>>.
Proof.
  unfold aq_process_dev_msg.
  destruct me_d; ss.
  2: {
    esplits; eauto.
    congruence.
  }

  rewrite byte_one_equiv.
  remember (Byte.signed (nth 0 b Byte.zero) =? 1)%Z as
      is_acq eqn: TMP.
  clear TMP.

  destruct is_acq.
  - (* acq *)
    unfold try_add_queue.

    hexploit match_try_add_queue; eauto.
    { inv MATCH_Q; ss. }
    { cut (length (@nil nat) + 3 = 3).
      { intro R. apply R. }
      ss.
    }
    { ss. }
    { ss. eauto. }
    { ss. }

    i. des.
    rewrite <- AQ'.
    replace (qrange_sanitize (CtrlState.queue_begin cst))
      with qb.
    2: {
      subst cst. ss.
      unfold qrange_sanitize.
      clear - MATCH_Q.
      inv MATCH_Q.
      { destruct (Z.leb_spec 0 qe); ss.
        2: { nia. }
        destruct (Z.ltb_spec qe QSIZE); ss.
        nia. }
      { destruct (Z.leb_spec 0 qb); ss.
        2: { nia. }
        destruct (Z.ltb_spec qb QSIZE); ss.
        nia. }
    }
    rewrite Nat.sub_diag in TRY_ADD.
    replace (adv_qidx_n 0 qb) with qb in * by ss.
    rewrite TRY_ADD.
    esplits; eauto.
    + rewrite MATCH_TIMEOUT. ss.
    + clear - AQ' EMPTY_QUEUE_TOUT_ZERO.
      i. desf.
      * eauto.
      * rewrite snoc_length in *. nia.

  - (* rel *)
    hexploit (match_try_release cst); eauto. i. des.
    ss.
    rewrite AQ_REM.
    rewrite TRY_ADD.
    exists aq, tout'.
    esplits; eauto.
Qed.


Lemma match_reduce_timeout
      aq tout
      cst md tout_z qb qe q
      (MATCH_Q: match_queue aq (qb, qe, q))
      (MATCH_TIMEOUT: tout_z = Z.of_nat tout)
      (CST: cst = CtrlState.mk md tout_z qb qe q)
      (WF_TIMEOUT: tout <= MAX_TIMEOUT)
      (WF_Q: abst_queue_wf aq)
      (EMPTY_QUEUE_TOUT_ZERO': length aq = 0 -> tout = 0)
  : exists aq' tout' qb' qe' q',
    <<AQ_REDUCE_TOUT:
      match tout with
      | 0 => (aq, 0)
      | 1 => (tl aq, 0)
      | S tout' => (aq, tout')
      end = (aq', tout')>> /\
    <<REDUCE_TOUT:
        reduce_timeout cst =
        CtrlState.mk md (Z.of_nat tout') qb' qe' q'>> /\
    <<MATCH_Q': match_queue aq' (qb', qe', q')>> /\
    <<WF_Q': abst_queue_wf aq'>> /\
    <<EMPTY_QUEUE_TOUT_ZERO': length aq' = 0 -> tout' = 0>>
.
Proof.
  unfold reduce_timeout.
  destruct tout as [| tout'].
  { (* tout = 0 *)
    replace (Z.of_nat 0) with 0%Z in MATCH_TIMEOUT by ss.
    subst tout_z cst.
    esplits; eauto.
    destruct (Z.eqb_spec 0 1); ss.
  }
  destruct tout' as [| tout''].
  { replace (Z.of_nat 1) with 1%Z in MATCH_TIMEOUT by ss.
    subst tout_z cst.
    rewrite Z.eqb_refl.

    inv MATCH_Q.
    { exfalso.
      hexploit EMPTY_QUEUE_TOUT_ZERO'; eauto. ss. }
    renames h t0 into hd tl.

    s. esplits; eauto.
    r in WF_Q. des.
    econs.
    - inv ELEMS_NODUP. ss.
    - inv EACH_DEV_TID. ss.
  }

  subst cst.
  destruct (Z.eqb_spec tout_z 1).
  { exfalso. nia. }
  destruct (Z.ltb_spec 1 tout_z).
  2: { exfalso. nia. }

  esplits; eauto.
  { f_equal.
    nia. }
  i. hexploit EMPTY_QUEUE_TOUT_ZERO'; eauto.
  i. ss.
Qed.


Lemma CtrlState_to_bytes_length
      st
      (WF: CtrlState.wf st)
  : length (CtrlState.to_bytes st) = 8.
Proof.
  inv WF. ss.
  rewrite map_length. nia.
Qed.

Lemma CtrlState_to_bytes_inv
      st
      (WF: CtrlState.wf st)
  : CtrlState.of_bytes (CtrlState.to_bytes st) = st.
Proof.
  inv WF. ss.
  unfold CtrlState.of_bytes. ss.
  rewrite Byte.signed_repr.
  2: { destruct md; ss. }
  rewrite Byte.signed_repr by range_stac.
  rewrite Byte.signed_repr by range_stac.
  rewrite Byte.signed_repr by range_stac.
  rewrite Forall_forall in RANGE_QUEUE.

  repeat (destruct q as [|? q]; ss).
  rewrite Byte.signed_repr.
  2: { eapply RANGE_QUEUE; eauto. }
  rewrite Byte.signed_repr.
  2: { eapply RANGE_QUEUE; eauto. }
  rewrite Byte.signed_repr.
  2: { eapply RANGE_QUEUE; eauto. }
  rewrite Byte.signed_repr.
  2: { eapply RANGE_QUEUE; eauto. }
  destruct md; ss.
Qed.


Lemma SNode_insert_get_outbox {msgT: Set}
      nt
      tid tids m (outb outb1: list msgT?)
      (LEN_OUTB: length outb = nt)
      (INSERT: outb1 = SNode.insert_msg tids m outb)
      (VALID_TIDS: Forall (fun tid => tid < nt) tids)
  : SNode.get_outbox_msg_by_dest tid outb1 =
    if existsb (Nat.eqb tid) tids then Some m
    else SNode.get_outbox_msg_by_dest tid outb.
Proof.
  unfold SNode.get_outbox_msg_by_dest.
  destruct (nth_error outb1 tid) as [m_tid| ] eqn: OUTB1_TID.
  2: {
    eapply nth_error_None in OUTB1_TID.
    unfold SNode.insert_msg in INSERT.

    assert (length outb = length outb1).
    { subst outb1. rewrite imap_length. ss. }

    assert (EXISTSB_F: existsb (Nat.eqb tid) tids = false).
    { eapply existsb_false_iff.
      eapply Forall_impl.
      2: { eapply VALID_TIDS. }
      s. intros a LT.
      destruct (Nat.eqb_spec tid a); ss.
      subst.
      rewrite imap_length in *. nia.
    }
    rewrite EXISTSB_F.
    rewrite nth_error_None2; ss. nia.
  }

  unfold SNode.insert_msg, SNode.insert_msg1 in *.
  subst outb1.
  apply imap_nth_error_inv in OUTB1_TID. des. ss.
  unfold SNode.is_in_tids in *.
  desf.
Qed.

Local Opaque CtrlState.to_bytes CtrlState.of_bytes.
Local Opaque Z.of_nat.
Local Opaque Nat.min.


Section DEV_1STEP.
  Variable sys: @SyncSys.t obsE bytes.
  Variable tm_init: nat.
  Hypothesis PERIOD_POS: SyncSys.period sys <> 0.
  Let dsys: DSys.t := SyncSys.as_dsys sys tm_init.
  Let period: nat := SyncSys.period sys.

  Let sntz := fun bs => Some (resize_bytes 8 bs).
  Let mcasts := [[tid_ctrl1; tid_ctrl2]].
  Hypothesis SNTZ_EQ: sntz = (SyncSys.sanitize_msg sys).
  Hypothesis MCASTS_EQ: mcasts = (SyncSys.mcasts sys).

  Lemma dev_1step_inv_prsv
        inb_c pex1 pex2 asd aq tout
        me_con me_c1 me_c2 me_d1 me_d2 me_d3
        tid_d inb_d me_d ast
        t st es out st'
        asd' aq' tout' owner_new
        (WF: wf (mk inb_c (pex1, pex2) asd aq tout))
        (INBOX_EQ: inb_c = [me_con; me_c1; me_c2;
                           me_d1; me_d2; me_d3])
        (SYNC_TIME: Nat.divide period t)
        (ST_EQ: st = SNode.State
                       tid_d (ITrSNode.to_snode dev_mod)
                       inb_d
                       (option_map (fun dst => Ret dst) ast))
        (INB_D: inb_dev (pex1, pex2) asd
                        aq tout tid_d = inb_d)

        (DEV_CASES: (tid_d = tid_dev1 /\ me_d = me_d1) \/
                    (tid_d = tid_dev2 /\ me_d = me_d2) \/
                    (tid_d = tid_dev3 /\ me_d = me_d3))
        (MATCH: option_rel1
                  (match_dev_state
                     aq tout tid_d me_d) ast)
        (WF_DEV: option_rel1 DevState.wf ast)
        (STEP: SNode.step sntz num_tasks mcasts
                          t st es out st')
        (NEXT_ABST_CTRL: next pex1 pex2 inb_c asd aq tout =
                         (asd', aq', tout', owner_new))
    : exists (ast': DevState.t?) (me_d': bytes?),
      <<WF_DEV': option_rel1 DevState.wf ast'>> /\
      <<ST_EQ': st' = SNode.State
                        tid_d (ITrSNode.to_snode dev_mod)
                        [None; None; None; None; None; None]
                        (option_map (fun dst => Ret dst) ast')
                        >> /\
      <<OUTB_EQ:
        forall tid',
          SNode.get_outbox_msg_by_dest tid' out =
          if orb (tid' =? 1) (tid' =? 2)
          then me_d' else None>> /\
      <<ONLY_OWNER_USE_RES:
            In (embed (Event (inl1 UseResource) tt)) es ->
            exists dst dmd,
              (0 < dmd) /\ (ast = Some dst) /\
              (dev_owner aq tout
                         (if asd then pex1 else pex2)
                         tid_d dst dmd)>> /\
      ((* device_fail *)
        <<DEVICE_FAIL: ~ exists v, In (embed (cevt v)) es>> \/
       (* compl *)
        <<MATCH_DEV': option_rel1 (match_dev_state
                                      aq' tout' tid_d me_d')
                                   ast'>> /\
        <<DEV_INVS_PRSV:
          forall dst dst' pex1' pex2'
            (DEV_ST: ast = Some dst)
            (DEV_ST': ast' = Some dst')
            (COMPL: pex1 = Compl /\ pex1' = Compl \/
                    pex2 = Compl /\ pex2' = Compl)
          ,
            <<BEGIN_WAITING:
              forall dmd_i
                (DMD_POS: (0 < Int.signed dmd_i)%Z)
                (DMD_IN_ES: In (embed (Event CheckDemand
                                             dmd_i)) es)
              ,
              exists dmd_n dmd,
                <<DMD_N: Z_to_nat2 (Int.signed dmd_i) = Some dmd_n>> /\
                <<DMD_EQ: dmd = Nat.min MAX_TIMEOUT dmd_n>> /\
                <<DEV_WAIT:
                  dev_wait aq' tout'
                           (if asd' then pex1' else pex2')
                           tid_d dmd (Some acq_msg) dst'
                           (2 + (MAX_TIMEOUT + 1) * 2)>> >> /\
            <<DEV_WAIT_PRSV:
              forall dmd wcnt
                (DEV_WAIT: dev_wait
                             aq tout
                             (if asd then pex1 else pex2)
                             tid_d dmd me_d dst (S wcnt)),
                dev_wait aq' tout'
                         (if asd' then pex1' else pex2')
                         tid_d dmd me_d' dst' wcnt>> /\
            <<DEV_OWNER_PRSV:
              forall dmd
                (DEV_OWNER: dev_owner aq tout
                                      (if asd then pex1 else pex2)
                                      tid_d
                                      dst (S (S dmd))),
                dev_owner aq' tout'
                          (if asd' then pex1' else pex2')
                          tid_d
                          dst' (S dmd)>>
                          >>).
  Proof.
    guardH DEV_CASES.
    subst.

    destruct ast as [dst |]; ss.
    2: {
      inv STEP; ss.
      - exists None, None.
        splits; ss.
        { intro tid'.
          rewrite if_both_eq.
          destruct tid'; ss. }
        left. ii. des. ss.
      - inv INIT_APP_STATE.
        exists (Some (AppMod.init_abst_state dev_mod)), None.
        splits; ss.
        { econs. nia. }
        { intro tid'.
          rewrite if_both_eq.
          destruct tid'; ss. }
        left.
        ii. des. ss.
    }

    inv STEP.
    existT_elim. ss. clarify.
    inv RUN_PERIOD.
    { exists None, None.
      splits; ss.
      { intro tid'.
        rewrite if_both_eq.
        destruct tid'; ss. }
      left. ii. des. ss.
    }

    inv PERIOD_BEGIN. ss. clarify.

    inv MATCH; ss.
    - (* uninit *)
      unfold dev_job, job_device_itree in STAR. ss.
      simpl_itree_hyp STAR.

      inv STAR.
      { exists None, None.
        splits; ss.
        { intro tid'.
          rewrite if_both_eq.
          repeat (destruct tid'; ss). }
        left. ii. des. ss. }
      { exfalso. ss. }

      inv ASTEP.
      { inv TAU_STEP. ss. }
      { inv AT_EVENT. existT_elim. ss. clarify. }
      inv AT_EVENT.
      existT_elim. ss. clarify.
      existT_elim. ss. clarify.
      inv AFT_EVENT.
      existT_elim. ss. clarify.
      existT_elim. ss. clarify.

      rename ASTAR' into STAR.
      simpl_itree_hyp STAR.
      inv STAR.
      { exists None, (Some rel_msg).
        splits; ss.
        { intro tid'.
          repeat (destruct tid'; ss). }
        left. ii. des. ss. }
      { exfalso. ss. }

      inv ASTEP; cycle 2.
      { inv AT_EVENT. existT_elim. ss. clarify. }
      { inv TAU_STEP. ss. }
      inv AT_EVENT.
      existT_elim. ss. clarify.
      existT_elim. ss. clarify.
      inv AFT_EVENT.
      existT_elim. ss. clarify.
      existT_elim. ss. clarify.
      destruct r.

      rename ASTAR' into STAR.
      inv STAR; cycle 2.
      { inv ASTEP; ss.
        - inv TAU_STEP. ss.
        - inv AT_EVENT; ss.
        - inv AT_EVENT; ss.
      }
      { (* compl & failed *)
        exists None, (Some rel_msg).
        splits; ss.
        { intro tid'.
          repeat (destruct tid'; ss). }
        { intro C. clear - C.
          exfalso.
          des; ss. }
        right.
        splits; ss.
      }
      { (* compl & success *)
        exists (Some (DevState.mk (Some false) 0)), (Some rel_msg).
        splits; ss.
        { econs. nia. }
        { intro tid'.
          repeat (destruct tid'; ss). }
        { intro C. clear - C.
          exfalso.
          des; ss. }
        right.
        splits; ss.
        { econs 2.
          left. eauto. }

        i. clarify.
        splits.
        - i. des; ss.
        - i. inv DEV_WAIT. ss.
        - i. inv DEV_OWNER.
      }

    - (* not owner, no demand *)
      (* guardH NO_DMD_CASES. *)
      (* unfold dev_job, job_device_itree in STAR. ss. *)
      (* unfold update_demand in STAR. ss. *)
      (* simpl_itree_hyp STAR. *)
      (* unfold get_new_demand in STAR. ss. *)
      (* simpl_itree_hyp STAR. *)
      (* simpl_itree_hyp STAR. *)

      (* inv STAR. *)
      (* { exists None, None. *)
      (*   splits; ss. *)
      (*   { intro tid'. *)
      (*     rewrite if_both_eq. *)
      (*     repeat (destruct tid'; ss). } *)
      (*   left. ss. *)
      (* } *)
      (* { exfalso. ss. } *)

      (* inv ASTEP; cycle 2. *)
      (* { inv AT_EVENT. existT_elim. subst. ss. } *)
      (* { inv TAU_STEP. ss. } *)
      (* inv AT_EVENT. *)
      (* existT_elim. ss. clarify. *)
      (* existT_elim. ss. clarify. *)
      (* inv AFT_EVENT. *)
      (* existT_elim. ss. clarify. *)
      (* existT_elim. ss. clarify. *)

      (* rename ASTAR' into STAR. *)
      (* simpl_itree_hyp STAR. *)
      (* simpl_itree_hyp STAR. *)

      (* rename r into dmd_r. *)

      (* assert (DMD_EQ: exists dmd, dmd = Nat.min MAX_TIMEOUT dmd_r). *)
      (* { esplits; eauto. } *)
      (* des. *)
      (* replace (if MAX_TIMEOUT <? dmd_r then MAX_TIMEOUT else dmd_r) *)
      (*   with dmd in *. *)
      (* 2: { subst dmd. *)
      (*      clear. *)
      (*      destruct (Nat.ltb_spec MAX_TIMEOUT dmd_r); nia. } *)

      (* assert (RANGE_DMD: dmd <= MAX_TIMEOUT). *)
      (* { subst dmd. *)
      (*   clear. nia. } *)
      (* guardH DMD_EQ. *)

      (* destruct (Nat.ltb_spec 0 dmd). *)
      (* + (* 0 < dmd *) *)
      (*   simpl_itree_hyp STAR. *)
      (*   inv STAR. *)
      (*   { exists None, None. *)
      (*     splits; ss. *)
      (*     { intro tid'. *)
      (*       rewrite if_both_eq. *)
      (*       repeat (destruct tid'; ss). } *)
      (*     { i. exfalso. *)
      (*       des; ss. } *)
      (*     left. *)
      (*     clear. *)
      (*     ii. des; ss. *)
      (*   } *)
      (*   { exfalso. ss. } *)

      (*   inv ASTEP. *)
      (*   { inv TAU_STEP. ss. } *)
      (*   { inv AT_EVENT. existT_elim. subst. ss. } *)
      (*   inv AT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)
      (*   inv AFT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)

      (*   rename ASTAR' into STAR. *)
      (*   simpl_itree_hyp STAR. *)

      (*   inv STAR. *)
      (*   { exists None, (Some acq_msg). *)
      (*     splits; ss. *)
      (*     { intro tid'. *)
      (*       repeat (destruct tid'; ss). } *)
      (*     { i. exfalso. *)
      (*       des; ss. } *)
      (*     left. *)
      (*     clear. *)
      (*     ii. des; ss. *)
      (*   } *)
      (*   { exfalso. ss. } *)

      (*   inv ASTEP; cycle 2. *)
      (*   { inv AT_EVENT. existT_elim. subst. ss. } *)
      (*   { inv TAU_STEP. ss. } *)
      (*   inv AT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)
      (*   inv AFT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)
      (*   destruct r. *)

      (*   rename ASTAR' into STAR. *)
      (*   inv STAR; cycle 2. *)
      (*   { inv ASTEP; ss. *)
      (*     - inv TAU_STEP. ss. *)
      (*     - inv AT_EVENT; ss. *)
      (*     - inv AT_EVENT; ss. *)
      (*   } *)
      (*   { exists None, (Some acq_msg). *)
      (*     splits; ss. *)
      (*     { intro tid'. *)
      (*       repeat (destruct tid'; ss). } *)
      (*     { i. exfalso. *)
      (*       des; ss. } *)

      (*     right. *)
      (*     split; ss. *)
      (*   } *)

      (*   exists (Some (DevState.mk (Some false) dmd)), *)
      (*   (Some acq_msg). *)
      (*   splits; ss. *)
      (*   { repeat (destruct tid'; ss). } *)
      (*   { clear. i. exfalso. des; ss. } *)

      (*   right. *)
      (*   splits. *)
      (*   { econs 3. *)
      (*     - ss. *)
      (*     - left. *)
      (*       split; ss. *)

      (*       admit. (* me_d = rel \/ (me_d = none /\ ~ In tid_d aq) -> ~ In tid_D aq' *) *)
      (*   } *)

      (*   i. clarify. *)
      (*   splits. *)
      (*   * (* wait start *) *)
      (*     intros dmd_r'. i. *)
      (*     desH DMD_IN_ES; ss. *)

      (*     assert (dmd_r' = dmd_r). *)
      (*     { clear - DMD_IN_ES. *)
      (*       unfold embed in *. *)
      (*       unf_resum. ss. clarify. existT_elim. ss. *)
      (*     } *)
      (*     subst dmd_r'. clear DMD_IN_ES. *)
      (*     exists dmd. *)
      (*     splits; ss. *)

      (*     econs; ss. *)
      (*     econs 1. ss. *)
      (*   * (* wait_decr *) *)
      (*     i. exfalso. *)
      (*     inv DEV_WAIT. clarify. nia. *)
      (*   * (* owner_decr *) *)
      (*     i. exfalso. *)
      (*     inv DEV_OWNER. *)

      (* + (* dmd = 0 *) *)
      (*   simpl_itree_hyp STAR. *)
      (*   simpl_itree_hyp STAR. *)
      (*   inv STAR. *)
      (*   { exists None, None. *)
      (*     splits; ss. *)
      (*     { intro tid'. *)
      (*       rewrite if_both_eq. *)
      (*       repeat (destruct tid'; ss). } *)
      (*     { i. exfalso. *)
      (*       des; ss. } *)
      (*     left. *)
      (*     clear. *)
      (*     ii. des; ss. *)
      (*   } *)
      (*   { exfalso. ss. } *)

      (*   inv ASTEP; cycle 2. *)
      (*   { inv AT_EVENT. existT_elim. subst. ss. } *)
      (*   { inv TAU_STEP. ss. } *)
      (*   inv AT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)
      (*   inv AFT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)
      (*   destruct r. *)

      (*   rename ASTAR' into STAR. *)
      (*   inv STAR; cycle 2. *)
      (*   { inv ASTEP; ss. *)
      (*     - inv TAU_STEP. ss. *)
      (*     - inv AT_EVENT; ss. *)
      (*     - inv AT_EVENT; ss. *)
      (*   } *)
      (*   { exists None, None. *)
      (*     splits; ss. *)
      (*     { intro tid'. *)
      (*       repeat (destruct tid'; ss). } *)
      (*     { i. exfalso. *)
      (*       des; ss. } *)

      (*     right. *)
      (*     split; ss. *)
      (*   } *)

      (*   exists (Some (DevState.mk (Some false) 0)), None. *)
      (*   splits; ss. *)
      (*   { repeat (destruct tid'; ss). } *)
      (*   { clear. i. exfalso. des; ss. } *)

      (*   right. *)
      (*   splits. *)
      (*   { econs 2. *)
      (*     right. *)
      (*     split; ss. *)
      (*     admit. (* me_d = rel \/ (me_d = none /\ ~ In tid_d aq) -> ~ In tid_d aq' *) *)
      (*   } *)
      (*   assert (dmd = 0) by nia. *)
      (*   subst dmd. *)
      (*   assert (dmd_r = 0). *)
      (*   { destruct dmd_r; ss. } *)

      (*   i. clarify. *)
      (*   splits. *)
      (*   * (* wait start *) *)
      (*     intro dmd_r'. i. exfalso. *)
      (*     desH DMD_IN_ES; ss. *)

      (*     assert (dmd_r' = 0). *)
      (*     { clear - DMD_IN_ES. *)
      (*       unfold embed in *. *)
      (*       unf_resum. ss. clarify. existT_elim. ss. *)
      (*     } *)
      (*     nia. *)
      (*   * (* wait_decr *) *)
      (*     i. exfalso. *)
      (*     inv DEV_WAIT. clarify. nia. *)
      (*   * (* owner_decr *) *)
      (*     i. exfalso. *)
    (*     inv DEV_OWNER. *)
      admit.

    - (* not owner, with demand *)
      guardH DMD_CASES.
      unfold dev_job, job_device_itree in STAR. ss.

      unfold update_demand in STAR. ss.
      destruct dmd as [| dmd'].
      { exfalso. nia. }
      unfold check_grant in STAR. ss.

      pose (pex_act := if asd then pex1 else pex2).
      destruct (is_updated pex_act) eqn: IS_UPD.
      2: {
        (* no grant *)
        fold pex_act.
        assert (sync_dev_state
                  (inb_dev (pex1, pex2) asd aq tout tid_d)
                  {| DevState.owner_status := Some false;
                     DevState.demand := S dmd' |} =
                {| DevState.owner_status := Some false;
                   DevState.demand := S dmd' |}).
        { unfold sync_dev_state.
          ss. destruct asd; ss.
          - unfold msg_c2d. ss.
            subst pex_act.
            rewrite IS_UPD. ss.
            rewrite andb_false_r. ss.
          - unfold msg_c2d. ss.
            subst pex_act.
            rewrite IS_UPD. ss.
            rewrite andb_false_r. ss.
        }

        admit.
      }
      destruct (grant_msg_loc aq tout) as [tid_gr|] eqn: GR_LOC.
      2: {
        (* no grant *)
        admit.
      }

      destruct (Nat.eqb_spec tid_gr tid_d).
      2: {
        (* no grant *)
        admit.
      }

      (* receiving grant *)
      subst tid_gr.
      pose (m_c1 := msg_c2d (is_active_side asd true) pex1 aq tout tid_d).
      pose (m_c2 := msg_c2d (is_active_side asd false) pex2 aq tout tid_d).
      unfold sync_dev_state in STAR.
      unfold inb_dev in STAR.
      fold m_c1 m_c2 in STAR.

      (* match type of STAR with *)
      (* | context[ (if ?c then _ else _, _) ] => *)
      (*   replace c with true in *; cycle 1 *)
      (* end. *)
      (* { destruct asd. *)
      (*   - subst pex_act. *)
      (*     assert (GRANT: m_c1 = Some grant_msg). *)
      (*     { apply grant_msg_cond. eauto. } *)
      (*     rewrite GRANT. ss. *)
      (*   - subst pex_act. *)
      (*     assert (GRANT: m_c2 = Some grant_msg). *)
      (*     { apply grant_msg_cond. eauto. } *)
      (*     rewrite GRANT. desf. *)
      (* } *)

      (* unfold run_device in STAR. ss. *)
      (* simpl_itree_hyp STAR. *)
      (* simpl_itree_hyp STAR. *)

      (* inv STAR. *)
      (* { exists None, None. *)
      (*   splits; ss. *)
      (*   { intro tid'. *)
      (*     rewrite if_both_eq. *)
      (*     repeat (destruct tid'; ss). } *)
      (*   left. ss. *)
      (* } *)
      (* { exfalso. ss. } *)

      (* inv ASTEP; cycle 2. *)
      (* { inv AT_EVENT. existT_elim. subst. ss. } *)
      (* { inv TAU_STEP. ss. } *)
      (* inv AT_EVENT. *)
      (* existT_elim. ss. clarify. *)
      (* existT_elim. ss. clarify. *)
      (* inv AFT_EVENT. *)
      (* existT_elim. ss. clarify. *)
      (* existT_elim. ss. clarify. *)
      (* destruct r. *)

      (* rename ASTAR' into STAR. *)
      (* simpl_itree_hyp STAR. ss. *)

      (* destruct dmd' as [| dmd'']. *)
      (* + (* release *) *)
      (*   rewrite Nat.eqb_refl in STAR. *)
      (*   simpl_itree_hyp STAR. *)

      (*   inv STAR. *)
      (*   { exists None, None. *)
      (*     splits; ss. *)
      (*     { intro tid'. *)
      (*       rewrite if_both_eq. *)
      (*       repeat (destruct tid'; ss). } *)
      (*     { intros _. *)
      (*       esplits; eauto. *)
      (*       econs; eauto. *)
      (*       fold pex_act. *)
      (*       apply grant_msg_cond. eauto. *)
      (*     } *)
      (*     left. *)
      (*     clear. ii. des; ss. *)
      (*   } *)
      (*   { exfalso. ss. } *)

      (*   inv ASTEP. *)
      (*   { inv TAU_STEP. ss. } *)
      (*   { inv AT_EVENT. existT_elim. subst. ss. } *)
      (*   inv AT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)
      (*   inv AFT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)

      (*   rename ASTAR' into STAR. *)
      (*   simpl_itree_hyp STAR. *)

      (*   inv STAR. *)
      (*   { exists None, (Some rel_msg). *)
      (*     splits; ss. *)
      (*     { intro tid'. *)
      (*       repeat (destruct tid'; ss). } *)
      (*     { intros _. *)
      (*       esplits; eauto. *)
      (*       econs; eauto. *)
      (*       fold pex_act. *)
      (*       apply grant_msg_cond. eauto. *)
      (*     } *)
      (*     left. *)
      (*     clear. *)
      (*     ii. des; ss. *)
      (*   } *)
      (*   { exfalso. ss. } *)

      (*   inv ASTEP; cycle 2. *)
      (*   { inv AT_EVENT. existT_elim. subst. ss. } *)
      (*   { inv TAU_STEP. ss. } *)
      (*   inv AT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)
      (*   inv AFT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)
      (*   destruct r. *)

      (*   rename ASTAR' into STAR. *)
      (*   inv STAR; cycle 2. *)
      (*   { inv ASTEP; ss. *)
      (*     - inv TAU_STEP. ss. *)
      (*     - inv AT_EVENT; ss. *)
      (*     - inv AT_EVENT; ss. *)
      (*   } *)
      (*   { exists None, (Some rel_msg). *)
      (*     splits; ss. *)
      (*     { intro tid'. *)
      (*       repeat (destruct tid'; ss). } *)
      (*     { intros _. *)
      (*       esplits; eauto. *)
      (*       econs; eauto. *)
      (*       fold pex_act. *)
      (*       apply grant_msg_cond. eauto. *)
      (*     } *)
      (*     right. *)
      (*     split; ss. *)
      (*   } *)

      (*   exists (Some (DevState.mk (Some false) 0)), (Some rel_msg). *)
      (*   splits; ss. *)
      (*   { econs. nia. } *)
      (*   { intro tid'. *)
      (*     repeat (destruct tid'; ss). } *)
      (*   { intros _. *)
      (*     esplits; eauto. *)
      (*     econs; eauto. *)
      (*     fold pex_act. *)
      (*     apply grant_msg_cond. eauto. *)
      (*   } *)
      (*   right. *)
      (*   splits; ss. *)
      (*   { econs 2. *)
      (*     left. ss. } *)

      (*   i. clarify. *)
      (*   splits. *)
      (*   * i. exfalso. *)
      (*     des; ss. *)
      (*   * i. exfalso. *)
      (*     inv DEV_WAIT. *)
      (*     clarify. *)
      (*     inv DEV_WAIT_CNT; ss. *)
      (*     { clear - DMD_CASES GR_LOC. *)
      (*       desH DMD_CASES; ss. *)
      (*       unfold grant_msg_loc in *. *)
      (*       desf. ss. eauto. } *)
      (*     { clear - WF GR_LOC WAITING_IN_QUEUE. *)

      (*       assert (nth_error aq 0 = Some tid_d). *)
      (*       { unfold grant_msg_loc in *. *)
      (*         desf. } *)
      (*       inv WF. *)
      (*       r in WF_AQ. desH WF_AQ. *)
      (*       rewrite NoDup_nth_error in ELEMS_NODUP. *)
      (*       hexploit (ELEMS_NODUP 0 (S i)). *)
      (*       { eapply nth_error_Some1'; eauto. } *)
      (*       { congruence. } *)
      (*       ss. *)
      (*     } *)
      (*     { fold pex_act in WCNT_EQ. *)
      (*       rewrite IS_UPD in WCNT_EQ. ss. } *)
      (*   * i. inv DEV_OWNER. *)

      (* + (* keep ownership *) *)
      (*   ss. *)
      (*   simpl_itree_hyp STAR. *)
      (*   inv STAR. *)
      (*   { exists None, None. *)
      (*     splits; ss. *)
      (*     { intro tid'. *)
      (*       repeat (destruct tid'; ss). } *)
      (*     { intros _. *)
      (*       esplits; eauto. *)
      (*       econs; eauto. *)
      (*       fold pex_act. *)
      (*       apply grant_msg_cond. eauto. *)
      (*     } *)
      (*     left. *)
      (*     clear. *)
      (*     ii. des; ss. *)
      (*   } *)
      (*   { exfalso. ss. } *)

      (*   inv ASTEP; cycle 2. *)
      (*   { inv AT_EVENT. existT_elim. subst. ss. } *)
      (*   { inv TAU_STEP. ss. } *)
      (*   inv AT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)
      (*   inv AFT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)
      (*   destruct r. *)

      (*   rename ASTAR' into STAR. *)
      (*   inv STAR; cycle 2. *)
      (*   { inv ASTEP; ss. *)
      (*     - inv TAU_STEP. ss. *)
      (*     - inv AT_EVENT; ss. *)
      (*     - inv AT_EVENT; ss. *)
      (*   } *)
      (*   { exists None, None. *)
      (*     splits; ss. *)
      (*     { intro tid'. *)
      (*       repeat (destruct tid'; ss). } *)
      (*     { intros _. *)
      (*       esplits; eauto. *)
      (*       econs; eauto. *)
      (*       fold pex_act. *)
      (*       apply grant_msg_cond. eauto. *)
      (*     } *)
      (*     right. *)
      (*     split; ss. *)
      (*   } *)

      (*   exists (Some (DevState.mk (Some true) (S dmd''))), None. *)
      (*   splits; ss. *)
      (*   { inv WF_DEV. *)
      (*     econs. nia. } *)
      (*   { intro tid'. *)
      (*     rewrite if_both_eq. *)
      (*     repeat (destruct tid'; ss). } *)
      (*   { intros _. *)
      (*     fold pex_act. *)
      (*     esplits; eauto. *)
      (*     econs 1; eauto. *)
      (*     apply grant_msg_cond. eauto. } *)

      (*   right. *)
      (*   fold pex_act. *)
      (*   splits; ss. *)
      (*   { econs 4; ss. *)
      (*     { fold pex_act in NEXT_ABST_CTRL. *)
      (*       admit. } *)
      (*     { admit. (* aq_update_queue -> cur_owner *) } *)
      (*   } *)

      (*   i. clarify. *)
      (*   guardH COMPL. *)
      (*   splits. *)
      (*   * i. exfalso. *)
      (*     des; ss. *)
      (*   * i. exfalso. *)
      (*     inv DEV_WAIT. clarify. *)
      (*     inv DEV_WAIT_CNT; ss. *)
      (*     { clear - DMD_CASES GR_LOC. *)
      (*       desH DMD_CASES; ss. *)
      (*       unfold grant_msg_loc in *. *)
      (*       desf. ss. eauto. } *)
      (*     { clear - WF GR_LOC WAITING_IN_QUEUE. *)

      (*       assert (nth_error aq 0 = Some tid_d). *)
      (*       { unfold grant_msg_loc in *. *)
      (*         desf. } *)
      (*       inv WF. *)
      (*       r in WF_AQ. desH WF_AQ. *)
      (*       rewrite NoDup_nth_error in ELEMS_NODUP. *)
      (*       hexploit (ELEMS_NODUP 0 (S i)). *)
      (*       { eapply nth_error_Some1'; eauto. } *)
      (*       { congruence. } *)
      (*       ss. *)
      (*     } *)
      (*     { fold pex_act in WCNT_EQ. *)
      (*       rewrite IS_UPD in WCNT_EQ. ss. } *)
      (*   * i. inv DEV_OWNER. *)
      (*     econs. nia. *)
      admit.

    - (* owner *)
      unfold dev_job, job_device_itree in STAR. ss.
      unfold update_demand in STAR. ss.
      destruct dmd as [| dmd'].
      { exfalso. nia. }

      unfold run_device in STAR. ss.
      (* simpl_itree_hyp STAR. *)
      (* simpl_itree_hyp STAR. *)

      (* inv STAR. *)
      (* { exists None, None. *)
      (*   splits; ss. *)
      (*   { intro tid'. *)
      (*     rewrite if_both_eq. *)
      (*     repeat (destruct tid'; ss). } *)
      (*   left. ss. *)
      (* } *)
      (* { exfalso. ss. } *)

      (* inv ASTEP; cycle 2. *)
      (* { inv AT_EVENT. existT_elim. subst. ss. } *)
      (* { inv TAU_STEP. ss. } *)
      (* inv AT_EVENT. *)
      (* existT_elim. ss. clarify. *)
      (* existT_elim. ss. clarify. *)
      (* inv AFT_EVENT. *)
      (* existT_elim. ss. clarify. *)
      (* existT_elim. ss. clarify. *)
      (* destruct r. *)

      (* rename ASTAR' into STAR. *)
      (* simpl_itree_hyp STAR. ss. *)

      (* destruct dmd' as [| dmd'']. *)
      (* + (* release *) *)
      (*   rewrite Nat.eqb_refl in STAR. *)
      (*   simpl_itree_hyp STAR. *)

      (*   inv STAR. *)
      (*   { exists None, None. *)
      (*     splits; ss. *)
      (*     { intro tid'. *)
      (*       rewrite if_both_eq. *)
      (*       repeat (destruct tid'; ss). } *)
      (*     { intros _. *)
      (*       esplits; eauto. *)
      (*       econs; eauto. *)
      (*     } *)
      (*     left. *)
      (*     clear. ii. des; ss. *)
      (*   } *)
      (*   { exfalso. ss. } *)

      (*   inv ASTEP. *)
      (*   { inv TAU_STEP. ss. } *)
      (*   { inv AT_EVENT. existT_elim. subst. ss. } *)
      (*   inv AT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)
      (*   inv AFT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)

      (*   rename ASTAR' into STAR. *)
      (*   simpl_itree_hyp STAR. *)

      (*   inv STAR. *)
      (*   { exists None, (Some rel_msg). *)
      (*     splits; ss. *)
      (*     { intro tid'. *)
      (*       repeat (destruct tid'; ss). } *)
      (*     { intros _. *)
      (*       esplits; eauto. *)
      (*       econs; eauto. *)
      (*     } *)
      (*     left. *)
      (*     clear. *)
      (*     ii. des; ss. *)
      (*   } *)
      (*   { exfalso. ss. } *)

      (*   inv ASTEP; cycle 2. *)
      (*   { inv AT_EVENT. existT_elim. subst. ss. } *)
      (*   { inv TAU_STEP. ss. } *)
      (*   inv AT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)
      (*   inv AFT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)
      (*   destruct r. *)

      (*   rename ASTAR' into STAR. *)
      (*   inv STAR; cycle 2. *)
      (*   { inv ASTEP; ss. *)
      (*     - inv TAU_STEP. ss. *)
      (*     - inv AT_EVENT; ss. *)
      (*     - inv AT_EVENT; ss. *)
      (*   } *)
      (*   { exists None, (Some rel_msg). *)
      (*     splits; ss. *)
      (*     { intro tid'. *)
      (*       repeat (destruct tid'; ss). } *)
      (*     { intros _. *)
      (*       esplits; eauto. *)
      (*       econs; eauto. *)
      (*     } *)
      (*     right. *)
      (*     split; ss. *)
      (*   } *)

      (*   exists (Some (DevState.mk (Some false) 0)), (Some rel_msg). *)
      (*   splits; ss. *)
      (*   { econs. nia. } *)
      (*   { intro tid'. *)
      (*     repeat (destruct tid'; ss). } *)
      (*   { intros _. *)
      (*     esplits; eauto. *)
      (*     econs; eauto. *)
      (*   } *)
      (*   right. *)
      (*   splits; ss. *)
      (*   { econs 2. *)
      (*     left. ss. } *)

      (*   i. clarify. *)
      (*   splits. *)
      (*   * i. exfalso. *)
      (*     des; ss. *)
      (*   * i. exfalso. *)
      (*     inv DEV_WAIT. *)
      (*     clarify. *)
      (*   * i. inv DEV_OWNER. *)

      (* + (* keep ownership *) *)
      (*   ss. *)
      (*   simpl_itree_hyp STAR. *)
      (*   inv STAR. *)
      (*   { exists None, None. *)
      (*     splits; ss. *)
      (*     { intro tid'. *)
      (*       repeat (destruct tid'; ss). } *)
      (*     { intros _. *)
      (*       eexists. exists (S (S dmd'')). *)
      (*       esplits; eauto. *)
      (*       { nia. } *)
      (*       econs; eauto. nia. *)
      (*     } *)
      (*     left. *)
      (*     clear. *)
      (*     ii. des; ss. *)
      (*   } *)
      (*   { exfalso. ss. } *)

      (*   inv ASTEP; cycle 2. *)
      (*   { inv AT_EVENT. existT_elim. subst. ss. } *)
      (*   { inv TAU_STEP. ss. } *)
      (*   inv AT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)
      (*   inv AFT_EVENT. *)
      (*   existT_elim. ss. clarify. *)
      (*   existT_elim. ss. clarify. *)
      (*   destruct r. *)

      (*   rename ASTAR' into STAR. *)
      (*   inv STAR; cycle 2. *)
      (*   { inv ASTEP; ss. *)
      (*     - inv TAU_STEP. ss. *)
      (*     - inv AT_EVENT; ss. *)
      (*     - inv AT_EVENT; ss. *)
      (*   } *)
      (*   { exists None, None. *)
      (*     splits; ss. *)
      (*     { intro tid'. *)
      (*       repeat (destruct tid'; ss). } *)
      (*     { intros _. *)
      (*       eexists. exists (S (S dmd'')). *)
      (*       splits; eauto. *)
      (*       { nia. } *)
      (*       econs; eauto. nia. *)
      (*     } *)
      (*     right. *)
      (*     split; ss. *)
      (*   } *)

      (*   exists (Some (DevState.mk (Some true) (S dmd''))), None. *)
      (*   splits; ss. *)
      (*   { inv WF_DEV. *)
      (*     econs. nia. } *)
      (*   { intro tid'. *)
      (*     rewrite if_both_eq. *)
      (*     repeat (destruct tid'; ss). } *)
      (*   { intros _. *)
      (*     eexists. exists (S (S dmd'')). *)
      (*     esplits; eauto. *)
      (*     { nia. } *)
      (*     econs 2; eauto. nia. } *)

      (*   right. *)
      (*   splits; ss. *)
      (*   { econs 4; ss. *)
      (*     { assert (S tout' = tout). *)
      (*       { admit. (* aq_update_queue *) *)

      (*       } *)
      (*       nia. *)
      (*     } *)
      (*     { admit. (* cur_owner *) } *)
      (*   } *)

      (*   i. clarify. *)
      (*   guardH COMPL. *)
      (*   splits. *)
      (*   * i. exfalso. *)
      (*     des; ss. *)
      (*   * i. exfalso. *)
      (*     inv DEV_WAIT. clarify. *)
      (*   * i. inv DEV_OWNER. *)
      (*     econs. nia. *)
      admit.
  Admitted.

End DEV_1STEP.







Section ABST_CTRL_NEXT.
  (* Import AbstCtrl. *)

  Variable ac: t.
  (* { inbox : list bytes ?; *)
  (*   failed_controller : (pexec_t * pexec_t)%type; *)
  (*   active_side : bool; *)
  (*   abst_queue : list nat; *)
  (*   owner_timeout : nat } *)

  Hypothesis WF: wf ac.

  Lemma replace_nth_neq A
        (l: list A) n a l' m
        (REPL: replace_nth l n a = l')
        (IDX_NEQ: m <> n)
    : nth_error l' m = nth_error l m.
  Proof.
    hexploit (replace_nth_spec _ l n a).
    i. des.
    - assert (l' = l) by congruence.
      clear REPL. subst l'. ss.
    - rewrite REPL in *. clear REPL.
      subst l l'.
      destruct (lt_ge_dec m (length l1)).
      { rewrite nth_error_app1 by ss.
        rewrite nth_error_app1 by ss. ss. }

      rewrite nth_error_app2 by ss.
      rewrite nth_error_app2 with (l':= [p] ++ l2) by ss.
      destruct (m - length l1) eqn: X; ss.
      nia.
  Qed.


  (* when other side is active & sent HB *)
  Lemma next_copy_hb
        (side: bool) (pex_this pex_other: pexec_t)
        (cst: CtrlState.t) inb_s
        mcon mc1 mc2
        (PREV_EXEC_PAIR:
           failed_controller ac =
           if side then (pex_this, pex_other)
           else (pex_other, pex_this))
        (MATCH: match_ctrl_state
                  (abst_queue ac) (owner_timeout ac)
                  (is_active_side (active_side ac) side)
                  pex_this cst)
        (HB_SENT: is_hb_sent pex_other = true)
        (NOT_ACTIVE: CtrlState.mode cst <> CtrlState.Active)
        (* (HB_FROM_OTHER: hb_of_abst_ctrl *)
        (*                   (is_active_side (active_side ac) *)
        (*                                   (negb side)) *)
        (*                   (abst_queue ac) (owner_timeout ac) *)
        (*                   pex_other mc_hb) *)
        (INB_THIS_SIDE: inb_s = AbstCtrl.drop_self_entry side (inbox ac))
        (INB_CON: nth_error (inbox ac) 0 = Some mcon)
        (INB_C1: nth_error (inbox ac) 1 = Some mc1)
        (INB_C2: nth_error (inbox ac) 2 = Some mc2)
        (* (CTRL_MENTRY_EQ: *)
        (*    if side then mc1 = None /\ mc2 = mc_hb *)
        (*    else mc1 = mc_hb /\ mc2 = None) *)
    : let asd' := next_active_side
                    mcon mc1 mc2 (active_side ac) in
      match_ctrl_state_temp
        (is_hb_sent (pex_prev_active ac))
        (abst_queue ac) (owner_timeout ac)
        (is_active_side asd' side)
        (* Compl *)
        (sync_istate (Z.of_nat (side2tid side)) cst inb_s).
  Proof.
    remember (next_active_side mcon mc1 mc2 (active_side ac))
      as asd' eqn: ASD'.
    guardH ASD'. s.

    destruct cst as [md_c tout_c qb_c qe_c q_c].
    unfold sync_istate. s.

    assert (TID_OTHER: Z.to_nat (3 - Z.of_nat (side2tid side)) =
                       side2tid (negb side)).
    { destruct side; ss. }

    pose (mc_hb := if side then mc2 else mc1).

    rewrite TID_OTHER.
    erewrite nth_error_nth.
    2: {
      instantiate (1:= mc_hb).
      destruct side; ss.
      - erewrite replace_nth_neq; eauto.
      - erewrite replace_nth_neq; eauto.
    }
    inv WF. ss.

    assert (HB_OF_AC: hb_of_abst_ctrl
                        (is_active_side asd (negb side))
                        aq tout pex_other mc_hb).
    { destruct side; clarify. }

    inv HB_OF_AC; ss.
    { exfalso.
      congruence. }

    rename msg into msg_hb. subst mc_hb.
    unfold CtrlState.copy_state_from_hb.
    unfold CtrlState.set_mode.
    rewrite CTRL_EQ.

    destruct md_c; ss.
    - (* Uninit -> Standby *)
      clarify.

      inv MATCH.
      2: { exfalso.
           destruct (is_active_side asd side); ss. }
      unfold CtrlState.init in *. clarify.

      assert (DONT_BE_ACTIVE: is_active_side asd' side = false).
      { destruct side; ss; clarify.
        - rewrite ASD'.
          inv ENTRY_C1; ss.
          clear.
          unfold next_active_side.
          desf.
        - rewrite ASD'.
          inv ENTRY_C2; ss.
          clear.
          unfold next_active_side.
          desf.
      }

      rewrite DONT_BE_ACTIVE.
      econs; eauto.
      unfold pex_prev_active. ss.

      destruct asd.
      + destruct side; ss.
        * clarify. ss.
          desf.
        * clarify. ss. desf.
      + destruct side; ss.
        * clarify. ss. desf.
        * clarify. ss. desf.

    - (* Standby -> _ *)
      clarify.

      inv MATCH; ss.

      assert (PREV_ACTIVE_SIDE: asd = negb side).
      { destruct side; ss.
        - destruct asd; ss.
        - destruct asd; ss.
      }

      assert (CUR_ACTIVE_SIDE:
                asd' = if mcon then side else negb side).
      { destruct side; ss; clarify.
        - rewrite ASD'.
          inv ENTRY_C1; ss.
          clear.
          desf.
        - rewrite ASD'.
          inv ENTRY_C2; ss.
          clear.
          desf.
      }

      subst asd asd'. ss.
      replace (is_active_side (negb side) side) with false in *.
      2: { destruct side; ss. }
      replace (is_active_side (negb side) (negb side)) with true in *.
      2: { destruct side; ss. }
      desH MATCH_MODE. clarify.

      econs; eauto.
      + destruct side; ss; clarify.
        { clear. desf. }
        { clear. desf. }
      + unfold pex_prev_active. ss.
        replace (if negb side then pex1 else pex2)
          with pex_other.
        2: { destruct side; clarify. }
        replace (is_hb_sent pex_other) with true. ss.
  Qed.


  Lemma next_no_copy_hb
        (side: bool)
        (pex_other: pexec_t)
        (cst: CtrlState.t) inb_s
        mcon mc1 mc2 (* mc_hb *)

        (PREV_EXEC_PAIR:
           failed_controller ac =
           if side then (Compl, pex_other)
           else (pex_other, Compl))
        (NO_COPY: is_hb_sent pex_other = false \/
                  CtrlState.mode cst = CtrlState.Active)
        (* (HB_FROM_OTHER: hb_of_abst_ctrl *)
        (*                   (is_active_side (active_side ac) *)
        (*                                   (negb side)) *)
        (*                   (abst_queue ac) (owner_timeout ac) *)
        (*                   pex_other mc_hb) *)
        (MATCH: match_ctrl_state
                  (abst_queue ac) (owner_timeout ac)
                  (is_active_side (active_side ac) side)
                  Compl cst)
        (INB_THIS_SIDE: inb_s = AbstCtrl.drop_self_entry side (inbox ac))
        (INB_CON: nth_error (inbox ac) 0 = Some mcon)
        (INB_C1: nth_error (inbox ac) 1 = Some mc1)
        (INB_C2: nth_error (inbox ac) 2 = Some mc2)
        (* (CTRL_MENTRY_EQ: *)
        (*    if side then mc1 = None /\ mc2 = mc_hb *)
        (*    else mc1 = mc_hb /\ mc2 = None) *)
    : let asd' := next_active_side
                    mcon mc1 mc2 (active_side ac) in
      match_ctrl_state_temp
        (is_hb_sent (pex_prev_active ac))
        (abst_queue ac) (owner_timeout ac)
        (is_active_side asd' side)
        (sync_istate (Z.of_nat (side2tid side)) cst inb_s).
  Proof.
    remember (next_active_side mcon mc1 mc2 (active_side ac))
      as asd' eqn: ASD'.
    guardH ASD'. s.

    destruct cst as [md_c tout_c qb_c qe_c q_c].
    unfold sync_istate. s.

    assert (TID_OTHER: Z.to_nat (3 - Z.of_nat (side2tid side)) =
                       side2tid (negb side)).
    { destruct side; ss. }

    pose (mc_hb := if side then mc2 else mc1).

    rewrite TID_OTHER.
    erewrite nth_error_nth.
    2: {
      instantiate (1:= mc_hb).
      destruct side; ss.
      - erewrite replace_nth_neq; eauto.
      - erewrite replace_nth_neq; eauto.
    }
    inv WF. ss. clarify.

    (* assert (HB_OF_AC: hb_of_abst_ctrl *)
    (*                     (is_active_side asd (negb side)) *)
    (*                     aq tout pex_other mc_hb). *)
    (* { destruct side; clarify. } *)

    (* inv HB_OF_AC; ss. *)
    (* { exfalso. *)
    (*   congruence. } *)

    (* rename msg into msg_hb. subst mc_hb. *)
    (* unfold CtrlState.copy_state_from_hb. *)
    (* unfold CtrlState.set_mode. *)
    (* rewrite CTRL_EQ. *)

    destruct md_c; ss.
    - exfalso.
      inv MATCH. desf.
    - (* Active -> _ *)
      inv MATCH.

      assert (PREV_ACTIVE_SIDE: asd = side).
      { destruct side; ss.
        - destruct asd; ss.
        - destruct asd; ss.
      }

      assert (CUR_ACTIVE_SIDE:
                asd' = if andb mcon mc_hb then negb side
                       else side).
      { destruct side; ss; clarify.
        - rewrite ASD'.
          inv ENTRY_C1; ss.
          clear.
          desf.
        - rewrite ASD'.
          inv ENTRY_C2; ss.
          clear. subst mc_hb.
          destruct mc1; destruct mcon; ss.
      }

      subst asd asd'. ss.
      replace (is_active_side side side) with true in *.
      2: { destruct side; ss. }

      unfold pex_prev_active. s.

      destruct mc_hb; s.
      + erewrite nth_error_nth.
        2: {
          unfold drop_self_entry.
          erewrite replace_nth_neq; eauto; ss.
          destruct side; ss.
        }
        s.
        destruct mcon; ss; clarify.
        * destruct side; ss; clarify.
        * destruct side; ss; clarify.
      + destruct mcon; ss; clarify.
        * destruct side; ss; clarify.
        * destruct side; ss; clarify.

    - (* Standby -> Active (no hb received) *)
      desH NO_COPY; ss.
      clear AT_LEAST_ONE_COMPL.

      assert (<<PREV_ACTIVE_SIDE: asd = negb side>> /\
              <<CUR_ACTIVE_SIDE: asd' = side>> /\
              <<HB_NONE: mc_hb = None>>).
      { subst mc_hb.
        destruct side; ss.
        - destruct asd; ss.
          + exfalso.
            clarify.
            inv MATCH. ss.
          + clarify.
            inv ENTRY_C2; s.
            2: { exfalso. congruence. }
            rewrite Bool.andb_false_r. ss.
            rewrite if_both_eq. ss.
        - destruct asd; ss.
          + clarify.
            inv ENTRY_C1; s.
            2: { exfalso. congruence. }
            rewrite if_both_eq. ss.
          + exfalso.
            clarify.
            inv MATCH. ss.
      }
      des. clear ASD'.
      subst.

      replace (is_active_side side side) with true in *.
      2: { destruct side; ss. }

      unfold pex_prev_active. s.
      rewrite HB_NONE.

      inv MATCH.
      destruct side; ss; clarify.
  Qed.


  Lemma next_sync_istate
        (side: bool) pex_this pex_other
        (cst: CtrlState.t) inb_s
        mcon mc1 mc2 (* mc_hb *)

        (PREV_EXEC_PAIR:
           failed_controller ac =
           if side then (pex_this, pex_other)
           else (pex_other, pex_this))
        (MATCH: match_ctrl_state
                  (abst_queue ac) (owner_timeout ac)
                  (is_active_side (active_side ac) side)
                  pex_this cst)
        (INB_THIS_SIDE: inb_s = AbstCtrl.drop_self_entry side (inbox ac))
        (INB_CON: nth_error (inbox ac) 0 = Some mcon)
        (INB_C1: nth_error (inbox ac) 1 = Some mc1)
        (INB_C2: nth_error (inbox ac) 2 = Some mc2)
        (* (CTRL_MENTRY_EQ: *)
        (*    if side then mc1 = None (* /\ mc2 = mc_hb *) *)
        (*    else (* mc1 = mc_hb /\ *) mc2 = None) *)
    : let asd' := next_active_side
                    mcon mc1 mc2 (active_side ac) in
      match_ctrl_state_temp
        (is_hb_sent (pex_prev_active ac))
        (abst_queue ac) (owner_timeout ac)
        (is_active_side asd' side)
        (* Compl *)
        (sync_istate (Z.of_nat (side2tid side))
                     cst inb_s).
  Proof.
    (* pose (pex_this := *)
    (*         if side then fst (failed_controller ac) *)
    (*         else snd (failed_controller ac)). *)
    (* pose (pex_other := *)
    (*         if side then snd (failed_controller ac) *)
    (*         else fst (failed_controller ac)). *)
    pose (hb := if side then mc2 else mc1).

    destruct (is_hb_sent pex_other) eqn: HB_SENT_OTHER.
    2: {
      assert (THIS_COMPL: pex_this = Compl).
      { inv WF. ss.
        destruct side.
        - clarify.
          destruct AT_LEAST_ONE_COMPL; ss.
          subst pex_other. ss.
        - clarify.
          destruct AT_LEAST_ONE_COMPL; ss.
          subst pex_other. ss.
      }
      subst pex_this.
      (* rewrite THIS_COMPL in *. *)
      eapply next_no_copy_hb; eauto.
    }

    destruct (CtrlState.mode cst) eqn:MODE.
    { eapply next_copy_hb; eauto.
      rewrite MODE. ss. }
    { inv MATCH; ss.
      eapply next_no_copy_hb; eauto.
      econs; eauto.
    }
    { eapply next_copy_hb; eauto.
      rewrite MODE. ss. }
  Qed.


  Lemma next_update_queue
        (side: bool)
        (* (pex_other: pexec_t) *)
        md1 md2 md3
        asd' cst1 inb_s
        (MATCH1: match_ctrl_state_temp
                   (is_hb_sent (pex_prev_active ac))
                   (abst_queue ac) (owner_timeout ac)
                   (is_active_side asd' side)
                   cst1)
        (INB_THIS_SIDE: inb_s = AbstCtrl.drop_self_entry side (inbox ac))
        (INB_CON: nth_error (inbox ac) 3 = Some md1)
        (INB_C1: nth_error (inbox ac) 4 = Some md2)
        (INB_C2: nth_error (inbox ac) 5 = Some md3)
    : exists aq' tout1,
      <<AQ_UPDQ: aq_update_queue
                   (abst_queue ac)
                   (if andb (negb (is_hb_sent (pex_prev_active ac)))
                            (owner_timeout ac =? MAX_TIMEOUT)
                    then 0 else owner_timeout ac)
                   [(3, md1); (4, md2); (5, md3)] = (aq', tout1)>> /\
      <<WF_AQ1: abst_queue_wf aq'>> /\
      <<TIMEOUT_LT_MAX: tout1 < MAX_TIMEOUT>> /\
      <<MATCH1: match_ctrl_state
                  aq' tout1 (is_active_side asd' side) Compl
                  (update_queue cst1 inb_s)>> /\
      <<EMPTY_QUEUE_TOUT_ZERO1: length aq' = 0 -> tout1 = 0>>
  .
  Proof.
    inv WF. ss. clarify.
    guardH AT_LEAST_ONE_COMPL.
    inv MATCH1.
    unfold aq_update_queue.
    unfold update_queue. s.

    unfold pex_prev_active. s.

    pose (b := (negb (is_hb_sent (if asd then pex1 else pex2))
                && (tout =? MAX_TIMEOUT))%bool).
    fold b.
    pose (tout_i := if b then O else tout).
    fold tout_i.

    replace (if b then 0%Z else Z.of_nat tout)
      with (Z.of_nat tout_i).
    2: { destruct b; ss. }

    match goal with
    | |- context [apply_devmsg ?x 3 _] => pose (cst := x)
    end.
    fold cst.

    unfold Pos.to_nat. s.
    unfold drop_self_entry.
    erewrite nth_error_nth.
    2: { erewrite replace_nth_neq; eauto. ss. desf. }
    erewrite nth_error_nth.
    2: { erewrite replace_nth_neq; eauto. ss. desf. }
    erewrite nth_error_nth.
    2: { erewrite replace_nth_neq; eauto. ss. desf. }

    pose (mode_this:= if is_active_side asd' side then
                        CtrlState.Active
                      else CtrlState.Standby).
    fold mode_this in cst.

    assert (exists aq1 tout1 qb1 qe1 q1,
               <<WF_TIMEOUT1: tout1 <= MAX_TIMEOUT>> /\
               <<PROC_DMSGS:
                 aq_process_dev_msgs
                   aq tout_i
                   [(3, md1); (4, md2); (5, md3)] = (aq1, tout1)>> /\
               <<CST1: apply_devmsg
                         (apply_devmsg
                            (apply_devmsg cst 3 md1) 4 md2)
                         5 md3 =
                       CtrlState.mk
                         mode_this
                         (Z.of_nat tout1) qb1 qe1 q1>> /\
               <<MATCH_Q1: match_queue aq1 (qb1, qe1, q1)>> /\
               <<WF_Q1: abst_queue_wf aq1>> /\
               <<EMPTY_QUEUE_TOUT_ZERO':
                   length aq1 = 0 -> tout1 = 0>>).
    { unfold aq_process_dev_msgs.
      unfold fold_left.

      (* device 1 *)
      hexploit (match_proc_dev_msg aq tout_i 3 md1 cst); eauto.
      { subst tout_i.
        destruct b.
        - nia.
        - ss. }
      { intro AUX.
        apply EMPTY_QUEUE_TOUT_ZERO in AUX.
        (* hexploit EMPTY_QUEUE_TOUT_ZERO; eauto. *)
        (* i. *)
        subst tout tout_i.
        rewrite if_both_eq. ss. }
      { subst cst. eauto. }
      { r. ss. eauto. }

      i. des.
      renames aq1 tout1 into aq_d3 tout_d3.
      renames qb1 qe1 q1 into qb_d3 qe_d3 q_d3.
      renames WF_TIMEOUT1 PROC1 into WF_TIMEOUT_D3 PROC_D3.
      renames CST1 MATCH_Q1 WF_Q1 into CST_D3 MATCH_Q_D3 WF_Q_D3.

      replace (Z.of_nat 3) with 3%Z in CST_D3 by ss.
      rewrite PROC_D3.

      (* device 2 *)
      hexploit (match_proc_dev_msg
                  aq_d3 tout_d3 4 md2
                  (apply_devmsg cst 3 md1)); eauto.
      { r. ss. eauto. }

      i. des.
      renames aq1 tout1 into aq_d4 tout_d4.
      renames qb1 qe1 q1 into qb_d4 qe_d4 q_d4.
      renames WF_TIMEOUT1 PROC1 into WF_TIMEOUT_D4 PROC_D4.
      renames CST1 MATCH_Q1 WF_Q1 into CST_D4 MATCH_Q_D4 WF_Q_D4.

      replace (Z.of_nat 4) with 4%Z in CST_D4 by ss.
      rewrite PROC_D4.

      (* device 3 *)
      hexploit (match_proc_dev_msg
                  aq_d4 tout_d4 5 md3
                  (apply_devmsg (apply_devmsg cst 3 md1)
                                4 md2)); eauto.
      { r. ss. eauto. }
    }
    des.
    rewrite CST1.
    rewrite PROC_DMSGS.

    hexploit (match_reduce_timeout aq1 tout1); eauto.
    i. des.
    rewrite CST1 in REDUCE_TOUT.
    rewrite REDUCE_TOUT.
    clear REDUCE_TOUT.

    exists aq', tout'.
    splits; eauto; ss.
    { destruct tout1; ss.
      - clarify. unfold MAX_TIMEOUT. nia.
      - destruct tout1; ss; clarify.
    }

    destruct tout1 as [| tout1].
    { clarify. ss.
      econs; ss.
      rewrite if_both_eq. ss. }
    destruct tout1 as [| tout1].
    { clarify. ss.
      econs; ss.
      rewrite if_both_eq. ss.
    }
    { clarify. ss.
      econs; ss.
      destruct (Nat.eqb_spec tout1 4).
      { exfalso.
        unfold MAX_TIMEOUT in *.
        nia. }
      rewrite if_both_eq. ss.
    }
  Qed.


  Lemma next_new_owner
        (side: bool) (asd': bool)
        aq' tout1 cst1
        (MATCH2: match_ctrl_state
                   aq' tout1 (is_active_side asd' side)
                   Compl cst1)
        (WF_AQ': abst_queue_wf aq')
        (TOUT_LT_MAX: tout1 < MAX_TIMEOUT)
        (EMPTY_TOUT_ZERO: length aq' = 0 -> tout1 = 0)
    : exists tout' nown cst' nown_z,
      <<NEW_OWNER: aq_new_owner aq' tout1 = (tout', nown)>> /\
      <<WF_TOUT': tout' <= MAX_TIMEOUT>> /\
      <<UPD_CST: update_owner cst1 = (cst', nown_z)>> /\
      <<MATCH': match_ctrl_state
                  aq' tout' (is_active_side asd' side)
                  Compl cst'>> /\
      <<NOWN_Z: nown_z = if is_active_side asd' side then
                           match nown with
                           | Some tid_nown => Z.of_nat tid_nown
                           | None => Z_mone
                           end
                         else Z_mone>> /\
      <<EMPTY_TOUT_ZERO: length aq' = 0 <-> tout' = 0>>.
  Proof.
    unfold aq_new_owner.
    unfold update_owner.
    inv MATCH2.
    inv MATCH_QUEUE.
    - (* empty *)
      hexploit EMPTY_TOUT_ZERO; eauto.
      i. subst. s.
      rewrite if_both_eq. s.
      rewrite Z.eqb_refl. s.

      esplits; eauto.
      { nia. }
      { s. rewrite if_both_eq.
        instantiate (1:= CtrlState.mk
                           (if is_active_side asd' side
                            then CtrlState.Active
                            else CtrlState.Standby)
                           0 qe_c qe_c q_c).
        desf. }
      { econs; ss.
        - rewrite if_both_eq. ss.
        - econs; ss. }

    - (* nonempty queue *)
      destruct (Z.eqb_spec qb_c qe_c); s.
      { exfalso. congruence. }

      destruct tout1 as [| tout1']; s.
      + (* tout1 = 0 *)
        rewrite if_both_eq. s.
        rewrite qrange_sanitize_id by ss.
        unfold get_queue.
        erewrite nth_error_nth by eauto.

        destruct (is_active_side asd' side) eqn: IS_ACT.
        * (* active *)
          esplits; eauto.
          2: { clear. ss. }
          econs; ss.
          econs; eauto.
        * (* standby *)
          esplits; eauto.
          2: { clear. ss. }
          econs; ss.
          econs; eauto.
      + (* 0 < tout1 *)
        destruct (Nat.eqb_spec tout1' 4); s.
        { exfalso. unfold MAX_TIMEOUT in *. nia. }
        rewrite if_both_eq.

        replace (Z.pos (Pos.of_succ_nat tout1')) with
            (1 + (Z.of_nat tout1'))%Z by nia.

        match goal with
        | |- context[(?x =? 0)%Z] =>
          destruct (Z.eqb_spec x 0)
        end.
        { exfalso. nia. }
        s.

        esplits; eauto.
        { nia. }
        { instantiate (1:= CtrlState.mk
                             (if is_active_side asd' side then
                                CtrlState.Active
                              else CtrlState.Standby)
                             (1 + Z.of_nat tout1')
                             qb_c qe_c q_c).
          s. desf. }
        { econs; ss.
          - destruct (Nat.eqb_spec tout1' 4); ss.
            rewrite if_both_eq. nia.
          - econs; ss.
        }
        { nia. }
  Qed.


  Lemma ctrl_sync_update
        (side: bool)
        (cst: CtrlState.t) inb_s pex
        mcon mc1 mc2 md1 md2 md3 asd'
        (PEX_THIS: pex = if side then fst (failed_controller ac)
                         else snd (failed_controller ac))
        (MATCH: match_ctrl_state
                  (abst_queue ac) (owner_timeout ac)
                  (is_active_side (active_side ac) side)
                  pex cst)
        (INB_THIS_SIDE: inb_s = AbstCtrl.drop_self_entry
                                  side (inbox ac))
        (INBOX: inbox ac = [mcon; mc1; mc2; md1; md2; md3])
        (ACTIVE_SIDE': asd' = next_active_side
                                mcon mc1 mc2 (active_side ac))
        (WF_CST: CtrlState.wf cst)
    : exists tout1 aq' tout' nown
        cst' nown_z,
      <<AQ_UPDQ: aq_update_queue
                   (abst_queue ac)
                   (if andb
                         (negb (is_hb_sent (pex_prev_active ac)))
                         (owner_timeout ac =? MAX_TIMEOUT)
                    then 0 else owner_timeout ac)
                   (* (owner_timeout ac) *)
                   [(3, md1); (4, md2); (5, md3)] =
                 (aq', tout1)>> /\
      <<AQ_NOWN: aq_new_owner aq' tout1 = (tout', nown)>> /\
      <<UPD: update_owner (update_istate
                             (Z.of_nat (side2tid side))
                             cst inb_s) =
             (cst', nown_z)>> /\
      <<MATCH': match_ctrl_state
                  aq' tout' (is_active_side asd' side)
                  Compl cst'>> /\
      <<NEW_OWNER:
        nown_z = if is_active_side asd' side then
                   match nown with
                   | Some tid_nown => Z.of_nat tid_nown
                   | None => Z_mone
                   end
                 else Z_mone>> /\
      <<TOUT1_LT_MAX: tout1 < MAX_TIMEOUT>> /\
      <<WF_CST': CtrlState.wf cst'>> /\
      <<WF_AQ': abst_queue_wf aq'>> /\
      <<TOUT'_LT_MAX: tout' <= MAX_TIMEOUT>>
  .
  Proof.
    unfold update_istate.
    assert (PREV_EXEC:
              exists pex_other,
                failed_controller ac =
                if side then (pex, pex_other)
                else (pex_other, pex)).
    { exists (if side then snd (failed_controller ac)
         else fst (failed_controller ac)).
      destruct side; subst; apply surjective_pairing.
    }
    clear PEX_THIS.
    des.

    hexploit next_sync_istate; eauto.
    { rewrite INBOX. ss. }
    { rewrite INBOX. ss. }
    { rewrite INBOX. ss. }
    rewrite <- ACTIVE_SIDE'.
    s. intro MATCH1.

    hexploit next_update_queue; eauto.
    { rewrite INBOX. ss. }
    { rewrite INBOX. ss. }
    { rewrite INBOX. ss. }
    i. des.

    hexploit next_new_owner; eauto.
    i. des.

    esplits; eauto.
    eapply wf_update_owner.
    2: { eauto. }
    apply wf_update_queue.
    apply wf_sync_istate.
    ss.
  Qed.

End ABST_CTRL_NEXT.


Section CTRL_1STEP.
  Variable sys: @SyncSys.t obsE bytes.
  Variable tm_init: nat.
  Hypothesis PERIOD_POS: SyncSys.period sys <> 0.
  Let dsys: DSys.t := SyncSys.as_dsys sys tm_init.
  Let period: nat := SyncSys.period sys.

  Let sntz := fun bs => Some (resize_bytes 8 bs).
  Let mcasts := [[tid_ctrl1; tid_ctrl2]].
  Hypothesis SNTZ_EQ: sntz = (SyncSys.sanitize_msg sys).
  Hypothesis MCASTS_EQ: mcasts = (SyncSys.mcasts sys).


  Lemma send_grant_aux
        tid_z nown_z
        es oast' out
        (is_active: bool)
        (k: unit -> itree _ _)
        (STAR: SNode.istar
                 sntz num_tasks mcasts
                 (ITrSNode.to_snode (ctrl_mod tid_z))
                 (ITree.bind (if (check_dev_id nown_z) then
                                trigger (AbstSendEvent (Z.to_nat nown_z) grant_msg)
                              else Ret tt)
                             k,
                  SNode.init_box num_tasks)
                 es (oast', out))
        (NOT_DEV_ID_MONE: check_dev_id nown_z = false -> nown_z = Z_mone)
        (* (K_NOT_FIN: ~ option_rel1 (fun x => ITrSNode.period_end (ctrl_mod tid_z) x) (Some (k tt))) *)
        (FINAL: option_rel1 (SNode.period_end _) oast')
    : <<FAILED: es = [] /\ oast' = None /\ out = SNode.init_box num_tasks>> \/
      (exists out1,
          <<OUTBOX1:
             forall tid',
               SNode.get_outbox_msg_by_dest tid' out1 =
               if (Z.of_nat tid' =? nown_z)%Z then
                 Some grant_msg
               else None>> /\
          <<OUTBOX_LEN1: length out1 = num_tasks>> /\
          <<STAR': SNode.istar sntz num_tasks mcasts
            (ITrSNode.to_snode (ctrl_mod tid_z))
            (k tt, out1) es (oast', out)>>).
  Proof.
    ss.
    destruct (check_dev_id nown_z) eqn: CHK_DEV_ID.
    2: { (* no send *)
      change k with (fun x => k x) in STAR.
      simpl_itree_hyp STAR.

      right.
      esplits; eauto.
      2: { unfold SNode.init_box. rewrite repeat_length. ss. }
      i. hexploit NOT_DEV_ID_MONE; eauto.
      clear.
      i. subst.
      replace (Z.of_nat tid' =? Z_mone)%Z with false.
      2: { unfold Z_mone.
           destruct (Z.eqb_spec (Z.of_nat tid') (-1)%Z); ss.
           nia. }
      repeat (destruct tid'; ss).
    }
    change k with (fun x => k x) in STAR.
    simpl_itree_hyp STAR.

    inv STAR.
    { left. ss. }
    { exfalso. inv FINAL. }

    inv ASTEP.
    { inv TAU_STEP. ss. }
    { inv AT_EVENT. existT_elim. ss. clarify. }

    inv AT_EVENT.
    existT_elim. ss. clarify.
    existT_elim. ss. clarify.
    inv AFT_EVENT.
    existT_elim. ss. clarify.
    existT_elim. ss. clarify.

    assert (exists tid_g, <<DEV_TID: is_dev_tid tid_g>> /\
                     <<DEV_TID_TO_Z: Z.of_nat tid_g = nown_z>>).
    { clear - CHK_DEV_ID.
      unfold check_dev_id in CHK_DEV_ID.
      eapply existsb_exists in CHK_DEV_ID. des. ss.
      destruct (Z.eqb_spec nown_z x); ss. subst.
      des; subst; ss.
      { exists 3. splits; ss. r. ss. eauto. }
      { exists 4. splits; ss. r. ss. eauto. }
      { exists 5. splits; ss. r. ss. eauto. }
    }
    des.

    replace (SNode.get_actual_dest num_tasks mcasts (Z.to_nat nown_z)) with [tid_g] in *.
    2: { unfold SNode.get_actual_dest.
         rewrite <- DEV_TID_TO_Z.
         rewrite Nat2Z.id.
         unfold num_tasks.
         r in DEV_TID. ss.
         des; subst; ss.
    }

    replace (SNode.check_available [tid_g] (SNode.init_box num_tasks)) with true in *.
    2: { unfold SNode.check_available, SNode.check_available1.
         ss.
         r in DEV_TID. ss.
         des; subst; ss.
    }

    replace (resize_bytes 8 grant_msg) with grant_msg
      in ASTAR' by ss.

    right.
    esplits; eauto.
    2: {
      unfold SNode.insert_msg.
      rewrite imap_length.
      unfold SNode.init_box. rewrite repeat_length. ss.
    }

    intro tid'.
    subst nown_z.
    rewrite Nat2Z_inj_eqb.
    clear - DEV_TID.
    destruct (Nat.eqb_spec tid' tid_g); subst.
    - r in DEV_TID. ss.
      des; subst; ss.
    - r in DEV_TID. ss.
      des; subst; ss.
      + repeat (destruct tid'; ss).
      + repeat (destruct tid'; ss).
      + repeat (destruct tid'; ss).
  Qed.


  Lemma send_hb_aux
        (side: bool)
        tid_z
        es oast' out
        cst
        (k: unit -> itree _ _) out1
        (*    SNode.get_outbox_msg_by_dest 1 out1 = None) *)
        (* (OUTBOX2_NO_HBS: *)
        (*    SNode.get_outbox_msg_by_dest 2 out1 = None) *)
        (STAR: SNode.istar
                 sntz num_tasks mcasts
                 (ITrSNode.to_snode (ctrl_mod tid_z))
                 (ITree.bind (send_hb_itree
                                cst tid_z) k, out1)
                 es (oast', out))
        (FINAL: option_rel1 (SNode.period_end _) oast')
        (WF_CST: CtrlState.wf cst)
        (TID_Z: tid_z = Z.of_nat (side2tid side))
        (OUTBOX_NO_HBS1: SNode.check_available [1] out1 = true)
        (OUTBOX_NO_HBS2: SNode.check_available [2] out1 = true)

    : <<FAILED: es = [] /\ oast' = None /\ out = out1>> \/
      (exists hb out',
          <<HB_EQ: hb = CtrlState.to_bytes cst>> /\
          <<OUTBOX': forall tid',
            SNode.get_outbox_msg_by_dest tid' out' =
            if tid' =? 1 then
              if side then None else Some hb
            else
              if tid' =? 2 then
                if side then Some hb else None
              else
                SNode.get_outbox_msg_by_dest
                  tid' out1>> /\
      <<STAR': SNode.istar
                 sntz num_tasks mcasts
                 (ITrSNode.to_snode (ctrl_mod tid_z))
                 (k tt, out') es (oast', out)>>).
  Proof.
    ss.
    change k with (fun x => k x) in STAR.
    unfold send_hb_itree in STAR.
    simpl_itree_hyp STAR.

    inv STAR.
    { left. ss. }
    { exfalso. inv FINAL. }

    inv ASTEP.
    { inv TAU_STEP. ss. }
    { inv AT_EVENT. existT_elim. ss. clarify. }

    inv AT_EVENT.
    existT_elim. ss. clarify.
    existT_elim. ss. clarify.
    inv AFT_EVENT.
    existT_elim. ss. clarify.
    existT_elim. ss. clarify.

    replace (Z.to_nat (3 - Z.of_nat (side2tid side))) with
        (side2tid (negb side)) in *.
    2: { destruct side; ss. }

    replace (SNode.get_actual_dest num_tasks mcasts (side2tid (negb side))) with [side2tid (negb side)] in *.
    2: { destruct side; ss. }

    replace (SNode.check_available [side2tid (negb side)] out1)
      with true in *.
    2: { destruct side; ss. }

    pose (hb := CtrlState.to_bytes cst).
    fold hb in ASTAR'.

    replace (resize_bytes 8 hb) with hb in ASTAR'.
    2: {
      subst hb.
      unfold resize_bytes.
      rewrite CtrlState_to_bytes_length by ss.
      rewrite Nat.sub_diag. ss.
      rewrite app_nil_r.
      rewrite firstn_all2; ss.
      rewrite CtrlState_to_bytes_length by ss.
      ss.
    }

    right.
    esplits; eauto.

    intro tid'.

    erewrite SNode_insert_get_outbox; try reflexivity.
    2: {
      destruct out1; ss.
      destruct out1; ss.
      destruct out1; ss.
      destruct side; ss.
      - econs; ss. nia.
      - econs; ss. nia.
    }

    destruct side; ss.
    - repeat (destruct tid'; ss).
      clear - OUTBOX_NO_HBS1.
      unfold SNode.check_available,
      SNode.check_available1 in *. ss.
      unfold SNode.get_outbox_msg_by_dest.
      desf.
    - repeat (destruct tid'; ss).
      clear - OUTBOX_NO_HBS2.
      unfold SNode.check_available,
      SNode.check_available1 in *. ss.
      unfold SNode.get_outbox_msg_by_dest.
      desf.
  Qed.


  Lemma ctrl_compl_aux
        tid_z t es oast' out
        (* (k: unit -> itree _ _) *)
        cst out'
        (STAR: SNode.istar
                 sntz num_tasks mcasts
                 (ITrSNode.to_snode (ctrl_mod tid_z))
                 (ITree.bind (trigger (MarkComplete t))
                             (fun _ => Ret cst), out')
                 es (oast', out))
        (FINAL: option_rel1 (SNode.period_end _) oast')
    : <<OUTBOX_EQ: out = out'>> /\
      (<<FAILED: es = [] /\ oast' = None>> \/
       (exists ocst',
           <<CST_FIN_OEQ: option_rel1 (fun cst' => cst' = cst) ocst'>> /\
           <<EVTS_COMPL: es = [embed (cevt t)]>> /\
           <<OAST'_EQ: oast' = option_map (fun cst => Ret cst) ocst'>>)).
  Proof.
    ss.
    simpl_itree_hyp STAR.

    inv STAR.
    { split; ss.
      left. ss. }
    { split; ss. }

    inv ASTEP; cycle 2.
    { inv AT_EVENT. existT_elim. ss. clarify. }
    { inv TAU_STEP. ss. }

    inv AT_EVENT.
    existT_elim. ss. clarify.
    existT_elim. ss. clarify.
    inv AFT_EVENT.
    existT_elim. ss. clarify.
    existT_elim. ss. clarify.
    unf_resum.
    destruct r.

    inv ASTAR'.
    { split; ss.
      right. exists None.
      esplits; ss. }
    { split; ss.
      right. exists (Some cst).
      esplits; ss. }
    { inv ASTEP.
      - inv TAU_STEP. ss.
      - inv AT_EVENT. existT_elim. ss.
      - inv AT_EVENT. existT_elim. ss.
    }
  Qed.

  (* Arguments Z.of_nat: simpl nomatch. *)

  Lemma ctrl_1step
        (side: bool)
        inb_c pex1 pex2 asd aq tout
        me_con me_c1 me_c2 me_d1 me_d2 me_d3
        tid pex inb_cb ast_c
        t st es out st'
        asd' aq' tout' owner_new
        (WF: wf (mk inb_c (pex1, pex2) asd aq tout))
        (INBOX_EQ: inb_c = [me_con; me_c1; me_c2;
                           me_d1; me_d2; me_d3])

        (* (WF_AQ: abst_queue_wf aq) *)
        (* (RANGE_TIMEOUT: tout <= MAX_TIMEOUT) *)
        (* (EMPTY_TIMEOUT_ZERO: length aq = 0 -> tout = 0) *)
        (* (INB_CTRL: inb_c = [me_con; me_c1; me_c2; me_d1; me_d2; me_d3]) *)

        (PEX_THIS: pex = if side then pex1 else pex2)
        (* (AT_LEAST_ONE_COMPL: pex1 = Compl \/ pex2 = Compl) *)

        (TID_CTRL: tid = side2tid side)
        (INBOX: inb_cb = drop_self_entry side inb_c)
        (SYNC_TIME: Nat.divide period t)
        (ST_EQ: st = SNode.State
                       tid (ITrSNode.to_snode
                              (ctrl_mod (Z.of_nat tid)))
                       inb_cb
                       (option_map (fun cst => Ret cst) ast_c))
        (MATCH: option_rel1
                  (match_ctrl_state
                     aq tout (is_active_side asd side) pex)
                  ast_c)
        (WF_CTRL: option_rel1 CtrlState.wf ast_c)

        (STEP: SNode.step sntz num_tasks mcasts
                          t st es out st')
        (NEXT_ABST_CTRL: next pex1 pex2 inb_c asd aq tout =
                         (asd', aq', tout', owner_new))
    : exists (pex': pexec_t) (hb_out: bytes?)
        (ast_c': CtrlState.t?)
    ,
      <<MATCH_CTRL': option_rel1 (match_ctrl_state
                                    aq' tout' (is_active_side asd' side) pex')
                                 ast_c'>> /\
      <<WF_CTRL': option_rel1 CtrlState.wf ast_c'>> /\
      <<HB': hb_of_abst_ctrl (is_active_side asd' side)
                             aq' tout' pex' hb_out>> /\
      <<INCOMPL_FLAG:
        if is_compl pex' then es = [embed (cevt t)]
        else es = [] >> /\
      <<CTRL_OUT_RW: forall tid',
          SNode.get_outbox_msg_by_dest tid' out =
          if tid' =? 1 then
            (if side then None else hb_out)
          else if tid' =? 2 then
                 (if side then hb_out else None)
               else if andb (3 <=? tid') (tid' <=? 5) then
                      msg_c2d (is_active_side asd' side)
                               pex' aq' tout' tid'
                    else None>> /\
      <<ST_EQ': st' = SNode.State
                        tid (ITrSNode.to_snode
                               (ctrl_mod (Z.of_nat tid)))
                        [None; None; None; None; None; None]
                        (option_map (fun cst => Ret cst) ast_c')
                        >>.
  Proof.
    subst.
    destruct ast_c as [cst |]; ss.
    - inv MATCH.
      + (* init *)

        assert (NEXT_ASD_NOT_ME: next_active_side me_con me_c1 me_c2 asd = negb side).
        { unfold next_active_side.
          inv WF.
          symmetry in INBOX_EQ. clarify.

          destruct side; ss.
          - subst pex1.
            desH AT_LEAST_ONE_COMPL; ss. subst.
            inv ENTRY_C1; ss.
            inv ENTRY_C2; ss.
            desf.
          - subst pex2.
            desH AT_LEAST_ONE_COMPL; ss. subst.
            inv ENTRY_C1; ss.
            inv ENTRY_C2; ss.
            desf.
        }

        assert (DROP_NOTHING:
                  drop_self_entry
                    side [me_con; me_c1; me_c2; me_d1; me_d2; me_d3] =
                  [me_con; me_c1; me_c2; me_d1; me_d2; me_d3]).
        { unfold drop_self_entry.
          destruct side.
          - cut (me_c1 = None).
            { intro R. rewrite R. ss. }
            inv WF. inv ENTRY_C1. clarify. ss.
          - cut (me_c2 = None).
            { intro R. rewrite R. ss. }
            inv WF. inv ENTRY_C2. clarify. ss.
        }
        rewrite DROP_NOTHING in *.

        inv STEP.
        existT_elim. subst.
        inv RUN_PERIOD; ss.
        { exists Nothing, None, None.
          splits; ss.
          - econs. ss.
          - intro tid'.
            unfold msg_c2d.
            repeat rewrite if_both_eq.
            destruct tid'; ss.
        }

        inv PERIOD_BEGIN. ss. clarify.
        pose (pex_other := if side then pex2 else pex1).
        assert (PEX_OTHER_COMPL: pex_other = Compl).
        { inv WF.
          symmetry in INBOX_EQ. clarify.
          subst pex_other.
          destruct side; ss.
          - des; clarify.
          - des; clarify.
        }

        unfold ctrl_job, job_controller_itree in STAR.
        hexploit ctrl_sync_update; eauto; ss.
        { econs 1; eauto. }
        s. unfold pex_prev_active. s.
        rewrite NEXT_ASD_NOT_ME.

        i. des.
        rewrite AQ_UPDQ, AQ_NOWN in *. clarify.
        rewrite DROP_NOTHING in UPD.
        rewrite UPD in STAR.

        hexploit send_grant_aux; eauto.
        { (* rewrite NEXT_ASD_NOT_ME. *)
          destruct side; ss. }
        i. des.
        { subst.
          exists Nothing, None, None.
          splits; ss.
          - econs; ss.
          - i. unfold msg_c2d. ss.
            repeat rewrite if_both_eq.
            repeat (destruct tid'; ss).
        }
        clear STAR. rename STAR' into STAR.

        rewrite NEXT_ASD_NOT_ME in *.
        replace (is_active_side (negb side) side)
          with false in *.
        2: { destruct side; ss. }

        hexploit send_hb_aux.
        { eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
        { destruct out1; ss.
          destruct out1; ss.
          unfold SNode.check_available,
          SNode.check_available1; ss.
          specialize (OUTBOX1 1). ss.
          unfold SNode.get_outbox_msg_by_dest in OUTBOX1.
          ss. clarify.
        }
        { destruct out1; ss.
          destruct out1; ss.
          destruct out1; ss.
          unfold SNode.check_available,
          SNode.check_available1; ss.
          specialize (OUTBOX1 2). ss.
          unfold SNode.get_outbox_msg_by_dest in OUTBOX1.
          ss. clarify.
        }
        i. des.
        { exists Nothing, None, None.
          subst.
          unfold msg_c2d. ss.
          repeat rewrite if_both_eq.

          splits; ss.
          - econs. ss.
          - intro tid'.
            repeat rewrite if_both_eq.
            rewrite OUTBOX1.
            destruct (Z.eqb_spec (Z.of_nat tid') Z_mone); ss.
            exfalso. unfold Z_mone in *. nia.
        }
        clear STAR. rename STAR' into STAR.
        guardH HB_EQ.

        assert (HB_OF_AC: forall pex,
                   pex = SendHB \/ pex = Compl ->
                   hb_of_abst_ctrl false aq' tout' pex (Some hb)).
        { intros pex [SHB | CMPL].
          - subst pex. inv MATCH'.
            econs; eauto.
            rewrite HB_EQ.
            rewrite CtrlState_to_bytes_inv; eauto.
          - subst pex. inv MATCH'.
            econs; eauto.
            rewrite HB_EQ.
            rewrite CtrlState_to_bytes_inv; eauto.
        }

        hexploit ctrl_compl_aux; eauto. i. des.
        { exists SendHB, (Some hb), None.
          inv MATCH'.
          splits; eauto; ss.

          intro tid'.
          rewrite OUTBOX'.
          rewrite OUTBOX1.

          destruct side.
          + repeat (destruct tid'; ss).
          + repeat (destruct tid'; ss).
        }
        subst.

        exists Compl, (Some hb), ocst'.
        splits; eauto; ss.
        { destruct ocst'; ss. subst. ss. }
        { destruct ocst'; ss. subst. ss. }

        intro tid'.
        rewrite OUTBOX'.
        rewrite OUTBOX1.
        repeat (destruct tid'; ss).

      + pose (asd'':= next_active_side me_con me_c1 me_c2 asd).
        fold asd'' in NEXT_ABST_CTRL.

        inv STEP.
        existT_elim. subst.
        inv RUN_PERIOD; ss.
        { exists Nothing, None, None.
          splits; ss.
          - econs. ss.
          - intro tid'.
            unfold msg_c2d.
            repeat rewrite if_both_eq.
            destruct tid'; ss.
        }

        inv PERIOD_BEGIN. ss. clarify.
        unfold ctrl_job, job_controller_itree in STAR.

        hexploit ctrl_sync_update; eauto; ss.
        { econs 2; eauto. }
        i. des.
        unfold pex_prev_active in AQ_UPDQ.
        simpl in AQ_UPDQ.

        rewrite AQ_UPDQ, AQ_NOWN in *. clarify.
        rewrite UPD in STAR.

        hexploit send_grant_aux; eauto.
        { fold asd''.
          destruct (is_active_side asd'' side); ss.
          destruct owner_new as [tid_new|].
          2: { ss. }

          hexploit aq_new_owner_grant_msg_loc; eauto.
          intro GR.
          hexploit wf_grant_msg_loc_dev_tid; eauto.
          rewrite GR. s.
          intro IS_DEV. r in IS_DEV.
          ss. des; subst; ss.
        }
        i. des.
        { subst.
          exists Nothing, None, None.
          splits; ss.
          - econs; ss.
          - i. unfold msg_c2d. ss.
            repeat rewrite if_both_eq.
            repeat (destruct tid'; ss).
        }
        clear STAR. rename STAR' into STAR.

        hexploit aq_new_owner_grant_msg_loc; eauto.
        intro GRANT_MSG_LOC.
        hexploit wf_grant_msg_loc_dev_tid; eauto.
        rewrite GRANT_MSG_LOC.
        intro OWNER_NEW_DEV_TID.
        fold asd'' in UPD, MATCH', OUTBOX1.

        hexploit send_hb_aux.
        { eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
        { destruct out1; ss.
          destruct out1; ss.
          unfold SNode.check_available,
          SNode.check_available1; ss.
          specialize (OUTBOX1 1).
          unfold SNode.get_outbox_msg_by_dest in OUTBOX1.
          ss. clarify.
          destruct (is_active_side asd'' side); ss.

          match goal with
          | |- context[if ?x then _ else _] =>
            replace x with false
          end.
          { ss. }

          destruct (grant_msg_loc aq' tout') eqn: GR.
          2: { ss. }
          hexploit wf_grant_msg_loc_dev_tid.
          { eauto. }
          { rewrite GR. ss.
            clear. intro DEV. r in DEV. ss.
            des; subst; ss.
          }
        }
        { destruct out1; ss.
          destruct out1; ss.
          destruct out1; ss.
          unfold SNode.check_available,
          SNode.check_available1; ss.
          specialize (OUTBOX1 2).
          unfold SNode.get_outbox_msg_by_dest in OUTBOX1.
          ss. clarify.
          destruct (is_active_side asd'' side); ss.

          match goal with
          | |- context[if ?x then _ else _] =>
            replace x with false
          end.
          { ss. }

          destruct (grant_msg_loc aq' tout') eqn: GR.
          2: { ss. }
          hexploit wf_grant_msg_loc_dev_tid.
          { eauto. }
          { rewrite GR. ss.
            clear. intro DEV. r in DEV. ss.
            des; subst; ss.
          }
        }
        i.
        des.
        { exists Update, None, None.
          subst.
          unfold msg_c2d. ss.
          repeat rewrite if_both_eq.

          splits; ss.
          - econs. ss.
          - intro tid'.
            rewrite OUTBOX1.
            destruct (is_active_side asd'' side).
            2: { repeat (destruct tid'; ss). }

            destruct (grant_msg_loc aq' tout'); ss.
            2: { repeat (destruct tid'; ss). }

            clear - OWNER_NEW_DEV_TID. r in OWNER_NEW_DEV_TID.
            rewrite CompcertLemmas.Nat2Z_inj_eqb.
            rewrite Nat.eqb_sym.
            destruct (Nat.eqb_spec n tid'); ss.
            2: { repeat (destruct tid'; ss). }
            subst.
            des; subst; ss.
        }

        clear STAR. rename STAR' into STAR.
        guardH HB_EQ.

        assert (HB_OF_AC: forall pex,
                   pex = SendHB \/ pex = Compl ->
                   hb_of_abst_ctrl (is_active_side asd'' side)
                                   aq' tout' pex (Some hb)).
        { intros pex [SHB | CMPL].
          - subst pex. inv MATCH'.
            econs; eauto.
            + rewrite HB_EQ.
              rewrite CtrlState_to_bytes_inv; eauto.
            + destruct (is_active_side asd'' side); ss.
          - subst pex. inv MATCH'.
            econs; eauto.
            + rewrite HB_EQ.
              rewrite CtrlState_to_bytes_inv; eauto.
            + destruct (is_active_side asd'' side); ss.
        }

        assert (OUTBOX_FIN_AUX:
                  forall pex tid'
                    (HB_SENT: is_hb_sent pex = true),
                    SNode.get_outbox_msg_by_dest tid' out' =
                    (if tid' =? 1
                     then if side then None else Some hb
                     else
                       if tid' =? 2
                       then if side then Some hb else None
                       else
                         if (match tid' with
                             | S (S (S _)) => true
                             | _ => false
                             end && (tid' <=? 5))%bool
                         then msg_c2d (is_active_side asd'' side) pex aq' tout' tid'
                         else None)).
        { intros pex' tid' PEX.
          rewrite OUTBOX'.
          rewrite OUTBOX1.

          destruct (is_active_side asd'' side).
          2: {
            replace (Z.of_nat tid' =? Z_mone)%Z with false.
            2: { clear.
                 destruct (Z.eqb_spec (Z.of_nat tid') Z_mone); ss.
                 unfold Z_mone in *. nia. }
            unfold msg_c2d.
            rewrite Bool.andb_false_r.
            rewrite if_both_eq. ss.
          }

          unfold msg_c2d.
          rewrite Bool.andb_true_r.
          destruct (grant_msg_loc aq' tout') as [tid_g1|]; ss.
          2: {
            clarify.
            repeat rewrite if_both_eq.
            repeat (destruct tid'; ss).
          }
          clarify.

          clear - OWNER_NEW_DEV_TID PEX.
          ss. r in OWNER_NEW_DEV_TID.
          replace (is_updated pex') with true.
          2: { destruct pex'; ss. }

          rewrite CompcertLemmas.Nat2Z_inj_eqb.
          rewrite (Nat.eqb_sym tid' tid_g1).
          destruct (Nat.eqb_spec tid_g1 tid'); ss.
          2: { repeat (destruct tid'; ss). }
          subst.
          des; subst; ss.
        }

        hexploit ctrl_compl_aux; eauto. i. des.
        { exists SendHB, (Some hb), None.
          inv MATCH'.
          splits; eauto; ss.
        }

        exists Compl, (Some hb), ocst'.
        splits; eauto; ss.
        { destruct ocst'; ss. subst. ss. }
        { destruct ocst'; ss. subst. ss. }
        { subst out. eauto. }
        { destruct ocst'; subst; ss. }

    - (* None *)
      exists Nothing, None.
      inv STEP.
      + (* Still None *)
        exists None.
        splits; ss.
        * econs; ss.
        * intro tid'.
          unfold msg_c2d. ss.
          repeat rewrite if_both_eq.
          destruct tid'; ss.
      + (* Turning on *)
        exists (Some CtrlState.init).
        splits; eauto; ss.
        * econs; ss.
        * econs; ss.
          repeat econs; ss.
        * econs. ss.
        * intro tid'.
          unfold msg_c2d. ss.
          repeat rewrite if_both_eq.
          destruct tid'; ss.
        * inv INIT_APP_STATE. ss.
  Qed.

End CTRL_1STEP.










Section PRE_LEMMAS.
  Import AbstCtrl.

  Variable sys: @SyncSys.t obsE bytes.
  Variable tm_init: nat.
  Hypothesis PERIOD_POS: SyncSys.period sys <> 0.
  Let dsys: DSys.t := SyncSys.as_dsys sys tm_init.
  Let period: nat := SyncSys.period sys.

  Let sntz := fun bs => Some (RTSysEnv.resize_bytes 8 bs).
  Let mcasts := [[tid_ctrl1; tid_ctrl2]].
  Hypothesis SNTZ_EQ: sntz = (SyncSys.sanitize_msg sys).
  Hypothesis MCASTS_EQ: mcasts = (SyncSys.mcasts sys).

  Lemma pre_ctrl_1step
        (b: bool)
        t tid hb1 hb2
        ment_con ast_c
        md1 md2 md3
        st es out st'
        (TID_CTRL_EQ: tid = if b then tid_ctrl1 else tid_ctrl2)
        (MENT_CON: option_rel1 (fun m => m = toggle_msg) ment_con)
        (ST_EQ: st = SNode.State
                       tid (ITrSNode.to_snode
                              (ctrl_mod (Z.of_nat tid)))
                       [ment_con; hb1; hb2; md1; md2; md3]
                       (option_map (fun cst => Ret cst) ast_c))
        (AST_C_INIT: option_rel1 (fun cst => cst = CtrlState.init) ast_c)
        (HB_IMPL_FAIL : (if b then hb1 else hb2) <> None ->
                        ast_c = None)
        (DROP_SELF_ENTRY: if b then hb1 = None else hb2 = None)
        (MENT_D1_REL: option_rel1 (fun m => m = rel_msg) md1)
        (MENT_D2_REL: option_rel1 (fun m => m = rel_msg) md2)
        (MENT_D3_REL: option_rel1 (fun m => m = rel_msg) md3)
        (HB_INIT1: option_rel1 (fun hb => exists md',
                                    CtrlState.of_bytes hb =
                                    CtrlState.set_mode
                                      md' CtrlState.init) hb1)
        (HB_INIT2: option_rel1 (fun hb => exists md',
                                    CtrlState.of_bytes hb =
                                    CtrlState.set_mode
                                      md' CtrlState.init) hb2)

        (SYNC_TIME: Nat.divide period t)
        (STEP: SNode.step sntz num_tasks mcasts
                          t st es out st')
    : exists (cst: (CtrlState.t)?) (hb1' hb2': bytes?)
        (md: CtrlState.mode_t),
      <<MODE_EQ: md = match hb1, hb2 with
                      | None, None =>
                        if b then CtrlState.Active
                        else CtrlState.Standby
                      | _, _ => CtrlState.Standby
                      end>> /\
      <<HB1': option_rel1
                (fun hb => CtrlState.of_bytes hb =
                        CtrlState.set_mode md CtrlState.init) hb1'>> /\
      <<HB2': option_rel1
                (fun hb => CtrlState.of_bytes hb =
                        CtrlState.set_mode md CtrlState.init) hb2'>> /\
      <<CTRL_OUT_RW: forall tid',
          SNode.get_outbox_msg_by_dest tid' out =
          if tid' =? 1 then hb1'
          else if tid' =? 2 then hb2'
               else None>> /\
      <<NO_SELFLOOP_MSGS: if b then hb1' = None else hb2' = None>> /\
      <<CTRL_ST_EQ': st' = SNode.State
                             tid (ITrSNode.to_snode
                                    (ctrl_mod (Z.of_nat tid)))
                             [None; None; None; None; None; None]
                             (option_map (fun st => Ret st) cst)>> /\
     <<CTRL_CASES:
            ((* not starting *)
              <<CTRL_ES: es = []>> /\
              <<HB_IMPL_FAIL: (hb1' = None /\ hb2' = None) \/
                              (ast_c = Some CtrlState.init /\cst = None) >> /\
              <<AST_INIT: option_rel1 (fun st => st = CtrlState.init) cst>>) \/
            ((* controller start *)
              <<CTRL_ES: es = [embed (cevt t)]>> /\
              <<SEND_HB: if b then hb2' <> None else hb1' <> None>> /\
              <<AST_INIT: option_rel1 (fun st => st = CtrlState.set_mode md CtrlState.init) cst>> /\
              <<NO_HB_SENT: ast_c = Some CtrlState.init>>
            )>>.
  Proof.
    subst. ss.
    destruct ast_c; cycle 1; ss.
    { (* Off *)
      inv STEP.
      - exists None, None, None.
        esplits; eauto; ss.
        + unfold SNode.get_outbox_msg_by_dest.
          intro tid'. destruct tid'; ss. desf.
        + desf.
        + left. eauto.
      - exists (Some CtrlState.init), None, None.
        inv INIT_APP_STATE.
        esplits; eauto; ss.
        + unfold SNode.get_outbox_msg_by_dest.
          intro tid'. destruct tid'; ss. desf.
        + desf.
        + left. eauto.
    }
    subst.

    inv STEP. existT_elim. subst.
    inv RUN_PERIOD.
    { (* run_period failed *)
      exists None, None, None.
      esplits; eauto; ss.
      - unfold SNode.get_outbox_msg_by_dest.
        intro tid'. destruct tid'; ss. desf.
      - desf.
      - left. eauto.
    }

    inv PERIOD_BEGIN. ss. clarify.
    unfold ctrl_job, job_controller_itree in STAR. ss.

    inv STAR.
    { (* istar_fail *)
      exists None, None, None.
      esplits; eauto; ss.
      - unfold SNode.get_outbox_msg_by_dest.
        intro tid'. repeat (destruct tid'; ss).
      - desf.
      - left. eauto.
    }
    { (* istar_base *)
      exfalso.
      ss. r in FINAL.
      unfold ITrSNode.period_end in FINAL.
      desf.
    }

    assert (HB_RCVED: exists hb_r, hb_r = if b then hb2 else hb1).
    { esplits; eauto. }
    des. guardH HB_RCVED.

    destruct hb_r as [hb|].
    - (* got hb *)
      match type of ASTEP with
      | context[update_owner ?x] =>
        replace x with (CtrlState.set_mode
                          CtrlState.Standby CtrlState.init)
          in ASTEP
      end.
      2: {
        clear - HB_RCVED HB_INIT1 HB_INIT2 DROP_SELF_ENTRY
                         MENT_D1_REL MENT_D2_REL MENT_D3_REL.
        destruct b; ss.
        - unguard. subst. ss. des.
          unfold update_istate, sync_istate. ss.
          erewrite copy_state_from_hb_spec by eauto.
          ss. unfold update_queue. ss.
          rewrite apply_devmsg_empty with (tid_d:=3%Z) by ss.
          rewrite apply_devmsg_empty with (tid_d:=4%Z) by ss.
          rewrite apply_devmsg_empty with (tid_d:=5%Z) by ss.
          ss.
        - unguard. subst. ss. des.
          unfold update_istate, sync_istate. ss.
          erewrite copy_state_from_hb_spec by eauto.
          ss. unfold update_queue. ss.
          rewrite apply_devmsg_empty with (tid_d:=3%Z) by ss.
          rewrite apply_devmsg_empty with (tid_d:=4%Z) by ss.
          rewrite apply_devmsg_empty with (tid_d:=5%Z) by ss.
          ss.
      }

      ss.
      simpl_itree_hyp ASTEP.
      unfold send_hb_itree in ASTEP.
      simpl_itree_hyp ASTEP. ss.
      replace (Z.to_nat (3 - Z.of_nat (if b then 1 else 2)))
        with (if b then 2 else 1) in ASTEP.
      2: { destruct b; ss. }

      inv ASTEP.
      { inv TAU_STEP. ss. }
      { inv AT_EVENT. existT_elim. clarify. }

      inv AT_EVENT. existT_elim. ss. clarify.
      existT_elim. clarify.
      inv AFT_EVENT. existT_elim. ss. clarify.
      existT_elim. clarify.
      unfold RTSysEnv.resize_bytes in ASTAR'. ss.

      rename ASTAR' into STAR.
      inv STAR.
      { (* istar_fail *)
        exists None.
        unguard.
        destruct b; subst.
        - clear.
          exists None, (Some (CtrlState.to_bytes
                           (CtrlState.set_mode
                              CtrlState.Standby CtrlState.init))).
          esplits; ss; eauto.
          + intro tid'. repeat (destruct tid'; ss).
          + left. eauto.
        - clear.
          exists (Some (CtrlState.to_bytes
                     (CtrlState.set_mode
                        CtrlState.Standby CtrlState.init))),
          None.
          esplits; ss; eauto.
          + intro tid'. repeat (destruct tid'; ss).
          + left. eauto.
      }
      { (* istar_base *)
        exfalso. ss. }

      simpl_itree_hyp ASTEP.
      inv ASTEP; cycle 2.
      { inv AT_EVENT. ss. existT_elim. clarify. }
      { inv TAU_STEP. ss. }

      inv AT_EVENT. existT_elim. ss. clarify.
      existT_elim. ss. clarify.
      inv AFT_EVENT. existT_elim. ss. clarify.
      existT_elim. ss. clarify.
      destruct r; ss.

      inv ASTAR'; cycle 2.
      { inv ASTEP; ss.
        - inv TAU_STEP. ss.
        - inv AT_EVENT. ss.
        - inv AT_EVENT. ss.
      }
      { (* istar_fail *)
        unguard.
        exists None.
        destruct b; subst; ss.
        - exists None, (Some (CtrlState.to_bytes
                           (CtrlState.set_mode
                              CtrlState.Standby
                              CtrlState.init))).
          esplits; eauto; ss.
          + intro tid'. repeat (destruct tid'; ss).
          + right. esplits; eauto. ss.

        - exists (Some (CtrlState.to_bytes
                     (CtrlState.set_mode
                        CtrlState.Standby
                        CtrlState.init))), None.
          esplits; eauto; ss.
          + intro tid'. repeat (destruct tid'; ss).
          + right.
            esplits; eauto. ss.
      }
      { (* success *)
        unguard.
        eexists (Some _).
        destruct b; subst; ss.
        - exists None, (Some (CtrlState.to_bytes
                           (CtrlState.set_mode
                              CtrlState.Standby
                              CtrlState.init))).
          esplits; eauto; ss.
          + intro tid'. repeat (destruct tid'; ss).
          + right. splits; eauto. ss.
        - exists (Some (CtrlState.to_bytes
                     (CtrlState.set_mode
                        CtrlState.Standby
                        CtrlState.init))), None.
          esplits; eauto; ss.
          + intro tid'. repeat (destruct tid'; ss).
          + right. splits; eauto. ss.
      }
    - (* didn't get hb *)
      match type of ASTEP with
      | context[update_owner ?x] =>
        replace (update_owner x) with
            ({|
                CtrlState.mode := if b then CtrlState.Active
                                  else CtrlState.Standby;
                CtrlState.timeout := 0;
                CtrlState.queue_begin := 0;
                CtrlState.queue_end := 0;
                CtrlState.queue := [0%Z; 0%Z; 0%Z; 0%Z] |},
             Z_mone)
            (* (CtrlState.set_mode *)
            (*               (if b then CtrlState.Active *)
            (*                else CtrlState.Standby) *)
            (*               CtrlState.init) *)
          in ASTEP
      end.
      2: {
        clear - HB_RCVED HB_INIT1 HB_INIT2 DROP_SELF_ENTRY
                         MENT_D1_REL MENT_D2_REL MENT_D3_REL.
        destruct b; ss.
        - unguard. subst. ss. des.
          unfold update_istate, sync_istate. ss.
          unfold update_queue. ss.
          rewrite apply_devmsg_empty with (tid_d:=3%Z) by ss.
          rewrite apply_devmsg_empty with (tid_d:=4%Z) by ss.
          rewrite apply_devmsg_empty with (tid_d:=5%Z) by ss.
          ss.
        - unguard. subst. ss. des.
          unfold update_istate, sync_istate. ss.
          unfold update_queue. ss.
          rewrite apply_devmsg_empty with (tid_d:=3%Z) by ss.
          rewrite apply_devmsg_empty with (tid_d:=4%Z) by ss.
          rewrite apply_devmsg_empty with (tid_d:=5%Z) by ss.
          ss.
      }

      ss.
      simpl_itree_hyp ASTEP.
      unfold send_hb_itree in ASTEP.
      simpl_itree_hyp ASTEP. ss.
      replace (Z.to_nat (3 - Z.of_nat (if b then 1 else 2)))
        with (if b then 2 else 1) in ASTEP.
      2: { destruct b; ss. }

      inv ASTEP.
      { inv TAU_STEP. ss. }
      { inv AT_EVENT. existT_elim. clarify. }

      inv AT_EVENT. existT_elim. ss. clarify.
      existT_elim. clarify.
      inv AFT_EVENT. existT_elim. ss. clarify.
      existT_elim. clarify.
      unfold RTSysEnv.resize_bytes in ASTAR'. ss.

      rename ASTAR' into STAR.
      inv STAR.
      { (* istar_fail *)
        exists None.
        unguard.
        destruct b; subst.
        - clear.
          eexists None, (Some _).
          esplits; ss; eauto; cycle 1.
          { intro tid'. repeat (destruct tid'; ss). }
          { left. eauto. }
          ss.
        - clear.
          eexists (Some _), None.
          esplits; ss; eauto; cycle 1.
          { intro tid'. repeat (destruct tid'; ss). }
          { left. eauto. }
          ss.
      }
      { (* istar_base *)
        exfalso. ss. }

      simpl_itree_hyp ASTEP.
      inv ASTEP; cycle 2.
      { inv AT_EVENT. ss. existT_elim. clarify. }
      { inv TAU_STEP. ss. }

      inv AT_EVENT. existT_elim. ss. clarify.
      existT_elim. ss. clarify.
      inv AFT_EVENT. existT_elim. ss. clarify.
      existT_elim. ss. clarify.
      destruct r; ss.

      inv ASTAR'; cycle 2.
      { inv ASTEP; ss.
        - inv TAU_STEP. ss.
        - inv AT_EVENT. ss.
        - inv AT_EVENT. ss.
      }
      { (* istar_fail *)
        unguard.
        exists None.
        destruct b; subst; ss.
        - exists None, (Some (CtrlState.to_bytes
                           (CtrlState.set_mode
                              CtrlState.Active
                              CtrlState.init))).
          esplits; eauto; ss.
          + intro tid'. repeat (destruct tid'; ss).
          + right.
            esplits; eauto. ss.
        - exists (Some (CtrlState.to_bytes
                     (CtrlState.set_mode
                        CtrlState.Standby
                        CtrlState.init))), None.
          esplits; eauto; ss.
          + intro tid'. repeat (destruct tid'; ss).
          + right.
            esplits; eauto. ss.
      }
      { (* success *)
        unguard.
        destruct b; subst; ss.
        - eexists (Some _), None,
          (Some (CtrlState.to_bytes
                   (CtrlState.set_mode
                      CtrlState.Active
                      CtrlState.init))).
          esplits; eauto; ss.
          + intro tid'. repeat (destruct tid'; ss).
          + right. splits; eauto. ss.
        - eexists (Some _),
          (Some (CtrlState.to_bytes
                   (CtrlState.set_mode
                      CtrlState.Standby
                      CtrlState.init))), None.
          esplits; eauto; ss.
          + intro tid'. repeat (destruct tid'; ss).
          + right. splits; eauto. ss.
      }
  Qed.


  Lemma pre_dev_1step
        tid st ast_d
        t es out st'
        (TID_DEV: is_dev_tid tid)
        (NST_D: st = SNode.State
                       tid snode_dev
                       [None; None; None; None; None; None]
                       (option_map (fun dst => Ret dst) ast_d))
        (INIT: option_rel1 (fun dst => dst = DevState.init) ast_d)
        (SYNC_TIME: Nat.divide period t)
        (STEP: SNode.step sntz num_tasks mcasts
                          t st es out st')
    : exists (dst: (DevState.t)?) (ment_d: bytes?),
      <<MENT_D: option_rel1 (fun m => m = rel_msg) ment_d>> /\
      <<DEV_OUT_RW: forall tid',
          SNode.get_outbox_msg_by_dest tid' out =
          if orb (tid' =? 1) (tid' =? 2) then ment_d
          else None>> /\
      <<DEV_ST_EQ': st' = SNode.State
                            tid snode_dev
                            [None; None; None; None; None; None]
                            (option_map (fun st => Ret st) dst)>> /\
      <<DEV_CASE:
      ((* NOT COMPLETED *)
          <<DEV_ES: es = []>> /\
          <<DEVMSG_IMPL_FAIL: dst = None \/ ment_d = None>> /\
          <<AST_TR_INIT: option_rel1 (fun st => st = DevState.init) dst>>
        ) \/
       ((* SUCCESS *)
        <<DEV_ES: es = [embed (cevt t)]>> /\
        <<MENT_D_REL: ment_d = Some rel_msg>> /\
        <<DEV_ST_TR': option_rel1 (fun dst_tr => dst_tr = DevState.mk (Some false) 0) dst>>)>>.
  Proof.
    subst. ss.
    destruct ast_d; cycle 1; ss.
    { (* Off *)
      inv STEP.
      - exists None, None.
        splits; eauto.
        unfold SNode.get_outbox_msg_by_dest.
        intro tid'. destruct tid'; ss; desf.
      - exists (Some DevState.init), None.
        inv INIT_APP_STATE.
        splits; eauto; ss.
        + unfold SNode.get_outbox_msg_by_dest.
          intro tid'. destruct tid'; ss; desf.
        + eauto.
    }
    subst.

    inv STEP. existT_elim. subst.
    inv RUN_PERIOD.
    { (* run_period failed *)
      exists None, None.
      splits; eauto; ss.
      unfold SNode.get_outbox_msg_by_dest.
      - intro tid'. destruct tid'; ss; desf.
      - eauto.
    }

    inv PERIOD_BEGIN. ss. clarify.
    unfold dev_job, job_device_itree in STAR. ss.

    inv STAR.
    { (* istar_fail *)
      exists None, None.
      splits; eauto.
      unfold SNode.get_outbox_msg_by_dest.
      intro tid'. repeat (destruct tid'; ss).
    }
    { (* istar_base *)
      exfalso. ss. }

    simpl_itree_hyp ASTEP. ss.

    inv ASTEP.
    { inv TAU_STEP. ss. }
    { inv AT_EVENT. existT_elim. clarify. }

    inv AT_EVENT. existT_elim. ss. clarify.
    existT_elim. clarify.
    inv AFT_EVENT. existT_elim. ss. clarify.
    existT_elim. clarify.
    unfold RTSysEnv.resize_bytes in ASTAR'. ss.

    rename ASTAR' into STAR.
    inv STAR.
    { (* istar_fail *)
      exists None, (Some rel_msg).
      splits; eauto; ss.
      intro tid'. repeat (destruct tid'; ss).
    }
    { (* istar_base *)
      exfalso. ss. }

    simpl_itree_hyp ASTEP.
    inv ASTEP; cycle 2.
    { inv AT_EVENT. ss. existT_elim. clarify. }
    { inv TAU_STEP. ss. }

    inv AT_EVENT. existT_elim. ss. clarify.
    existT_elim. ss. clarify.
    inv AFT_EVENT. existT_elim. ss. clarify.
    existT_elim. ss. clarify.
    destruct r; ss.

    inv ASTAR'; cycle 2.
    { inv ASTEP; ss.
      - inv TAU_STEP. ss.
      - inv AT_EVENT. ss.
      - inv AT_EVENT. ss.
    }
    { (* istar_fail *)
      exists None.
      esplits; eauto; ss.
      intro tid'. repeat (destruct tid'; ss).
    }
    { (* success *)
      eexists (Some (DevState.mk (Some false) 0)).
      esplits; eauto; cycle 1.
      { intro tid'. repeat (destruct tid'; ss). }
      { right. ss. }
      ss.
    }
  Qed.

  Lemma console_1step
        st ast
        t es out st'
        (NST: st = SNode.State
                     tid_con snode_con
                     [None; None; None; None; None; None]
                     (option_map (fun x => Ret x) ast))
        (* (INIT: option_rel1 (fun dst => dst = tt) ast) *)
        (SYNC_TIME: Nat.divide period t)
        (STEP: SNode.step sntz num_tasks mcasts
                          t st es out st')
    : exists (ast': unit?) (ment_con: bytes?),
      <<CONSOLE_ES: Forall (fun e => exists e',
                                DSys.filter_nb1 e = Some e' /\
                                ~ dev_event e') es>> /\

      <<MENT_CON_TGL:
        option_rel1 (fun m => m = toggle_msg) ment_con>> /\
      <<OUT_CON_RW: forall tid,
          SNode.get_outbox_msg_by_dest tid out =
          if orb (tid =? 1) (tid =? 2) then ment_con
          else None>> /\
      <<CONSOLE_ST_EQ': st' = SNode.State
                                tid_con snode_con
                                [None; None; None;
                                None; None; None]
                                (option_map (fun x => Ret x) ast')>>.
  Proof.
    subst.
    destruct ast; ss.
    2: {
      inv STEP.
      - exists None, None.
        splits; eauto; ss.
        unfold SNode.get_outbox_msg_by_dest.
        intro tid'. destruct tid'; ss. desf.
      - ss. inv INIT_APP_STATE.
        exists (Some tt), None.
        splits; eauto; ss.
        unfold SNode.get_outbox_msg_by_dest.
        intro tid'. destruct tid'; ss. desf.
    }

    inv STEP. existT_elim. clarify.
    inv RUN_PERIOD.
    { exists None, None.
      splits; eauto; ss.
      unfold SNode.get_outbox_msg_by_dest.
      intro tid'. destruct tid'; ss. desf.
    }

    ss.
    inv PERIOD_BEGIN. ss. clarify.
    destruct ast0; ss.

    inv STAR; ss.
    { exists None, None.
      esplits; eauto; ss.
      unfold SNode.get_outbox_msg_by_dest.
      intro tid'. repeat (destruct tid'; ss).
    }

    unfold con_job in ASTEP.
    simpl_itree_hyp ASTEP.

    inv ASTEP; ss; cycle 2.
    { inv AT_EVENT. existT_elim. clarify. }
    { inv TAU_STEP. ss. }

    inv AT_EVENT.
    existT_elim. ss. clarify.
    existT_elim. ss. clarify.
    inv AFT_EVENT. existT_elim. ss. clarify.
    existT_elim. clarify.
    rename ASTAR' into STAR.

    destruct r.
    - inv STAR; ss.
      { exists None, None.
        splits; eauto; ss.
        - econs; ss.
          esplits; ss.
          intro DEV. r in DEV.
          des; ss.
        - unfold SNode.get_outbox_msg_by_dest.
          intro tid'. repeat (destruct tid'; ss).
      }

      simpl_itree_hyp ASTEP.
      inv ASTEP.
      { inv TAU_STEP; ss. }
      { inv AT_EVENT. existT_elim. ss. clarify. }
      inv AT_EVENT. existT_elim. ss. clarify.
      existT_elim. ss. clarify.
      inv AFT_EVENT. existT_elim. ss. clarify.
      existT_elim. clarify.

      rename ASTAR' into STAR.
      inv STAR; ss.
      { exists None, (Some toggle_msg).
        splits; eauto; ss.
        - econs; eauto.
          esplits; ss.
          intro DEV. r in DEV.
          des; ss.
        - intro tid'.
          repeat (destruct tid'; ss).
      }

      inv ASTEP; cycle 2.
      { inv AT_EVENT. existT_elim. ss. clarify. }
      { inv TAU_STEP. ss. }

      inv AT_EVENT. existT_elim. ss. clarify.
      existT_elim. ss. clarify.
      inv AFT_EVENT. existT_elim. ss. clarify.
      existT_elim. ss. clarify.
      destruct r.

      inv ASTAR'; ss.
      { exists None, (Some toggle_msg).
        splits; eauto; ss.
        - econs; ss.
          + esplits; ss.
            intro DEV. r in DEV.
            des; ss.
          + econs; ss.
            esplits; ss.
            intro DEV. r in DEV.
            des; ss.
        - intro tid'. repeat (destruct tid'; ss).
      }
      2: {
        inv ASTEP.
        - inv TAU_STEP. ss.
        - inv AFT_EVENT. existT_elim. ss.
        - inv AFT_EVENT. existT_elim. ss.
      }

      exists (Some tt), (Some toggle_msg).
      splits; eauto; ss.
      + econs; ss.
        * esplits; ss.
          intro DEV. r in DEV.
          des; ss.
        * econs; ss.
          esplits; ss.
          intro DEV. r in DEV.
          des; ss.
      + intro tid'. repeat (destruct tid'; ss).

    - inv STAR; ss.
      { exists None, None.
        splits; eauto.
        - econs; ss.
          esplits; ss.
          intro DEV. r in DEV.
          des; ss.
        - intro tid'. repeat (destruct tid'; ss).
      }

      simpl_itree_hyp ASTEP.
      inv ASTEP; cycle 2.
      { inv AT_EVENT. existT_elim. ss. clarify. }
      { inv TAU_STEP. ss. }

      inv AT_EVENT. existT_elim. ss. clarify.
      existT_elim. ss. clarify.
      inv AFT_EVENT. existT_elim. ss. clarify.
      existT_elim. ss. clarify.
      destruct r.

      inv ASTAR'; ss.
      { exists None, None.
        splits; ss.
        - econs; ss.
          + esplits; eauto; ss.
            intro DEV. r in DEV.
            des; ss.
          + econs; ss.
            esplits; ss.
            intro DEV. r in DEV.
            des; ss.
        - intro tid'. repeat (destruct tid'; ss).
      }
      2: {
        inv ASTEP.
        - inv TAU_STEP. ss.
        - inv AFT_EVENT. existT_elim. ss.
        - inv AFT_EVENT. existT_elim. ss.
      }

      exists (Some tt), None.
      splits; eauto; ss.
      + econs; ss.
        * esplits; ss.
          intro DEV. r in DEV.
          des; ss.
        * econs; ss.
          esplits; ss.
          intro DEV. r in DEV.
          des; ss.
      + intro tid'. repeat (destruct tid'; ss).
  Qed.

  Lemma inv_prsv_pre_1step
        st t
        (PRE: AbstCtrl.pre st)
        (SYS_TIME: t = SyncSys.time st)
        (SYNC_TIME: Nat.divide period t)
    : forall tr st'
        (MSTEPS: msteps dsys 1 st tr st')
    ,
      (<<PRE': AbstCtrl.pre st'>> /\
       <<ONLY_CONSOLE_ALIVE:
         forall tid' t' e'
           (EVENT: event_in_tr tid' t' e' tr),
           tid' = tid_con /\ ~ dev_event e'>>) \/
      ((* DEV_COMPL_FIRST *)
         exists tid_d,
           <<TID_DEV: is_dev_tid tid_d>> /\
           <<DEV_COMPL: event_in_tr tid_d t (cevt t) tr>> /\
           <<CTRL1_NCOMPL: ~ event_in_tr tid_ctrl1 t (cevt t) tr>> /\
           <<CTRL2_NCOMPL: ~ event_in_tr tid_ctrl2 t (cevt t) tr>>) \/
      ((* LOCK SERVICE START *)
        exists actrl,
          <<INV': AbstCtrl.match_state actrl st'>> /\
          <<MATCH_TR_FC:
            match_trace_fc
              (failed_controller actrl) t tr>> /\
          <<NO_DEV_EVENTS:
              forall tid' t' e'
                (EVENT: event_in_tr tid' t' e' tr),
                ~ dev_event e'>>).
  Proof.
    i. inv MSTEPS.
    inv MSTEPS_REST.
    inv STEP; ss.

    clear WAIT.
    renames ess es1 into ess_r tes.
    unfold SyncSys.num_sites in CONS_EVENTS. ss.
    rewrite map_length in CONS_EVENTS.
    eapply DSys_filter_nb_sysstep_inv in FILTER_NB.

    inv PRE.

    inv STEPS.
    rename P_HOLDS into STEP_CON.
    renames b c d into es_con out_con st_con'.

    rename FORALL_T into X. inv X. rename P_HOLDS into STEP_C1.
    renames b c d into es_c1 out_c1 st_c1'.
    rename FORALL_T into X. inv X. rename P_HOLDS into STEP_C2.
    renames b c d into es_c2 out_c2 st_c2'.
    rename FORALL_T into X. inv X. rename P_HOLDS into STEP_D1.
    renames b c d into es_d1 out_d1 st_d1'.
    rename FORALL_T into X. inv X. rename P_HOLDS into STEP_D2.
    renames b c d into es_d2 out_d2 st_d2'.
    rename FORALL_T into X. inv X. rename P_HOLDS into STEP_D3.
    renames b c d into es_d3 out_d3 st_d3'.
    inv FORALL_T. ss.

    rewrite <- SNTZ_EQ in STEP_CON, STEP_C1, STEP_C2,
                         STEP_D1, STEP_D2, STEP_D3.
    rewrite <- MCASTS_EQ in STEP_CON, STEP_C1, STEP_C2,
                           STEP_D1, STEP_D2, STEP_D3.

    rename ment_con into ment_con_p.
    renames ment_d1 ment_d2 ment_d3 into
            ment_d1_p ment_d2_p ment_d3_p.


    eapply (pre_ctrl_1step true) in STEP_C1; eauto; cycle 1.
    { econs. }
    nbdes. guardH MODE_EQ.
    renames cst md MODE_EQ into cst1' md1 MODE_EQ1.
    renames CTRL_OUT_RW NO_SELFLOOP_MSGS CTRL_ST_EQ' into
            CTRL_OUT_RW1 NO_SELFLOOP_MSGS1 CTRL_ST_EQ1'.
    renames hb2' HB2' CTRL_CASES into hb'12 HB'12 CTRL_CASES1.
    subst hb1'. clear HB1'.

    eapply (pre_ctrl_1step false) in STEP_C2; eauto; cycle 1.
    { econs. }
    nbdes. guardH MODE_EQ.
    renames cst md MODE_EQ into cst2' md2 MODE_EQ2.
    renames CTRL_OUT_RW NO_SELFLOOP_MSGS CTRL_ST_EQ' into
            CTRL_OUT_RW2 NO_SELFLOOP_MSGS2 CTRL_ST_EQ2'.
    renames hb1' HB1' CTRL_CASES into hb'21 HB'21 CTRL_CASES2.
    subst hb2'. clear HB2'.

    eapply console_1step in STEP_CON; eauto.
    nbdes.

    eapply pre_dev_1step in STEP_D1; eauto; cycle 1.
    { r. ss. eauto. }
    nbdes.
    renames dst ment_d MENT_D into dst1 ment_d1 MENT_D1.
    renames DEV_OUT_RW DEV_ST_EQ' DEV_CASE into
            DEV_OUT_RW1 DEV_ST_EQ1 DEV_CASE1.

    eapply pre_dev_1step in STEP_D2; eauto; cycle 1.
    { r. ss. eauto. }
    nbdes.
    renames dst ment_d MENT_D into dst2 ment_d2 MENT_D2.
    renames DEV_OUT_RW DEV_ST_EQ' DEV_CASE into
            DEV_OUT_RW2 DEV_ST_EQ2 DEV_CASE2.

    eapply pre_dev_1step in STEP_D3; eauto; cycle 1.
    { r. ss. eauto. }
    nbdes.
    renames dst ment_d MENT_D into dst3 ment_d3 MENT_D3.
    renames DEV_OUT_RW DEV_ST_EQ' DEV_CASE into
            DEV_OUT_RW3 DEV_ST_EQ3 DEV_CASE3.

    clear dependent ast_con. clear dependent ast_d1.
    clear dependent ast_d2. clear dependent ast_d3.

    clear ment_con_p ment_d1_p ment_d2_p ment_d3_p
          MENT_CON MENT_D1_REL MENT_D2_REL MENT_D3_REL.

    destruct CTRL_CASES1.
    - nbdes. subst.
      renames HB_IMPL_FAIL AST_INIT into HB_FAIL1 CTRL_INIT1.

      assert (CTRL1_NCOMPL: ~ event_in_tr 1 tm (cevt tm) tr).
      { clear - FILTER_NB CONS_EVENTS.
        cut (nth_error tr 1 = Some [(tm, [])]).
        { clear. intros TR1 C. inv C.
          clarify.
          ss. des; ss. clarify. }
        eapply Forall3_nth2 with (n:=1) in CONS_EVENTS.
        2: { ss. }
        des. subst.
        rewrite NTH3. clear NTH3. f_equal. f_equal.

        eapply Forall2_nth1 with (n:=1) in FILTER_NB.
        2: { ss. }
        des. clarify.
        clear NTH2.
        unfold DSys.filter_nb_localstep in P_FA. ss. clarify.
      }

      destruct CTRL_CASES2.
      + (* both ctrl failed *)
        nbdes. subst.
        renames HB_IMPL_FAIL AST_INIT into HB_FAIL2 CTRL_INIT2.

        assert (CTRL2_NCOMPL: ~ event_in_tr 2 tm (cevt tm) tr).
        { clear - FILTER_NB CONS_EVENTS.
          cut (nth_error tr 2 = Some [(tm, [])]).
          { clear. intros TR2 C. inv C.
            clarify.
            ss. des; ss. clarify. }
          eapply Forall3_nth2 with (n:=2) in CONS_EVENTS.
          2: { ss. }
          des. subst.
          rewrite NTH3. clear NTH3. f_equal. f_equal.

          eapply Forall2_nth1 with (n:=2) in FILTER_NB.
          2: { ss. }
          des. clarify.
          clear NTH2.
          unfold DSys.filter_nb_localstep in P_FA. ss. clarify.
        }

        destruct DEV_CASE1.
        2: {
          nbdes. subst.
          (* service start failed *)
          right. left.
          exists tid_dev1.

          esplits; ss.
          - r. ss. eauto.
          - clear - FILTER_NB CONS_EVENTS.
            eapply Forall2_nth1 with (n:=3) in FILTER_NB.
            2: { ss. }
            des.
            destruct e2 as [t' es_d].
            renames NTH2 P_FA into TES_N FLT_NB.
            eapply filter_nb_localstep_inv in FLT_NB.

            simpl in FLT_NB. des. clarify.
            unfold cevt in *.

            eapply Forall3_nth1 in CONS_EVENTS; eauto.
            des. subst.
            simpl in NTH2. clarify.

            econs; eauto.
            { ss. eauto. }
            clear TES_N NTH3.
            inv FILTERED_NB_EACH. ss. clarify.
            eauto.
        }

        (* d1 no devevts *)
        nbdes. subst.
        rename AST_TR_INIT into DEV_INIT1.

        destruct DEV_CASE2.
        2: {
          nbdes. subst.
          (* service start failed *)
          right. left.
          exists tid_dev2.

          esplits; ss.
          - r. ss. eauto.
          - clear - FILTER_NB CONS_EVENTS.
            eapply Forall2_nth1 with (n:=4) in FILTER_NB.
            2: { ss. }
            des.
            destruct e2 as [t' es_d].
            renames NTH2 P_FA into TES_N FLT_NB.
            eapply filter_nb_localstep_inv in FLT_NB.

            simpl in FLT_NB. des. clarify.
            unfold cevt in *.

            eapply Forall3_nth1 in CONS_EVENTS; eauto.
            des. subst.
            simpl in NTH2. clarify.

            econs; eauto.
            { ss. eauto. }
            clear TES_N NTH3.
            inv FILTERED_NB_EACH. ss. clarify.
            eauto.
        }

        (* d1 no devevts *)
        nbdes. subst.
        rename AST_TR_INIT into DEV_INIT2.

        destruct DEV_CASE3.
        2: {
          nbdes. subst.
          (* service start failed *)
          right. left.
          exists tid_dev3.

          esplits; ss.
          - r. ss. eauto.
          - clear - FILTER_NB CONS_EVENTS.
            eapply Forall2_nth1 with (n:=5) in FILTER_NB.
            2: { ss. }
            des.
            destruct e2 as [t' es_d].
            renames NTH2 P_FA into TES_N FLT_NB.
            eapply filter_nb_localstep_inv in FLT_NB.

            simpl in FLT_NB. des. clarify.
            unfold cevt in *.

            eapply Forall3_nth1 in CONS_EVENTS; eauto.
            des. subst.
            simpl in NTH2. clarify.

            econs; eauto.
            { ss. eauto. }
            clear TES_N NTH3.
            inv FILTERED_NB_EACH. ss. clarify.
            eauto.
        }

        (* d1 no devevts *)
        nbdes. subst.
        rename AST_TR_INIT into DEV_INIT3.

        (* still pre *)
        left.
        esplits; ss.
        2: {
          i. inv EVENT.
          eapply Forall3_nth3 in CONS_EVENTS; eauto.
          clear - CONS_EVENTS FILTER_NB CONSOLE_ES
                              EVTS_AT_T IN_EVTS.
          des. subst.

          assert (<<TID_RANGE: tid' < 6>> /\
                  <<E2_EQ: e2 = []>>).
          { split.
            - apply nth_error_Some1' in NTH2. ss.
            - clear - NTH2.
              repeat (destruct tid' as [|tid']; ss; clarify).
          }
          clear NTH2. des. subst e2.
          destruct e1 as [t'' es'']. ss.
          des; ss. clarify.
          rename NTH1 into TES_N.

          eapply Forall2_nth2 in FILTER_NB; eauto. des.
          destruct e1 as [tm' es'].
          eapply filter_nb_localstep_inv in P_FA.
          des; ss. clarify.
          eapply In_nth_error in IN_EVTS. des.
          rename NTH1 into TR_N.
          eapply Forall2_nth2 in FILTERED_NB_EACH; eauto. des.

          destruct tid' as [| tid']; ss.
          { split; ss.
            clarify.
            eapply Forall_nth1 in CONSOLE_ES; eauto. des.
            clarify. }

          exfalso.
          assert (t' = tm /\ es' = []).
          { repeat (destruct tid' as [|tid']; ss; clarify). }
          des. subst.
          destruct n; ss.
        }

        (* pre invariant *)
        unguard. subst. ss.

        clear HB_INIT1 HB_INIT2.

        do 6 rewrite OUT_CON_RW.
        clear dependent out_con.
        do 6 rewrite CTRL_OUT_RW1.
        clear dependent out_c1.
        do 6 rewrite CTRL_OUT_RW2.
        clear dependent out_c2.
        do 6 rewrite DEV_OUT_RW1.
        clear dependent out_d1.
        do 6 rewrite DEV_OUT_RW2.
        clear dependent out_d2.
        do 6 rewrite DEV_OUT_RW3.
        clear dependent out_d3.
        s. econs; eauto.
        * tauto.
        * tauto.
        * clear - HB'12.
          destruct hb'12 as [hb|]; ss.
          esplits; eauto.
        * clear - HB'21.
          destruct hb'21 as [hb|]; ss.
          esplits; eauto.

      + (* ctrl2 starts *)
        nbdes. subst.
        rename AST_INIT into CTRL_INIT2.
        right. right.

        exists (mk [ment_con; hb'12; hb'21; ment_d1; ment_d2; ment_d3]
              true (Some true) [] 0).

        assert (hb2 = None).
        { clear - HB_IMPL_FAIL2.
          destruct hb2; ss.
          exfalso. hexploit HB_IMPL_FAIL2; ss. }
        subst hb2.

        ss.
        repeat rewrite OUT_CON_RW, CTRL_OUT_RW1, CTRL_OUT_RW2,
        DEV_OUT_RW1, DEV_OUT_RW2, DEV_OUT_RW3.
        s.

        esplits; ss.
        * (* match_state *)
          econs; eauto; ss.
          { (* wf *)
            econs; eauto; ss.
            - econs; ss. econs.
            - nia.
            - clear - HB'12 MODE_EQ1.
              destruct hb'12; ss.
              econs; eauto.
              econs; ss.
            - clear - HB'21 MODE_EQ2.
              destruct hb'21; ss.
              econs; eauto.
              + econs; ss.
              + splits; ss. desf.
            - clear - MENT_D1.
              destruct ment_d1; ss. eauto.
            - clear - MENT_D2.
              destruct ment_d2; ss. eauto.
            - clear - MENT_D3.
              destruct ment_d3; ss. eauto.
          }
          { (* match_ctrl1 *)
            destruct cst1'; ss.
            subst.
            econs; ss.
          }
          { (* match_ctrl2 *)
            clear - CTRL_INIT2 MODE_EQ2.
            destruct cst2'; ss.
            subst.
            assert (md2 = CtrlState.Standby).
            { desf. }
            subst md2. clear MODE_EQ2.
            econs 2; ss.
            econs; ss.
          }
          { clear - DEV_CASE1.
            des; subst; ss.
            - destruct dst1; ss. subst.
              econs. nia.
            - destruct dst1; ss. subst.
              econs. nia.
          }
          { clear - DEV_CASE2.
            des; subst; ss.
            - destruct dst2; ss. subst.
              econs. nia.
            - destruct dst2; ss. subst.
              econs. nia.
          }
          { clear - DEV_CASE3.
            des; subst; ss.
            - destruct dst3; ss. subst.
              econs. nia.
            - destruct dst3; ss. subst.
              econs. nia.
          }
        * (* no_dev_events *)
          intros tid' t' e' IN_TR DEV_EVT.
          inv IN_TR.
          eapply Forall3_nth3 in CONS_EVENTS; eauto.
          desH CONS_EVENTS.
          destruct e1 as [t1 es1].
          clear LOCAL_EXEC.

          eapply nth_error_In in NTH2.
          assert (e2 = []).
          { clear - NTH2.
            ss. repeat des; ss. }
          clear NTH2.
          subst. ss.
          destruct EVTS_AT_T; ss. clarify.
          rename NTH1 into TES_N.

          eapply Forall2_nth2 in FILTER_NB; eauto.
          desH FILTER_NB.
          clear TES_N.
          destruct e1 as [t1 es1].
          eapply filter_nb_localstep_inv in P_FA.
          desH P_FA. ss. clarify.

          eapply In_nth_error in IN_EVTS. desH IN_EVTS.
          rename NTH1 into ES_N.
          eapply Forall2_nth2 in FILTERED_NB_EACH; eauto.
          desH FILTERED_NB_EACH.

          destruct tid'; ss.
          { clarify.
            eapply Forall_nth1 in CONSOLE_ES; eauto.
            desH CONSOLE_ES. clarify. }
          destruct tid'; ss.
          { clarify.
            destruct n; ss. }
          destruct tid'; ss.
          { clarify.
            destruct n as [| []]; ss.
            clarify. ss. unf_resum. clarify.
            destruct es; ss. clarify.
            r in DEV_EVT. desH DEV_EVT; ss.
          }
          destruct tid'; ss.
          { clarify.
            desH DEV_CASE1; clarify.
            - destruct n; ss.
            - destruct n; ss.
            - destruct n as [|[]]; ss.
              clarify. ss.
              unf_resum. clarify.
              destruct es; ss. clarify.
              r in DEV_EVT. des; ss.
          }
          destruct tid'; ss.
          { clarify.
            desH DEV_CASE2; clarify.
            - destruct n; ss.
            - destruct n; ss.
            - destruct n as [|[]]; ss.
              clarify. ss.
              unf_resum. clarify.
              destruct es; ss. clarify.
              r in DEV_EVT. des; ss.
          }
          destruct tid'; ss.
          { clarify.
            desH DEV_CASE3; clarify.
            - destruct n; ss.
            - destruct n; ss.
            - destruct n as [|[]]; ss.
              clarify. ss.
              unf_resum. clarify.
              destruct es; ss. clarify.
              r in DEV_EVT. des; ss.
          }
          destruct tid'; ss.

    - (* ctrl1 starts *)
      nbdes. subst.
      renames AST_INIT SEND_HB into CTRL_INIT1 SEND_HB1.
      right. right.

      assert (hb1 = None).
      { clear - HB_IMPL_FAIL1.
        destruct hb1; ss.
        exfalso. hexploit HB_IMPL_FAIL1; ss. }
      subst hb1.

      destruct CTRL_CASES2.
      + (* ctrl2 no start *)
        nbdes. subst.
        renames HB_IMPL_FAIL AST_INIT into HB_FAIL2 CTRL_INIT2.

        assert (CTRL2_NCOMPL: ~ event_in_tr 2 tm (cevt tm) tr).
        { clear - FILTER_NB CONS_EVENTS.
          cut (nth_error tr 2 = Some [(tm, [])]).
          { clear. intros TR2 C. inv C.
            clarify.
            ss. des; ss. clarify. }
          eapply Forall3_nth2 with (n:=2) in CONS_EVENTS.
          2: { ss. }
          des. subst.
          rewrite NTH3. clear NTH3. f_equal. f_equal.

          eapply Forall2_nth1 with (n:=2) in FILTER_NB.
          2: { ss. }
          des. clarify.
          clear NTH2.
          unfold DSys.filter_nb_localstep in P_FA. ss. clarify.
        }

        exists (mk [ment_con; hb'12; hb'21; ment_d1; ment_d2; ment_d3]
              (if hb2 then false else true) (Some false) [] 0).

        ss.
        repeat rewrite OUT_CON_RW, CTRL_OUT_RW1, CTRL_OUT_RW2,
        DEV_OUT_RW1, DEV_OUT_RW2, DEV_OUT_RW3.
        s.

        esplits; ss.
        * (* match_state *)
          econs; eauto; ss.
          { (* wf *)
            econs; eauto; ss.
            - econs; ss. econs.
            - nia.
            - clear - HB'12 MODE_EQ1.
              destruct hb'12; ss.
              econs; eauto.
              + econs; ss.
              + destruct hb2; ss.
            - clear - HB'21 MODE_EQ2 HB_FAIL2 HB_IMPL_FAIL2.
              destruct hb'21; ss.
              econs; eauto.
              + econs; ss.
              + splits; ss.
                destruct hb2; ss.
                exfalso.
                des; ss.
                hexploit HB_IMPL_FAIL2; ss.
                i. congruence.
            - clear - MENT_D1.
              destruct ment_d1; ss. eauto.
            - clear - MENT_D2.
              destruct ment_d2; ss. eauto.
            - clear - MENT_D3.
              destruct ment_d3; ss. eauto.
          }
          { (* match_ctrl1 *)
            clear - CTRL_INIT1 MODE_EQ1.
            destruct cst1'; ss.
            subst.

            unguard.
            destruct hb2; subst.
            - econs 2; eauto.
              econs; ss.
            - econs 2; eauto.
              econs; ss.
          }
          { (* match_ctrl2 *)
            clear - CTRL_INIT2.
            destruct cst2'; ss.
            subst.
            econs; ss.
          }
          { clear - DEV_CASE1.
            des; subst; ss.
            - destruct dst1; ss. subst.
              econs. nia.
            - destruct dst1; ss. subst.
              econs. nia.
          }
          { clear - DEV_CASE2.
            des; subst; ss.
            - destruct dst2; ss. subst.
              econs. nia.
            - destruct dst2; ss. subst.
              econs. nia.
          }
          { clear - DEV_CASE3.
            des; subst; ss.
            - destruct dst3; ss. subst.
              econs. nia.
            - destruct dst3; ss. subst.
              econs. nia.
          }

        * (* no_dev_events *)
          intros tid' t' e' IN_TR DEV_EVT.
          inv IN_TR.
          eapply Forall3_nth3 in CONS_EVENTS; eauto.
          desH CONS_EVENTS.
          destruct e1 as [t1 es1].
          clear LOCAL_EXEC.

          eapply nth_error_In in NTH2.
          assert (e2 = []).
          { clear - NTH2.
            ss. repeat des; ss. }
          clear NTH2.
          subst. ss.
          destruct EVTS_AT_T; ss. clarify.
          rename NTH1 into TES_N.

          eapply Forall2_nth2 in FILTER_NB; eauto.
          desH FILTER_NB.
          clear TES_N.
          destruct e1 as [t1 es1].
          eapply filter_nb_localstep_inv in P_FA.
          desH P_FA. ss. clarify.

          eapply In_nth_error in IN_EVTS. desH IN_EVTS.
          rename NTH1 into ES_N.
          eapply Forall2_nth2 in FILTERED_NB_EACH; eauto.
          desH FILTERED_NB_EACH.

          destruct tid'; ss.
          { clarify.
            eapply Forall_nth1 in CONSOLE_ES; eauto.
            desH CONSOLE_ES. clarify. }
          destruct tid'; ss.
          { clarify.
            destruct n as [| []]; ss.
            clarify. ss. unf_resum. clarify.
            destruct es; ss. clarify.
            r in DEV_EVT. desH DEV_EVT; ss.
          }
          destruct tid'; ss.
          { clarify.
            destruct n; ss. }
          destruct tid'; ss.
          { clarify.
            desH DEV_CASE1; clarify.
            - destruct n; ss.
            - destruct n; ss.
            - destruct n as [|[]]; ss.
              clarify. ss.
              unf_resum. clarify.
              destruct es; ss. clarify.
              r in DEV_EVT. des; ss.
          }
          destruct tid'; ss.
          { clarify.
            desH DEV_CASE2; clarify.
            - destruct n; ss.
            - destruct n; ss.
            - destruct n as [|[]]; ss.
              clarify. ss.
              unf_resum. clarify.
              destruct es; ss. clarify.
              r in DEV_EVT. des; ss.
          }
          destruct tid'; ss.
          { clarify.
            desH DEV_CASE3; clarify.
            - destruct n; ss.
            - destruct n; ss.
            - destruct n as [|[]]; ss.
              clarify. ss.
              unf_resum. clarify.
              destruct es; ss. clarify.
              r in DEV_EVT. des; ss.
          }
          destruct tid'; ss.

      + (* ctrl2 start *)
        nbdes. subst.
        renames AST_INIT SEND_HB into CTRL_INIT2 SEND_HB2.

        assert (hb2 = None).
        { clear - HB_IMPL_FAIL2.
          destruct hb2; ss.
          exfalso. hexploit HB_IMPL_FAIL2; ss. }
        subst hb2.

        exists (mk [ment_con; hb'12; hb'21; ment_d1; ment_d2; ment_d3]
              true None [] 0).

        ss.
        repeat rewrite OUT_CON_RW, CTRL_OUT_RW1, CTRL_OUT_RW2,
        DEV_OUT_RW1, DEV_OUT_RW2, DEV_OUT_RW3.
        s.

        esplits; ss.
        * (* match_state *)
          econs; eauto; ss.
          { (* wf *)
            econs; eauto; ss.
            - econs; ss. econs.
            - nia.
            - clear - HB'12 MODE_EQ1.
              destruct hb'12; ss.
              econs; eauto.
              econs; ss.
            - clear - HB'21 MODE_EQ2.
              destruct hb'21; ss.
              econs; eauto.
              econs; ss.
            - clear - MENT_D1.
              destruct ment_d1; ss. eauto.
            - clear - MENT_D2.
              destruct ment_d2; ss. eauto.
            - clear - MENT_D3.
              destruct ment_d3; ss. eauto.
          }
          { (* match_ctrl1 *)
            clear - CTRL_INIT1 MODE_EQ1.
            destruct cst1'; ss.
            subst.
            unguard. subst.
            econs 2; ss.
            econs; ss.
          }
          { (* match_ctrl2 *)
            clear - CTRL_INIT2 MODE_EQ2.
            destruct cst2'; ss.
            subst.
            unguard. subst.
            econs 2; ss.
            econs; ss.
          }
          { clear - DEV_CASE1.
            des; subst; ss.
            - destruct dst1; ss. subst.
              econs. nia.
            - destruct dst1; ss. subst.
              econs. nia.
          }
          { clear - DEV_CASE2.
            des; subst; ss.
            - destruct dst2; ss. subst.
              econs. nia.
            - destruct dst2; ss. subst.
              econs. nia.
          }
          { clear - DEV_CASE3.
            des; subst; ss.
            - destruct dst3; ss. subst.
              econs. nia.
            - destruct dst3; ss. subst.
              econs. nia.
          }

        * (* no_dev_events *)
          intros tid' t' e' IN_TR DEV_EVT.
          inv IN_TR.
          eapply Forall3_nth3 in CONS_EVENTS; eauto.
          desH CONS_EVENTS.
          destruct e1 as [t1 es1].
          clear LOCAL_EXEC.

          eapply nth_error_In in NTH2.
          assert (e2 = []).
          { clear - NTH2.
            ss. repeat des; ss. }
          clear NTH2.
          subst. ss.
          destruct EVTS_AT_T; ss. clarify.
          rename NTH1 into TES_N.

          eapply Forall2_nth2 in FILTER_NB; eauto.
          desH FILTER_NB.
          clear TES_N.
          destruct e1 as [t1 es1].
          eapply filter_nb_localstep_inv in P_FA.
          desH P_FA. ss. clarify.

          eapply In_nth_error in IN_EVTS. desH IN_EVTS.
          rename NTH1 into ES_N.
          eapply Forall2_nth2 in FILTERED_NB_EACH; eauto.
          desH FILTERED_NB_EACH.

          destruct tid'; ss.
          { clarify.
            eapply Forall_nth1 in CONSOLE_ES; eauto.
            desH CONSOLE_ES. clarify. }
          destruct tid'; ss.
          { clarify.
            destruct n as [| []]; ss.
            clarify. ss. unf_resum. clarify.
            destruct es; ss. clarify.
            r in DEV_EVT. desH DEV_EVT; ss.
          }
          destruct tid'; ss.
          { clarify.
            destruct n as [| []]; ss.
            clarify. ss. unf_resum. clarify.
            destruct es; ss. clarify.
            r in DEV_EVT. desH DEV_EVT; ss.
          }
          destruct tid'; ss.
          { clarify.
            desH DEV_CASE1; clarify.
            - destruct n; ss.
            - destruct n; ss.
            - destruct n as [|[]]; ss.
              clarify. ss.
              unf_resum. clarify.
              destruct es; ss. clarify.
              r in DEV_EVT. des; ss.
          }
          destruct tid'; ss.
          { clarify.
            desH DEV_CASE2; clarify.
            - destruct n; ss.
            - destruct n; ss.
            - destruct n as [|[]]; ss.
              clarify. ss.
              unf_resum. clarify.
              destruct es; ss. clarify.
              r in DEV_EVT. des; ss.
          }
          destruct tid'; ss.
          { clarify.
            desH DEV_CASE3; clarify.
            - destruct n; ss.
            - destruct n; ss.
            - destruct n as [|[]]; ss.
              clarify. ss.
              unf_resum. clarify.
              destruct es; ss. clarify.
              r in DEV_EVT. des; ss.
          }
          destruct tid'; ss.
  Qed.

End PRE_LEMMAS.
