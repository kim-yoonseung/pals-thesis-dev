From Paco Require Import paco.
From ITree Require Import ITree.
Require Import sflib.

Require Import StdlibExt IntegersExt.
Require Import SysSem.
Require Import SyncSysModel Executable.

Require Import MSteps FMSim FMSim_Switch.
Require Import PALSSystem.

Require console ctrl dev.

Require Import AcStSystem.
Require Import SpecConsole SpecController SpecDevice.
Require Import VerifConsole VerifController VerifDevice.

Require Import AcStRefinement.

Require Import CProgEventSem.
(* Require Import AsyncSyncRef. *)

Require Import ITreeTac.

Require Import RTSysEnv.

Require Import VerifController_Base VerifController_Updq.
Require Import CompcertLemmas.

Require Import BehavUtils ExecutableUtils.

Require Import ZArith Streams List Lia Bool.

(* Local Opaque Z.of_nat Z.to_nat. *)

Import ActiveStandby.
Import ExecutableSpec.
Import ITreeNotations.

Set Nested Proofs Allowed.


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
      if (h =? tid) && ((0 <? Z.of_nat tout)%Z && (Z.of_nat tout <? SpecController.MAX_TIMEOUT)%Z)
      then 1 else tout
    | _ => tout
    end).

(* The two controller nodes simulates
   a (more reliable) single abstract controller *)


(* Definition mod_con: AppMod.t := con_mod. *)
(* Definition mod_c1: AppMod.t := (ctrl_mod 1). *)
(* Definition mod_c2 := ITrSNode.to_snode (ctrl_mod 2). *)
(* Definition snode_dev := ITrSNode.to_snode dev_mod. *)

(* Ltac unf_resum := *)
(*   unfold resum, ReSum_id, id_, Id_IFun in *. *)

(* pervious execution result *)
(* Inductive pexec_t: Set := *)
(*   Nothing | Update | SendHB | Compl. *)

(* Definition is_hb_sent (pex: pexec_t): bool := *)
(*   match pex with *)
(*   | Nothing | Update => false *)
(*   | _ => true *)
(*   end. *)

(* Definition is_updated (pex: pexec_t): bool := *)
(*   match pex with *)
(*   | Nothing => false *)
(*   | _ => true *)
(*   end. *)

(* Definition is_compl (pex: pexec_t): bool := *)
(*   match pex with *)
(*   | Compl => true *)
(*   | _ => false *)
(*   end. *)

Definition is_hb_sent (sd: bool) (hb1 hb2: bytes?): bool :=
  if sd then hb1 else hb2.

Definition is_active_side (asd side: bool): bool :=
  Bool.eqb asd side.

Definition is_failed_side (fsd: bool?) (side: bool): bool :=
  match fsd with
  | None => false
  | Some fsd' => Bool.eqb fsd' side
  end.


Definition side2tid (side: bool): nat :=
  if side then tid_ctrl1 else tid_ctrl2.


Module AbsData.
  Record ctrl_t: Type :=
    Ctrl { (* controllers *)
        (* inbox: list bytes? ; *)
        msg_from_console: unit? ;
        hb_from_c1: unit? ;
        hb_from_c2: unit? ;
        msg_from_d1: bool? ;
        msg_from_d2: bool? ;
        msg_from_d3: bool? ;

        (* failed_controller: pexec_t * pexec_t ; *)
        failed_controller: bool? ;
        active_side: bool ; (* true => first is active *)

        abst_queue: list nat ;
        owner_timeout: nat ;

        (* devs *)
        (* (grant_msg, dev_st) *)

        (* abst_dev1: DevState.t? ; *)
        (* abst_dev2: DevState.t? ; *)
        (* abst_dev3: DevState.t? ; *)
      }.

  Definition cur_owner (aq: list nat) (tout: nat): nat? :=
    match aq with
    | [] => None
    | h :: _ => if andb (0 <? tout) (tout <? MAX_TIMEOUT) then Some h else None
    end.

  (* Definition grant_msg_loc (aq: list nat) (tout: nat): nat? := *)
  (*   match aq with *)
  (*   | [] => None *)
  (*   | h :: _ => if MAX_TIMEOUT =? tout then Some h else None *)
  (*   end. *)

  (* Lemma wf_grant_msg_loc_dev_tid *)
  (*       aq tout *)
  (*       (WF: abst_queue_wf aq) *)
  (*   : option_rel1 is_dev_tid (grant_msg_loc aq tout). *)
  (* Proof. *)
  (*   unfold grant_msg_loc. *)
  (*   destruct aq; ss. *)
  (*   r in WF. des. *)
  (*   inv EACH_DEV_TID. *)
  (*   desf; ss. *)
  (* Qed. *)

  (* Definition pex_prev_active (ac: t): pexec_t := *)
  (*   if (active_side ac) then *)
  (*     fst (failed_controller ac) *)
  (*   else *)
  (*     snd (failed_controller ac). *)

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

  (* Lemma aq_new_owner_grant_msg_loc *)
  (*       aq tout *)
  (*       tout' nown *)
  (*       (TIMEOUT_LT_MAX: tout < MAX_TIMEOUT) *)
  (*       (AQ_NEW_OWNER: aq_new_owner aq tout = *)
  (*                      (tout', nown)) *)
  (*   : grant_msg_loc aq tout' = nown. *)
  (* Proof. *)
  (*   unfold aq_new_owner, grant_msg_loc in *. *)
  (*   ss. desf. *)
  (*   unfold MAX_TIMEOUT in *. nia. *)
  (* Qed. *)

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
             (* (pex1 pex2: pexec_t) *)
             (inb: list bytes?) (asd: bool)
             (aq: list nat) (tout: nat)
    : bool * list nat * nat * nat? :=
    match inb with
    | mcon :: mc1 :: mc2 :: md1 :: md2 :: md3 :: nil =>
      let asd': bool := next_active_side mcon mc1 mc2 asd in
      let tout_ug :=
          if andb (negb (is_hb_sent asd mc1 mc2))
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

  Inductive hb_of_abs_ctrl (is_active: bool)
            (aq: list nat) (tout: nat)
    : bytes -> Prop :=
  (* | HBOfAbstCtrl_None *)
  (*     pex *)
  (*     (HB_NOT_SENT: is_hb_sent pex = false) *)
  (*   : hb_of_abst_ctrl is_active aq tout pex None *)
  | HBOfAbsCtrl
      msg
      cst_m md_m tout_m qb_m qe_m q_m
      (* (HB_SENT: is_hb_sent pex = true) *)
      (CTRL_OF_BYTES: CtrlState.of_bytes msg = cst_m)
      (CTRL_EQ: cst_m = CtrlState.mk md_m tout_m
                                     qb_m qe_m q_m)
      (MATCH_QUEUE: match_queue aq (qb_m, qe_m, q_m))
      (TIMEOUT: tout_m = Z.of_nat tout)
      (MATCH_MODE:
         md_m = if is_active then CtrlState.Active
                else CtrlState.Standby)
    : hb_of_abs_ctrl is_active aq tout msg
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

  Inductive ctrl_wf: ctrl_t -> Tid? -> Prop :=
    CtrlWf fsd asd aq tout
       am_con am_c1 am_c2 am_d1 am_d2 am_d3
       grant_loc
       (WF_AQ: abst_queue_wf aq)
       (RANGE_TIMEOUT: tout <= MAX_TIMEOUT)
       (EMPTY_QUEUE_TOUT_ZERO: length aq = 0 <-> tout = 0)
       (* (INBOX_EQ: inb = [me_con; me_c1; me_c2; *)
       (*                  me_d1; me_d2; me_d3]) *)
       (ENTRY_C1: fsd = Some true \/ am_c1 = Some tt)
                  (* exists hb1, *)
                  (*   hb_of_abst_ctrl (is_active_side asd true) aq tout hb1 /\ *)
                  (*   me_c1 = Some hb1) *)
       (ENTRY_C2: fsd = Some false \/ am_c2 = Some tt)
       (GRANT_COND:
          match hd_error aq with
          | None => grant_loc = None
          | Some tid_hd =>
            if (tout =? MAX_TIMEOUT) then
              if negb (is_failed_side fsd asd) then
                grant_loc = Some tid_hd
              else
                option_rel1 (fun tid => tid = tid_hd) grant_loc
            else grant_loc = None
          end)

                  (* exists hb2, *)
                  (*   hb_of_abst_ctrl (is_active_side asd false) aq tout hb2 /\ *)
                  (*   me_c2 = Some hb2) *)

       (* (ENTRY_C1: hb_of_abst_ctrl (is_active_side asd true) *)
       (*                            aq tout pex1 me_c1) *)
       (* (ENTRY_C2: hb_of_abst_ctrl (is_active_side asd false) *)
       (*                            aq tout pex2 me_c2) *)

       (* (ENTRY_D1: option_rel1 (fun m => m = rel_msg \/ m = acq_msg) me_d1) *)
       (* (ENTRY_D2: option_rel1 (fun m => m = rel_msg \/ m = acq_msg) me_d2) *)
       (* (ENTRY_D3: option_rel1 (fun m => m = rel_msg \/ m = acq_msg) me_d3) *)
    : ctrl_wf (Ctrl am_con am_c1 am_c2 am_d1 am_d2 am_d3
                    fsd asd aq tout) grant_loc.

  Inductive match_ctrl_state
            (actrl: ctrl_t)
    (* (q: list nat) (tout: nat) (fsd: bool?) (asd: bool) (sd: bool) *)
            (sd: bool)
    : CtrlState.t -> Prop :=
  | MatchCtrlState_Uninit
      cst
      (INIT_STATE: cst = CtrlState.init)
      (THIS_FAILED: failed_controller actrl = Some sd)
    : match_ctrl_state actrl sd cst
  | MatchCtrlState
      md_c tout_c qb_c qe_c q_c
      (* (WF_CST: CtrlState.wf (CtrlState.mk md_c tout_c *)
      (*                                     qb_c qe_c q_c)) *)
      (MODE: md_c = if is_active_side (active_side actrl) sd then
                      CtrlState.Active
                    else CtrlState.Standby)
      (TIMEOUT: tout_c = Z.of_nat (owner_timeout actrl))
      (MATCH_QUEUE: match_queue (abst_queue actrl) (qb_c, qe_c, q_c))
      (THIS_NOT_FAILED: failed_controller actrl <> Some sd)
    : match_ctrl_state (* q tout *)
        (* fsd asd *)
        actrl sd
        (CtrlState.mk md_c tout_c qb_c qe_c q_c).

  (* (* match_state that timeout invariant becomes temporarily relaxed. *) *)
  (* Inductive match_ctrl_state_temp *)
  (*           (is_prev_active_sent_hb: bool) *)
  (*           (q: list nat) (tout: nat) (is_active: bool) *)
  (*   : CtrlState.t -> Prop := *)
  (* | MatchCtrlStateTemp *)
  (*     md_c tout_c qb_c qe_c q_c *)
  (*     (* (WF_CST: CtrlState.wf (CtrlState.mk md_c tout_c *) *)
  (*     (*                                     qb_c qe_c q_c)) *) *)
  (*     (MODE: md_c = if is_active then *)
  (*                     CtrlState.Active *)
  (*                   else CtrlState.Standby) *)
  (*     (TIMEOUT_EQ: tout_c = *)
  (*                  if ((* is_active && *) *)
  (*                      ((negb is_prev_active_sent_hb) && *)
  (*                       (tout =? MAX_TIMEOUT))) *)
  (*                  then 0%Z *)
  (*                  else Z.of_nat tout) *)
  (*     (MATCH_QUEUE: match_queue q (qb_c, qe_c, q_c)) *)
  (*   : match_ctrl_state_temp *)
  (*       is_prev_active_sent_hb *)
  (*       q tout is_active *)
  (*       (CtrlState.mk md_c tout_c qb_c qe_c q_c). *)


  (* Definition det_send_grant *)
  (*            (is_active: bool) *)
  (*            (aq: list nat) (tout: nat) *)
  (*   : nat? := *)
  (*   if is_active then *)
  (*     grant_msg_loc aq tout *)
  (*   else None. *)

  (* Definition msg_c2d *)
  (*            (is_active: bool) (pex: pexec_t) *)
  (*            (aq: list nat) (tout: nat) *)
  (*            (tid_d: nat) *)
  (*   : bytes? := *)
  (*   if andb (is_updated pex) is_active then *)
  (*     match grant_msg_loc aq tout with *)
  (*     | None => None *)
  (*     | Some tid_g => *)
  (*       if tid_g =? tid_d then *)
  (*         Some grant_msg *)
  (*       else None *)
  (*     end *)
  (*   else None. *)

  (* Definition msg_c2d *)
  (*            (asd: bool) (pex1 pex2: pexec_t) *)
  (*            (aq: list nat) (tout: nat) *)
  (*            (tid_d: nat) *)
  (*   : list bytes? := *)
  (*   match grant_msg_loc aq tout with *)
  (*   | None => [None; None] *)
  (*   | Some tid_g => *)
  (*     let pex := if asd then pex1 else pex2 in *)

  (*     if tid_g =? tid_d then *)
  (*       if asd then [Some grant_msg; None] *)
  (*       else [None; Some grant_msg] *)
  (*     else [None; None] *)
  (*   end. *)

  (* Definition msg_pair_c2d *)
  (*            (fc: pexec_t * pexec_t) *)
  (*            (asd: bool) aq tout (tid_d: nat) *)
  (*   : bytes? * bytes? := *)
  (*   (msg_c2d (is_active_side asd true) (fst fc) aq tout tid_d, *)
  (*    msg_c2d (is_active_side asd false) (snd fc) aq tout tid_d). *)

  (* Definition inb_dev (fc: pexec_t * pexec_t) *)
  (*            asd aq tout (tid_d: nat) *)
  (*   : list bytes? := *)
  (*   let (m1, m2) := msg_pair_c2d fc asd aq tout tid_d in *)
  (*   [None; m1; m2; None; None; None]. *)

  Definition drop_self_entry (sd: bool) (inb_c: list bytes?)
    : list bytes? :=
    replace_nth inb_c (if sd then 1 else 2) None.

  (* Inductive match_ctrl_nst *)
  (*           (asd: bool) (tout: nat) (q: list nat) *)
  (*           (b: bool) *)
  (*   : (* @SNode.state sysE bytes *) CtrlState.t? -> Prop := *)
  (*   MatchCtrlNodeState *)
  (*     (MATCH_CTRL: option_rel1 (match_ctrl_state *)
  (*                                 asd tout q b) ast_c) *)
  (*   : match_ctrl_nst asd tout q b ast_c. *)

  (* Inductive match_failed_ctrl: bool? -> pexec_t -> pexec_t -> Prop := *)
  (* | MatchFailedNone *)
  (*   : match_failed_ctrl None Compl Compl *)
  (* | MatchFailedFirst *)
  (*     pex1 *)
  (*     (FIRST_FAILED: pex1 <> Compl) *)
  (*   : match_failed_ctrl (Some true) pex1 Compl *)
  (* | MatchFailedSecond *)
  (*     pex2 *)
  (*     (SECOND_FAILED: pex2 <> Compl) *)
  (*   : match_failed_ctrl (Some false) Compl pex2 *)
  (* . *)


  (* { owner_status : bool ?;  demand : nat } *)
  (* 1. uninit (None, 0) -> no (acq \/ rel)  *)
  (* 2. NotOwnerWithoutDemand -> (Some false, 0), not in q or rel  *)
  (* 3. NotOwnerWithDemand -> (Some false, d>0), in q \/ acq *)
  (* 4. Owner -> (Some true, d>0), cur_owner *)

  Inductive match_dev_state
            (q: list nat) (tout: nat)
            (tid_d: nat)
            (m_d2c: bool?)
    : (* bytes? (* d2c *) -> bytes? (* c2d *) -> *)
      DevState.t -> Prop :=
  | MatchDevState_Uninit
      cst
      (INIT_STATE: cst = DevState.init)
      (NO_MSG_TO_CTRL: m_d2c = None)
    : match_dev_state q tout tid_d m_d2c cst
  | MatchDevState_NotOwnerNoDemand
      (NO_DMD_CASES: m_d2c = Some false \/
                     (m_d2c = None /\ ~ In tid_d q))
    : match_dev_state q tout tid_d m_d2c
                      (DevState.mk (Some false) 0)
  | MatchDevState_NotOwnerWithDemand
      dmd
      (DMD_POS: 0 < dmd)
      (DMD_CASES: (m_d2c = Some true /\ ~ In tid_d q) \/
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

  Record t: Type :=
    mk { abs_ctrl: ctrl_t ;
         sent_grant_msg: Tid? ;

         dev1_state: DevState.t? ;
         dev2_state: DevState.t? ;
         dev3_state: DevState.t? ;
      }.

  Inductive match_inb_ctrl (sd: bool): ctrl_t -> list bytes? -> Prop :=
    MatchInbCtrl
      am_con am_c1 am_c2 am_d1 am_d2 am_d3
      fsd asd q tout
      om_con om_c1 om_c2 om_d1 om_d2 om_d3
      (OM_CON: om_con = if (am_con: unit?) then Some toggle_msg else None)
      (OM_C1: option_(hb_of_abs_ctrl (is_active_side asd true) q tout)
         if
         om_con = if (am_con: unit?) then Some toggle_msg else None)
    : match_inb_ctrl sd
                     (Ctrl am_con am_c1 am_c2 am_d1 am_d2 am_d3
                           fsd asd q tout)
                     [om_con; om_c1; om_c2; om_d1; om_d2; om_d3]
  .


  Inductive match_state
    : t -> list (list bytes?) -> list (@loc_state obsE bytes) -> Prop :=
  | MatchState
      actrl grant_loc dev1 dev2 dev3
      inb_empty inb_c1 inb_c2 inb_d1 inb_d2 inb_d3
      oast_con oast_c1 oast_c2
      (WF_ACTRL: ctrl_wf actrl grant_loc)
      (MATCH_CTRL1: option_rel1 (match_ctrl_state actrl true) oast_c1)
      (MATCH_CTRL2: option_rel1 (match_ctrl_state actrl false) oast_c2)

      (INB_CON: inb_empty = repeat None num_tasks)
      (INB_C1: inb_c1 =

    : match_state (mk actrl grant_loc dev1 dev2 dev3)
                  [inb_empty; inb_c1; inb_c2;
                  inb_d1; inb_d2; inb_d3]
                  [LocState con_mod oast_con;
                  LocState (ctrl_mod 1%Z) oast_c1;
                  LocState (ctrl_mod 2%Z) oast_c2;
                  LocState dev_mod dev1;
                  LocState dev_mod dev2;
                  LocState dev_mod dev3]
  .
