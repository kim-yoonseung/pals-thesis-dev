From ITree Require Import ITree.
Require Import sflib.
Require Import StdlibExt.

Require Import ITreeTac.

Require Import ZArith List Lia.

Import ITreeNotations.

Local Opaque Nat.min.

Set Nested Proofs Allowed.

Ltac unf_resum :=
  unfold resum, ReSum_id, id_, Id_IFun in *.

Inductive msg_t: Type :=
| Acquire
| Release
| Grant
.

Inductive sysE: Type -> Type :=
| Demand: sysE nat
| UseRes: sysE unit
| Compl: sysE unit
.

Inductive event: Type :=
| Event (R: Type) (e: sysE R) (r: R).

Inductive ctrl_err: Set :=
  Success | FailBefore | FailAfter.

Definition Tid: Set := nat.

Definition MAX_TOUT: nat := 5.

Inductive sendE: Type -> Type :=
  Send (dest: Tid) (m: msg_t): sendE unit.

Definition msgbox_t: Set := msg_t? * msg_t? * msg_t?.

Definition update_msgbox
           (mbox: msgbox_t)
           (tid: nat) (msg: msg_t)
  : msgbox_t :=
  let '(m1, m2, m3) := mbox in
  match tid with
  | 1 => (Some msg, m2, m3)
  | 2 => (m1, Some msg, m3)
  | 3 => (m1, m2, Some msg)
  | _ => mbox
  end.


Module Ctrl.

  Record t : Type :=
    mk { timeout: nat ;
         queue: list Tid ;
       }.

  Definition init: t := mk O [].

  Definition try_addq (tid: nat) (st: t): t :=
    let 'mk tout q := st in
    if existsb (Nat.eqb tid) q then st
    else mk tout (snoc q tid).

  Definition try_relq (tid: nat) (st: t): t :=
    let 'mk tout q := st in
    if orb (tout =? O) (tout =? MAX_TOUT) then st
    else
      match q with
      | [] => st
      | h :: t =>
        if tid =? h then mk 1 (h :: t) else st
      end.

  Definition apply_msg
             (tid: nat) (msg: msg_t?)
             (st: t)
    : t :=
    match msg with
    | None => st
    | Some m =>
      match m with
      | Acquire => try_addq tid st
      | Release => try_relq tid st
      | _ => st
      end
    end.

  Definition reduce_timeout (st: t): t * bool :=
    match timeout st with
    | O => (st, true)
    | 1 => (mk O (tl (queue st)), false)
    | S (S n) => (mk (S n) (queue st), false)
    end.

  Definition update
             (inb_c: msgbox_t)
             (st: t): t * bool :=
    let '(cm1, cm2, cm3) := inb_c in
    let st1 := apply_msg 1 cm1 st in
    let st2 := apply_msg 2 cm2 st1 in
    let st3 := apply_msg 3 cm3 st2 in
    reduce_timeout st3.

  (* Do this if tout = 0 & queue is nonempty: *)
  (* if tzero_flag is true, ignore cerr *)
  (* if cerr = success, set tout to max & send Grant *)
  (* if cerr = failafter, send Grant *)
  (* if cerr = failbefore, do nothing *)
  Definition send_grant (cerr: ctrl_err) (st: t)
             (tzero_flag: bool)
    : itree (sysE +' sendE) t :=
    if timeout st =? O then
      match queue st with
      | [] => Ret st
      | h :: t =>
        let cerr' :=
            if tzero_flag then Success else cerr in
        match cerr' with
        | FailBefore => Ret st
        | FailAfter =>
          trigger (Send h Grant);;
          Ret (mk 0 (h :: t))
        | Success =>
          trigger (Send h Grant);;
          Ret (mk MAX_TOUT (h :: t))
        end
      end
    else Ret st.

  Definition send_grant_func (cerr: ctrl_err) (st: t)
             (tzero_flag: bool)
    : t * (Tid * msg_t)? :=
    if timeout st =? O then
      match queue st with
      | [] => (st, None)
      | h :: t =>
        let cerr' :=
            if tzero_flag then Success else cerr in
        match cerr' with
        | FailBefore => (st, None)
        | FailAfter =>
          (mk 0 (h :: t), Some (h, Grant))
          (* trigger (Send h Grant);; *)
          (* Ret (mk 0 (h :: t)) *)
        | Success =>
          (* trigger (Send h Grant);; *)
          (* Ret (mk MAX_TOUT (h :: t)) *)
          (mk MAX_TOUT (h :: t), Some (h, Grant))
        end
      end
    else (st, None).


  Definition job (cerr: ctrl_err)
             (inbox: msgbox_t)
             (st: t): itree (sysE +' sendE) t :=
    let (st_upd, tzero_flag) := update inbox st in
    st' <- send_grant cerr st_upd tzero_flag ;;
    Ret st'.
    (* st' <- match new_owner with *)
    (*       | None => Ret st_upd *)
    (*       | Some tid_nown => *)
    (*         match cerr with *)
    (*         | FailBefore => *)
    (*           Ret (set_tout_zero st_upd) *)
    (*         | FailAfter => *)
    (*           trigger (Send tid_nown Grant);; *)
    (*           Ret (set_tout_zero st_upd) *)
    (*         | Success => *)
    (*           trigger (Send tid_nown Grant);; *)
    (*           Ret st_upd *)
    (*         end *)
    (*       end;; *)
    (* trigger Compl;; *)
    (* Ret st'. *)

  Definition job_func (cerr: ctrl_err)
             (inbox: msgbox_t)
             (st: t)
    : t * msgbox_t :=
    let (st_upd, tzero_flag) := update inbox st in
    let (st', om) := send_grant_func
                      cerr st_upd tzero_flag in
    let outbox_i := (None, None, None) in
    let outbox := match om with
                  | None => outbox_i
                  | Some (tid, msg) =>
                    update_msgbox outbox_i tid msg
                  end in
    (st', outbox).

  Inductive run_itree
            (itr: itree (sysE +' sendE) t)
            (out: msgbox_t)
    : list event -> t -> msgbox_t -> Prop :=
  | RunITree_Ret
      st'
      (OBS_RET: observe itr = RetF st')
    : run_itree itr out [] st' out
  | RunITree_Tau
      itr' es st' out'
      (OBS_TAU: observe itr = TauF itr')
      (RUN_REST: run_itree itr' out es st' out')
    : run_itree itr out es st' out'
  | RunITree_SysEvt
      R (syse: sysE R) (k: R -> itree _ t) (r: R)
      e es st' out'
      (OBS_EVT: observe itr = VisF (inl1 syse) k)
      (RUN_REST: run_itree (k r) out es st' out')
      (EVENT: e = Event _ syse r)
    : run_itree itr out (e :: es) st' out'
  | RunITree_Send
      tid msg (k: unit -> itree _ t)
      out_upd es st' out'
      (OBS_EVT: observe itr = VisF (inr1 (Send tid msg)) k)
      (UPDATE_OUTBOX: out_upd = update_msgbox
                                  out tid msg)
      (RUN_REST: run_itree (k tt) out_upd es st' out')
    : run_itree itr out es st' out'
  .

  Lemma run_itree_func
        cerr inb st es st' out
        (RUN: run_itree (job cerr inb st)
                        (None, None, None) es st' out)
    : <<CTRL_SILENT: es = []>> /\
      <<JOB_FUNC: job_func cerr inb st = (st', out)>>.
  Proof.
    unfold job in RUN.
    unfold job_func.

    assert (AUX1: exists st_upd tzero_flag,
               update inb st = (st_upd, tzero_flag)).
    { esplits. eapply surjective_pairing. }
    des.
    rewrite AUX1 in *.

    destruct st_upd as [tout q].
    unfold send_grant in RUN.
    unfold send_grant_func.
    ss.

    destruct  (Nat.eqb_spec tout 0); ss.
    2: {
      simpl_itree_hyp RUN.
      inv RUN; ss.
      clarify.
    }

    destruct q as [| qh qt].
    { simpl_itree_hyp RUN.
      inv RUN; ss. clarify. }
    { destruct tzero_flag; ss.
      - simpl_itree_hyp RUN.
        simpl_itree_hyp RUN.
        inv RUN; ss.
        clarify. existT_elim. subst.
        simpl_itree_hyp RUN_REST.

        inv RUN_REST; ss. clarify.
      - simpl_itree_hyp RUN.
        destruct cerr.
        + simpl_itree_hyp RUN.
          inv RUN; ss.
          clarify. existT_elim. subst.
          inv RUN_REST; ss.
          clarify.
        + inv RUN; ss.
          clarify.
        + simpl_itree_hyp RUN.
          inv RUN; ss.
          clarify. existT_elim. subst.
          inv RUN_REST; ss.
          clarify.
    }
  Qed.

  Inductive step (inb: msgbox_t)
    : t -> list event -> t -> msgbox_t -> Prop :=
  | Step
      (cerr: ctrl_err)
      st es st' out
      (RUN_ITREE: run_itree (job cerr inb st)
                            (None, None, None)
                            es st' out)
    : step inb st es st' out
  .


End Ctrl.


Module Dev.
  Inductive t: Type :=
  | Init
  | Running (is_owner: bool) (demand: nat)
  .

  Definition update_ownership
             (inb: msg_t?) (is_owner: bool): bool :=
    match inb with
    | None => is_owner
    | Some m =>
      match m with
      | Grant => true
      | _ => is_owner
      end
    end.

  Definition update_demand (dmd: nat)
    : itree (sysE +' sendE) (nat * bool) :=
    if dmd =? O then
      dmd' <- trigger Demand;;
      Ret (Nat.min MAX_TOUT dmd', true)
    else Ret (dmd, false).


  Definition use_res (own: bool) (dmd: nat)
    : itree (sysE +' sendE) nat :=
    if andb own (0 <? dmd) then
      trigger UseRes;; Ret (pred dmd)
    else Ret dmd.

  Definition send_msg (own: bool) (dmd: nat) (dupd: bool)
    : itree (sysE +' sendE) bool :=
    if andb own (dmd =? O) then
      trigger (Send 0 Release);; Ret false
    else
      if andb (negb own) (andb (0 <? dmd) dupd) then
        trigger (Send 0 Acquire);; Ret own
       else Ret own.

  Definition job
             (inbox: msg_t?) (st: t)
    : itree (sysE +' sendE) t :=
    match st with
    | Init =>
      trigger (Send 0 Release) ;;
      Ret (Running false 0)
    | Running is_owner dmd =>
      let is_owner1 := update_ownership inbox is_owner in
      '(dmd1, dmd_upd) <- update_demand dmd ;;
      dmd' <- use_res is_owner1 dmd1 ;;
      is_owner'<- send_msg is_owner1 dmd' dmd_upd ;;
      trigger Compl ;;
      Ret (Running is_owner' dmd')
    end.

  Inductive run_itree
            (itr: itree (sysE +' sendE) t)
            (out: msg_t?)
    : list event -> t? -> msg_t? -> Prop :=
  | RunITree_Fail
    : run_itree itr out [] None out
  | RunITree_Ret
      st'
      (OBS_RET: observe itr = RetF st')
    : run_itree itr out [] (Some st') out
  | RunITree_Tau
      itr' es ost' out'
      (OBS_TAU: observe itr = TauF itr')
      (RUN_REST: run_itree itr' out es ost' out')
    : run_itree itr out es ost' out'
  | RunITree_SysEvt
      R (syse: sysE R) (k: R -> itree _ t) (r: R)
      e es ost' out'
      (OBS_EVT: observe itr = VisF (inl1 syse) k)
      (RUN_REST: run_itree (k r) out es ost' out')
      (EVENT: e = Event _ syse r)
    : run_itree itr out (e :: es) ost' out'
  | RunITree_Send
      tid msg (k: unit -> itree _ t)
      es ost' out'
      (OBS_EVT: observe itr = VisF (inr1 (Send tid msg)) k)
      (RUN_REST: run_itree (k tt) (Some msg) es ost' out')
    : run_itree itr out es ost' out'
  .

  Lemma job_dzero_ngrant_cases
        es ost' out
        (RUN: run_itree (job None (Running false 0))
                        None es ost' out)
    : <<FAILED: es = [] /\ out = None /\ ost' = None>>
        \/
      <<DEMAND_FAILED: exists dmd',
        es = [Event _ Demand dmd'] /\
        out = None /\ ost' = None>>
        \/
      <<DEMAND_ZERO_SUCC:
        es = [Event _ Demand 0; Event _ Compl tt] /\
        out = None /\
        option_rel1 (fun st => st = Running false 0) ost'>>
        \/
      <<DEMAND_ACQ_FAILED: exists dmd',
          0 < dmd' /\
          es = [Event _ Demand dmd'] /\
          out = Some Acquire /\ ost' = None>> \/
      <<DEMAND_ACQ_SUCC: exists dmd',
          0 < dmd' /\
          es = [Event _ Demand dmd'; Event _ Compl tt] /\
          out = Some Acquire /\
          option_rel1 (fun st => st = Running false
                                           (Nat.min MAX_TOUT dmd')) ost'>>
  .
  Proof.
      unfold job in RUN.
      unfold update_demand in RUN.
      rewrite Nat.eqb_refl in RUN.
      simpl_itree_hyp RUN.
      simpl_itree_hyp RUN.

      inv RUN; ss.
      { left. eauto. }

      clarify. existT_elim. subst.
      rename RUN_REST into RUN.
      simpl_itree_hyp RUN.
      unfold use_res in RUN. ss.
      simpl_itree_hyp RUN.
      unfold send_msg in RUN. ss.

      pose (dmd_trim := Nat.min MAX_TOUT r).
      fold dmd_trim in RUN.

      destruct (Nat.ltb_spec 0 dmd_trim); ss.
      2: {
        assert (r = 0).
        { subst dmd_trim.
          destruct r; ss.
          exfalso. unfold MAX_TOUT in *. nia.
        }
        subst r.

        simpl_itree_hyp RUN.
        simpl_itree_hyp RUN.
        inv RUN; ss.
        { right. left. eauto. }

        clarify. existT_elim. subst.
        inv RUN_REST; ss.
        { right. right. left.
          esplits; eauto.
          destruct r; ss. }

        clarify.
        destruct r; ss.

        right. right. left.
        esplits; eauto.
      }

      assert (0 < r).
      { subst dmd_trim.
        destruct r; ss. nia. }

      simpl_itree_hyp RUN.
      simpl_itree_hyp RUN.
      inv RUN; ss.
      { right. left. eauto. }

      clarify. existT_elim. subst.
      rename RUN_REST into RUN.
      simpl_itree_hyp RUN.
      simpl_itree_hyp RUN.

      inv RUN; ss.
      { right. right. right. left.
        esplits; eauto. }

      clarify. existT_elim. subst.
      destruct r0; ss.

      inv RUN_REST; ss.
      { right. right. right. right.
        esplits; eauto. }

      clarify.
      right. right. right. right.
      esplits; eauto.
  Qed.

  Lemma job_dzero_grant_cases
        es ost' out
        (RUN: run_itree (job (Some Grant) (Running false 0))
                        None es ost' out)
    : <<FAILED: es = [] /\ out = None /\ ost' = None>>
        \/
      <<DEMAND_FAILED: exists dmd',
        es = [Event _ Demand dmd'] /\
        out = None /\ ost' = None>>
        \/
      <<DEMAND_ZERO_REL:
        es = [Event _ Demand 0] /\
        out = Some Release /\
        ost' = None>>
        \/
      <<DEMAND_ZERO_SUCC:
        es = [Event _ Demand 0; Event _ Compl tt] /\
        out = Some Release /\
        option_rel1 (fun st => st = Running false 0) ost'>>
        \/
      <<DEMAND_USE_FAILED: exists dmd',
          0 < dmd' /\
          es = [Event _ Demand dmd'; Event _ UseRes tt] /\
          out = None /\ ost' = None>> \/
      <<DEMAND_USE_FAILED: exists dmd',
          0 < dmd' /\
          es = [Event _ Demand dmd'; Event _ UseRes tt] /\
          out = None /\ ost' = None>> \/
      <<DEMAND_ACQ_SUCC: exists dmd',
          0 < dmd' /\
          es = [Event _ Demand dmd'; Event _ Compl tt] /\
          out = Some Acquire /\
          option_rel1 (fun st => st = Running false
                                           (Nat.min MAX_TOUT dmd')) ost'>>
  .
  Proof.


  Inductive step (inbox: msg_t?)
    : t? -> list event -> t? -> msg_t? -> Prop :=
  | Step_Fail st
    : step inbox st [] None None
  | Step_Init
    : step inbox None [] (Some Init) None
  | Step_Run
      st es ost' out
      (RUN: run_itree (job inbox st)
                      None es ost' out)
    : step inbox (Some st) es ost' out
  .

End Dev.


Module Sys.
  Record t: Set :=
    mk { time: nat ;
         inbox_controller: msgbox_t ;
         controller: Ctrl.t ;

         inbox_device1: msg_t? ;
         device1: Dev.t? ;
         inbox_device2: msg_t? ;
         device2: Dev.t? ;
         inbox_device3: msg_t? ;
         device3: Dev.t? ;
       }.

  Definition sys_trace_t: Type :=
    list (nat * event) *
    list (nat * event) *
    list (nat * event) *
    list (nat * event).

  Inductive step: t -> sys_trace_t -> t -> Prop :=
    Step
      tm inbc ctrl
      dm1 dev1 dm2 dev2 dm3 dev3
      es_c ctrl' dm1' dm2' dm3'
      es_d1 dev1' cm1'
      es_d2 dev2' cm2'
      es_d3 dev3' cm3'
      inbc' tr
      (STEP_C: Ctrl.step inbc ctrl es_c ctrl'
                         (dm1', dm2', dm3'))
      (STEP_D1: Dev.step dm1 dev1 es_d1 dev1' cm1')
      (STEP_D2: Dev.step dm2 dev2 es_d2 dev2' cm2')
      (STEP_D3: Dev.step dm3 dev3 es_d3 dev3' cm3')
      (INB_CTRL': inbc' = (cm1', cm2', cm3'))
      (TRACE: tr = (map (fun x => (tm, x)) es_c ,
                    map (fun x => (tm, x)) es_d1 ,
                    map (fun x => (tm, x)) es_d2 ,
                    map (fun x => (tm, x)) es_d3))
    : step (mk tm inbc ctrl
               dm1 dev1 dm2 dev2 dm3 dev3)
           tr
           (mk (S tm) inbc' ctrl'
               dm1' dev1' dm2' dev2' dm3' dev3').

  Definition init: t :=
    mk O (None, None, None) Ctrl.init
       None None None None None None.

  Inductive state_trace
    : t -> sys_trace_t -> t -> Prop :=
  | StateTrace_Base st
    : state_trace st ([], [], [], []) st

  | StateTrace_Step
      st tr1 tr2 tr3 tr4 st1
      tr1' tr2' tr3' tr4' st'
      str
      (STEP: step st (tr1, tr2, tr3, tr4) st1)
      (REST: state_trace st1 (tr1', tr2', tr3', tr4') st')
      (TRACES: str = (tr1 ++ tr1', tr2 ++ tr2',
                      tr3 ++ tr3', tr4 ++ tr4'))
    : state_trace st str st'
  .

End Sys.


Section PF.

  Definition wf_queue (q: list nat): Prop :=
    <<NODUP_Q: NoDup q >> /\
    <<VALID_IDS: Forall (fun x => 1 <= x <= 3) q>>.

  Inductive tout_grant_rel: nat -> msg_t? -> Prop :=
  | TOutGrant_MaxSent
    : tout_grant_rel MAX_TOUT (Some Grant)
  | TOutGrant_ZeroSent
    : tout_grant_rel 0 (Some Grant)
  | TOutGrant_ZeroNotSent
    : tout_grant_rel 0 None
  .

  Inductive dms_inv: nat -> list Tid -> msgbox_t -> Prop :=
  | DMSInv_NoMsgs
      tout q
      (NO_MSGS_COND: q = [] \/ (0 < tout < MAX_TOUT))
    : dms_inv tout q (None, None, None)

  | DMSInv_Dev1
      tout q' dm1
      (DM1: tout_grant_rel tout dm1)
    : dms_inv tout (1::q') (dm1, None, None)
  | DMSInv_Dev2
      tout q' dm2
      (DM2: tout_grant_rel tout dm2)
    : dms_inv tout (2::q') (None, dm2, None)
  | DMSInv_Dev3
      tout q' dm3
      (DM3: tout_grant_rel tout dm3)
    : dms_inv tout (3::q') (None, None, dm3)
  .

  Inductive ctrl_inv: Ctrl.t -> msgbox_t -> Prop :=
    CtrlInv
      tout q dms
      (RANGE_TOUT: 0 <= tout <= MAX_TOUT)
      (WF_Q: wf_queue q)
      (EMPTY_QUEUE_TOUT_ZERO: length q = 0 -> tout = 0)
      (DMS_INV: dms_inv tout q dms)
    : ctrl_inv (Ctrl.mk tout q) dms.

  Inductive dev_inv (tid: Tid) (ctrl: Ctrl.t)
    : Dev.t? -> msg_t? -> Prop :=
  | DevInv_Off cm
    : dev_inv tid ctrl None cm
  | DevInv_Init
    : dev_inv tid ctrl (Some Dev.Init) None
  | DevInv_NotOwnerWithDemand
      dmd cm
      (QHD_NEQ: hd_error (Ctrl.queue ctrl) = Some tid ->
                Ctrl.timeout ctrl = 0 \/
                Ctrl.timeout ctrl = MAX_TOUT)
      (DMD_POS: 0 < dmd <= MAX_TOUT)
      (CM_CASES: cm = None \/ cm = Some Acquire)
      (CTRL_KNOWS_DEMAND: In tid (Ctrl.queue ctrl) \/
                          cm = Some Acquire)
    : dev_inv tid ctrl
              (Some (Dev.Running false dmd)) cm
  | DevInv_NotOwnerWithoutDemand
      cm
      (QHD_REL: hd_error (Ctrl.queue ctrl) = Some tid ->
                0 < Ctrl.timeout ctrl < MAX_TOUT ->
                cm = Some Release)
      (CM_CASES: cm = None \/ cm = Some Release)
    : dev_inv tid ctrl
              (Some (Dev.Running false 0)) cm
  | DevInv_Owner
      dmd
      (DMD_POS: 0 < dmd < MAX_TOUT)
      (DMD_LE_TOUT:dmd <= Ctrl.timeout ctrl)
      (QHD_EQ: hd_error (Ctrl.queue ctrl) = Some tid)
    : dev_inv tid ctrl
              (Some (Dev.Running true dmd)) None
  .

  Inductive sys_inv: Sys.t -> Prop :=
    SysInv
      tm cm1 cm2 cm3 ctrl
      dm1 dev1 dm2 dev2 dm3 dev3
      (INV_CTRL: ctrl_inv ctrl (dm1, dm2, dm3))
      (INV_DEV1: dev_inv 1 ctrl dev1 cm1)
      (INV_DEV2: dev_inv 2 ctrl dev2 cm2)
      (INV_DEV3: dev_inv 3 ctrl dev3 cm3)
    : sys_inv (Sys.mk tm (cm1, cm2, cm3) ctrl
                      dm1 dev1 dm2 dev2 dm3 dev3).


  Lemma sys_inv_init
    : sys_inv Sys.init.
  Proof.
    econs.
    - econs; ss.
      { nia. }
      { r. splits.
        - econs.
        - econs.
      }
      { econs 1. eauto. }
    - econs 1.
    - econs 1.
    - econs 1.
  Qed.

  (* Lemma ctrl_inv_prsv *)
  (*       ctrl dms cms *)
  (*       es ctrl' dms' *)
  (*       (INV: ctrl_inv ctrl dms) *)
  (*       (STEP: Ctrl.step cms *)
  (*                        ctrl es ctrl' dms') *)
  (*   : ctrl_inv ctrl' dms'. *)
  (* Proof. *)
  (*   inv INV. *)
  (*   inv STEP. *)
  (* Admitted. *)


  (* Lemma new_owner_timeout_aux1 *)
  (*       tid cerr ms tout q *)
  (*       ctrl' ms' *)
  (*       (* (IF_QHD_TOUT_ZERO: hd_error q = Some tid -> tout = 0) *) *)
  (*       (QHD_NEQ: hd_error q <> Some tid) *)
  (*       (JOB_FUNC: Ctrl.job_func cerr ms (Ctrl.mk tout q) = (ctrl', ms')) *)
  (*       (QHD': hd_error (Ctrl.queue ctrl') = Some tid) *)
  (*   : Ctrl.timeout ctrl' = 0 \/ *)
  (*     Ctrl.timeout ctrl' = MAX_TOUT. *)
  (* Proof. *)
  (*   unfold Ctrl.job_func in *. *)
  (* Admitted. *)


  (* Lemma new_owner_timeout_aux2 *)
  (*       tid cerr ms tout q *)
  (*       ctrl' ms' *)
  (*       (* (IF_QHD_TOUT_ZERO: hd_error q = Some tid -> tout = 0) *) *)
  (*       (QHD_NEQ: hd_error q = Some tid) *)
  (*       (TIMEOUT: tout = 0) *)
  (*       (JOB_FUNC: Ctrl.job_func cerr ms (Ctrl.mk tout q) = (ctrl', ms')) *)
  (*   : hd_error (Ctrl.queue ctrl') = Some tid /\ *)
  (*     Ctrl.timeout ctrl' = MAX_TOUT. *)
  (* Proof. *)
  (* Admitted. *)

  Lemma inv_prsv_each_dev
        (tid: Tid) (ctrl: Ctrl.t) (dev: Dev.t?)
        (cm cm1 cm2 cm3: msg_t?)
        (dm dm1 dm2 dm3: msg_t?)
        es_c ctrl'
        dm1' dm2' dm3'
        es_d dev' cm'
        (DEV_CASES:
           (tid = 1 /\ cm = cm1 /\ dm = dm1) \/
           (tid = 2 /\ cm = cm2 /\ dm = dm2) \/
           (tid = 3 /\ cm = cm3 /\ dm = dm3))
        (INV_CTRL: ctrl_inv ctrl (dm1, dm2, dm3))
        (INV_DEV: dev_inv tid ctrl dev cm)
        (STEP_C : Ctrl.step (cm1, cm2, cm3)
                            ctrl es_c ctrl'
                            (dm1', dm2', dm3'))
        (STEP_D : Dev.step dm dev es_d dev' cm')
    : <<INV_CTRL': ctrl_inv ctrl' (dm1', dm2', dm3')>> /\
      <<INV_DEV': dev_inv tid ctrl' dev' cm'>>.
  Proof.
    des; ss.
    - subst.
      inv INV_CTRL.
      inv INV_DEV.
      + (* dev none *)
        assert (CTRL': ctrl_inv ctrl' (dm1', dm2', dm3')).
        { admit. }
        des.

        inv STEP_D.
        { splits.
          2: { econs 1. }
          eauto.
        }
        { splits.
          2: { econs 2. }
          eauto.
        }
      + (* init *)
        assert (CTRL': ctrl_inv ctrl' (dm1', dm2', dm3')).
        { admit. }

        inv STEP_D.
        { splits.
          2: { econs 1. }
          eauto.
        }
        { inv RUN; ss.
          { splits.
            2: { econs 1. }
            eauto.
          }

          unfold Dev.job in OBS_EVT.
          simpl_itree_hyp OBS_EVT.
          ss. clarify. existT_elim. subst.
          rename RUN_REST into RUN.
          inv RUN; ss.
          { esplits.
            2: { econs 1. }
            eauto.
          }

          clarify.
          splits.
          2: { econs 4; eauto. }
          eauto.
        }
      + (* not_owner with_demand *)
        guardH CM_CASES. ss.
        guardH CTRL_KNOWS_DEMAND.

        assert (<<CTRL': ctrl_inv ctrl' (dm1', dm2', dm3')>> /\
                <<IN_Q': In 1 (Ctrl.queue ctrl')>>).
                (* <<QHD': hd_error q = Some 1 /\ tout = 0 -> *)
                (*       hd_error (Ctrl.queue ctrl') = Some 1 /\ tout = MAX_TOUT>>). *)
        { admit. }
        des.

        splits; ss.
        inv STEP_D.
        { econs. }

        unfold Dev.job in RUN.
        unfold Dev.update_demand in RUN.

        destruct (Nat.eqb_spec dmd 0).
        { exfalso. nia. }

        unfold Dev.use_res in RUN.
        simpl_itree_hyp RUN.

        assert (DM_CASES: dm1 = None \/ dm1 = Some Grant).
        { inv DMS_INV; ss; eauto.
          inv DM1; eauto. }
        desH DM_CASES.
        { subst dm1.
          unfold Dev.send_msg in RUN.
          simpl in RUN.
          simpl_itree_hyp RUN.
          rewrite Bool.andb_false_r in RUN.
          simpl_itree_hyp RUN.
          simpl_itree_hyp RUN.

          inv RUN; ss.
          { econs. }

          clarify. existT_elim. subst.
          inv RUN_REST; ss.
          { econs 1. }
          clarify.

          econs 3; eauto.

          assert (IF_QHD_TOUT_ZERO:
                    hd_error q = Some 1 -> tout = 0).
          { intro HD.
            inv DMS_INV; ss.
            - desH NO_MSGS_COND; ss.
              + subst q. ss.
              + exfalso.
                hexploit QHD_NEQ; eauto. nia.
            - inv DM1. ss.
          }
          (* from DMS_INV *)
          intro QHD'.

          inv STEP_C.
          hexploit Ctrl.run_itree_func; eauto.
          intro AUX1. desH AUX1. subst.

          (* eapply new_owner_timeout_aux; eauto. *)
          admit.
        }
        { (* dm1 = Some Grant *)
          subst dm1.
          ss.

          assert (QHD_EQ: hd_error q = Some 1).
          { inv DMS_INV.
            inv DM1; ss. }

          destruct (Nat.ltb_spec 0 dmd); ss.
          2: { nia. }
          simpl_itree_hyp RUN.
          simpl_itree_hyp RUN.

          inv RUN; ss.
          { econs. }
          clarify. existT_elim. subst.

          simpl_itree_hyp RUN_REST.
          unfold Dev.send_msg in RUN_REST. ss.

          destruct (pred dmd) as [| dmd'] eqn:DMD'; ss.
          - simpl_itree_hyp RUN_REST.
            simpl_itree_hyp RUN_REST.
            rename RUN_REST into RUN.
            inv RUN; ss.
            { econs. }
            clarify. existT_elim. subst.

            simpl_itree_hyp RUN_REST.
            simpl_itree_hyp RUN_REST.
            rename RUN_REST into RUN.
            inv RUN; ss.
            { econs 1. }

            clarify. existT_elim. subst.
            inv RUN_REST; ss.
            { econs 1. }
            clarify.
            econs 4; eauto.

          - simpl_itree_hyp RUN_REST.
            simpl_itree_hyp RUN_REST.
            rename RUN_REST into RUN.
            inv RUN; ss.
            { econs 1. }
            clarify. existT_elim. subst.
            inv RUN_REST; ss.
            { econs 1. }
            clarify.

            assert (CASES': hd_error (Ctrl.queue ctrl') = Some 1 /\
                    ((Ctrl.timeout ctrl') = MAX_TOUT \/
                     (Ctrl.timeout ctrl') = pred MAX_TOUT)).
            { admit. }
            desH CASES'.
            { econs 5; eauto.
              nia. }
            { econs 5; eauto.
              nia. }
        }

      + (* not owner, without_demand *)
        guardH CM_CASES. ss.

        assert (<<CTRL': ctrl_inv ctrl' (dm1', dm2', dm3')>> /\
                <<IF_QHD_EQ': hd_error (Ctrl.queue ctrl') = Some 1 ->
                              Ctrl.timeout ctrl' = 0 \/
                              Ctrl.timeout ctrl' = MAX_TOUT>>).
        { admit. }
        des.

        splits; ss.
        inv STEP_D.
        { econs. }

        unfold Dev.job in RUN.
        unfold Dev.update_demand in RUN.
        rewrite Nat.eqb_refl in RUN.
        simpl_itree_hyp RUN.
        simpl_itree_hyp RUN.

        inv RUN; ss.
        { econs 1. }

        destruct dm1 as [m|].
        * (* grant *)
          clarify. existT_elim. subst.

          inv DMS_INV.
          assert (TOUT_CASES: m = Grant /\
                              (tout = 0 \/ tout = MAX_TOUT)).
          { inv DM1; eauto. }
          destruct TOUT_CASES as [? TOUT_CASES].
          subst m. guardH TOUT_CASES.
          clear DM1. ss.

          rename RUN_REST into RUN.
          simpl_itree_hyp RUN.
          unfold Dev.use_res in RUN. ss.

          pose (dmd' := Nat.min MAX_TOUT r).
          fold dmd' in RUN.

          destruct (Nat.ltb_spec 0 dmd').
          {






          guardH TOUT_CASES.





        TODO


        assert (DM_CASES: dm1 = None \/ dm1 = Some Grant).
        { inv DMS_INV; ss; eauto.
          inv DM1; eauto. }
        desH DM_CASES.
        { subst dm1.
          unfold Dev.send_msg in RUN.
          simpl in RUN.
          simpl_itree_hyp RUN.
          rewrite Bool.andb_false_r in RUN.
          simpl_itree_hyp RUN.
          simpl_itree_hyp RUN.

          inv RUN; ss.
          { econs. }

          clarify. existT_elim. subst.
          inv RUN_REST; ss.
          { econs 1. }
          clarify.

          econs 3; eauto.

          assert (IF_QHD_TOUT_ZERO:
                    hd_error q = Some 1 -> tout = 0).
          { intro HD.
            inv DMS_INV; ss.
            - desH NO_MSGS_COND; ss.
              + subst q. ss.
              + exfalso.
                hexploit QHD_NEQ; eauto. nia.
            - inv DM1. ss.
          }
          (* from DMS_INV *)
          intro QHD'.

          inv STEP_C.
          hexploit Ctrl.run_itree_func; eauto.
          intro AUX1. desH AUX1. subst.

          (* eapply new_owner_timeout_aux; eauto. *)
          admit.
        }
        { (* dm1 = Some Grant *)
          subst dm1.
          ss.

          assert (QHD_EQ: hd_error q = Some 1).
          { inv DMS_INV.
            inv DM1; ss. }

          destruct (Nat.ltb_spec 0 dmd); ss.
          2: { nia. }
          simpl_itree_hyp RUN.
          simpl_itree_hyp RUN.

          inv RUN; ss.
          { econs. }
          clarify. existT_elim. subst.

          simpl_itree_hyp RUN_REST.
          unfold Dev.send_msg in RUN_REST. ss.

          destruct (pred dmd) as [| dmd'] eqn:DMD'; ss.
          - simpl_itree_hyp RUN_REST.
            simpl_itree_hyp RUN_REST.
            rename RUN_REST into RUN.
            inv RUN; ss.
            { econs. }
            clarify. existT_elim. subst.

            simpl_itree_hyp RUN_REST.
            simpl_itree_hyp RUN_REST.
            rename RUN_REST into RUN.
            inv RUN; ss.
            { econs 1. }

            clarify. existT_elim. subst.
            inv RUN_REST; ss.
            { econs 1. }
            clarify.
            econs 4. eauto.

          - simpl_itree_hyp RUN_REST.
            simpl_itree_hyp RUN_REST.
            rename RUN_REST into RUN.
            inv RUN; ss.
            { econs 1. }
            clarify. existT_elim. subst.
            inv RUN_REST; ss.
            { econs 1. }
            clarify.

            assert (CASES': hd_error (Ctrl.queue ctrl') = Some 1 /\
                    ((Ctrl.timeout ctrl') = MAX_TOUT \/
                     (Ctrl.timeout ctrl') = pred MAX_TOUT)).
            { admit. }
            desH CASES'.
            { econs 5; eauto.
              nia. }
            { econs 5; eauto.
              nia. }
        }



    }






        desH CM_CASES.
        * subst cm1.
          desH CTRL_KNOWS_DEMAND; ss.

          assert (<<CTRL': ctrl_inv ctrl' (dm1', dm2', dm3')>> /\
                  <<IN_Q': In 1 (Ctrl.queue ctrl')>>).
          { admit. }
          des.

          splits; ss.
          inv STEP_D.
          { econs. }

          unfold Dev.job in RUN.
          unfold Dev.update_demand in RUN.

          destruct (Nat.eqb_spec dmd 0).
          { exfalso. nia. }

          unfold Dev.use_res in RUN.
          simpl_itree_hyp RUN.

          assert (DM_CASES: dm1 = None \/ dm1 = Some Grant).
          { admit. }
          desH DM_CASES.
          { subst dm1.
            unfold Dev.send_msg in RUN.
            simpl in RUN.
            simpl_itree_hyp RUN.
            rewrite Bool.andb_false_r in RUN.
            simpl_itree_hyp RUN.
            simpl_itree_hyp RUN.

            inv RUN; ss.
            { econs. }

            clarify. existT_elim. subst.
            inv RUN_REST; ss.
            { econs 1. }
            clarify.

            econs 3; eauto.

            assert (hd_error q = Some 1 -> tout = 0).
            { intro HD.
              inv DMS_INV; ss.
              - des; ss.
                + subst q. ss.
                + hexploit QHD_NEQ; eauto. nia.
              - inv DM1. ss.
            }
            (* from DMS_INV *)
            admit. (* if tout = 0, nxt timeout should be MAX_TOUT *)
          }
          { (* dm1 = Some Grant *)
            subst dm1.
            ss.

            assert (QHD_EQ: hd_error q = Some 1).
            { inv DMS_INV.
              inv DM1; ss. }

            destruct (Nat.ltb_spec 0 dmd); ss.
            2: { nia. }
            simpl_itree_hyp RUN.
            simpl_itree_hyp RUN.

            inv RUN; ss.
            { econs. }
            clarify. existT_elim. subst.

            simpl_itree_hyp RUN_REST.
            unfold Dev.send_msg in RUN_REST. ss.

            destruct (pred dmd) as [| dmd'] eqn:DMD'; ss.
            - simpl_itree_hyp RUN_REST.
              simpl_itree_hyp RUN_REST.
              rename RUN_REST into RUN.
              inv RUN; ss.
              { econs. }
              clarify. existT_elim. subst.

              simpl_itree_hyp RUN_REST.
              simpl_itree_hyp RUN_REST.
              rename RUN_REST into RUN.
              inv RUN; ss.
              { econs 1. }

              clarify. existT_elim. subst.
              inv RUN_REST; ss.
              { econs 1. }
              clarify.
              econs 4. eauto.

            - simpl_itree_hyp RUN_REST.
              simpl_itree_hyp RUN_REST.
              rename RUN_REST into RUN.
              inv RUN; ss.
              { econs 1. }
              clarify. existT_elim. subst.
              inv RUN_REST; ss.
              { econs 1. }
              clarify.

              assert (hd_error (Ctrl.queue ctrl') = Some 1 /\
                      ((Ctrl.timeout ctrl') = MAX_TOUT \/
                       (Ctrl.timeout ctrl') = pred MAX_TOUT)).
              { admit. }
              des.
              { econs 5; eauto.
                nia. }
              { econs 5; eauto.
                nia. }
          }

        * (* cm1 is Acquire *)
          subst cm1. ss.
          clear CTRL_KNOWS_DEMAND.

          assert (CTRL': ctrl_inv ctrl' (dm1', dm2', dm3')).
          { admit. }

          splits; eauto.

          inv STEP_D.
          { econs 1. }

          unfold Dev.job in RUN.
          unfold Dev.update_demand in RUN.

          destruct (Nat.eqb_spec dmd 0).
          { exfalso. nia. }

          unfold Dev.use_res in RUN.
          simpl_itree_hyp RUN.

          assert (DM_CASES: dm1 = None \/ dm1 = Some Grant).
          { admit. }
          desH DM_CASES.
          { subst dm1.
            unfold Dev.send_msg in RUN.
            simpl in RUN.
            simpl_itree_hyp RUN.
            rewrite Bool.andb_false_r in RUN.
            simpl_itree_hyp RUN.
            simpl_itree_hyp RUN.

            inv RUN; ss.
            { econs. }

            clarify. existT_elim. subst.
            inv RUN_REST; ss.
            { econs 1. }
            clarify.

            econs 3; eauto.

            assert (hd_error q = Some 1 -> tout = 0).
            { intro HD.
              inv DMS_INV; ss.
              - des; ss.
                + subst q. ss.
                + hexploit QHD_NEQ; eauto. nia.
              - inv DM1. ss.
            }
            (* from DMS_INV *)
            admit. (* if tout = 0, nxt timeout should be MAX_TOUT *)
          }
          { (* dm1 = Some Grant *)
            subst dm1.
            ss.

            assert (QHD_EQ: hd_error q = Some 1).
            { inv DMS_INV.
              inv DM1; ss. }

            destruct (Nat.ltb_spec 0 dmd); ss.
            2: { nia. }
            simpl_itree_hyp RUN.
            simpl_itree_hyp RUN.

            inv RUN; ss.
            { econs. }
            clarify. existT_elim. subst.

            simpl_itree_hyp RUN_REST.
            unfold Dev.send_msg in RUN_REST. ss.

            destruct (pred dmd) as [| dmd'] eqn:DMD'; ss.
            - simpl_itree_hyp RUN_REST.
              simpl_itree_hyp RUN_REST.
              rename RUN_REST into RUN.
              inv RUN; ss.
              { econs. }
              clarify. existT_elim. subst.

              simpl_itree_hyp RUN_REST.
              simpl_itree_hyp RUN_REST.
              rename RUN_REST into RUN.
              inv RUN; ss.
              { econs 1. }

              clarify. existT_elim. subst.
              inv RUN_REST; ss.
              { econs 1. }
              clarify.
              econs 4. eauto.

            - simpl_itree_hyp RUN_REST.
              simpl_itree_hyp RUN_REST.
              rename RUN_REST into RUN.
              inv RUN; ss.
              { econs 1. }
              clarify. existT_elim. subst.
              inv RUN_REST; ss.
              { econs 1. }
              clarify.

              assert (hd_error (Ctrl.queue ctrl') = Some 1 /\
                      ((Ctrl.timeout ctrl') = MAX_TOUT \/
                       (Ctrl.timeout ctrl') = pred MAX_TOUT)).
              { admit. }
              des.
              { econs 5; eauto.
                nia. }
              { econs 5; eauto.
                nia. }
          }



          inv RUN; ss.







              econs 5.
              { (* dmd <= Ctrl.timeout -> dmd' <= Ctrl.timeout' *)
                admit. }



              destruct (Nat.eqb_spec dmd 0); ss.

            inv RUN_REST; ss.
            { econs. }

            simpl_itree_hyp OBS_RET.
            ss.




          inv RUN; ss.
          { econs. }









        destruct q as [| qh qt].
        { hexploit EMPTY_QUEUE_TOUT_ZERO; eauto.
          clear EMPTY_QUEUE_TOUT_ZERO.
          i. subst.

          inv DMS_INV.
          clear NO_MSGS_COND WF_Q RANGE_TOUT.

          inv STEP_D.
          - esplits.
            2: { econs. }
            admit. (* ctrl_inv prsv *)
          -





  Admitted.


  Lemma sys_inv_prsv
        st str st'
        (INV: sys_inv st)
        (STEP: Sys.step st str st')
    : sys_inv st'.
  Proof.
    inv INV.
    inv STEP.

    hexploit (inv_prsv_each_dev 1); eauto.
    hexploit (inv_prsv_each_dev 2); eauto.
    hexploit (inv_prsv_each_dev 3); eauto.
    i. des.
    econs; eauto.
  Qed.
