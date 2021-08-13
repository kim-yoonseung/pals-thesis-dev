From ITree Require Import ITree.
From compcert Require Coqlib.
From compcert Require Import
     AST Memory Globalenvs Maps Values Linking
     Ctypes Clight Clightdefs.

Require Import ZArith String Bool List Lia.

Require Import sflib.
Require Import StdlibExt IntegersExt.
Require Import DiscreteTimeModel IPModel.

Require Import SysSem.
Require Import NWSysModel.
Require Import OSModel OSNodes.
Require Import RTSysEnv.
Require Import CProgEventSem.
Require Import SyncSysModel.
Require Import ProgSem.
Require Import LinkLemmas.
Require Import MWITree.

Require Import config_prm main_prm SystemProgs.
Require Import VerifProgBase.
Require Import MWLinkInversion.
Require Import PALSSystem.

Require Import ctrl.
Require Import AcStSystem.

Local Opaque Z.to_nat Z.of_nat PTree.combine.

Import ITreeNotations.
Import ListNotations.

Import ActiveStandby.

Set Nested Proofs Allowed.

Local Open Scope Z.


(* Definition MAX_TIMEOUT: nat := 5. *)
Definition MAX_TIMEOUT: Z := 5.
Definition QSIZE: Z := 4.

Module CtrlState.

  Inductive mode_t: Type :=
  | Uninit | Active | Standby.

  Definition mode_to_Z (md: mode_t): Z :=
    match md with
    | Uninit => 0
    | Active => 1
    | Standby => 2
    end.

  Definition mode_of_Z (md_z: Z): mode_t :=
    if md_z =? 1 then Active
    else if md_z =? 2 then Standby
         else Uninit.

  Definition default_mode (tid: Z): mode_t :=
    if tid =? 1 then Active else Standby.

  Record t: Type :=
    mk { mode: mode_t ;
         timeout: Z ;

         queue_begin: Z ;
         queue_end: Z ;
         queue: list Z ;
       }.

  Inductive wf: t -> Prop :=
    Wf md tout qb qe q
       (RANGE_TOUT: IntRange.sintz8 tout)
       (RANGE_QBGN: IntRange.sintz8 qb)
       (RANGE_QEND: IntRange.sintz8 qe)
       (RANGE_QUEUE: Forall IntRange.sintz8 q)
       (QUEUE_LENGTH: length q = 4%nat)
    : wf (mk md tout qb qe q).

  Definition init: t :=
    mk Uninit 0 0 0 [0; 0; 0; 0].

  Lemma wf_init: wf init.
  Proof.
    econs; ss.
    do 4 (econs; ss).
  Qed.

  Definition set_mode (md: mode_t) (st: t): t :=
    let 'mk _ tout qb qe q := st in
    mk md tout qb qe q.

  Lemma wf_set_mode md st
        (WF: wf st)
    : wf (set_mode md st).
  Proof.
    inv WF. econs; ss.
  Qed.

  (* Definition copy_state_from_hb *)
  (*            (st: t) (msg: list byte): t := *)
  (*   (* let 'CtrlState md tout qb qe q := st in *) *)
  (*   let tout_msg := Byte.signed (nth 1 msg Byte.zero) in *)
  (*   let qb_msg := Byte.signed (nth 2 msg Byte.zero) in *)
  (*   let qe_msg := Byte.signed (nth 3 msg Byte.zero) in *)
  (*   let q1_msg := Byte.signed (nth 4 msg Byte.zero) in *)
  (*   let q2_msg := Byte.signed (nth 5 msg Byte.zero) in *)
  (*   let q3_msg := Byte.signed (nth 6 msg Byte.zero) in *)
  (*   let q4_msg := Byte.signed (nth 7 msg Byte.zero) in *)
  (*   mk (mode st) tout_msg qb_msg qe_msg *)
  (*      [q1_msg; q2_msg; q3_msg; q4_msg]. *)

  Definition of_bytes (msg: bytes): t :=
    let md_msg := Byte.signed (nth 0 msg Byte.zero) in
    let tout_msg := Byte.signed (nth 1 msg Byte.zero) in
    let qb_msg := Byte.signed (nth 2 msg Byte.zero) in
    let qe_msg := Byte.signed (nth 3 msg Byte.zero) in
    let q1_msg := Byte.signed (nth 4 msg Byte.zero) in
    let q2_msg := Byte.signed (nth 5 msg Byte.zero) in
    let q3_msg := Byte.signed (nth 6 msg Byte.zero) in
    let q4_msg := Byte.signed (nth 7 msg Byte.zero) in
    mk (mode_of_Z md_msg) tout_msg qb_msg qe_msg
       [q1_msg; q2_msg; q3_msg; q4_msg].

  Lemma wf_of_bytes msg: wf (of_bytes msg).
  Proof.
    econs.
    - apply Byte.signed_range.
    - apply Byte.signed_range.
    - apply Byte.signed_range.
    - econs; [ apply Byte.signed_range |].
      econs; [ apply Byte.signed_range |].
      econs; [ apply Byte.signed_range |].
      econs; [ apply Byte.signed_range |].
      econs.
    - ss.
  Qed.

  (* Definition copy_state_from_hb *)
  (*            (st: t) (msg: list byte): t := *)
  (*   set_mode (mode st) (of_bytes msg). *)

  Definition copy_state_from_hb
             (md: mode_t) (msg: list byte): t :=
    set_mode md (of_bytes msg).

  Lemma wf_copy_state_from_hb md msg
    : wf (copy_state_from_hb md msg).
  Proof.
    unfold copy_state_from_hb.
    apply wf_set_mode.
    apply wf_of_bytes.
  Qed.

  Definition to_bytes (st: t): bytes :=
    let 'mk md tout qb qe q := st in
    map Byte.repr (mode_to_Z md :: tout :: qb :: qe :: q).

End CtrlState.


Definition qrange_sanitize (i: Z): Z :=
  if (andb (0 <=? i) (i <? QSIZE)) then i else 0.

Lemma range_qrange_sanitize i
  : IntRange.sintz8 (qrange_sanitize i).
Proof.
  unfold qrange_sanitize.
  destruct (Z.leb_spec 0 i);
    destruct (Z.ltb_spec i QSIZE); ss.
  unfold QSIZE in *.
  r.
  pose proof int_consts_lts as X; desH X.
  split.
  - nia.
  - etransitivity.
    { instantiate (1:= 4). nia. }
    { ss. }
Qed.

Definition adv_qidx (i: Z): Z :=
  qrange_sanitize (i + 1).

Lemma range_adv_qidx i
  : IntRange.sintz8 (adv_qidx i).
Proof.
  apply range_qrange_sanitize.
Qed.

Definition check_dev_id (id: Z): bool :=
  existsb (Z.eqb id) [Z.of_nat tid_dev1;
                     Z.of_nat tid_dev2;
                     Z.of_nat tid_dev3].

Import CtrlState.

(* Activate state in case of failure at other side *)
Definition activate_nhb (st: CtrlState.t)
  : CtrlState.t :=
  let 'CtrlState.mk _ tout qb qe q := st in
  let tout' := if (tout =? MAX_TIMEOUT)%Z then 0 else tout in
  CtrlState.mk Active tout' qb qe q.

Definition sync_istate (tid: Z) (st: CtrlState.t)
           (inb: list bytes?)
  : CtrlState.t :=
  let other_tid: Z := 3 - tid in
  let msg_con := nth 0 inb None in
  let msg_hb := nth (Z.to_nat other_tid) inb None in

  match st.(mode) with
  | Uninit =>
    match msg_hb with
    | Some hb =>
      copy_state_from_hb Standby hb
    | None =>
      set_mode (default_mode tid) st
    end
  | Active =>
    match msg_hb, msg_con with
    | Some _ , Some _ => set_mode Standby st
    | _, _ => st
    end
  | Standby =>
    match msg_hb with
    | Some hb =>
      let md' := if msg_con then Active else Standby in
      copy_state_from_hb md' hb
    | None =>
      activate_nhb st
    end
  end.

Lemma wf_sync_istate
      tid st inb
      (WF_ST: wf st)
  : wf (sync_istate tid st inb).
Proof.
  inv WF_ST.
  unfold sync_istate. ss.
  desf.
  - apply wf_copy_state_from_hb.
  - apply wf_copy_state_from_hb.
  - apply wf_copy_state_from_hb.
Qed.


Definition get_queue (csr: Z) (q: list Z): Z :=
  nth (Z.to_nat csr) q 0.

Lemma range_get_queue
      csr q
      (RANGE_Q: Forall IntRange.sintz8 q)
  : IntRange.sintz8 (get_queue csr q).
Proof.
  unfold get_queue.
  rewrite Forall_nth in RANGE_Q.

  destruct (lt_ge_dec (Z.to_nat csr) (length q)).
  - hexploit (nth_error_Some2 _ q (Z.to_nat csr)); eauto.
    i. des.
    erewrite nth_error_nth; eauto.
    specialize (RANGE_Q (Z.to_nat csr)).
    r in RANGE_Q. desf.
  - rewrite nth_overflow by ss.
    range_stac.
Qed.

Definition set_queue (csr: Z) (elem: Z) (q: list Z)
  : list Z :=
  replace_nth q (Z.to_nat csr) elem.

Lemma range_len_set_queue
      csr elem q
      (RANGE_Q: Forall IntRange.sintz8 q)
      (RANGE_ELEM: IntRange.sintz8 elem)
  : Forall IntRange.sintz8 (set_queue csr elem q) /\
    length (set_queue csr elem q) = length q.
Proof.
  unfold set_queue.
  generalize (Z.to_nat csr) as idx. clear csr. i.

  generalize (replace_nth_spec _ q idx elem).
  intros [ [LEN_OF REPL_EQ] | AUX ].
  { rewrite REPL_EQ. ss. }

  destruct AUX as (l1 & p & l2 & Q_EQ & LEN & REPL_EQ).
  rewrite REPL_EQ. subst q.

  apply Forall_app_inv in RANGE_Q. des.
  apply Forall_app_inv in RANGE_Q0. des.
  split.
  2: { repeat rewrite app_length. ss. }
  apply Forall_app; eauto.
  apply Forall_app; eauto.
Qed.


Fixpoint try_add_queue_loop
         (st: CtrlState.t) (* (qe: Z) *) (id_dev: Z)
         (n: nat) (csr: Z)
  : CtrlState.t :=
  match n with
  | O => st
  | S n' =>
    let 'mk md tout qb qe q := st in
    if csr =? qe then
      let q' := set_queue csr id_dev q in
      let qe' := adv_qidx csr in
      mk md tout qb qe' q'
    else
      if get_queue csr q =? id_dev then
        st (* already in queue *)
      else
        try_add_queue_loop st id_dev n' (adv_qidx csr)
  end.

Lemma wf_try_add_queue_loop
      st id_dev
      n csr
      (WF_ST: wf st)
      (RANGE_ID_DEV: IntRange.sintz8 id_dev)
  : wf (try_add_queue_loop st id_dev n csr).
Proof.
  depgen csr.
  induction n as [| n' IH]; i; ss.

  inv WF_ST.
  destruct (Z.eqb_spec csr qe); eauto.
  2: { desf. }

  subst csr.
  hexploit (range_len_set_queue qe id_dev); eauto. i. des.
  econs; eauto.
  - apply range_adv_qidx.
  - congruence.
Qed.


Definition try_add_queue (st: CtrlState.t) (id_dev: Z)
  : CtrlState.t :=
  let qb := qrange_sanitize (queue_begin st) in
  try_add_queue_loop st (* (queue_end st) *) id_dev 3 qb.

Lemma wf_try_add_queue
      st id_dev
      (WF_ST: wf st)
      (RANGE_ID_DEV: IntRange.sintz8 id_dev)
  : wf (try_add_queue st id_dev).
Proof.
  apply wf_try_add_queue_loop; eauto.
Qed.


Definition try_release (st: CtrlState.t) (id_dev: Z)
  : CtrlState.t :=
  let 'mk md tout qb qe q := st in
  if andb (andb (negb (qb =? qe))
                (get_queue (qrange_sanitize qb) q =? id_dev))
          (andb (0 <? tout) (tout <? MAX_TIMEOUT))
  then
    mk md 1 qb qe q
  else st.

Lemma wf_try_release
      st id_dev
      (WF_ST: wf st)
  : wf (try_release st id_dev).
Proof.
  unfold try_release.
  inv WF_ST.
  desf.
Qed.


Definition apply_devmsg (st: CtrlState.t)
           (id_dev: Z) (ment: bytes?)
  : CtrlState.t :=
  match ment with
  | Some msg =>
    let b: Z := Byte.signed (nth 0 msg Byte.zero) in
    if (b =? 1) then
      (* acquire *)
      try_add_queue st id_dev
    else
      (* release *)
      try_release st id_dev
  | None => st
  end.

Lemma wf_apply_devmsg
      st id_dev ment
      (WF_ST: wf st)
      (RANGE_ID_DEV: IntRange.sintz8 id_dev)
  : wf (apply_devmsg st id_dev ment).
Proof.
  unfold apply_devmsg.
  inv WF_ST.
  destruct ment; ss.
  desf.
  apply wf_try_add_queue; eauto.
  econs; eauto.
Qed.


Definition reduce_timeout (st: CtrlState.t)
  : CtrlState.t :=
  let 'mk md tout qb qe q := st in
  if (tout =? 1) then
    mk md 0 (adv_qidx qb) qe q
  else
    if (1 <? tout) then
      mk md (tout - 1) qb qe q
    else st.

Lemma wf_reduce_timeout
      st
      (WF_ST: wf st)
  : wf (reduce_timeout st).
Proof.
  inv WF_ST.
  unfold reduce_timeout.
  desf.
  - econs; eauto.
    + range_stac.
    + apply range_adv_qidx.
  - econs; eauto.
    destruct (Z.ltb_spec 1 tout); ss.
    range_stac.
Qed.


Fixpoint update_queue_loop (inb: list bytes?)
         (id_devs: list Z)
         (st: CtrlState.t)
  : CtrlState.t :=
  match id_devs with
  | [] => st
  | id_dev :: id_devs' =>
    let devmsg: bytes? := nth (Z.to_nat id_dev) inb None in
    let st' := apply_devmsg st id_dev devmsg in
    update_queue_loop inb id_devs' st'
  end.

Lemma wf_update_queue_loop
      inb id_devs st
      (WF_ST: wf st)
      (RANGE_ID_DEVS: Forall IntRange.sintz8 id_devs)
  : wf (update_queue_loop inb id_devs st).
Proof.
  revert st WF_ST.
  induction RANGE_ID_DEVS.
  - i. ss.
  - i. ss.
    eapply IHRANGE_ID_DEVS.
    apply wf_apply_devmsg; eauto.
Qed.


Definition update_queue (st: CtrlState.t) (inb: list bytes?)
  : CtrlState.t :=
  let st' := update_queue_loop inb [3; 4; 5] st in
  reduce_timeout st'.

Lemma wf_update_queue
      st inb
      (WF_ST: wf st)
  : wf (update_queue st inb).
Proof.
  unfold update_queue.
  apply wf_reduce_timeout.
  apply wf_update_queue_loop; eauto.
  do 3 (econs; ss).
Qed.

Definition update_istate (tid: Z)
           (st: CtrlState.t) (inb: list bytes?)
  : CtrlState.t :=
  let st1 := sync_istate tid st inb in
  update_queue st1 inb.

Lemma wf_update_istate
      tid st inb
      (WF_ST: wf st)
  : wf (update_istate tid st inb).
Proof.
  apply wf_update_queue.
  apply wf_sync_istate. ss.
Qed.

Definition update_owner (st: CtrlState.t)
  : CtrlState.t * Z :=
  let 'mk md tout qb qe q := st in
  let qhd := get_queue (qrange_sanitize qb) q in

  if andb (tout =? 0) (negb (qb =? qe)) then
    let st' := mk md MAX_TIMEOUT qb qe q in
    let tid_gr: Z :=
        match md with
        | Active => qhd
        | _ => Z_mone
        end
    in
    (st', tid_gr)
  else (st, Z_mone).
(* match md with *)
(* | Active => *)
(*   if andb (tout =? 0) (* (0 <? qhd) *) (negb (qb =? qe)) then *)
(*     (mk md MAX_TIMEOUT qb qe q, qhd) *)
(*   else (st, Z_mone) *)
(* | _ => (st, Z_mone) *)
(* end. *)

Lemma wf_update_owner
      st st' retz
      (WF_ST: wf st)
      (UPD_OWNER: update_owner st = (st', retz))
  : <<WF_ST': wf st'>> /\
    <<RANGE_RETZ: IntRange.sintz8 retz>>.
Proof.
  unfold update_owner in *.
  inv WF_ST.

  desf.
  splits.
  - econs; ss.
  - apply range_get_queue. ss.
Qed.


Definition send_hb_itree (st: CtrlState.t) (tid: Z)
  : itree appE unit :=
  trigger (AbstSendEvent (Z.to_nat (3 - tid))
                         (CtrlState.to_bytes st)).

Definition job_controller_itree
           (tid: Z) (st: CtrlState.t)
           (sytm: Z) (inb: list bytes?)
  : itree appE CtrlState.t :=
  let st1 := update_istate tid st inb in
  let (st2, tid_owner) := update_owner st1 in

  (if check_dev_id tid_owner then
     trigger (AbstSendEvent (Z.to_nat tid_owner) grant_msg)
   else Ret tt) ;;
  send_hb_itree st2 tid ;;
  (* trigger (WriteLog (CtrlState.mode_to_Z (CtrlState.mode st2))) ;; *)
  Ret st2.


Definition ctrl_job (tid: Z) (sytm: Z)
           (inb: list bytes?) (st: CtrlState.t)
  : itree (obsE +' bsendE) CtrlState.t :=
  job_controller_itree tid st sytm inb.

Definition ctrl_mod (tid: Z): @AppMod.t obsE bytes :=
  {| AppMod.abst_state_t := CtrlState.t ;
     AppMod.job_itree := ctrl_job tid ;
     AppMod.init_abst_state := CtrlState.init |}.
