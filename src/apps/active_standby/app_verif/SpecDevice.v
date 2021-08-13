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

Require Import dev.
Require Import AcStSystem.
(* Require Import LinkDevice. *)

Local Opaque Z.to_nat Z.of_nat PTree.combine.

Import ITreeNotations.
Import ListNotations.

(* Import ActiveStandby. *)

Set Nested Proofs Allowed.

Local Open Scope Z.


Definition MAX_TIMEOUT: nat := 5.


Module DevState.

  Record t: Type :=
    mk { owner_status: bool? ;
         demand: nat ;
       }.

  Inductive wf: t -> Prop :=
    Wf own dmd
       (RANGE_TOUT: (dmd <= MAX_TIMEOUT)%nat)
    : wf (mk own dmd).

  Definition init: t :=
    mk None O.

  Lemma wf_init: wf init.
  Proof.
    econs; ss. nia.
  Qed.

  Definition set_owner_status (own: bool) (st: t): t :=
    let 'mk _ dmd := st in
    mk (Some own) dmd.

  Lemma wf_set_owner_status own st
        (WF: wf st)
    : wf (set_owner_status own st).
  Proof.
    inv WF. econs; ss.
  Qed.

  Definition set_demand (dmd: nat) (st: t): t :=
    let 'mk own _ := st in
    mk own dmd.

  Lemma wf_set_demand
        dmd st
        (VALID_DMD: (dmd <= MAX_TIMEOUT)%nat)
    : wf (set_demand dmd st).
  Proof.
    destruct st.
    econs; ss.
  Qed.

  Definition reduce_demand (st: t): t :=
    let 'mk own dmd := st in
    mk own (pred dmd).

  Lemma wf_reduce_demand
        st (WF_ST: wf st)
    : wf (reduce_demand st).
  Proof.
    inv WF_ST.
    econs; ss.
    nia.
  Qed.


  (* Definition of_bytes (msg: bytes): t := *)
  (*   let md_msg := Byte.signed (nth 0 msg Byte.zero) in *)
  (*   let tout_msg := Byte.signed (nth 1 msg Byte.zero) in *)
  (*   let qb_msg := Byte.signed (nth 2 msg Byte.zero) in *)
  (*   let qe_msg := Byte.signed (nth 3 msg Byte.zero) in *)
  (*   let q1_msg := Byte.signed (nth 4 msg Byte.zero) in *)
  (*   let q2_msg := Byte.signed (nth 5 msg Byte.zero) in *)
  (*   let q3_msg := Byte.signed (nth 6 msg Byte.zero) in *)
  (*   let q4_msg := Byte.signed (nth 7 msg Byte.zero) in *)
  (*   mk (mode_of_Z md_msg) tout_msg qb_msg qe_msg *)
  (*      [q1_msg; q2_msg; q3_msg; q4_msg]. *)

  (* Lemma wf_of_bytes msg: wf (of_bytes msg). *)
  (* Proof. *)
  (*   econs. *)
  (*   - apply Byte.signed_range. *)
  (*   - apply Byte.signed_range. *)
  (*   - apply Byte.signed_range. *)
  (*   - econs; [ apply Byte.signed_range |]. *)
  (*     econs; [ apply Byte.signed_range |]. *)
  (*     econs; [ apply Byte.signed_range |]. *)
  (*     econs; [ apply Byte.signed_range |]. *)
  (*     econs. *)
  (*   - ss. *)
  (* Qed. *)

  Definition owner_status_to_Z (own: bool?): Z :=
    match own with
    | None => 0
    | Some b => if b then 1 else 2
    end.

  Definition to_bytes (st: t): bytes :=
    [ Byte.repr (owner_status_to_Z (owner_status st)) ;
    Byte.repr (Z.of_nat (demand st))].

End DevState.


Import DevState.

Definition check_grant (inb: list bytes?): bool :=
  match nth 1%nat inb None, nth 2%nat inb None with
  | None, None => false
  | _, _ => true
  end.

Definition sync_dev_state (inb: list bytes?) (st: t): t :=
  match nth 1%nat inb None, nth 2%nat inb None with
  | None, None => st
  | _, _ => set_owner_status true st
  end.

Lemma wf_sync_dev_state
      inb st
      (WF_ST: wf st)
  : wf (sync_dev_state inb st).
Proof.
  inv WF_ST.
  unfold sync_dev_state. ss.
  desf.
Qed.

Definition get_new_demand: itree appE nat :=
  d_raw_i <- trigger CheckDemand ;;
  let d_raw := Z.to_nat (Int.signed d_raw_i) in
  Ret (if (MAX_TIMEOUT <? d_raw)%nat then MAX_TIMEOUT else d_raw).

Definition update_demand (st: t): itree appE (t * bool) :=
  if (demand st =? O)%nat then
    d <- get_new_demand ;;
    Ret (if (0 <? d)%nat then
           (set_demand d st, true)
         else (st, false))
  else Ret (st, false).

Definition run_device (st: t): itree appE t :=
  if (0 <? demand st)%nat then
    trigger UseResource ;;
    Ret (reduce_demand st)
  else Ret st.

Definition job_device_itree (sytm: Z) (st: t) (inb: list bytes?)
  : itree appE t :=
  match owner_status st with
  | None =>
    trigger (AbstSendEvent mid_mcast rel_msg) ;;
    trigger (WriteLog 0);;
    Ret (set_owner_status false st)
  | Some is_owner =>
    let st_sync := sync_dev_state inb st in
    '(st_ud, is_dupd) <- update_demand st_sync ;;
    match owner_status st_ud with
    | None => Ret st_ud (* unreachable *)
    | Some is_owner_ud =>
      if is_owner_ud then
        st1 <- run_device st_ud ;;
        if (demand st1 =? O)%nat then
          trigger (AbstSendEvent mid_mcast rel_msg) ;;
          trigger (WriteLog 0);;
          Ret (set_owner_status false st1)
        else
          trigger (WriteLog 0);;
          Ret st1
      else
        (if (is_dupd: bool) then
           trigger (AbstSendEvent mid_mcast acq_msg)
         else Ret tt) ;;
        trigger (WriteLog 0);;
        Ret st_ud
    end
  end.


Definition dev_job
           (sytm: Z) (inb: list bytes?) (st: DevState.t)
  : itree (obsE +' bsendE) DevState.t :=
  job_device_itree sytm st inb.

Definition dev_mod: @AppMod.t obsE bytes :=
  {| AppMod.abst_state_t := DevState.t ;
     AppMod.job_itree := dev_job ;
     AppMod.init_abst_state := DevState.init |}.
