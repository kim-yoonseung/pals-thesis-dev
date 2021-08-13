From ITree Require Import ITree.
From compcert Require Coqlib.
From compcert Require Import
     AST Memory Globalenvs Maps Values Linking
     Ctypes Clight Clightdefs.

Require Import sflib.
Require Import StdlibExt IntegersExt.
Require Import DiscreteTimeModel IPModel.

Require Import SysSem.
Require Import NWSysModel.
Require Import RTSysEnv.
Require Import CProgEventSem.
Require Import SyncSysModel.

Require Import AcStSystem.
Require Import SpecController.

Require Import ZArith String Bool List Lia.

Import ActiveStandby.


Definition make_stutter (stutter: bool) (st: CtrlState.t): CtrlState.t :=
  if stutter
  then
    let 'CtrlState.mk md tout qb qe q := st in
    CtrlState.mk md 0 qb qe q
  else st.

Definition next_state (stutter: bool) (st: CtrlState.t) (inb: list bytes?):
  (Tid * bytes)? * CtrlState.t :=
  let st0 := make_stutter stutter st in
  let st1 := update_queue st0 inb in
  let (st2, tid_owner) := update_owner st1 in
  let omsg :=
      if check_dev_id tid_owner
      then Some (Z.to_nat tid_owner, grant_msg)
      else None
  in
  (omsg, st2).

Definition active (ctrl: CtrlState.t): CtrlState.t :=
  CtrlState.set_mode CtrlState.Active ctrl.


Module SingleCtrlSNode.
  Definition astate_t: Type := bool * CtrlState.t.
  Definition init: astate_t := (false, active CtrlState.init).

  Inductive astep (inb: list bytes?): astate_t -> (Tid * bytes)? -> astate_t -> Prop :=
  | AStepNormal
      sttr1 ctrl1 omsg ctrl2
      (NEXT: (omsg, ctrl2) = next_state sttr1 (active ctrl1) inb):
      astep inb (sttr1, ctrl1) omsg (false, ctrl2)
  | AStepStutter
      ctrl1 omsg omsg' ctrl2
      (NEXT: (omsg, ctrl2) = next_state false (active ctrl1) inb)
      (TOUT: ctrl2.(CtrlState.timeout) = MAX_TIMEOUT)
      (MSG: omsg' = omsg \/ omsg' = None):
      astep inb (false, ctrl1) omsg' (true, ctrl2)
  .

  Inductive t :=
  | PrdBegin (inb: list bytes?) (ast: astate_t)
  | Send (tid: Tid) (msg: bytes) (ast: astate_t)
  | PrdEnd (ast: astate_t)
  .

  Inductive init_app_state: t -> Prop :=
  | InitAppState:
      init_app_state (PrdEnd init)
  .

  Inductive period_begin (sytm: Z) (inb: list bytes?): t -> t -> Prop :=
  | PeriodBegin ast:
      period_begin sytm inb (PrdEnd ast) (PrdBegin inb ast)
  .

  Inductive app_step: t -> t -> Prop :=
  | AppStepSilent
      inb ast ast'
      (ASTEP: astep inb ast None ast'):
      app_step (PrdBegin inb ast) (PrdEnd ast')
  | AppStepSend
      inb ast tid msg ast'
      (ASTEP: astep inb ast (Some (tid, msg)) ast'):
      app_step (PrdBegin inb ast) (Send tid msg ast')
  .

  Inductive at_event: t -> event_call (obsE +' abst_sendE) -> Prop :=
  | AtEvent
      tid msg ast:
      at_event (Send tid msg ast) (EventCall (inr1 (AbstSendEvent tid msg)))
  .

  Inductive after_event: t -> event (obsE +' abst_sendE) -> t -> Prop :=
  | AfterEvent
      tid msg ast:
      after_event (Send tid msg ast) (Event (inr1 (AbstSendEvent tid msg)) tt) (PrdEnd ast)
  .

  Definition period_end (st: t): bool :=
    match st with
    | PrdEnd _ => true
    | _ => false
    end.

  Definition to_snode: SNode.t :=
    SNode.mk t
             init_app_state period_begin
             app_step at_event after_event period_end.
End SingleCtrlSNode.
