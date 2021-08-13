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

Require Import ZArith String Bool List Lia.
Require Import SpecController.

Local Opaque Z.to_nat Z.of_nat PTree.combine.

Import ITreeNotations.
Import ListNotations.

Import ActiveStandby.


Module DummySNode.
  Section DummySNode.
    Context {sysE: Type -> Type}.
    Context {msgT: Set}.

    Let sendE: Type -> Type := @abst_sendE msgT.
    Let appE: Type -> Type := sysE +' sendE.

    Let t: Type := unit.

    Inductive init_app_state: t -> Prop :=
    | InitAppState: init_app_state tt.

    Inductive period_begin (zsytm: Z) (inb: list msgT?): t -> t -> Prop :=
    | PeriodBegin: period_begin zsytm inb tt tt.

    Inductive app_step: t -> t -> Prop :=
    .

    Inductive at_event: t -> event_call appE -> Prop :=
    .

    Inductive after_event: t -> event appE -> t -> Prop :=
    .

    Definition period_end: t -> bool := fun _ => true.

    Definition to_snode: SNode.t :=
      SNode.mk t
               init_app_state period_begin
               app_step at_event after_event period_end.
  End DummySNode.
End DummySNode.
