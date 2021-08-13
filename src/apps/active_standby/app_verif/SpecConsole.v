From ITree Require Import ITree.
From compcert Require Coqlib.
From compcert Require Import AST Memory Globalenvs Maps Values Linking
     Ctypes  Clight Clightdefs.

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

Require Import config_prm main_prm SystemProgs.
Require Import VerifProgBase.
Require Import MWLinkInversion.
Require Import PALSSystem.

Require Import console.
Require Import AcStSystem.


Require Import ZArith String Bool List Lia.

Local Opaque Z.to_nat Z.of_nat PTree.combine.

Import ITreeNotations.
Import ListNotations.

Import ActiveStandby.

Set Nested Proofs Allowed.


Definition con_job (sytm: Z) (_: list bytes?) (_: unit)
  : itree appE unit :=
  inp <- trigger GetUserInput;;
  (if negb (Int.eq Int.zero inp) then
     trigger (BSendEvent mid_mcast toggle_msg)
   else Ret tt);;
  trigger (WriteLog 0).

Definition con_mod: @AppMod.t obsE bytes :=
  {| AppMod.abst_state_t := unit ;
     AppMod.job_itree := con_job ;
     AppMod.init_abst_state := tt |}.
