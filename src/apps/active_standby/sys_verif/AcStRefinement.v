From Paco Require Import paco.
Require Import sflib.

Require Import SysSem.
Require Import PALSSystem.

Require console ctrl dev.

Require Import AcStSystem.
Require Import SpecConsole SpecController SpecDevice.
Require Import VerifConsole VerifController VerifDevice.

Require Import ZArith List Lia.

Local Opaque Z.of_nat Z.to_nat.

Program Definition active_standby_system
  : PALSSys.t :=
  {| (* PALSSys.RNWSParamsObj := _ ; *)
     (* PALSSys.SystemEnvObj := _ ; *)
     (* PALSSys.sysE := ActiveStandby.sysE; *)
     (* PALSSys.CProgSysEventObj := _; *)
     PALSSys.tasks := [task_con; task_ctrl1; task_ctrl2;
                      task_dev1; task_dev2; task_dev3] ;
  |}.
Next Obligation.
  ss.
Qed.
Next Obligation.
  repeat (econs; ss).
Qed.


(* Lemma active_standby_system_refinement1 *)
(*         tm_init *)
(*         (TM_INIT: Z.to_nat ActiveStandby.period <= tm_init) *)
(*   : DSys.behav_sys (PALSSys.dsys_nc *)
(*                       active_standby_system tm_init) <1= *)
(*     DSys.behav_sys (PALSSys.dsys_exec *)
(*                       active_standby_system tm_init). *)
(* Proof. *)
(*   apply impl_spec_refinement1. *)
(*   ss. *)
(* Qed. *)

Theorem active_standby_system_refinement
        tm_init
        (TM_INIT: Z.to_nat ActiveStandby.period <= tm_init)
  : DSys.behav_sys2 _ (PALSSys.dsys_nc
                         active_standby_system tm_init) <1=
    DSys.behav_sys2 _ (PALSSys.dsys_exec
                         active_standby_system tm_init).
Proof.
  apply impl_spec_refinement.
  ss.
Qed.
