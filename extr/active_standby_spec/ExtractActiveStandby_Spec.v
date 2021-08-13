From ITree Require Import ITree.
From Paco Require Import paco.
From compcert Require Import Integers.

Require Import sflib.

Require Import StdlibExt.
Require Import IntegersExt.
Require Import SyncSysModel.

Require Import Executable.
Require Import PALSSystem.

Require Import AcStSystem.
Require Import SpecConsole SpecController SpecDevice.
Require Import AcStRefinement.

From Coq Require Extraction ExtrOcamlBasic ExtrOcamlString.

Require Import ZArith List Lia.


Definition exec_sys: ExecutableSpec.t :=
  PALSSys.as_exec active_standby_system.

Definition resize_bytes: bytes -> bytes? :=
  (fun bs => Some (RTSysEnv.resize_bytes 8 bs)).

(* We extract this instead of exec_sys for lighter extraction result. *)
Definition app_system: ExecutableSpec.t :=
  ExecutableSpec.mk _ (list byte)
                    ActiveStandby.period
                    [con_mod; ctrl_mod 1%Z; ctrl_mod 2%Z;
                    dev_mod; dev_mod; dev_mod]
                    [[1; 2]]
                    resize_bytes
.

Local Opaque ActiveStandby.period.
Local Opaque Z.of_nat Z.to_nat.

Lemma exec_sys_equiv: exec_sys = app_system.
Proof.
  unfold exec_sys.
  unfold PALSSys.as_exec.
  unfold RTSysEnv.period. s.
  rewrite Z2Nat.id by ss.
  ss.
Qed.

Definition app_system_itree
  : _ -> _ -> itree _ _ :=
  ExecutableSpec.sys_itree app_system.

Cd "./extr/active_standby_spec".
Extraction "AppSystem.ml" app_system app_system_itree.
Cd "../..".
