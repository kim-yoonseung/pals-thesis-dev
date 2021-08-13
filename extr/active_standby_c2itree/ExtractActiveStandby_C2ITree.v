From ITree Require Import ITree.
From Paco Require Import paco.
From compcert Require Import Integers.

Require Import sflib.

Require Import StdlibExt.
Require Import IntegersExt.
Require Import SyncSysModel.

Require Import Executable.
Require Import PALSSystem.

Require Import ConvC2ITree.

Require Import AcStSystem.
Require Import SpecConsole SpecController SpecDevice.
Require Import AcStRefinement.

From Coq Require Extraction ExtrOcamlBasic ExtrOcamlString.

Require Import ZArith List Lia.

Definition max_num_tasks: nat := 16.
Definition msg_size_k: Z := 1.
Definition msg_size: Z := 8.

Definition resize_bytes: bytes -> bytes? :=
  (fun bs => Some (RTSysEnv.resize_bytes 8 bs)).

Definition oapp_con: AppMod.t ? :=
  cprog2app console.prog max_num_tasks msg_size_k msg_size.
Definition oapp_ctrl1: AppMod.t ? :=
  cprog2app (ctrl.prog 1) max_num_tasks msg_size_k msg_size.
Definition oapp_ctrl2: AppMod.t ? :=
  cprog2app (ctrl.prog 2) max_num_tasks msg_size_k msg_size.
Definition oapp_dev1: AppMod.t ? :=
  cprog2app (dev.prog 3) max_num_tasks msg_size_k msg_size.
Definition oapp_dev2: AppMod.t ? :=
  cprog2app (dev.prog 4) max_num_tasks msg_size_k msg_size.
Definition oapp_dev3: AppMod.t ? :=
  cprog2app (dev.prog 5) max_num_tasks msg_size_k msg_size.

Definition app_system : ExecutableSpec.t :=
  let apps :=
      match deopt_list [oapp_con; oapp_ctrl1; oapp_ctrl2; oapp_dev1; oapp_dev2; oapp_dev3] with
      | None => []
      | Some apps => apps
      end
  in
  ExecutableSpec.mk _ _ ActiveStandby.period
                    apps [[1; 2]]
                    resize_bytes.

Definition app_system_itree: Z -> option Z -> itree _ unit :=
  @ExecutableSpec.sys_itree _ _ app_system.

Cd "./extr/active_standby_c2itree".
Extraction "AppSystem.ml" app_system app_system_itree.
Cd "../..".
