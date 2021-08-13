From ITree Require Import ITree.
From Paco Require Import paco.
From compcert Require Import Integers.

Require Import sflib.

Require Import StdlibExt.
Require Import IntegersExt.
Require Import ConvC2ITree.
Require Import SyncSysModel.

Require Import Executable.
Require Import PALSSystem.

Require master worker.

From Coq Require Extraction ExtrOcamlBasic ExtrOcamlString.

Require Import ZArith List Lia.

Definition resize_bytes: bytes -> bytes? :=
  (fun bs => Some (RTSysEnv.resize_bytes 2 bs)).

Definition max_num_tasks: nat := 16.
Definition msg_size_k: Z := 1.
Definition msg_size: Z := 2.

Definition oapp_mast: AppMod.t ? :=
  cprog2app master.prog max_num_tasks msg_size_k msg_size.
Definition oapp_work (tid: Z): AppMod.t ? :=
  cprog2app (worker.prog tid) max_num_tasks msg_size_k msg_size.

Definition JobDistr_period: Z := 1000000000.

Definition app_system : ExecutableSpec.t :=
  let apps :=
      match deopt_list
              [oapp_mast; oapp_work 1; oapp_work 2;
              oapp_work 3; oapp_work 4; oapp_work 5;
              oapp_work 6; oapp_work 7; oapp_work 8] with
      | None => []
      | Some apps => apps
      end
  in
  ExecutableSpec.mk _ _ JobDistr_period
                    apps [[0;1;2;3;4;5;6;7;8]]
                    resize_bytes.

Definition app_system_itree: Z -> option Z -> itree _ unit :=
  @ExecutableSpec.sys_itree _ _ app_system.

Cd "./extr/job_assn_c2itree".
Extraction "AppSystem.ml" app_system app_system_itree.
Cd "../..".
