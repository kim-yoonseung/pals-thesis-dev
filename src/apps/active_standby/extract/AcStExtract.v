From ITree Require Import ITree.
From Paco Require Import paco.
From compcert Require Import Integers.

Require Import sflib.

Require Import StdlibExt.
Require Import IntegersExt.
Require Import SyncSysModel.

Require Import Executable.
Require Import PALSSystem.

(* Require console ctrl dev. *)

Require Import AcStSystem.
Require Import SpecConsole SpecController SpecDevice.
(* Require Import VerifConsole VerifController VerifDevice. *)
Require Import AcStRefinement.

From Coq Require Extraction ExtrOcamlBasic ExtrOcamlString.
(* To avoid stack overflow *)
(* From Coq Require ExtrOcamlNatBigInt. *)

Require Import ZArith List Lia.


Definition exec_sys: ExecutableSpec.t :=
  PALSSys.as_exec active_standby_system.

(* Extraction Inline exec_sys active_standby_system PALSSys.as_exec . *)

(* extracting this directly makes a huge ml file *)
(* Definition active_standby_itree (tm_init: nat) (tm_fin: option nat) *)
(*   : itree _ _ := *)
(*   ExecutableSpec.exec_itree exec_sys tm_init tm_fin. *)

Definition resize_bytes: bytes -> bytes? :=
  (fun bs => Some
            (firstn 8 bs ++
                    repeat Byte.zero (8 - length bs))).

Definition exec_sys': ExecutableSpec.t :=
  ExecutableSpec.mk _ (list byte)
                    ActiveStandby.period
                    [con_mod; ctrl_mod 1%Z; ctrl_mod 2%Z;
                    dev_mod; dev_mod; dev_mod]
                    [[1; 2]]
                    resize_bytes
.

Local Opaque ActiveStandby.period.
Local Opaque Z.of_nat Z.to_nat.

Lemma exec_sys_equiv: exec_sys = exec_sys'.
Proof.
  unfold exec_sys.
  unfold PALSSys.as_exec.
  unfold RTSysEnv.period. s.
  rewrite Z2Nat.id by ss.
  ss.
Qed.

Definition system_itree
  : _ -> _ -> itree _ _ :=
  ExecutableSpec.sys_itree exec_sys'.

Definition system_synch_period: Z := ActiveStandby.period.

Cd "./extract/ActiveStandby".
Extraction "AppSystem.ml" system_itree system_synch_period.
Cd "../..".

(** Extracting ITree system *)

(* Extraction "ExecITree.ml" ExecutableSpec.exec_itree. *)

(* Definition max_num_tasks: nat := 16. *)
(* Definition msg_size_k: Z := 1. *)
(* Definition msg_size: Z := 8. *)

(* Definition oapp_con: AppMod.t ? := *)
(*   cprog2app console.prog max_num_tasks msg_size_k msg_size. *)
(* Definition oapp_ctrl1: AppMod.t ? := *)
(*   cprog2app (ctrl.prog 1) max_num_tasks msg_size_k msg_size. *)
(* Definition oapp_ctrl2: AppMod.t ? := *)
(*   cprog2app (ctrl.prog 2) max_num_tasks msg_size_k msg_size. *)
(* Definition oapp_dev1: AppMod.t ? := *)
(*   cprog2app (dev.prog 3) max_num_tasks msg_size_k msg_size. *)
(* Definition oapp_dev2: AppMod.t ? := *)
(*   cprog2app (dev.prog 4) max_num_tasks msg_size_k msg_size. *)
(* Definition oapp_dev3: AppMod.t ? := *)
(*   cprog2app (dev.prog 5) max_num_tasks msg_size_k msg_size. *)

(* Definition exec_spec : ExecutableSpec.t := *)
(*   let apps := *)
(*       match deopt_list [oapp_con; oapp_ctrl1; oapp_ctrl2; oapp_dev1; oapp_dev2] with *)
(*       | None => [] *)
(*       | Some apps => apps *)
(*       end *)
(*   in *)
(*   ExecutableSpec.mk _ _ ActiveStandby.period *)
(*                     apps [[1; 2]] *)
(*                     resize_bytes. *)

(* Definition active_standby_itree_decomp: Z -> option Z -> itree _ unit := *)
(*     @ExecutableSpec.sys_itree _ _ exec_spec. *)

(* Cd "./extract_itree/ActiveStandby". *)
(* Extraction "AppSystem.ml" active_standby_itree_decomp. *)
(* Cd "../..". *)
