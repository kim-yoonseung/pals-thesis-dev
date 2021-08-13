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
(* Require console ctrl dev. *)

(* Require Import AcStSystem. *)
(* Require Import SpecConsole SpecController SpecDevice. *)
(* (* Require Import VerifConsole VerifController VerifDevice. *) *)
(* Require Import AcStRefinement. *)

From Coq Require Extraction ExtrOcamlBasic ExtrOcamlString.
(* To avoid stack overflow *)
(* From Coq Require ExtrOcamlNatBigInt. *)

Require Import ZArith List Lia.


(* Definition exec_sys: ExecutableSpec.t := *)
(*   PALSSys.as_exec active_standby_system. *)

(* Extraction Inline exec_sys active_standby_system PALSSys.as_exec . *)

(* extracting this directly makes a huge ml file *)
(* Definition active_standby_itree (tm_init: nat) (tm_fin: option nat) *)
(*   : itree _ _ := *)
(*   ExecutableSpec.exec_itree exec_sys tm_init tm_fin. *)

Definition resize_bytes: bytes -> bytes? :=
  (fun bs => Some
            (firstn 2 bs ++
                    repeat Byte.zero (2 - length bs))).

(* Definition exec_sys': ExecutableSpec.t := *)
(*   ExecutableSpec.mk _ (list byte) *)
(*                     ActiveStandby.period *)
(*                     [con_mod; ctrl_mod 1%Z; ctrl_mod 2%Z; *)
(*                     dev_mod; dev_mod; dev_mod] *)
(*                     [[1; 2]] *)
(*                     resize_bytes *)
(* . *)

(* Local Opaque ActiveStandby.period. *)
(* Local Opaque Z.of_nat Z.to_nat. *)

(* Lemma exec_sys_equiv: exec_sys = exec_sys'. *)
(* Proof. *)
(*   unfold exec_sys. *)
(*   unfold PALSSys.as_exec. *)
(*   unfold RTSysEnv.period. s. *)
(*   rewrite Z2Nat.id by ss. *)
(*   ss. *)
(* Qed. *)

(* Definition active_standby_itree *)
(*   : _ -> _ -> itree _ _ := *)
(*   ExecutableSpec.sys_itree exec_sys'. *)

(* (* Cd "./extract/ActiveStandby". *) *)
(* (* Extraction "AppSystem.ml" active_standby_itree. *) *)
(* (* Cd "../..". *) *)

(** Extracting ITree system *)

(* Extraction "ExecITree.ml" ExecutableSpec.exec_itree. *)

Definition max_num_tasks: nat := 16.
Definition msg_size_k: Z := 1.
Definition msg_size: Z := 2.

Definition oapp_mast: AppMod.t ? :=
  cprog2app master.prog max_num_tasks msg_size_k msg_size.
Definition oapp_work (tid: Z): AppMod.t ? :=
  cprog2app (worker.prog tid) max_num_tasks msg_size_k msg_size.

Definition JobDistr_period: Z := 1000000000.

Definition exec_sys' : ExecutableSpec.t :=
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

Definition system_itree: Z -> option Z -> itree _ unit :=
  @ExecutableSpec.sys_itree _ _ exec_sys'.

Definition system_synch_period: Z := JobDistr_period.

Cd "./extract_job_distr/JobDistr".
Extraction "AppSystem.ml" system_itree system_synch_period.
Cd "../..".
