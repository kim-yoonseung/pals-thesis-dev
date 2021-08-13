From ITree Require Import ITree.
From Paco Require Import paco.
From compcert Require Import Integers.

Require Import sflib.

Require Import StdlibExt.
Require Import IntegersExt.
Require Import SyncSysModel.
Require Import CProgEventSem.
Require Import Executable.
Require Import PALSSystem.

From Coq Require Extraction ExtrOcamlBasic ExtrOcamlString.
Require Import ZArith List Lia.

Definition resize_bytes (sz: nat): bytes -> bytes? :=
  (fun bs => Some (RTSysEnv.resize_bytes sz bs)).

Definition generic_itree: @ExecutableSpec.t obsE bytes ->
                          Z -> option Z -> itree _ unit :=
  ExecutableSpec.sys_itree.

Cd "./extr/generic".
Extraction "Generic.ml" resize_bytes generic_itree.
Cd "../..".
