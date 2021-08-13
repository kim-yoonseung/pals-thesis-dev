From ITree Require Import ITree.
From compcert Require Import Maps AST Values Memory Globalenvs Ctypes.
From compcert Require Coqlib Clight Clightdefs.
From Paco Require Import paco.

Require Import Arith ZArith Bool.
Require Import String List Lia.

Require Import sflib.
Require Import Axioms StdlibExt IntegersExt ITreeTac.

Require Import SysSem.
Require Import IPModel DiscreteTimeModel IntByteModel.
Require Import OSNodes.

Require Import ProgSem CProgEventSem.
Require Import ProgSim CProgSimLemmas.
Require Import SyncSysModel.
Require Import RTSysEnv MWITree.
Require Import NWSysModel.

Require Import config_prm main_prm SystemProgs.
Require Import VerifProgBase.
Require Import VerifMainUtil VerifFetchMsgs VerifTask VerifInit.

Import Clight Clightdefs.
Import ITreeNotations.

Set Nested Proofs Allowed.

Section VERIF_MAIN.
  Context `{SimApp}.
  Let prog: Prog.t := prog_of_clight cprog.
  Let ge := Clight.globalenv cprog.

  (* Context `{ SimApp cprog }. *)
  Context `{ genv_props
               ge
               (main_gvar_ilist tid ++ app_gvar_ilist)
               (main_gfun_ilist ++ app_gfun_ilist)
               (main_cenv_ilist ++ app_cenv_ilist) }.

  Notation sim := (paco3 (_sim_itree _)).
  (* Notation progE := (OSModel.osE +' OSNodes.tlimE +' extcallE). *)

  Hypothesis INIT_MEM_OK: Genv.init_mem cprog <> None.
  (* Hypothesis INV_APP_INIT: *)
  (*   forall m_i, Genv.init_mem cprog = Some m_i -> *)
  (*          inv_app ge ast_i m_i. *)
  Hypothesis MAIN_IDENT: prog_main cprog = _main.

  Let prog_itree: itree progE unit :=
    MWITree.main_itree tid app_mod.

  Lemma sim_main: sim_itree_prog prog prog_itree.
  Proof.
    eapply sim_init; eauto. i.
    eapply sim_run_task; eauto.
  Qed.

End VERIF_MAIN.
