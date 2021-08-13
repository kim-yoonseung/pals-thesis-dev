From Paco Require Import paco.
From ITree Require Import ITree.
Require Import sflib.

Require Import StdlibExt IntegersExt.
Require Import SysSem.
Require Import SyncSysModel.
Require Import RTSysEnv.
Require Import Executable.

Require Import MSteps.
Require Import FMSim FMSim_Switch.
Require Import PALSSystem.
Require Import BehavUtils.
Require Import CProgEventSem.

Require Import ZArith Streams List Lia.

Local Opaque Z.of_nat Z.to_nat.

Set Nested Proofs Allowed.

(* Arguments Nat.min: simpl nomatch. *)
(* Arguments nth_error: simpl nomatch. *)

Import ExecutableSpec.
Import ITreeNotations.

Section EXECUTABLE_PROPS.
  Context {E: Type -> Type}.
  Context {msgT: Set}.
  Notation lst_t := (@loc_state E msgT).

  Variable sys: @ExecutableSpec.t E msgT.
  Variable tm_init: Z.
  Let dsys: DSys.t := ExecutableSpec.as_dsys sys tm_init None.

  Let prd: Z := period sys.
  Let nts: nat := (length (apps sys)).
  Let mcs: list (list nat) := (mcasts sys).
  Let sntz: msgT -> msgT? := (sanitize_msg sys).

  (* Definition safe_trace (tr: events obsE): Prop := *)
  (*   Forall (fun evt => exists (evt_ec: event extcallE), *)
  (*               evt = embed evt_ec) tr. *)

  Inductive run_itree {ast_t: Type}
            (outbox: list (msgT?))
            (itr: itree (E +' @abst_sendE msgT) ast_t)
    : events E -> ast_t? -> list (msgT?) -> Prop :=
  | RunITree_Fail
    : run_itree outbox itr [] None outbox
  | RunITree_Ret
      ast_f
      (OBS_RET: observe itr = RetF ast_f)
    : run_itree outbox itr [] (Some ast_f) outbox
  | RunITree_Tau
      itr' es oast outbox'
      (OBS_TAU: observe itr = TauF itr')
      (RUN_REST: run_itree outbox itr' es oast outbox')
    : run_itree outbox itr es oast outbox'
  | RunITree_Event
      R (e: E R) (k: R -> itree _ ast_t)
      (r: R) es' oast outbox'
      (OBS_EVT: observe itr = VisF (inl1 e) k)
      (RUN_REST: run_itree outbox (k r) es' oast outbox')
    : run_itree outbox itr (Event e r :: es') oast outbox'
  | RunITree_Send
      tid_d msg outbox1
      (k: unit -> itree _ ast_t)
      es oast outbox'
      (OBS_SEND: observe itr = VisF (inr1 (AbstSendEvent
                                             tid_d msg)) k)
      (UPDATE_OUTBOX: update_outbox
                        nts mcs sntz
                        outbox tid_d msg = outbox1)
      (RUN_REST: run_itree outbox1 (k tt) es oast outbox')
    : run_itree outbox itr es oast outbox'
  .

  Inductive run_local (sytm: Z)
            (inb: list (msgT?))
    : lst_t -> events E -> lst_t * list (msgT?) -> Prop :=
  | RunLocal_Off
      app oast
    : run_local sytm inb
                (LocState app oast) [] (LocState app None, [])

  | RunLocal_On
      app ast
      (INIT_AST: ast = AppMod.init_abst_state app)
    : run_local sytm inb
                (LocState app None) [] (LocState app (Some ast), [])

  | RunLocal_RunPeriod
      app ast
      itr es out oast'
      (PINIT_ITREE: itr = AppMod.job_itree app sytm inb ast)
      (RUN_ITREE: run_itree (repeat None (length (apps sys))) itr
                            es oast' out)
    : run_local sytm inb
                (LocState app (Some ast)) es (LocState app oast', out)
  .

  Definition state_of (tm_p tm: Z)
             (inbs: list (list msgT?)) (lsts: list lst_t)
    : Z * itree (tgd (E +' randE) +' tspE) unit :=
    (tm_p, interp_ainvk
             sys unit
             (synch_itree_loop nts prd None tm inbs)
             lsts ;;
           Ret tt).

  Definition lift_trace (tm: Z) (tr: list (events E))
    : list (list (Z * events E)) :=
    map (fun es: events E => [(tm, es)]) tr.


  Inductive abs_step (tm: Z)
            (inbs: list (list msgT?))
            (lsts: list lst_t)
    : (list (list (Z * events E)) *
       list (list msgT?) * list lst_t) -> Prop :=
    AbsStep
      tr_raw lsts_out
      inbs' lsts' tr
      (LOCAL_STEPS: Forall4 (run_local tm) inbs lsts
                            tr_raw lsts_out)
      (INBS1: inbs' = imap (fun tid _ => map (SNode.get_outbox_msg_by_dest tid) (map snd lsts_out))
                           0 (repeat tt nts))
      (LSTS1: lsts' = map fst lsts_out)
      (TR_EQV: Forall2 tes_equiv tr (lift_trace tm tr_raw))
    : abs_step tm inbs lsts (tr, inbs', lsts').

  Lemma exec_div_one_period
        tm_p (tm: Z) inbs lsts st exec
        (SYNC: (prd | tm)%Z)
        (STATE: st = state_of tm_p tm inbs lsts)
        (EXEC_ST: DSys.exec_state dsys st exec)
    : exists scnt tr inbs' lsts'
        st' exec',
      <<EXEC_DIV: sapp_each_rel tr exec' exec>> /\
      <<MSTEPS_PRD: msteps dsys scnt st tr st'>> /\
      <<ABS_STEP: abs_step tm inbs lsts (tr, inbs', lsts')>> /\
      <<STATE': st' = state_of tm (tm + prd)%Z inbs' lsts'>> /\
      <<EXEC_ST': DSys.exec_state dsys st' exec'>>.
  Proof.
  Admitted.

  Inductive exec_chain (tm: Z)
            (inbs: list (list msgT?))
            (lsts: list lst_t)
    : list (list (list (Z * events E)) *
            list (list msgT?) * list lst_t) -> Prop :=
  | ExecChain_Base
    : exec_chain tm inbs lsts []
  | ExecChain_Cons
      tr inbs1 lsts1 echn_t
      (ABS_STEP: abs_step tm inbs lsts (tr, inbs1, lsts1))
      (REST_CHAIN: exec_chain (tm + prd)%Z inbs1 lsts1 echn_t)
    : exec_chain tm inbs lsts ((tr, inbs1, lsts1) :: echn_t).

  Fixpoint app_each_c {A}
           (l1 l2: list (list A)): list (list A) :=
    match l1, l2 with
    | [], _ => []
    | _, [] => []
    | h1 :: t1, h2 :: t2 => ((h1 ++ h2) :: app_each_c t1 t2)
    end.

  Fixpoint trace_of_chain
           (chn: list (list (list (Z * events E)) *
                       list (list msgT?) * list lst_t))
    : list (list (Z * events E)) :=
    match chn with
    | [] => repeat [] nts
    | h :: t => app_each_c (fst (fst h)) (trace_of_chain t)
    end.

  Definition echn_last inbs lsts
             (echn: list (list (list (Z * events E)) *
                          list (list msgT?) * list lst_t))
    : list (list msgT?) * list lst_t :=
    last' (map (fun x => (snd (fst x), snd x)) echn) (inbs, lsts).

  Lemma exec_div_k_times
        tm_p (tm: Z) inbs lsts st exec
        (k: nat)
        (SYNC: (prd | tm)%Z)
        (STATE: st = state_of tm_p tm inbs lsts)
        (EXEC_ST: DSys.exec_state dsys st exec)
    : exists tr exec' scnt st'
        echn inbs' lsts'
        tm_p'
    ,
      <<EXEC_DIV: sapp_each_rel tr exec' exec>> /\
      <<MSTEPS_PRD: msteps dsys scnt st tr st'>> /\
      <<EXEC_CHAIN: exec_chain tm inbs lsts echn>> /\
      <<ECHN_LAST: echn_last inbs lsts echn = (inbs', lsts')>> /\
      <<ECHN_LEN: length echn = k>> /\

      <<TR_EQV: Forall2 tes_equiv tr (trace_of_chain echn)>> /\
      <<STATE': st' = state_of tm_p' (tm + Z.of_nat k * prd)%Z inbs' lsts'>> /\
      <<EXEC_ST': DSys.exec_state dsys st' exec'>>.
  Proof.
  Admitted.

  Lemma exec_event_time_cond
        tm_p (tm: Z) inbs lsts st exec
        tid_evt tm_evt (evt: event E)
        (SYNC: (prd | tm)%Z)
        (STATE: st = state_of tm_p tm inbs lsts)
        (EXEC_ST: DSys.exec_state dsys st exec)
        (EVENT_IN_EXEC: event_in_exec tid_evt tm_evt evt exec)
    : <<TM_EVT_SYNC: (prd | tm_evt)%Z>> /\
      <<TM_EVT_NOT_PAST: (tm <= tm_evt)%Z>>.
  Proof.
  Admitted.

  Lemma event_in_exec_must_in_tr
        (exec exec': exec_t E) tr
        tid (t:Z) e st'
        tm_p' tm' inbs' lsts'
        (IN_EXEC: event_in_exec tid t e exec)
        (EXEC_DIV: sapp_each_rel tr exec' exec)
        (EXEC_STATE: DSys.exec_state dsys st' exec')
        (STATE: st' = state_of tm_p' tm' inbs' lsts')
        (TIME_BEFORE: (t < tm')%Z)
    : event_in_tr tid t e tr.
  Proof.
  Admitted.

End EXECUTABLE_PROPS.
