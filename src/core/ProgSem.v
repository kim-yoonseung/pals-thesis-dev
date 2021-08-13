From ITree Require Import ITree Recursion Interp.
From compcert Require Clight.
From compcert Require Import Values Memory Globalenvs.

Require Import Paco.paco.

Require Import sflib ITreeTac.
Require Import StdlibExt.
Require Import SysSem.
(* Require Import IPModel. *)

Require Import Lia.

Generalizable Variable progE.


Module Prog.
  Record t {progE: Type -> Type}: Type :=
    mk { state: Type ;

         initial_state: state -> Prop ;
         step: state -> state -> Prop;
         at_event: state -> event_call progE -> Prop ;
         after_event: state -> event progE -> state -> Prop ;
         final_state: state -> Prop ;

         (* step_event_disjoint: *)
         (*   forall st, ~ ((exists st', step st st') /\ *)
         (*            (exists R (e: extE R), at_event st e)) ; *)
       }.

  Inductive stuckstate {progE} (prog: @t progE)
            (st: prog.(state)): Prop :=
    StuckState
      (STUCK_STEP: ~ exists st', prog.(step) st st')
      (NOT_AT_EVENT: ~ exists (ec: event_call progE),
                         prog.(at_event) st ec)
      (NOT_FINAL: ~ prog.(final_state) st)
  .

  Definition prog_behavior (progE: Type -> Type) : Type :=
    colist (event progE).

  (* internal star-steps *)
  Inductive tau_steps {progE} (prog: @t progE)
    : state prog -> state prog -> Prop :=
  | TauSteps_Refl st
    : tau_steps prog st st
  | TauSteps_Trans
      st0 st1 st2
      (STEP1: step _ st0 st1)
      (TAU_STEPS_REST: tau_steps prog st1 st2)
    : tau_steps prog st0 st2
  .

  Lemma tau_steps_app
        progE (prog: @t progE)
        pst1 pst2 pst3
        (TAU1: tau_steps prog pst1 pst2)
        (TAU2: tau_steps prog pst2 pst3)
    : tau_steps prog pst1 pst3.
  Proof.
    induction TAU1; ss.
    econs; eauto.
  Qed.

  (* For now, not used in our development*)
  Section PROG_BEHAVIOR.
    Context {progE: Type -> Type}.
    Variable prog: @t progE.

    Inductive _behav_state
              (behav_state: state prog -> prog_behavior progE -> Prop)
      : state prog -> prog_behavior progE -> Prop :=
    | BehavState_UB
        st st_stk pbeh
        (TAU_STEPS_TO_STUCK: tau_steps prog st st_stk)
        (STUCK: stuckstate prog st_stk)
      : _behav_state behav_state st pbeh

    | BehavState_Term
        st
        (FINAL_STATE: final_state _ st)
      : _behav_state behav_state st cnil
    | BehavState_Inftau (* both terminating & silent looping *)
        st st'
        (STEP: step _ st st')
        (INFTAU: behav_state st' cnil)
      : _behav_state behav_state st cnil
    | BehavState_Step
        R (e: progE R) (r: R) pbeh
        st0 st1 st2
        (TAU_STEPS: tau_steps _ st0 st1)
        (AT_EVT: at_event _ st1 (EventCall e))
        (AFT_EVT: after_event _ st1 (Event e r) st2)
        (BEH_AFTER: behav_state st2 pbeh)
      : _behav_state behav_state st0 (ccons (Event e r) pbeh)
    .

    Hint Constructors _behav_state : paco.

    Lemma behav_state_monotone: monotone2 _behav_state.
    Proof. pmonauto. Qed.

    Definition behav_state
      : state prog -> prog_behavior progE -> Prop :=
      paco2 _behav_state bot2.

    Definition behav_prog (pbeh: prog_behavior progE): Prop :=
      ~ (exists st_i: state prog, initial_state _ st_i) \/
      (exists st_i, initial_state _ st_i /\
               behav_state st_i pbeh).

  End PROG_BEHAVIOR.

  Section WF.
    (* Context `{event_conds progE}. *)
    Context `{progE: Type -> Type}.
    Variable prog: @t progE.

    Record wf: Prop :=
      Wf { step_evt_disj:
             forall pst,
               ~ ((exists pst', Prog.step prog pst pst') /\
                  (exists (ec: event_call progE),
                      Prog.at_event prog pst ec)) ;
           final_nostep:
             forall pst
               (FINAL: Prog.final_state prog pst),
               (~ exists pst', Prog.step prog pst pst') /\
               (~ exists (ec: event_call progE),
                     Prog.at_event prog pst ec) ;
           at_event_det:
             forall pst (ec1 ec2: event_call progE)
               (AT_EVT1: Prog.at_event prog pst ec1)
               (AT_EVT2: Prog.at_event prog pst ec2),
               ec1 = ec2 ;
         }.

  End WF.
End Prog.

Hint Resolve Prog.behav_state_monotone: paco.
(* Hint Resolve Prog.safe_state_monotone: paco. *)


(** ** InteractionTree Program Semantics *)

Section ITREE_PROG.
  Variable progE: Type -> Type.
  Let t : Type := nat * itree progE unit.

  Inductive itree_step: t -> t -> Prop :=
  | ITreeStep_Index
      idx itr
    : itree_step (S idx, itr) (idx, itr)
  | ITreeStep_ObsTau
      itr idx' itr'
      (OBS_TAU: observe itr = TauF itr')
    : itree_step (O, itr) (idx', itr')
  .

  Inductive itree_at_event: t -> event_call progE -> Prop :=
    ITreeAtEvent
      R itr (e: progE R) k
      (OBS: observe itr = VisF e k)
    : itree_at_event (O, itr) (EventCall e)
  .

  Inductive itree_after_event: t -> event progE -> t -> Prop :=
    ITreeAfterEvent
      R itr (e: progE R) k (r: R) itr' idx'
      (OBS: observe itr = VisF e k)
      (AFTER_EVENT: k r = itr')
    : itree_after_event (O, itr) (Event e r) (idx', itr')
  .

  Inductive itree_final_state: t -> Prop :=
    ITreeFinalState
      itr
      (OBS_RET: observe itr = RetF tt)
    : itree_final_state (O, itr)
  .

  Inductive itree_init_state (itr: itree _ _): t -> Prop :=
    ITreeInitState idx
    : itree_init_state itr (idx, itr)
  .

  Definition prog_of_itree (itr: itree _ _)
    : @Prog.t progE :=
    Prog.mk _ _
            (itree_init_state itr) itree_step
            (@itree_at_event) (@itree_after_event)
            itree_final_state
  .

  Lemma wf_prog_of_itree itr
    : Prog.wf (prog_of_itree itr).
  Proof.
    econs.
    - ss. intros pst [STEP AT_EVT].
      des.
      inv STEP; inv AT_EVT.
      congruence.
    - ss. intros pst FIN.
      inv FIN.
      split.
      + intro STEP. des.
        inv STEP. congruence.
      + intro AT_EVT. des.
        inv AT_EVT. congruence.
    - i. inv AT_EVT1. inv AT_EVT2.
      rewrite OBS in *. clarify. existT_elim.
      congruence.
  Qed.

End ITREE_PROG.


Section ITREE_PROG_LEMMAS.
  Context {E: Type -> Type}.
  Variable itr_prog: itree E unit.
  Let prog: Prog.t := prog_of_itree _ itr_prog.

  Lemma iprog_tau_idx_decr
        k n itr
        (IDX : k <= n)
    : Prog.tau_steps prog (n, itr) (k, itr).
  Proof.
    induction n as [| n' IH]; ss.
    { assert (k = 0) by nia.
      subst k. econs 1. }

    inv IDX.
    - econs 1.
    - hexploit IH; eauto. i.
      econs 2; eauto.
      econs.
  Qed.

  Corollary iprog_tau_idx_zero itr idx
    : Prog.tau_steps prog (idx, itr) (0, itr).
  Proof.
    apply iprog_tau_idx_decr. nia.
  Qed.

  Lemma iprog_tau_cases
        pst n itr
    : Prog.tau_steps prog (n, itr) pst <->
      (exists k, k <= n /\ pst = (k, itr)) \/
      Prog.tau_steps prog (0, itr) pst.
  Proof.
    induction n as [| n' IH]; ss.
    { split; eauto.
      intros [IDX | TAUS]; ss.
      des.
      assert (k = 0) by nia.
      subst. econs.
    }

    split.
    - intros TAUS_S.
      inv TAUS_S.
      + left. esplits; eauto.
      + inv STEP1.
        eapply IH in TAU_STEPS_REST.
        des; eauto.
    - intros [IDX | TAUS].
      + des. subst. eapply iprog_tau_idx_decr; eauto.
      + destruct IH as [? IH2].
        hexploit IH2.
        { right. apply TAUS. }
        i. econs 2; eauto.
        econs.
  Qed.

  Lemma iprog_two_taus_det
        pst itr1 itr2
        (TAU1: Prog.tau_steps prog pst (O, itr1))
        (TAU2: Prog.tau_steps prog pst (O, itr2))
    : Prog.tau_steps prog (O, itr1) (O, itr2) \/
      Prog.tau_steps prog (O, itr2) (O, itr1).
  Proof.
    induction TAU1; i; ss.
    { eauto. }
    inv STEP1; ss.
    - (* index *)
      inv TAU2. ss.
      inv STEP1.
      eapply IHTAU1; eauto.
    - (* itree tau *)
      inv TAU2; ss.
      + right. econs 2; eauto.
        econs; eauto.
      + assert (exists n, st1 = (n, itr')).
        { inv STEP1.
          eexists. f_equal.
          congruence.
        }
        des. subst.
        eapply IHTAU1.

        clear - TAU_STEPS_REST.
        eapply iprog_tau_cases in TAU_STEPS_REST. des.
        * clarify.
          eapply iprog_tau_idx_decr. nia.
        * eapply iprog_tau_cases. eauto.
  Qed.

  Lemma iprog_tau_ret_noevt
        pst pst_f pst'
        (TAU_STEPS1: Prog.tau_steps prog pst pst_f)
        (PROG_FINAL: itree_final_state _ pst_f)
        (TAU_STEPS2: Prog.tau_steps prog pst pst')
    : forall (ec: event_call E), ~ itree_at_event _ pst' ec.
  Proof.
    intros ? AT_EVT.
    inv AT_EVT.
    destruct pst_f as [? itr_f]. inv PROG_FINAL.
    hexploit (iprog_two_taus_det pst itr_f itr); eauto.
    intros [A|B]; ss.
    - inv A.
      + congruence.
      + inv STEP1. congruence.
    - inv B.
      + congruence.
      + inv STEP1. congruence.
  Qed.


  Lemma iprog_at_event_eq
        pst pst1 pst2
        (ec1 ec2: event_call E)
        (TAU1: Prog.tau_steps prog pst pst1)
        (OBS_EVT1: itree_at_event E pst1 ec1)
        (TAU2: Prog.tau_steps prog pst pst2)
        (OBS_EVT2: itree_at_event E pst2 ec2)
    : fst pst1 = O /\ fst pst2 = O /\
      snd pst1 = snd pst2.
  Proof.
    inv OBS_EVT1. inv OBS_EVT2.
    splits; eauto. ss.
    exploit (iprog_two_taus_det pst).
    { eapply TAU1. }
    { eapply TAU2. }
    intro TAU_CASE. des.
    - inv TAU_CASE; ss.
      inv STEP1. congruence.
    - inv TAU_CASE; ss.
      inv STEP1. congruence.
  Qed.

  Lemma iprog_itree_tau_star_until_zero
        itr itr' idx
        (ITREE_STEPS: itree_tau_star itr itr')
    : Prog.tau_steps prog (idx, itr) (0, itr').
  Proof.
    induction ITREE_STEPS.
    { apply iprog_tau_idx_zero. }
    eapply Prog.tau_steps_app.
    { apply iprog_tau_idx_zero. }

    econs 2; eauto.
    ss. econs. eauto.
  Qed.

End ITREE_PROG_LEMMAS.


(** ** C Program Semantics *)

Class cprog_event (progE: Type -> Type) (* `{event_conds progE} *) : Type :=
  { (* check_event_ef: AST.external_function -> bool ; *)
    cprog_event_call:
      Senv.t -> AST.external_function ->
      list val -> Mem.mem -> event_call progE -> Prop ;
    cprog_event_step:
      Senv.t -> event progE ->
      list val -> Mem.mem -> val -> Mem.mem -> Prop ;

    (* cprog_event_rsp_cond: forall {R}, progE R -> R -> Prop ; *)

    cprog_event_call_det:
      forall ef senv args mem
        (ec1: event_call progE)
        (ec2: event_call progE)
        (AT_EVT1: cprog_event_call senv ef args mem ec1)
        (AT_EVT2: cprog_event_call senv ef args mem ec2),
        ec1 = ec2 ;
  }.


Section CPROG_SEM.
  Variable cprog: Clight.program.
  Context `{cevts: cprog_event progE}.
  Context `{errE -< progE}.

  Let ge : Clight.genv := Clight.globalenv cprog.
  Let state: Type := Clight.state.
  (* Notation progE := (extE +' errE). *)

  Definition cp_at_event_ef (st: state): bool :=
    match st with
    | Clight.Callstate (Ctypes.External ef _ _ _) _ _ _ =>
      (* check_event_ef ef *)
      true
    | _ => false
    end.

  Inductive cp_at_event: state -> event_call progE -> Prop :=
  | CProgAtEvent
      fd args k m
      ef targs tres cconv ec ec'
      (FUNDEF: fd = Ctypes.External ef targs tres cconv)
      (* (CHECK_EVENT: check_event_ef ef = true) *)
      (CPROG_AT_EVENT:
         cprog_event_call (Clight.genv_genv ge) ef
                          args m ec)
      (EXTE_EVENT_CALL: ec' = embed ec)
    : cp_at_event (Clight.Callstate fd args k m) ec'
  | CProgStep_Stuck
      st err_e
      (NON_EVENT_EF: cp_at_event_ef st = false)
      (STEP: forall st', ~ Clight.step2 ge st [] st')
      (NOT_FINAL: forall ret, ~ Clight.final_state st ret)
      (ERR_EVENT: err_e = subevent _ ErrorEvent)
    : cp_at_event st (EventCall err_e)
  .

  Inductive cp_after_event: state -> event progE -> state -> Prop :=
    CProgAfterEvent
      fd args k m
      evt vres m' evt'
      (CPROG_AFTER_EVENT: cprog_event_step
                            (Clight.genv_genv ge) evt
                            args m vres m')
      (EVENT: evt' = embed evt)
    : cp_after_event (Clight.Callstate fd args k m) evt'
                     (Clight.Returnstate vres k m').

  Inductive cp_step: state -> state -> Prop :=
  | CProgStep
      st st'
      (NON_EVENT_EF: cp_at_event_ef st = false)
      (STEP: Clight.step2 ge st [] st')
    : cp_step st st'
  .

  Inductive cp_final_state : state -> Prop :=
    CProgFinalState
      st vret
      (CLIGHT_FINAL: Clight.final_state st vret)
    : cp_final_state st.

  Definition prog_of_clight: @Prog.t progE :=
    Prog.mk progE state
      (Clight.initial_state cprog)
      cp_step cp_at_event cp_after_event cp_final_state
  .

  Definition cprog_wf : @Prog.wf progE prog_of_clight.
  Proof.
    econs; ss.
    - i. intros [CP_STEP CP_EVT]. des.
      inv CP_STEP. inv CP_EVT; ss.
      eapply STEP0. eauto.
    - intros pst CP_FINAL.
      inv CP_FINAL. inv CLIGHT_FINAL.
      split.
      + intro CP_STEP. des. inv CP_STEP. ss.
        inv STEP.
      + intro CP_EVT. des. inv CP_EVT.
        ss.
        eapply NOT_FINAL. econs.

    - intros ? ? ? AT_EVT1 AT_EVT2.
      inv AT_EVT1; inv AT_EVT2; clarify.
      cut (ec = ec0).
      { i. clarify. }
      eapply cprog_event_call_det; eauto.
  Qed.

End CPROG_SEM.
