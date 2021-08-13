Require Import Paco.paco.
From ITree Require Import ITree.

Require Import sflib.
Require Import ITreeTac.
Require Import Axioms.
Require Import StdlibExt.

Require Import Streams.
Require Import List.
Require Import Arith ZArith Lia.

(* Set Implicit Arguments. *)
Set Nested Proofs Allowed.


(* Lemma stream_app_eq_prefix_eq A *)
(*       pref (s1 s2: stream A) *)
(*   : s1 = s2 <-> stream_app pref s1 = stream_app pref s2. *)
(* Proof. *)
(*   induction pref as [| h t IH]; ss. *)
(*   split. *)
(*   - intro TEQ. subst. clarify. *)
(*   - intro CONS_EQ. clarify. *)
(*     apply IH. eauto. *)
(* Qed. *)




(* Lemma deopt_list_Some_length A *)
(*       (l: list A?) (l': list A) *)
(*       (DEOPT: deopt_list l = Some l') *)
(*   : length l' = length l. *)
(* Proof. *)
(*   depgen l'. *)
(*   induction l as [| h t IH]; i; ss. *)
(*   { clarify. } *)

(*   destruct h; desf. *)
(*   hexploit IH; eauto. i. ss. *)
(*   congruence. *)
(* Qed. *)


(** * Basic Event Definitions *)

(** InteractionTree-style events *)

(* event call (without response) *)
Inductive event_call (E: Type -> Type): Type :=
  EventCall: forall R (e: E R), event_call E.

(* visible event (with response) *)
Inductive event (E: Type -> Type): Type :=
  Event: forall {R} (e: E R) (r: R), event E.

Definition events (E: Type -> Type): Type :=
  list (event E).

Arguments EventCall {E R}.
Arguments Event {E R}.

(* A special event type that cancels execution *)
Inductive nbE: Type -> Type :=
| NobehEvent : nbE unit
.

Inductive errE: Type -> Type :=
| ErrorEvent : errE unit
.


Instance embed_event_call {E1 E2}
         `{E1 -< E2}
  : Embeddable (event_call E1) (event_call E2) :=
  fun ec1 =>
    match ec1 with
    | EventCall e =>
      EventCall (subevent _ e)
    end.

Instance embed_events {E1 E2}
         `{E1 -< E2}
  : Embeddable (event E1) (event E2) :=
  fun ev1 =>
    match ev1 with
    | Event e r =>
      Event (subevent _ e) r
    end.

Instance embed_list {X Y}
         `{Embeddable X Y}
  : Embeddable (list X) (list Y) :=
  List.map (fun x => embed x).

Instance embed_id A
  : Embeddable A A := id.

Instance embed_pair {A A' B B'}
         `{Embeddable A A'}
         `{Embeddable B B'}
  : Embeddable (A * B) (A' * B') :=
  fun x => (embed (fst x), embed (snd x)).

Class EventRetInhabit (E: Type -> Type): Prop :=
  { event_return_inhabit
    : forall R (e: E R), exists r: R, True ; }.

(** * System Semantics *)

(* timestamp type *)
Notation tsp := Z (only parsing).

Definition flatten_te {sysE: Type -> Type}
         (ftr1: tsp * events sysE)
  : list (tsp * event sysE) :=
  map (fun e => (fst ftr1, e)) (snd ftr1).

Definition flatten_tes {sysE: Type -> Type}
         (ftr: list (tsp * events sysE))
  : list (tsp * event sysE) :=
  List.concat (map flatten_te ftr).


Definition tes_equiv {sysE: Type -> Type}
           (ftr1 ftr2: list (tsp * events sysE)): Prop :=
  flatten_tes ftr1 = flatten_tes ftr2.


Lemma tes_equiv_trans E
      (ft1 ft2 ft3: list (tsp * events E))
      (EQV1: tes_equiv ft1 ft2)
      (EQV2: tes_equiv ft2 ft3)
  : tes_equiv ft1 ft3.
Proof.
  inv EQV1. inv EQV2.
  r. congruence.
Qed.


Lemma flatten_tes_app E
      (l1 l2: list (tsp * events E))
  : flatten_tes (l1 ++ l2) =
    flatten_tes l1 ++ flatten_tes l2.
Proof.
  unfold flatten_tes.
  rewrite map_app.
  rewrite concat_app. ss.
Qed.


Lemma Forall2_tes_equiv_trans E
      (trsl1 trsl2 trsl3: list (list (tsp * events E)))
      (EQV1: Forall2 tes_equiv trsl1 trsl2)
      (EQV2: Forall2 tes_equiv trsl2 trsl3)
  : Forall2 tes_equiv trsl1 trsl3.
Proof.
  depgen trsl3.
  induction EQV1; i; ss.
  inv EQV2.
  econs.
  { eapply tes_equiv_trans; eauto. }
  eauto.
Qed.


Lemma tes_when_eff_tstamp_identical E
      tsp1 (tr: list (tsp * events E))
      (TSP_ID: Forall (fun tes => fst tes = tsp1 \/ snd tes = []) tr)
  : flatten_tes tr =
    map (fun e => (tsp1, e)) (concat (map snd tr)).
Proof.
  unfold flatten_tes.
  induction tr as [| h t IH]; ss.
  rewrite map_app. ss.
  inv TSP_ID.
  rewrite IH; eauto.
  f_equal.
  destruct h as [tsp' es'].
  des; ss; subst; ss.
Qed.

Lemma Forall2_tes_equiv_refl E
      (trsl: list (list (tsp * events E)))
  : Forall2 tes_equiv trsl trsl.
Proof.
  induction trsl; ss.
  econs; ss.
Qed.


Section BEHAV_DEF.
  (* Variable ts_t: Type. (* timestamp *) *)
  Variable sysE: Type -> Type. (* system event kind *)

  (* concrete behavior: including tau-event *)
  Definition lexec_t: Type := stream (tsp * events sysE).
  Definition exec_t: Type := list lexec_t.

  Definition lbehav_t: Type := colist (tsp * event sysE).
  Definition behav_t: Type := list lbehav_t.

  (** ** Relations between executions and behaviors *)

  Definition inftau_lexec (lexec: lexec_t): Prop :=
    Forall_stream (fun x => snd x = []) lexec.

  Definition silent_local_trace (tr_loc: list (tsp * events sysE)): Prop :=
    Forall (fun x => snd x = []) tr_loc.


  Lemma inftau_lexec_pref_iff
        (lexec: lexec_t) pref
    : <<INFTAU: inftau_lexec lexec>> /\
      <<SILENT_PREF: silent_local_trace pref>> <->
      inftau_lexec (stream_app pref lexec).
  Proof.
    split.
    - i. des.
      induction pref as [|h t IH]; ss.
      inv SILENT_PREF.
      destruct h as [ts []]; ss.
      pfold. econs; ss.
      left. apply IH. ss.
    - intro INFTAU.
      induction pref as [|h t IH]; ss.
      { esplits; ss. }

      punfold INFTAU. inv INFTAU.
      destruct h as [ts []]; ss.
      pclearbot.
      hexploit IH; eauto. i. des.
      esplits; ss.
      econs; ss.
  Qed.


  Inductive _local_exec_behav
            (_leb: lexec_t -> lbehav_t -> Prop)
    : lexec_t -> lbehav_t -> Prop :=
  | LocalExecBehav_Inftau
      lexec
      (EXEC_SILENT: inftau_lexec lexec)
    : _local_exec_behav _leb lexec cnil

  | LocalExecBehav_Events
      lexec tr_tau lexec' ts es
      beh' beh
      (LOCAL_EXEC_PREFIX: lexec = stream_app tr_tau (Cons (ts, es) lexec'))
      (TRACE_TAU: silent_local_trace tr_tau)
      (EVENTS_NONNIL: es <> [])
      (LOCAL_EXEC_BEHAV_REST: _leb lexec' beh')
      (BEHAVIOR: beh = colist_app (flatten_te (ts, es)) beh')
    : _local_exec_behav _leb lexec beh.

  Hint Constructors _local_exec_behav: paco.

  Lemma local_exec_behav_monotone: monotone2 _local_exec_behav.
  Proof. pmonauto. Qed.

  Definition local_exec_behav: lexec_t -> lbehav_t -> Prop :=
    paco2 _local_exec_behav bot2.

  Definition exec_behav : exec_t -> behav_t -> Prop :=
    List.Forall2 local_exec_behav.

  Hint Resolve local_exec_behav_monotone: paco.

  Lemma not_inftau_ex_events
    : forall exec
        (NOT_EX: ~ exists taus ts es exec',
                     exec = stream_app taus (Cons (ts, es) exec') /\
                     silent_local_trace taus /\
                     es <> []),
      inftau_lexec exec.
  Proof.
    pcofix CIH. i.
    destruct exec as [[ts es] exec'].
    pfold.

    destruct es; ss.
    2: {
      exfalso.
      eapply NOT_EX.
      exists [].
      esplits; eauto; ss.
    }

    econs; eauto; ss.
    right.
    eapply CIH.
    intros (taus' & ts' & es' & exec'' & A & B & C).
    apply NOT_EX.
    exists ((ts, []) :: taus').
    esplits; eauto.
    - subst. ss.
    - r. econs; ss.
  Qed.

  Lemma exec_div_ex
        (lexec: lexec_t)
    : exists ox,
      match ox with
      | None => inftau_lexec lexec
      | Some x =>
        let '(tr_tau, lexec', ts, es) := x in
        lexec = stream_app tr_tau (Cons (ts, es) lexec') /\
        silent_local_trace tr_tau /\
        es <> []
      end.
  Proof.
    destruct (classic (exists tr_tau ts es lexec',
                          lexec = stream_app
                                    tr_tau (Cons (ts, es) lexec') /\
                          silent_local_trace tr_tau /\
                          es <> [])).
    { des.
      eexists (Some (_, _, _, _)).
      esplits; eauto. }

    hexploit not_inftau_ex_events; eauto.
    i.
    exists None. ss.
  Qed.

  Lemma exec_div_sig
        (lexec: lexec_t)
    : { ox |
        match ox with
        | None => inftau_lexec lexec
        | Some x =>
          let '(tr_tau, lexec', ts, es) := x in
          lexec = stream_app tr_tau (Cons (ts, es) lexec') /\
          silent_local_trace tr_tau /\
          es <> []
        end }.
  Proof.
    apply constructive_indefinite_description.
    eapply exec_div_ex.
  Qed.

  CoFixpoint local_exec_beh_constr
    : forall (t: Z) (pref: events sysE) (lexec: lexec_t), lbehav_t.
  Proof.
    i.
    destruct pref as [| e_h pref'].
    2: { exact (ccons (t, e_h) (local_exec_beh_constr
                                  t pref' lexec)). }

    pose (SIG := exec_div_sig lexec).

    destruct (proj1_sig SIG) eqn:SIG_DES.
    2: { econs 1. }

    destruct p as [[[tr_tau lexec'] ts] es].

    destruct es as [| es_h es_t].
    { (* exfalso. des. ss. } *)
      econs 1. }

    econs 2.
    { exact (ts, es_h). }



    (* generalize (proj2_sig SIG). *)
    (* rewrite SIG_DES. i. *)
    (* destruct es as [| es_h es_t]. *)
    (* { exfalso. des. ss. } *)

    (* econs 2. *)
    (* { eapply (ts, es_h). } *)
    eapply (local_exec_beh_constr ts es_t lexec').
  Defined.

  Lemma local_exec_beh_constr_pref
        t es exec
    : local_exec_beh_constr t es exec =
      colist_app (map (fun e => (t, e)) es)
                 (local_exec_beh_constr t [] exec).
  Proof.
    induction es as [ | e es' IH]; ss.
    match goal with
    | |- ?lhs = _ =>
      rewrite (unfold_colist _ lhs)
    end.
    s. rewrite IH. ss.
  Qed.

  Lemma local_exec_behav_ex exec
    : exists beh, local_exec_behav exec beh.
  Proof.
    exists (local_exec_beh_constr 0 [] exec).
    generalize 0%Z.
    revert exec.
    pcofix CIH. i.

    match goal with
    | |- paco2 _ _ _ ?c =>
      rewrite (unfold_colist _ c)
    end.
    s.
    remember (exec_div_sig exec) as SIG.
    destruct SIG. ss.

    destruct x.
    2: { pfold. econs 1. ss. }

    destruct p as [[[tr_tau lexec'] ts] es].
    desf.
    rewrite local_exec_beh_constr_pref.
    pfold. econs 2; eauto; ss.
  Qed.

  Lemma local_exec_behav_det
    : forall exec beh1 beh2
        (EXEC_BEH1: local_exec_behav exec beh1)
        (EXEC_BEH2: local_exec_behav exec beh2),
      colist_eq beh1 beh2.
  Proof.
    pcofix CIH. i.
    punfold EXEC_BEH1. punfold EXEC_BEH2.
    inv EXEC_BEH1; inv EXEC_BEH2.
    - pfold. econs 1.
    - exfalso.
      clear - EXEC_SILENT EVENTS_NONNIL.

      induction tr_tau as [| ctr_h ctr_t IH]; ss.
      { punfold EXEC_SILENT. inv EXEC_SILENT. ss. }
      r in EXEC_SILENT.
      punfold EXEC_SILENT. inv EXEC_SILENT.

      pclearbot. eauto.
    - exfalso.
      clear - EXEC_SILENT EVENTS_NONNIL.

      induction tr_tau as [| ctr_h ctr_t IH]; ss.
      { punfold EXEC_SILENT. inv EXEC_SILENT. ss. }
      r in EXEC_SILENT.
      punfold EXEC_SILENT. inv EXEC_SILENT.

      pclearbot. eauto.

    - assert (tr_tau0 = tr_tau /\ ts0 = ts /\ es0 = es /\ lexec'0 = lexec').
      { hexploit stream_app_3ways; eauto. i. des.
        { exfalso.
          destruct l2r as [|hr tr]; ss.
          { rewrite app_nil_r in *. subst. nia. }
          clarify.
          rr in TRACE_TAU0.
          rewrite Forall_forall in TRACE_TAU0.
          hexploit TRACE_TAU0.
          { instantiate (1:= (ts, es)).
            apply in_or_app. right. ss. eauto. }
          ss.
        }
        { exfalso.
          destruct l1r as [|hr tr]; ss.
          { rewrite app_nil_r in *. subst. nia. }
          clarify.
          rr in TRACE_TAU.
          rewrite Forall_forall in TRACE_TAU.
          hexploit TRACE_TAU.
          { instantiate (1:= (ts0, es0)).
            apply in_or_app. right. ss. eauto. }
          ss.
        }
        clarify.
      }
      des. clarify. pclearbot.

      destruct es as [| es_h es_t]; ss.
      pfold. econs 2.

      induction es_t as [| h t IH]; ss.
      { eauto. }
      left. pfold. econs 2.
      apply IH; ss.
  Qed.


  Lemma inftau_lexec_Cons
        (lexec: lexec_t) ts
    : inftau_lexec lexec <->
      inftau_lexec (Cons (ts, []) lexec).
  Proof.
    split.
    - i. pfold. econs; ss.
      left. ss.
    - intro CONS. punfold CONS. inv CONS. ss. pclearbot. ss.
  Qed.


  Lemma local_exec_beh_div
        (lexec: lexec_t) beh
        tr lexec'
        (EBEH: local_exec_behav lexec beh)
        (LEXEC_DIV: lexec = stream_app tr lexec')
    : exists beh',
      <<BEH_DIV: beh = colist_app (flatten_tes tr) beh'>> /\
      <<EBEH': local_exec_behav lexec' beh'>>.
  Proof.
    subst lexec. depgen beh.
    induction tr as [| h_tr t_tr IH]; i; ss.
    { esplits; eauto. }

    destruct h_tr as [ts [| h_e t_e]].
    { unfold flatten_tes. ss.
      fold (flatten_tes t_tr).

      eapply (IH beh).
      punfold EBEH. inv EBEH.
      - pfold. econs.
        apply inftau_lexec_Cons in EXEC_SILENT. ss.
      - destruct tr_tau as [| h_tau t_tau]; ss; clarify.
        pclearbot.
        pfold. econs 2; eauto.
        inv TRACE_TAU. ss.
    }

    punfold EBEH. inv EBEH.
    - exfalso.
      punfold EXEC_SILENT. inv EXEC_SILENT. ss.
    - destruct tr_tau; ss.
      2: { exfalso. clarify.
           inv TRACE_TAU. ss. }
      clarify. rename ts0 into ts.
      pclearbot.
      hexploit IH; eauto. i. des. clarify.
      esplits; eauto.
      ss. rewrite colist_app_assoc. ss.
  Qed.

  (* silent *)
  Lemma flatten_silent_local_trace_iff
        (tr: list (tsp * events sysE))
    : silent_local_trace tr <->
      flatten_tes tr = [].
  Proof.
    unfold flatten_tes, silent_local_trace.
    split.
    - intro SILENT_PREF.
      induction SILENT_PREF; ss.
      destruct x; ss. clarify.
    - intro MAP.
      induction tr; ss.
      destruct a as [ts []]; ss.
      econs; ss.
      apply IHtr. ss.
  Qed.

  Lemma silent_tes_equiv
        (tr1 tr2: list (tsp * events sysE))
        (SILENT: silent_local_trace tr2)
        (EQUIV: tes_equiv tr1 tr2)
    : silent_local_trace tr1.
  Proof.
    unfold tes_equiv in EQUIV.
    apply flatten_silent_local_trace_iff in SILENT.
    apply flatten_silent_local_trace_iff.
    congruence.
  Qed.

End BEHAV_DEF.

Section BEHAV2_DEF.
  (* behavior considering ErrorEvent *)
  Variable safe_sysE: Type -> Type.

  Notation sysE := (safe_sysE +' errE).

  Fixpoint trace_find_error (es: events sysE)
    : (events safe_sysE) * bool :=
    match es with
    | [] => ([], false)
    | Event e r :: es' =>
      match e with
      | inl1 ssys_e =>
        let (ssys_es', b) := trace_find_error es' in
        (Event ssys_e r :: ssys_es', b)
      | inr1 err_e =>
        ([], true)
      end
    end.


  Lemma trace_find_error_spec
        (es: events sysE) es_s b
        (TR_ERR: trace_find_error es = (es_s, b))
    : (if b then
         exists es1 es2,
           es = es1 ++ [Event (inr1 ErrorEvent) tt] ++ es2 /\
           map embed es_s = es1
       else map embed es_s = es:Prop).
  Proof.
    depgen es_s.
    induction es as [| h t]; i; ss.
    { clarify. }
    destruct h as [T [] r].
    2: {
      clarify.
      destruct e.
      destruct r.
      exists [].
      esplits; ss.
    }

    destruct (trace_find_error t) as [es_s' b'].
    clarify.
    hexploit IHt; eauto. i.
    destruct b.
    - des. subst.
      eexists (Event (inl1 s) r :: _).
      esplits; ss.
    - subst. ss.
  Qed.


  Inductive _local_exec_behav2
            (_leb: lexec_t sysE -> lbehav_t safe_sysE -> Prop)
    : lexec_t sysE -> lbehav_t safe_sysE -> Prop :=
  | LocalExecBehav2_Inftau
      lexec
      (EXEC_SILENT: inftau_lexec _ lexec)
    : _local_exec_behav2 _leb lexec cnil

  | LocalExecBehav2_Events
      lexec tr_tau lexec' ts es
      beh' beh
      es_safe is_err
      (LOCAL_EXEC_PREFIX: lexec = stream_app tr_tau (Cons (ts, es) lexec'))
      (TRACE_TAU: silent_local_trace _ tr_tau)
      (EVENTS_NONNIL: es <> [])
      (TRACE_ERROR: trace_find_error es = (es_safe, is_err))
      (LOCAL_EXEC_BEHAV_REST:
         if is_err then True else _leb lexec' beh')
      (BEHAVIOR: beh = colist_app (flatten_te (ts, es_safe)) beh')
    : _local_exec_behav2 _leb lexec beh
  .

  Hint Constructors _local_exec_behav2: paco.

  Lemma local_exec_behav2_monotone: monotone2 _local_exec_behav2.
  Proof.
    ii. inv IN.
    - eauto with paco.
    - desf.
      + econs; eauto.
      + econs; eauto.
        s. eauto.
  Qed.

  Definition local_exec_behav2: lexec_t _ -> lbehav_t _ -> Prop :=
    paco2 _local_exec_behav2 bot2.

  Definition exec_behav2 : exec_t _ -> behav_t _ -> Prop :=
    List.Forall2 local_exec_behav2.


End BEHAV2_DEF.

Arguments inftau_lexec [sysE].
Arguments local_exec_behav [sysE].
Arguments exec_behav [sysE].
Arguments local_exec_behav2 [safe_sysE].
Arguments exec_behav2 [safe_sysE].

Hint Resolve local_exec_behav_monotone: paco.
Hint Resolve local_exec_behav2_monotone: paco.


(* Distributed system *)
Module DSys.
  Section SYSTEM_SEM.
    Context {sysE: Type -> Type}.

    Definition filter_nb1 (e: event (nbE +' sysE))
      : (event sysE)? :=
      match e with
      | Event er r =>
        match er with
        | inl1 nbe => None
        | inr1 syse => Some (Event syse r)
        end
      end.

    Definition filter_nb_localstep
               (tes: (tsp * events (nbE +' sysE)))
      : (tsp * events sysE)? :=
      let es' := deopt_list (map filter_nb1 (snd tes)) in
      option_map (fun es => (fst tes, es)) es'.

    Definition filter_nb_sysstep
               (es: list (tsp * events (nbE +' sysE)))
      : (list (tsp * events sysE))? :=
      deopt_list (List.map filter_nb_localstep es).

    (** ** System Semantics  *)
    Record t: Type :=
      mk { state: Type ;
           num_sites : state -> nat ;
           step: state -> list (tsp * events (nbE +' sysE)) -> state -> Prop ;
           initial_state: state -> Prop ;

           step_prsv_num_sites:
             forall st es st' (STEP: step st es st'),
               <<NUM_EVTS: length es = num_sites st>> /\
               <<NUM_SITES_AFTER:
                 num_sites st' = num_sites st>> ;
        }.


    (* Lemma filter_nobeh_Some_length *)
    (*       es es' *)
    (*       (FILTER: filter_nobeh es = Some es') *)
    (*   : length es' = length es. *)
    (* Proof. *)
    (*   unfold filter_nobeh in *. *)
    (*   hexploit deopt_list_Some_length; eauto. *)
    (*   rewrite map_length. ss. *)
    (* Qed. *)

    Section BEHAVIOR.
      (* Context {sys: t}. *)
      Variable sys: t.

      Inductive _exec_state
                (exec_st: state sys -> exec_t sysE -> Prop)
        : state sys -> exec_t sysE -> Prop :=
      | ExecState_Stuck
          st exec_undef
          (STUCK: ~ exists es st', step _ st es st')
          (EXEC_LEN: length exec_undef = num_sites _ st)
        : _exec_state exec_st st exec_undef

      | ExecState_Step
          st es st'
          es_sysE exec' exec
          (STEP: step _ st es st')
          (FILTER_NOBEH: filter_nb_sysstep es = Some es_sysE)
          (BEH_CONS: Cons_each_rel es_sysE exec' exec)
          (EXEC_REST: exec_st st' exec')
        : _exec_state exec_st st exec
      .

      Hint Constructors _exec_state: paco.

      Lemma exec_state_monotone: monotone2 _exec_state.
      Proof. pmonauto. Qed.

      Definition exec_state
        : state sys -> exec_t sysE -> Prop :=
        paco2 _exec_state bot2.

      Definition behav_state
                 (st: state sys) (beh: behav_t sysE): Prop :=
        exists exec, <<EXEC_ST: exec_state st exec>> /\
                <<EXEC_BEH: exec_behav exec beh>>.

      Definition behav_sys (beh: behav_t sysE): Prop :=
        (~ exists st_i, initial_state sys st_i) \/
        (exists st_i, <<INIT_STATE: initial_state sys st_i>> /\
                 <<BEH_ST:behav_state st_i beh>>).

    End BEHAVIOR.

    Section SAFE.

      Inductive _safe_state {sys: t}
                (safe_st: state sys -> Prop)
      : state sys -> Prop :=
      | SafeState
          st
          (PROGRESS: exists syse st', step _ st syse st')
          (SAFE_NXT: forall syse st'
                       (STEP: step _ st syse st')
                       (INTACT: filter_nb_sysstep syse <> None),
              safe_st st')
        : _safe_state safe_st st.

      Hint Constructors _safe_state: paco.

      Lemma safe_state_monotone sys
        : monotone1 (@_safe_state sys).
      Proof. pmonauto. Qed.

      Definition safe_state {sys: t}: state sys -> Prop :=
        paco1 _safe_state bot1.

      Inductive safe (sys: t) : Prop :=
        Safe
          (INIT_EXISTS: exists st_i, initial_state sys st_i)
          (ALL_INIT_SAFE:
             forall st_i (INIT: initial_state sys st_i),
               safe_state st_i)
      .

    End SAFE.

  End SYSTEM_SEM.

  Section DSYS_WITH_ERROR.
    Variable safe_sysE: Type -> Type.
    Notation sysE := (safe_sysE +' errE).

    Section BEHAVIOR.
      (* Context {sys: t}. *)
      Variable sys: @DSys.t sysE.

      Definition behav_state2
                 (st: DSys.state sys) (beh: behav_t safe_sysE): Prop :=
        exists exec, <<EXEC_ST: DSys.exec_state _ st exec>> /\
                           <<EXEC_BEH: exec_behav2 exec beh>>.

      Definition behav_sys2 (beh: behav_t safe_sysE): Prop :=
        (~ exists st_i, DSys.initial_state sys st_i) \/
        (exists st_i, <<INIT_STATE: DSys.initial_state sys st_i>> /\
                               <<BEH_ST: behav_state2 st_i beh>>).

    End BEHAVIOR.

    Inductive _lbeh_err_incl
              (err_incl: lbehav_t sysE -> lbehav_t safe_sysE -> Prop)
      : lbehav_t sysE -> lbehav_t safe_sysE -> Prop :=
    | LBehErrIncl_Inftau
      : _lbeh_err_incl err_incl cnil cnil
    | LBehErrIncl_SafeEvent
        tsp (h1: event sysE) (h2: event safe_sysE)
        t1 t2
        (SAFE_EVENT: h1 = embed h2)
        (INCL_REST: err_incl t1 t2)
      : _lbeh_err_incl err_incl (ccons (tsp, h1) t1)
                       (ccons (tsp, h2) t2)
    | LBehErrIncl_Error
        err t1 any tsp
        (ERROR_EVENT: err = (tsp, Event (inr1 ErrorEvent) tt))
      : _lbeh_err_incl err_incl (ccons err t1) any
    .

    Definition lbeh_err_incl
      : lbehav_t sysE -> lbehav_t safe_sysE -> Prop :=
      paco2 _lbeh_err_incl bot2.

    Hint Constructors _lbeh_err_incl: paco.

    Lemma lbeh_err_incl_monotone: monotone2 _lbeh_err_incl.
    Proof. pmonauto. Qed.

    Hint Resolve lbeh_err_incl_monotone: paco.

    Definition beh_err_incl
      : behav_t sysE -> behav_t safe_sysE -> Prop :=
      Forall2 lbeh_err_incl.


    Lemma lbeh_err_incl_safe_prefix
          ts (es_safe: events safe_sysE)
          beh1' beh2
          (INCL: lbeh_err_incl (colist_app (flatten_te (ts, map embed es_safe)) beh1') beh2)
      : exists beh2',
        beh2 = colist_app (flatten_te (ts, es_safe)) beh2' /\
        lbeh_err_incl beh1' beh2'.
    Proof.
      depgen beh2.
      induction es_safe as [| h t IH]; i; ss.
      { esplits; eauto. }
      destruct h.

      punfold INCL. inv INCL.
      2: { ss. }

      pclearbot.
      destruct h2. clarify.
      existT_elim. subst.
      unf_resum. subst.

      hexploit IH; eauto.
      i. des.
      esplits; eauto.
      subst. eauto.
    Qed.


    Lemma err_incl_inv
          ts es beh' beh2
          es_safe err
          (INCL : lbeh_err_incl (colist_app (flatten_te (ts, es)) beh') beh2)
          (ERR: trace_find_error _ es = (es_safe, err))
      : exists beh2',
        (if err then True else lbeh_err_incl beh' beh2') /\
        beh2 = colist_app (flatten_te (ts, es_safe)) beh2'.
    Proof.
      generalize (trace_find_error_spec _ es es_safe err ERR).
      intro ERR_CASES.

      destruct err.
      - des. subst.

        unfold flatten_te in INCL. ss.
        rewrite map_app in INCL.
        rewrite colist_app_assoc in INCL.

        apply lbeh_err_incl_safe_prefix in INCL. des.
        subst. esplits; eauto.

      - subst.
        apply lbeh_err_incl_safe_prefix in INCL. des.
        subst.
        esplits; eauto.
    Qed.


    Lemma local_exec_behav_12
      : forall lexec (beh1: lbehav_t sysE) (beh2: lbehav_t safe_sysE)
          (LEXEC_BEHAV: local_exec_behav lexec beh1)
          (INCL: lbeh_err_incl beh1 beh2),
        local_exec_behav2 lexec beh2.
    Proof.
      pcofix CIH. i.
      punfold LEXEC_BEHAV. inv LEXEC_BEHAV.
      { punfold INCL.
        pfold. inv INCL.
        econs 1. ss. }

      pclearbot.

      assert (ERR: exists es_safe err,
                 trace_find_error _ es = (es_safe, err)).
      { eexists. eexists.
        apply surjective_pairing. }
      des.

      hexploit err_incl_inv; eauto.
      intros (beh2' & INCL_REST & BEH2_EQ).
      subst.

      pfold.
      econs 2; eauto.
      destruct err.
      - ss.
      - right.
        eapply CIH; eauto.
    Qed.

    Lemma exec_behav_12
          exec (beh1: behav_t sysE) (beh2: behav_t safe_sysE)
          (EXEC_BEHAV: exec_behav exec beh1)
          (INCL: beh_err_incl beh1 beh2)
      : exec_behav2 exec beh2.
    Proof.
      apply Forall2_nth'.
      split.
      { eapply Forall2_length in INCL.
        eapply Forall2_length in EXEC_BEHAV.
        nia. }
      i.
      eapply Forall2_nth1 in EXEC_BEHAV; eauto.
      eapply Forall2_nth2 in INCL; eauto.
      des.
      eapply local_exec_behav_12; eauto.
      clarify.
    Qed.

    Lemma paco2_err_incl_app
          (r: lbehav_t sysE -> lbehav_t safe_sysE -> Prop)
          (es_safe: events safe_sysE)
          ts t1 t2
          (INCL_TLS: paco2 _lbeh_err_incl r t1 t2)
      : paco2 _lbeh_err_incl r
              (colist_app (map (fun e => (ts, e))
                               (map embed es_safe)) t1)
              (colist_app (map (fun e => (ts, e)) es_safe) t2).
    Proof.
      induction es_safe as [| h t].
      { ss. }
      s. pfold.
      econs 2; ss.
      left. eauto.
    Qed.



    Lemma local_exec_behav_21
          lexec (lbeh2: lbehav_t safe_sysE)
          (LEXEC_BEHAV2: local_exec_behav2 lexec lbeh2)
      : exists (lbeh1: lbehav_t sysE),
          <<INCL: lbeh_err_incl lbeh1 lbeh2>> /\
          <<LEXEC_BEHAV2: local_exec_behav lexec lbeh1>>.
    Proof.
      generalize (local_exec_behav_ex _ lexec).
      intros [beh1 LEXEC_BEHAV1].
      esplits; eauto.
      revert_until safe_sysE.
      pcofix CIH.
      i.
      punfold LEXEC_BEHAV1.
      inv LEXEC_BEHAV1.
      { punfold LEXEC_BEHAV2.
        inv LEXEC_BEHAV2.
        { pfold. econs 1. }
        exfalso.
        clear - EXEC_SILENT EVENTS_NONNIL.
        rewrite <- inftau_lexec_pref_iff in EXEC_SILENT.
        des.
        punfold INFTAU. inv INFTAU. ss.
      }

      renames tr_tau ts es into tr_tau1 ts1 es1.
      renames lexec' beh' TRACE_TAU into lexec'1 beh'1 TRACE_TAU1.
      renames EVENTS_NONNIL LOCAL_EXEC_BEHAV_REST into
              EVENTS_NONNIL1 LOCAL_EXEC_BEHAV_REST1.

      punfold LEXEC_BEHAV2.
      inv LEXEC_BEHAV2.
      { exfalso.
        clear - EXEC_SILENT EVENTS_NONNIL1.
        rewrite <- inftau_lexec_pref_iff in EXEC_SILENT.
        des.
        punfold INFTAU. inv INFTAU. ss.
      }

      assert (ts1 = ts /\ es1 = es /\ lexec'1 = lexec').
      { clear - LOCAL_EXEC_PREFIX TRACE_TAU1 TRACE_TAU
                                  EVENTS_NONNIL1 EVENTS_NONNIL.
        depgen tr_tau.
        induction TRACE_TAU1 as [| h_tau1 t_tau1 IH]; i; ss.
        { inv TRACE_TAU; ss.
          { clarify. }
          clarify.
        }

        inv TRACE_TAU; ss.
        { clarify. }
        clarify.
        hexploit IH; eauto.
      }
      des. subst.

      generalize (trace_find_error_spec
                    _ es es_safe is_err TRACE_ERROR).
      intro ERR.

      destruct is_err.
      { des. subst.
        (* pfold. *)
        unfold flatten_te. ss.
        rewrite map_app. ss.
        rewrite colist_app_assoc. s.

        eapply paco2_err_incl_app.
        pfold. econs 3; eauto.
      }

      hexploit (des_snoc _ es_safe).
      { destruct es_safe; ss.
        { congruence. }
        nia. }
      i. des.
      subst es_safe.
      subst es.
      unfold snoc. unfold flatten_te. s.
      pclearbot.

      repeat rewrite map_app.
      repeat rewrite colist_app_assoc.
      eapply paco2_err_incl_app. s.

      pfold. econs 2; ss.
      eauto.
    Qed.


    Lemma exec_behav_21
          exec (beh2: behav_t safe_sysE)
          (EXEC_BEHAV: exec_behav2 exec beh2)
      : exists (beh1: behav_t sysE),
          <<INCL: beh_err_incl beh1 beh2>> /\
          <<EXEC_BEHAV2: exec_behav exec beh1>>.
    Proof.
      cut (forall n (N_UBND: n < length beh2),
              exists lbeh1,
                (forall lexec lbeh2
                    (LEXEC: nth_error exec n = Some lexec)
                    (LBEH2: nth_error beh2 n = Some lbeh2),
                    <<LINCL: lbeh_err_incl lbeh1 lbeh2>> /\
                    <<LEXEC_BEH: local_exec_behav lexec lbeh1>>)).
      { intro AUX.
        eapply exists_list in AUX.
        des.
        exists l.
        splits.
        - r.
          apply Forall2_nth'.
          split; ss.
          i. eapply Forall2_nth2 in EXEC_BEHAV; eauto.
          des.
          hexploit NTH_PROP; eauto. i. des.
          eauto.
        - r.
          apply Forall2_nth'.
          split; ss.
          { eapply Forall2_length in EXEC_BEHAV.
            congruence. }
          i. eapply Forall2_nth1 in EXEC_BEHAV; eauto.
          des.
          hexploit NTH_PROP; eauto. i. des.
          eauto.
      }

      i.
      hexploit (nth_error_Some2 _ beh2 n); eauto.
      i. des.
      eapply Forall2_nth2 in EXEC_BEHAV; eauto.
      des.
      hexploit local_exec_behav_21; eauto.
      i. des.
      esplits; eauto.
      i. clarify.
      split; eauto.
    Qed.

    Lemma lbeh_err_ub_incl_any
          lbeh' lbeh_ub
          tsp tl
          (LBEH_UB_EQ: lbeh_ub = ccons (tsp, Event (inr1 ErrorEvent) tt) tl)
      : lbeh_err_incl lbeh_ub lbeh'.
    Proof.
      subst lbeh_ub.
      pfold. econs 3; eauto.
    Qed.

    Lemma beh_err_ub_incl_any
          beh' beh_ub
          (BEH_UB: Forall (fun x => exists tsp tl,
                               x = ccons (tsp, Event (inr1 ErrorEvent) tt) tl) beh_ub)
          (LEN_EQ: length beh' = length beh_ub)
      : beh_err_incl beh_ub beh'.
    Proof.
      apply Forall2_nth'.
      split; ss.
      i.
      eapply Forall_nth1 in BEH_UB; eauto.
      des.
      eapply lbeh_err_ub_incl_any; eauto.
    Qed.

    Lemma behav1_refine_impl_behav2_refine
          (dsys1 dsys2: @DSys.t sysE)
          (REF1: DSys.behav_sys dsys1 <1= DSys.behav_sys dsys2)
      : behav_sys2 dsys1 <1= behav_sys2 dsys2.
    Proof.
      intros beh BEH_SYS1.
      inv BEH_SYS1.
      { assert (ANY_BEH: forall beh_any, behav_sys dsys1 beh_any).
        { i. econs 1. ss. }

        assert (ANY_BEH2: forall beh_any, behav_sys dsys2 beh_any).
        { intro beh_any.
          hexploit ANY_BEH; eauto. }

        pose (beh_ub:= map (fun _ => ccons (0%Z, Event (inr1 ErrorEvent) tt: event sysE) cnil) beh).
        specialize (ANY_BEH2 beh_ub).

        inv ANY_BEH2.
        { econs 1. eauto. }

        des.
        econs 2.
        esplits; eauto.
        r in BEH_ST.
        r.
        des.
        esplits; eauto.
        eapply exec_behav_12; eauto.

        eapply beh_err_ub_incl_any.
        { subst beh_ub.
          apply Forall_forall.
          intros x IN.
          apply in_map_iff in IN. des.
          clarify.
          esplits; eauto.
        }
        subst beh_ub.
        rewrite map_length. ss.
      }

      des.
      r in BEH_ST. des.
      hexploit exec_behav_21; eauto.
      i. des.
      hexploit REF1; eauto.
      { econs 2. esplits; eauto.
        econs; eauto. }

      intro BEH1.
      r in BEH1. des.
      - econs 1. eauto.
      - econs 2.
        esplits; eauto.
        r in BEH_ST. r.
        des.
        esplits; eauto.
        eapply exec_behav_12; eauto.
    Qed.

  End DSYS_WITH_ERROR.

End DSys.

(* TODO: position? *)
Hint Resolve DSys.exec_state_monotone: paco.
Hint Resolve DSys.safe_state_monotone: paco.



Lemma exec_state_len sysE
      (sys: @DSys.t sysE) (st: DSys.state sys) exec
      (EXEC_ST: DSys.exec_state _ st exec)
  : length exec = DSys.num_sites sys st.
Proof.
  punfold EXEC_ST. inv EXEC_ST.
  - ss.
  - unfold DSys.filter_nb_sysstep in *.
    hexploit deopt_list_length; eauto.
    rewrite map_length. i.
    hexploit Forall3_length; eauto. i. des.
    hexploit (DSys.step_prsv_num_sites sys); eauto. i. des.
    rewrite <- NUM_EVTS.
    unfold lexec_t, events in *. nia.
Qed.

Lemma behav_state_len sysE
      (sys: @DSys.t sysE) (st: DSys.state sys) beh
      (BEH_ST: DSys.behav_state _ st beh)
  : length beh = DSys.num_sites sys st.
Proof.
  rr in BEH_ST. des.
  hexploit exec_state_len; eauto. intro LEN.
  rr in EXEC_BEH.
  hexploit Forall2_length; eauto. i. nia.
Qed.

Lemma DSys_filter_nb_localstep_inv E
      tes_r (tes: tsp * events E)
      (FILTER_LOC: DSys.filter_nb_localstep tes_r =
                   Some tes)
  : <<TIMESTAMP_EQ: fst tes_r = fst tes>> /\
    <<FILTERED_NB_EACH:
    Forall2 (fun e_r e => DSys.filter_nb1 e_r = Some e)
            (snd tes_r) (snd tes)>>.
Proof.
  unfold DSys.filter_nb_localstep in *.
  destruct (deopt_list (map DSys.filter_nb1 (snd tes_r)))
    as [l'| ] eqn: DEOPT.
  2: { ss. }
  destruct tes as [t es].
  destruct tes_r as [t' es_r].
  ss. clarify.
  split; ss.

  apply Forall2_nth. i.
  hexploit deopt_list_length; eauto.
  rewrite map_length. intro LEN_EQ.
  apply deopt_list_Some_iff in DEOPT.

  destruct (nth_error es_r n) eqn: ES_R_N.
  2: {
    destruct (nth_error es n) eqn: ES_N.
    2: { econs. }
    exfalso.
    apply nth_error_Some1' in ES_N.
    apply nth_error_None in ES_R_N. nia.
  }

  destruct (nth_error es n) eqn: ES_N.
  2: { exfalso.
       apply nth_error_Some1' in ES_R_N.
       apply nth_error_None in ES_N. nia. }

  econs.
  apply f_equal with (f:= fun l => nth_error l n) in DEOPT.
  do 2 rewrite map_nth_error_rw in DEOPT.
  rewrite ES_N, ES_R_N in DEOPT. ss. clarify.
Qed.

Lemma DSys_filter_nb_sysstep_repeat_nil E
      tm n
  : DSys.filter_nb_sysstep (repeat (tm, @nil (event (nbE +' E))) n) =
    Some (repeat (tm, []) n).
Proof.
  unfold DSys.filter_nb_sysstep.
  apply deopt_list_Some_iff.
  do 2 rewrite map_repeat. ss.
Qed.

Lemma filter_nb_localstep_embed E
      tm (es: events E)
  : DSys.filter_nb_localstep (tm, embed es) =
    Some (tm, es).
Proof.
  unfold DSys.filter_nb_localstep. ss.
  induction es as [|h t IH]; ss.
  replace (DSys.filter_nb1 (embed h)) with (Some h).
  2: { unfold DSys.filter_nb1.
       destruct h; ss. }

  unfold embed in IH.
  destruct (deopt_list (map DSys.filter_nb1 (embed_list t))) eqn: DEOPT; ss.
  clarify.
Qed.

Lemma DSys_filter_nb_sysstep_inv E
      es_r (es: list (tsp * events E))
      (FILTER_SYS: DSys.filter_nb_sysstep es_r = Some es)
  : Forall2 (fun es1 es2 =>
               DSys.filter_nb_localstep es1 = Some es2)
            es_r es.
Proof.
  unfold DSys.filter_nb_sysstep in *.
  apply deopt_list_Some_iff in FILTER_SYS.
  depgen es.
  induction es_r as [| hr tr IH]; i; ss.
  { destruct es; ss. }
  destruct es as [| h t]; ss.
  clarify.
  econs; eauto.
Qed.



Lemma filter_nb_localstep_app E
      tm es1 tr1 (syse: event E)
      (FLT1: DSys.filter_nb_localstep (tm, es1) = Some tr1)
  : DSys.filter_nb_localstep (tm, es1 ++ [embed syse]) =
    Some (fst tr1, snd tr1 ++ [syse]).
Proof.
  unfold DSys.filter_nb_localstep. ss.
  rewrite map_app.

  unfold DSys.filter_nb_localstep in FLT1.
  match type of FLT1 with
  | option_map _ ?x = _ =>
    destruct x eqn: DEOPT1; ss
  end.

  clarify.
  erewrite deopt_list_app; cycle 1.
  { eauto. }
  { destruct syse. ss. }
  ss.
Qed.


Lemma tes_equiv_sym E
      (t1 t2: list (tsp * events E))
      (EQV: tes_equiv t1 t2)
  : tes_equiv t2 t1.
Proof.
  unfold tes_equiv in *. ss.
Qed.


Lemma Forall2_tes_equiv_sym E
      (t1 t2: list (list (tsp * events E)))
      (EQV: Forall2 tes_equiv t1 t2)
  : Forall2 tes_equiv t2 t1.
Proof.
  depgen t2.
  induction t1; i; ss.
  { inv EQV. econs. }
  inv EQV. econs; ss. eauto.
Qed.
