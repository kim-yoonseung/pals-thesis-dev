From ITree Require Import ITree Eq EqAxiom.
From compcert Require Import Integers.

Require Import sflib.
Require Import StdlibExt IntegersExt.

Require Import SysSem.
Require Import SyncSysModel.
Require Import RTSysEnv.

Require Import Basics String List Lia.
Require Import Arith ZArith.



(* Import ListNotations. *)
Import ITreeNotations.

(* Choosing a random value  *)
Inductive randE : Type -> Type :=
| RandFailure: randE bool (* true -> stay alive / false -> fail *)
| RandRecovery: randE bool (* true -> recover / false -> stay off *)
| RandFuel: randE nat
.

Inductive tgd (E: Type -> Type) : Type -> Type :=
| Tagged R (task_id: nat) (e: E R): tgd E R.

(* timestamp-setting events *)
Inductive tspE: Type -> Type :=
| SetTimestamp (tm: Z): tspE unit.

Inductive app_invkE {msgT: Set}: Type -> Type :=
| AppInvok (sytm: Z) (tid: nat) (inbox: list (msgT?))
  : app_invkE (list (msgT?)).


Module ExecutableSpec.

  Definition check_halt (tm_fin: Z?) (tm: Z): bool :=
    match tm_fin with
    | None => false
    | Some tm_fin_v => (tm_fin_v <=? tm)%Z
    end.

  Section SYNCH_ITREE.
    Context {msgT: Set}.
    Variable num_tasks: nat.
    Variable period: Z.

    Fixpoint step_itree (sytm: Z) (tid: nat) (inbs: list (list msgT?))
      : itree (@app_invkE msgT +' tspE) (list (list msgT?)) :=
      match inbs with
      | inb_h :: inbs_t =>
        out_h <- trigger (AppInvok sytm tid inb_h) ;;
        outs_t <- step_itree sytm (S tid) inbs_t ;;
        Ret (out_h :: outs_t)
      | _ => Ret []
      end.

    CoFixpoint synch_itree_loop
               (tm_fin: Z?)
               (tm: Z)
               (inbs: list (list msgT?))
      : itree (@app_invkE msgT +' tspE) unit :=
      if (check_halt tm_fin tm)%nat then Ret tt else
        trigger (SetTimestamp tm) ;;
        'outs <- step_itree tm O inbs ;;
        let inbs' := imap (fun tid _ => map (SNode.get_outbox_msg_by_dest tid) outs)
                          0 (repeat tt num_tasks) in
        Tau (synch_itree_loop tm_fin (tm + period) inbs').

    Lemma observe_synch_itree_loop
          tm_fin tm inbs
      : observe (synch_itree_loop tm_fin tm inbs) =
        observe
          (if (check_halt tm_fin tm)%nat then Ret tt else
             trigger (SetTimestamp tm) ;;
             'outs <- step_itree tm O inbs ;;
             let inbs' := imap (fun tid _ => map (SNode.get_outbox_msg_by_dest tid) outs)
                               0 (repeat tt num_tasks) in
             Tau (synch_itree_loop tm_fin (tm + period) inbs')).
    Proof. ss. Qed.

    Lemma unfold_synch_itree_loop
          (tm_fin: Z?)
          (tm: Z)
          (inbs: list (list msgT?))
      : synch_itree_loop tm_fin tm inbs =
        if (check_halt tm_fin tm)%nat then Ret tt else
          trigger (SetTimestamp tm) ;;
          'outs <- step_itree
                    (* (mcasts sys) *)
                    tm O inbs ;;
          let inbs' := imap (fun tid _ => map (SNode.get_outbox_msg_by_dest tid) outs)
                            0 (repeat tt num_tasks) in
          Tau (synch_itree_loop tm_fin (tm + period) inbs').
    Proof.
      apply bisimulation_is_eq.
      rewrite (itree_eta (synch_itree_loop tm_fin tm inbs)).
      rewrite observe_synch_itree_loop.

      destruct (check_halt tm_fin tm) eqn: CHK_HALT; ss.
      { reflexivity. }

      rewrite <- itree_eta. reflexivity.
    Qed.


    Definition synch_itree
               (tm_init: Z) (tm_fin: Z?)
      : itree (@app_invkE msgT +' tspE) unit :=
      let inbs_init: list (list msgT?) :=
          repeat (repeat None num_tasks) num_tasks in
      let n_pre: Z :=
          (let m: Z := tm_init mod period in
           if (m =? 0)%Z then 0 else (period - m))%Z
      in
      let tm_fst: Z := (tm_init + n_pre)%Z in
      synch_itree_loop tm_fin tm_fst inbs_init.

  End SYNCH_ITREE.

  Section EVENT_HANDLER.
    Context {sysE: Type -> Type}.
    Context {msgT: Set}.
    Variable num_tasks: nat.
    Variable mcasts : list (list nat).
    Variable sntz: msgT -> msgT?.

    Notation E := (sysE +' @abst_sendE msgT).

    Definition update_outbox
               (outb: list msgT?)
               (tid_d: Tid)
               (msg: msgT)
      : list msgT? :=
      match sntz msg with
      | None => outb
      | Some msg_s =>
        let tids_ad := SNode.get_actual_dest
                         num_tasks mcasts tid_d in
        if SNode.check_available tids_ad outb then
          SNode.insert_msg tids_ad msg_s outb
        else outb
      end.

    Definition app_event_handler (tid: nat)
      : forall R (e: E R),
        (list msgT? -> itree (tgd (sysE +' randE) +' tspE) (list msgT? * R)) :=
      fun R (e: E R) (outbox: list msgT?) =>
        (* match e with *)
        (* | Tagged _ tid e => *)
          match e with
          | inl1 sys_e =>
            r <- trigger (Tagged _ _ tid (inl1 sys_e));;
            Ret (outbox, r)
          | inr1 send_e =>
            match send_e with
            | AbstSendEvent tid_dest bs =>
              let outbox' := update_outbox
                               outbox tid_dest bs in
              Tau (Ret (outbox', tt)) (* Tau just for least change *)
            (* end *)
          end
        end.

      (*   (list msgT? -> list msgT? * itree (tgd (sysE +' randE) +' tspE) R) := *)
      (* fun R (e: E R) (outbox: list msgT?) => *)
      (*   (* match e with *) *)
      (*   (* | Tagged _ tid e => *) *)
      (*     match e with *)
      (*     | inl1 sys_e => *)
      (*       (outbox, trigger (Tagged _ _ tid (inl1 sys_e))) *)
      (*     | inr1 send_e => *)
      (*       match send_e with *)
      (*       | AbstSendEvent tid_dest bs => *)
      (*         let outbox' := update_outbox *)
      (*                          outbox tid_dest bs in *)
      (*         (outbox, Ret tt) *)
      (*       (* end *) *)
      (*     end *)
      (*   end. *)

    Record loc_state: Type :=
      LocState {
          app_mod: @AppMod.t sysE msgT ;
          app_state: (AppMod.abst_state_t app_mod) ? ;
        }.

    (* basically, interp with fuel *)
    Fixpoint run_with_fuel
             (app: @AppMod.t sysE msgT)
             (tid: nat)
             (fuel:nat)
             (outbox: list (msgT?))
             (itr: itree (sysE +' (@abst_sendE msgT))
                         (AppMod.abst_state_t app))
      : itree (tgd (sysE +' randE) +' tspE)
              ((AppMod.abst_state_t app)? * list msgT?) :=
      match fuel with
      | O => Ret (None, outbox)
      | S fuel' =>
        match observe itr with
        | RetF ast_f => Ret (Some ast_f, outbox)
        | TauF itr' => Tau (run_with_fuel app tid fuel' outbox itr')
        | VisF _ e k =>
          '(outbox', r) <- app_event_handler tid _ e outbox ;;
          run_with_fuel app tid fuel' outbox' (k r)
        end
      end.


    Definition run_period_itree
               (* (app: @AppMod.t sysE msgT) *)
               (sytm: Z) (tid: nat)
               (inb: list msgT?)
      (* (oast: (AppMod.abst_state_t app)?) *)
               (lst: loc_state)
      : itree (tgd (sysE +' randE) +' tspE)
              (* ((AppMod.abst_state_t app)? * list msgT?) := *)
              (loc_state * list msgT?) :=
      match lst with
      | LocState app oast =>
        match oast with
        | None =>
          turn_on <- trigger (Tagged _ _ tid (inr1 RandRecovery)) ;;
          if turn_on: bool then
            Ret (LocState app (Some (AppMod.init_abst_state app)), [])
                (* outbox_init) *)
          else
            Ret (LocState app None, (* outbox_init *) [])
        | Some ast =>
          pinit_ok <- trigger (Tagged _ _ tid (inr1 RandFailure)) ;;
          if (pinit_ok: bool) then
            fuel <- trigger (Tagged _ _ tid (inr1 RandFuel)) ;;
            let itr_app: itree _ (AppMod.abst_state_t app) :=
                AppMod.job_itree app sytm inb ast in
            let outbox_init: list msgT? :=
                repeat None num_tasks in
            '(oast', out) <- run_with_fuel app tid fuel outbox_init itr_app ;;
            Ret (LocState app oast', out)
          else Ret (LocState app None, [])
        end
      end.

    Definition app_invk_event_handler
      : forall R (e: (@app_invkE msgT +' tspE) R),
        list loc_state ->
        itree (tgd (sysE +' randE) +' tspE) (list loc_state * R) :=
      fun _ e lsts =>
        match e with
        | inl1 ainvk_e =>
          match ainvk_e with
          | AppInvok sytm tid inb =>
            match nth_error lsts tid with
            | None => Ret (lsts, [])
            | Some lst =>
              '(lst', outbox) <- run_period_itree sytm tid inb lst ;;
              Ret (replace_nth lsts tid lst', outbox)
            end
          end
        | inr1 tsp_e =>
          match tsp_e with
          | SetTimestamp tm =>
            trigger (SetTimestamp tm);; Ret (lsts, tt)
          end
        end.

  End EVENT_HANDLER.

  Record t {sysE : Type -> Type} {msgT : Set} : Type :=
    mk { period : Z;
         apps : list (@AppMod.t sysE msgT);
         mcasts : list (list nat);
         sanitize_msg : msgT -> msgT ?
       }.

  Section SYSTEM.
    Context {sysE : Type -> Type}.
    Context {msgT : Set}.
    Variable sys: @t sysE msgT.

    Definition init_loc_state (app: @AppMod.t sysE msgT)
      : @loc_state sysE msgT :=
      LocState app None.

    Definition init_loc_states: list (@loc_state sysE msgT) :=
      map init_loc_state (apps sys).

    Let num_tasks: nat := length (apps sys).

    Definition interp_ainvk
      : forall R,
        itree (app_invkE +' tspE) R ->
        list loc_state ->
        itree (tgd (sysE +' randE) +' tspE) (list loc_state * R) :=
      (interp (M:= (fun R => list (@loc_state sysE msgT) ->
                          itree (tgd (sysE +' randE) +' tspE)
                                (list (@loc_state sysE msgT) * R)))
              (app_invk_event_handler
                 num_tasks (mcasts sys) (sanitize_msg sys))).

    Definition sys_itree
               (tm_init: Z) (tm_fin: Z?)
      : itree (tgd (sysE +' randE) +' tspE)
              (* (list (loc_state _ _) * unit) := *)
              unit :=
      (interp_ainvk
         unit
         (synch_itree num_tasks (period sys) tm_init tm_fin)
         init_loc_states) ;;
      Ret tt.

  End SYSTEM.


  Section DSYS.
    Context {sysE: Type -> Type}.
    Context {msgT: Set}.
    (* Variable sys: @t sysE msgT. *)

    Let state: Type :=
      Z * itree (tgd (sysE +' randE) +' tspE) unit.

    Inductive step (num_tasks: nat)
      : state -> list (tsp * events (nbE +' sysE)) -> state -> Prop :=
    | Step_Ret
        tr_emp
        tspv itr
        (OBS_RET: observe itr = RetF tt)
        (EMPTY_TRACE: tr_emp = List.repeat (tspv, []) num_tasks)
      : step num_tasks (tspv, itr) tr_emp (tspv, itr)
    | Step_Tau
        tr_emp
        tspv itr itr'
        (OBS_TAU: observe itr = TauF itr')
        (EMPTY_TRACE: tr_emp = List.repeat (tspv, []) num_tasks)
      : step num_tasks (tspv, itr) tr_emp (tspv, itr')
    | Step_Timestamp
        tspv itr
        tr_emp
        tspv' itr'
        (k: unit -> itree (tgd (sysE +' randE) +' tspE) unit)
        (OBS_VIS: observe itr = VisF (inr1 (SetTimestamp tspv')) k)
        (EMPTY_TRACE: tr_emp = List.repeat (tspv, []) num_tasks)
        (ITREE': itr' = k tt)
      : step num_tasks (tspv, itr) tr_emp (tspv', itr')
    | Step_SystemEvent
        R (ret: R)
        tspv itr
        tr_emp tr itr'
        (tid: Tid) (syse: sysE R)
        (k: R -> itree (tgd (sysE +' randE) +' tspE) unit)
        (OBS_VIS: observe itr = VisF (inl1 (Tagged _ _ tid (inl1 syse))) k)
        (EMPTY_TRACE: tr_emp = List.repeat (tspv, []) num_tasks)
        (TRACE: tr = replace_nth tr_emp tid (tspv, [embed (Event syse ret)]))
        (ITREE': itr' = k ret)
      : step num_tasks (tspv, itr) tr (tspv, itr')
    | Step_RandomEvent
        R (ret: R)
        tspv itr
        tr_emp itr'
        (tid: Tid) (rnde: randE R)
        (k: R -> itree (tgd (sysE +' randE) +' tspE) unit)
        (OBS_VIS: observe itr = VisF (inl1 (Tagged _ _ tid (inr1 rnde))) k)
        (EMPTY_TRACE: tr_emp = List.repeat (tspv, []) num_tasks)
        (ITREE': itr' = k ret)
      : step num_tasks (tspv, itr) tr_emp (tspv, itr')
    .

    Program Definition as_dsys (sys: @t sysE msgT)
               (tm_init: Z) (tm_fin: Z?)
      : DSys.t :=
      {| DSys.state := state;
         DSys.num_sites := fun _ => length (apps sys) ;
         DSys.step := step (length (apps sys)) ;
         DSys.initial_state :=
           fun st => st = (0%Z, sys_itree sys tm_init tm_fin);
      |}.
    Next Obligation.
      splits.
      - inv STEP.
        + rewrite repeat_length. ss.
        + rewrite repeat_length. ss.
        + rewrite repeat_length. ss.
        + rewrite replace_nth_length.
          rewrite repeat_length. ss.
        + rewrite repeat_length. ss.
      - ss.
    Qed.

  End DSYS.

End ExecutableSpec.
