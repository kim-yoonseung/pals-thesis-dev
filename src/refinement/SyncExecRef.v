From ITree Require Import ITree Eq EqAxiom.
From compcert Require Coqlib.
From Paco Require Import paco.

Require Import List.
Require Import Arith ZArith Lia.

Require Import sflib.
Require Import Axioms StdlibExt IntegersExt.

Require Import ITreeTac.

Require Import SysSem.
Require Import IPModel DiscreteTimeModel.
Require Import NWSysModel.
Require Import RTSysEnv.
Require Import SyncSysModel Executable.

Require Import MSteps.
Require Import FMSim.
Require Import FMSim_Switch.

(* move some lemmas in this to StdlibExt *)
Require Import CompcertLemmas.

Set Nested Proofs Allowed.

Import ITreeNotations.

Import ExecutableSpec.


Lemma replace_nth_exact A
      n (a a': A) l1 l2
      (LEN: length l1 = n)
  : replace_nth (l1 ++ a :: l2) n a' =
    l1 ++ a' :: l2.
Proof.
  hexploit (replace_nth_spec _ (l1 ++ [a] ++ l2) n).
  intros [LHS | RHS].
  { exfalso.
    do 2 rewrite app_length in LHS.
    des. ss. nia. }
  destruct RHS as (l1' & a'' & l2' & EQ1 & LEN1 & REPL_EQ).

  cut (l1 = l1').
  { i. subst l1'.
    rewrite REPL_EQ.
    apply app_inv_head in EQ1. ss.
    clarify. }

  clear - LEN LEN1 EQ1.
  rewrite <- LEN1 in LEN. clear LEN1.
  depgen l1'.
  induction l1 as [| h1 t1 IH]; i; ss.
  { destruct l1'; ss. }
  destruct l1'; ss.
  clarify.
  hexploit IH; eauto.
  i. subst. ss.
Qed.


Lemma in_btw_cant_divide
      d n x
      (D_POS: 0 < d)
      (DIV: Nat.divide d n)
      (BTW: n < x < n + d)
  : ~ Nat.divide d x.
Proof.
  r in DIV. des. subst.
  rename z into z_n.
  intro DIV_X.
  r in DIV_X. des. subst.
  rename z into z_x.
  assert (z_n < z_x /\ z_x <= z_n) by nia.
  nia.
Qed.



Lemma cons_each_length A
      (l1: list A) l2
      (LEN_EQ: length l1 = length l2)
  : length (cons_each l1 l2) = length l1.
Proof.
  depgen l2.
  induction l1 as [| h1 t1 IH]; i; ss.
  destruct l2 as [| h2 t2]; ss.
  hexploit IH; eauto.
Qed.



Section UNFOLD_INTERP_AINVK.
  Context {sysE: Type -> Type}.
  Context {msgT: Set}.
  Variable sys: @t sysE msgT.

  Lemma unfold_interp_ainvk_tau
        R
        (itr itr': itree (app_invkE +' tspE) R)
        (OBS: observe itr = TauF itr')
        (lsts: list loc_state)
    : interp_ainvk sys R itr lsts =
      Tau (interp_ainvk sys R itr' lsts).
  Proof.
    apply bisimulation_is_eq.
    unfold interp_ainvk.
    unfold interp. unfold Basics.iter, MonadIter_stateT0.
    unfold Basics.iter, MonadIter_itree.
    ss.
    rewrite unfold_iter.
    rewrite bind_bind. ss.
    desf.
    rewrite bind_ret_l. ss.
    rewrite bind_ret_l. ss.
    reflexivity.
  Qed.

  Lemma unfold_interp_ainvk_ret R
        (itr: itree (app_invkE +' tspE) R)
        lsts (r: R)
        (OBS: observe itr = RetF r)
    : interp_ainvk sys _ itr lsts = Ret (lsts, r).
  Proof.
    apply bisimulation_is_eq.
    unfold interp_ainvk.
    unfold interp. unfold Basics.iter, MonadIter_stateT0.
    unfold Basics.iter, MonadIter_itree.
    ss.
    rewrite unfold_iter.
    rewrite bind_bind. ss.
    desf.
    rewrite bind_ret_l. ss.
    rewrite bind_ret_l. ss.
    reflexivity.
  Qed.

  Lemma unfold_interp_ainvk_vis_tsp R S
        (tsp_ec: tspE R) (k: _ -> itree _ S)
        (itr: itree (app_invkE +' tspE) _)
        (* (itr: itree (sysE +' bsendE) astate_t) *)
        (* (sh: list bool) *)
        lsts
        (OBS: observe itr = VisF (inr1 tsp_ec) k)
    : interp_ainvk sys _ itr lsts =
      Vis (subevent _ tsp_ec)
          (fun r => Tau (interp_ainvk sys S (k r) lsts)).
  Proof.
    apply bisimulation_is_eq.
    unfold interp_ainvk.
    destruct tsp_ec.
    unfold interp.
    unfold Basics.iter, MonadIter_stateT0.
    unfold Basics.iter, MonadIter_itree.
    rewrite unfold_iter.
    repeat change (fun x => ?h x) with h in *.

    desf; ss.
    { exfalso. congruence. }
    { exfalso. congruence. }
    rewrite Heq in OBS. clarify.
    existT_elim. subst.

    rewrite bind_bind.
    unfold ITree.map.
    rewrite bind_bind. ss.
    rewrite bind_bind.
    setoid_rewrite bind_ret_l. ss.
    setoid_rewrite bind_ret_l. ss.
    setoid_rewrite bind_ret_l. ss.
    rewrite bind_trigger. ss.

    eapply eqit_Vis.
    i. destruct u.
    reflexivity.
  Qed.

  Lemma unfold_interp_ainvk_vis_invoke
        R (* (ainvk_ec: app_invkE R) *) (k: _ -> itree _ R)
        (itr: itree (app_invkE +' tspE) R)
        sytm tid inb lsts
        (OBS: observe itr = VisF (inl1 (AppInvok sytm tid inb)) k)
    : interp_ainvk sys R itr lsts =
      '(lsts', outb) <-
      (match nth_error lsts tid with
       | None => Ret (lsts, [])
       | Some lst =>
         '(lst', outbox) <- run_period_itree
                              (length (apps sys)) (mcasts sys)
                              (sanitize_msg sys)
                              sytm tid inb lst ;;
         Ret (replace_nth lsts tid lst', outbox)
       end) ;;
      Tau (interp_ainvk sys R (k outb) lsts').
  Proof.
    apply bisimulation_is_eq.
    unfold interp_ainvk.
    unfold interp.
    unfold Basics.iter, MonadIter_stateT0.
    unfold Basics.iter, MonadIter_itree.

    rewrite unfold_iter. ss.
    repeat change (fun x => ?h x) with h.
    rewrite OBS.
    unfold ITree.map.
    rewrite bind_bind.
    rewrite bind_bind. ss.
    setoid_rewrite bind_ret_l.
    setoid_rewrite bind_ret_l.
    unfold ITree.iter. ss.

    eapply eqit_bind; s.
    2: { reflexivity. }
    ii. destruct a; ss. reflexivity.
  Qed.

End UNFOLD_INTERP_AINVK.


Section PROOF.
  Context {sysE: Type -> Type}.
  Context {msgT: Set}.
  (* Context `{rnws_params}. *)
  (* Context `{SystemEnv}. *)

  Variable app_mods: list (@AppMod.t sysE msgT).

  Let nodes: list (@SNode.t sysE msgT) :=
    map ITrSNode.to_snode app_mods.
  Let num_tasks: nat := length app_mods.

  Variable period: nat.
  Variable mcasts: list (list Tid).
  Variable sntz_msg: msgT -> msgT?.

  Variable tm_init: nat.
  (* Hypothesis TM_INIT_SYTM: Nat.divide period (tm_init + max_clock_skew). *)

  Hypothesis PERIOD_POS: (0 < period)%nat.
  Hypothesis TM_INIT_COND: (period <= tm_init)%nat.

  Let exec_sys: ExecutableSpec.t :=
    ExecutableSpec.mk _ _ (Z.of_nat period) app_mods mcasts sntz_msg.

  Let sync_sys: SyncSys.t :=
    SyncSys.mk period nodes mcasts sntz_msg.

  Let sys_src := ExecutableSpec.as_dsys exec_sys (Z.of_nat tm_init) None.

  Let sys_tgt := SyncSys.as_dsys
                   sync_sys (* (tm_init + max_clock_skew). *)
                   tm_init.

  Inductive match_loc_state
            (tid: Tid)
            (inbs: list msgT?)
    : @loc_state sysE msgT -> @SNode.state sysE msgT -> Prop :=
    MatchLocState
      app oast ost_tgt
      (OST_TGT: ost_tgt = option_map (fun ast => Ret ast) oast)
    : match_loc_state
        tid inbs (LocState app oast)
        (SNode.State tid (ITrSNode.to_snode app)
                     inbs ost_tgt)
  .


  Lemma sim_snode_istar
        tid app ast
        tm es_r out es
        oast' out'
        (k: _ -> itree _ _)
        (RANGE_TID: tid < num_tasks)
        (ISTAR: SNode.istar sntz_msg num_tasks mcasts
                            (ITrSNode.to_snode app)
                            (ast, out) es_r (oast', out'))
        (FINAL: option_rel1 (fun x => SNode.period_end
                                     (ITrSNode.to_snode app) x)
                            oast')
        (FLT_LOC: DSys.filter_nb_localstep (tm, es_r) =
                  Some (tm, es))
    : exists fuel o_app_st' n es_lstep es_tid,
      <<MSTEPS_SRC:
        msteps sys_src n (tm, x <- run_with_fuel
                                    num_tasks mcasts sntz_msg
                                    app tid fuel out ast ;;
                              k x)
               es_lstep
               (tm, k (o_app_st', out'))>> /\
      <<OPT_APP_ST: option_map (fun x => Ret x) o_app_st' = oast'>> /\
      <<EVENT_TID: nth_error es_lstep tid = Some es_tid>> /\
      <<FLATTEN: flatten_tes es_tid = (map (fun e => (tm, e))) es>> /\
      <<EVENT_OTHER:
          forall tid' es'
            (TID_NEQ: tid' <> tid)
            (ES_LSTEP': nth_error es_lstep tid' = Some es'),
            Forall (fun x => snd x = []) es'>>
  .
  Proof.
    remember (ast, out) as st eqn: STATE.
    remember (oast', out') as st' eqn: STATE'.
    depgen es. depgen out. depgen ast.

    induction ISTAR; i; ss.
    { clarify.
      exists 0, None, 0, (repeat [] num_tasks), [].
      splits; ss.
      - simpl_itree_goal.
        econs; ss.
      - eapply repeat_nth_error_Some. ss.
      - apply DSys_filter_nb_localstep_inv in FLT_LOC.
        des; ss. inv FILTERED_NB_EACH. ss.
      - i.
        eapply nth_error_In in ES_LSTEP'.
        eapply repeat_spec in ES_LSTEP'.
        subst. econs.
    }
    { clarify.
      rr in FINAL.
      rename ast0 into ast_f.
      unfold ITrSNode.period_end in FINAL.

      destruct (observe ast_f) eqn:OBS; ss.
      rename r into app_st_f.

      exists 1, (Some app_st_f), 0, (repeat [] num_tasks), [].
      apply DSys_filter_nb_localstep_inv in FLT_LOC.
      des; ss.
      rewrite OBS.
      inv FILTERED_NB_EACH.

      splits; ss.
      - simpl_itree_goal.
        econs; eauto.
      - f_equal.
        rewrite itree_eta_ with (t:= ast_f).
        rewrite itree_eta_ with (t:= Ret app_st_f).
        rewrite OBS. ss.
      - apply repeat_nth_error_Some. ss.
      - i.
        eapply nth_error_In in ES_LSTEP'.
        eapply repeat_spec in ES_LSTEP'.
        subst. econs.
    }

    clarify.
    renames es1 es2 es0 into oe_r es2_r es.

    assert (exists es1 es2,
               <<ES_DIV: es = es1 ++ es2>> /\
               <<FLT1: DSys.filter_nb_localstep (tm, opt2list oe_r) =
                       Some (tm, es1)>> /\
               <<FLT2: DSys.filter_nb_localstep (tm, es2_r) =
                       Some (tm, es2)>>).
    { clear - FLT_LOC.
      destruct oe_r as [e_r|]; ss.
      - unfold DSys.filter_nb_localstep in *. ss.
        desf. ss. clarify.
        esplits; eauto. ss.
      - exists [], es.
        splits; eauto. }
    des. subst.

    assert (exists (tes1_r: list (tsp * events (nbE +' sysE)))
              (tes1: list (tsp * events sysE)),
               <<TES1_R: tes1_r = replace_nth (repeat (tm, []) (length app_mods)) tid (tm, embed es1)>> /\
               <<FLT_TES1: DSys.filter_nb_sysstep tes1_r =
                           Some tes1>> /\
               <<LEN_TES1: length tes1 = num_tasks>> /\
               <<EVT_TID: nth_error tes1 tid = Some (tm, es1)>> /\
               <<OTHER_SILENT:
                 forall tid' es'
                   (TID_NEQ: tid' <> tid)
                   (NTH: nth_error tes1 tid' = Some es'),
                   es' = (tm, [])>>).
    { exists (map (fun e => (tm, e)) (repeat [] tid ++ (embed es1) :: repeat [] (num_tasks - S tid))),
      (map (fun e => (tm, e)) (repeat [] tid ++ es1 :: repeat [] (num_tasks - S tid))).
      splits; ss.
      - eapply nth_eq_list_eq'.
        { rewrite map_length. rewrite app_length. s.
          rewrite replace_nth_length.
          do 3 rewrite repeat_length. nia. }
        intros p [] [] NTH1 NTH2.
        apply map_nth_error_iff in NTH1. des. clarify.

        assert (P_CASES: p < tid \/ p = tid \/ tid < p) by nia.
        des.
        + rewrite nth_error_app1 in NTH1.
          2: { rewrite repeat_length. ss. }

          eapply repeat_spec_nth in NTH1. subst.
          rewrite replace_nth_gso in NTH2 by nia.
          apply repeat_spec_nth in NTH2. clarify.
        + subst.
          rewrite nth_error_app2 in NTH1.
          2: { rewrite repeat_length. ss. }
          rewrite repeat_length in NTH1.
          rewrite Nat.sub_diag in NTH1. ss. clarify.

          rewrite replace_nth_gss in NTH2.
          2: { rewrite repeat_length. nia. }
          clarify.
        + rewrite nth_error_app2 in NTH1.
          2: { rewrite repeat_length. nia. }
          rewrite repeat_length in NTH1.

          rewrite replace_nth_gso in NTH2 by nia.
          apply repeat_spec_nth in NTH2. clarify.
          destruct (p - tid) eqn: P_TID; ss.
          { exfalso. nia. }
          eapply repeat_spec_nth in NTH1.
          subst. ss.

      - unfold DSys.filter_nb_sysstep.
        apply deopt_list_Some_iff.
        repeat rewrite map_app.
        repeat rewrite map_map.
        repeat rewrite map_repeat.
        f_equal. ss.
        f_equal.
        { rewrite filter_nb_localstep_embed. ss. }
        apply nth_eq_list_eq'.
        { do 2 rewrite map_length.
          do 2 rewrite repeat_length. ss. }
        i.
        apply map_nth_error_iff in NTH1.
        apply map_nth_error_iff in NTH2.
        des; ss. clarify.
        apply nth_error_In in NTH1.
        apply nth_error_In in NTH2.
        apply repeat_spec in NTH1.
        apply repeat_spec in NTH2.
        subst. ss.
      - rewrite map_length.
        rewrite app_length. s.
        do 2 rewrite repeat_length.
        nia.
      - rewrite map_app.
        rewrite nth_error_app2.
        2: { rewrite map_length. rewrite repeat_length. ss. }
        rewrite map_length. rewrite repeat_length.
        rewrite Nat.sub_diag. ss.
      - i. rewrite map_nth_error_iff in NTH. des.
        subst. ss.
        assert (TID'_CASES: tid' < tid \/ tid < tid') by nia.
        des.
        + rewrite nth_error_app1 in NTH.
          2: { rewrite repeat_length. ss. }
          apply nth_error_In in NTH.
          apply repeat_spec in NTH. subst. ss.
        + rewrite nth_error_app2 in NTH.
          2: { rewrite repeat_length. nia. }
          rewrite repeat_length in NTH.

          destruct (tid' - tid) eqn:TID'; ss.
          { exfalso. nia. }
          apply nth_error_In in NTH.
          apply repeat_spec in NTH. subst. ss.
    }
    des.
    guardH TES1_R.

    hexploit IHISTAR; eauto. i. des.
    assert (ES_TOT: exists es_tot,
               cons_each_rel tes1 es_lstep es_tot).
    { exists (cons_each tes1 es_lstep).
      eapply cons_each_impl_rel.
      rewrite LEN_TES1.
      eapply msteps_num_sites_eq in MSTEPS_SRC.
      des; ss. }
    des.

    exists (S fuel), o_app_st', (S n), es_tot, ((tm, es1) :: es_tid).

    splits; ss.
    - econs; eauto.
      apply DSys_filter_nb_sysstep_inv in FLT_TES1.

      inv ASTEP.
      + (* TAU *)
        inv TAU_STEP.
        rewrite OBS_TAU.

        assert (tes1_r = repeat (tm, []) num_tasks).
        { eapply nth_eq_list_eq'.
          { rewrite repeat_length.
            eapply Forall2_length in FLT_TES1. nia. }
          intros i [] [] TES1_R_I NTH_NIL.
          apply nth_error_In in NTH_NIL.
          eapply repeat_spec in NTH_NIL. subst.

          eapply Forall2_nth1 in FLT_TES1; eauto. des.
          assert (I_CASES: i = tid \/ i <> tid) by nia.
          des.
          - subst i.
            clarify. ss.
            apply DSys_filter_nb_localstep_inv in FLT1.
            des; ss. clarify.
            inv FILTERED_NB_EACH.
            apply DSys_filter_nb_localstep_inv in P_FA.
            des; ss. clarify.
            inv FILTERED_NB_EACH. ss.
          - hexploit OTHER_SILENT; eauto.
            destruct e2; ss. i. subst.
            eapply DSys_filter_nb_localstep_inv in P_FA.
            des; ss. clarify.
            inv FILTERED_NB_EACH. ss.
        }
        subst tes1_r.
        econs 2; ss.

      + (* system event *)
        clear AT_EVENT.
        inv AFT_EVENT.
        existT_elim. ss. clarify.
        rewrite OBS.

        unfold app_event_handler.
        simpl_itree_goal.
        simpl_itree_goal.
        simpl_itree_goal.

        econs 4; eauto; ss.
        2: { s. symmetry.
             simpl_itree_goal.
             reflexivity. }
        rewrite TES1_R.
        repeat f_equal.
        apply DSys_filter_nb_localstep_inv in FLT1.
        des; ss.
        clear - FILTERED_NB_EACH.
        inv FILTERED_NB_EACH.
        match goal with
        | H: Forall2 _ [] _ |- _ => inv H
        end.
        unfold DSys.filter_nb1 in *. ss. clarify.

      + (* send event *)
        clear AT_EVENT.
        inv AFT_EVENT.
        existT_elim. ss. clarify.
        rewrite OBS.

        unfold app_event_handler.
        simpl_itree_goal.
        simpl_itree_goal.

        econs 2; eauto; ss.
        { simpl_itree_goal. ss. }
        rewrite TES1_R.
        eapply nth_eq_list_eq'.
        { rewrite replace_nth_length.
          rewrite repeat_length. ss. }
        intros i [] [] NTH1 NTH2.

        assert (I_CASES: i = tid \/ i <> tid) by nia.
        des.
        * subst i.
          rewrite replace_nth_gss in NTH1.
          2: { rewrite repeat_length. nia. }
          clarify.
          apply repeat_spec_nth in NTH2. clarify.
          clear - FLT1.
          eapply DSys_filter_nb_localstep_inv in FLT1. des; ss.
          inv FILTERED_NB_EACH. ss.
        * rewrite replace_nth_gso in NTH1 by nia.
          clarify.

    - eapply Forall3_nth1 in ES_TOT; eauto.
      des. subst. clarify.
    - rewrite rw_cons_app.
      rewrite flatten_tes_app.
      rewrite FLATTEN.
      rewrite map_app.
      f_equal.
      unfold flatten_tes. ss.
      rewrite app_nil_r. ss.
    - i.
      eapply Forall3_nth3 in ES_TOT; eauto.
      des. clarify.
      econs.
      2: { hexploit EVENT_OTHER; eauto. }
      hexploit OTHER_SILENT; eauto. i. subst. ss.
  Qed.

  Lemma sim_run_period_itree
        tid inb lst_src
        tm lst_tgt es_r out lst_tgt' es
        (k: _ -> itree _ _)
        (RANGE_TID: tid < num_tasks)
        (MATCH: match_loc_state tid inb lst_src lst_tgt)
        (STEP: SNode.step sntz_msg num_tasks mcasts tm
                          lst_tgt es_r out lst_tgt')
        (FLT_LOC: DSys.filter_nb_localstep (Z.of_nat tm, es_r) =
                  Some (Z.of_nat tm, es))
    : exists lst_src' n es_lstep es_tid,
      <<MATCH': match_loc_state tid (SNode.init_box num_tasks)
                                lst_src' lst_tgt'>> /\
      <<MSTEPS_SRC:
        msteps sys_src n
               (Z.of_nat tm,
                x <- run_period_itree
                      num_tasks mcasts sntz_msg
                      (Z.of_nat tm) tid inb lst_src;;
                k x)

 (*  ` r : (AppMod.abst_state_t app) ? * list msgT ? <- *)
 (*  run_period_itree (length app_mods) mcasts sntz_msg app (Z.of_nat tm) tid inb oast;; *)


 (* (Z.of_nat tm, x <- lstep_itree *)
 (*                                    sntz_msg num_tasks mcasts *)
 (*                                    (Z.of_nat tm) tid inb lst_src;; *)
 (*                              k x) *)
               es_lstep
               (Z.of_nat tm, k (lst_src', out))>> /\
      <<EVENT_TID: nth_error es_lstep tid = Some es_tid>> /\
      <<FLATTEN: flatten_tes es_tid = (map (fun e => (Z.of_nat tm, e))) es>> /\
      <<EVENT_OTHER:
          forall tid' es'
            (TID_NEQ: tid' <> tid)
            (ES_LSTEP': nth_error es_lstep tid' = Some es'),
            Forall (fun x => snd x = []) es'>>
  .
  Proof.
    inv MATCH.
    inv STEP; ss.
    { existT_elim.
      destruct oast; ss. clear_tt.
      apply DSys_filter_nb_localstep_inv in FLT_LOC.
      des. ss.
      inv FILTERED_NB_EACH. clear_tt.

      exists (LocState app None), 1,
      (repeat [(Z.of_nat tm, [])] num_tasks),
      [(Z.of_nat tm, [])].

      splits.
      - econs. ss.
      - econs; ss.
        3: { econs; eauto. }
        + simpl_itree_goal.
          simpl_itree_goal.

          econs 5; ss.
          instantiate (1:= false). ss.
          symmetry.
          simpl_itree_goal.
          ss.
        + apply DSys_filter_nb_sysstep_repeat_nil.
        + s.
          apply Forall3_nth'.
          splits.
          { do 2 rewrite repeat_length. ss. }
          { do 2 rewrite repeat_length. ss. }
          i.
          apply nth_error_In in NTH_A.
          apply nth_error_In in NTH_B.
          apply nth_error_In in NTH_C.
          apply repeat_spec in NTH_A.
          apply repeat_spec in NTH_B.
          apply repeat_spec in NTH_C.
          subst. ss.
      - eapply repeat_nth_error_Some. ss.
      - ss.
      - i.
        eapply nth_error_In in ES_LSTEP'.
        apply repeat_spec in ES_LSTEP'. subst.
        econs; ss.
    }
    { existT_elim.
      destruct oast; ss. clear_tt.
      apply DSys_filter_nb_localstep_inv in FLT_LOC.
      des. ss.
      inv FILTERED_NB_EACH. clear_tt.
      inv INIT_APP_STATE.

      exists (LocState app (Some (AppMod.init_abst_state app))), 1,
      (repeat [(Z.of_nat tm, [])] num_tasks), [(Z.of_nat tm, [])].

      splits.
      - econs. ss.
      - econs; ss.
        3: { econs; eauto. }
        + simpl_itree_goal.
          simpl_itree_goal.
          econs 5; ss.
          instantiate (1:= true). ss.
          symmetry.
          simpl_itree_goal.
          ss.
        + apply DSys_filter_nb_sysstep_repeat_nil.
        + s.
          apply Forall3_nth'.
          splits.
          { do 2 rewrite repeat_length. ss. }
          { do 2 rewrite repeat_length. ss. }
          i.
          apply nth_error_In in NTH_A.
          apply nth_error_In in NTH_B.
          apply nth_error_In in NTH_C.
          apply repeat_spec in NTH_A.
          apply repeat_spec in NTH_B.
          apply repeat_spec in NTH_C.
          subst. ss.
      - eapply repeat_nth_error_Some. ss.
      - ss.
      - i.
        eapply nth_error_In in ES_LSTEP'.
        apply repeat_spec in ES_LSTEP'. subst.
        econs; ss.
    }

    existT_elim.
    destruct oast as [ast|]; ss. clarify.

    inv RUN_PERIOD.
    { apply DSys_filter_nb_localstep_inv in FLT_LOC. des. ss.
      inv FILTERED_NB_EACH. clear_tt.
      exists (LocState app None), 1,
      (repeat [(Z.of_nat tm, [])] num_tasks), [(Z.of_nat tm, [])].

      splits.
      - econs. ss.
      - econs; ss.
        3: { econs; eauto. }
        + simpl_itree_goal.
          simpl_itree_goal.
          econs 5; ss.
          instantiate (1:= false). ss.
          symmetry.
          simpl_itree_goal.
          ss.
        + apply DSys_filter_nb_sysstep_repeat_nil.
        + s.
          apply Forall3_nth'.
          splits.
          { do 2 rewrite repeat_length. ss. }
          { do 2 rewrite repeat_length. ss. }
          i.
          apply nth_error_In in NTH_A.
          apply nth_error_In in NTH_B.
          apply nth_error_In in NTH_C.
          apply repeat_spec in NTH_A.
          apply repeat_spec in NTH_B.
          apply repeat_spec in NTH_C.
          subst. ss.
      - eapply repeat_nth_error_Some. ss.
      - ss.
      - i.
        eapply nth_error_In in ES_LSTEP'.
        apply repeat_spec in ES_LSTEP'. subst.
        econs; ss.
    }

    inv PERIOD_BEGIN. ss. symmetry in RET. clarify.
    hexploit sim_snode_istar; try eapply STAR; eauto.
    instantiate (1:= fun r =>
                       x <- (let (oast'0, outmsgs) := r in Ret ({| app_mod := app; app_state := oast'0 |}, outmsgs));;
                       k x).
    i. des.

    eexists _.
    exists (S (S n)). exists (map (fun l => (Z.of_nat tm, [])::(Z.of_nat tm, [])::l) es_lstep).
    exists ((Z.of_nat tm, [])::(Z.of_nat tm, [])::es_tid).
    splits.
    { econs; eauto. }
    { econs; ss.
      { simpl_itree_goal.
        simpl_itree_goal.
        eapply Step_RandomEvent with (ret:= true); ss. }
      { eapply DSys_filter_nb_sysstep_repeat_nil. }
      2: {
        instantiate (1:= map (fun l => (Z.of_nat tm, []) :: l) es_lstep).
        apply Forall3_nth'.
        splits.
        { rewrite repeat_length, map_length.
          eapply msteps_num_sites_eq in MSTEPS_SRC.
          des. ss. }
        { rewrite repeat_length, map_length.
          eapply msteps_num_sites_eq in MSTEPS_SRC.
          des. ss. }

        intros m a b c. i.
        eapply nth_error_In in NTH_A.
        apply repeat_spec in NTH_A. subst a.
        rewrite map_nth_error_iff in NTH_B.
        rewrite map_nth_error_iff in NTH_C.
        des. clarify.
      }
      econs; ss.
      { simpl_itree_goal.
        simpl_itree_goal.
        eapply Step_RandomEvent with (ret:= fuel); ss. }
      { eapply DSys_filter_nb_sysstep_repeat_nil. }
      2: {
        instantiate (1:= es_lstep).
        apply Forall3_nth'.
        splits.
        { rewrite repeat_length.
          eapply msteps_num_sites_eq in MSTEPS_SRC.
          des. ss. }
        { rewrite repeat_length, map_length.
          eapply msteps_num_sites_eq in MSTEPS_SRC.
          des. ss. }

        intros m a b c. i.
        eapply nth_error_In in NTH_A.
        apply repeat_spec in NTH_A. subst a.
        rewrite map_nth_error_iff in NTH_C.
        des. unfold events in *. clarify.
      }

      match goal with
      | H: msteps _ _ (_, ?itr1) _ (_, ?itr2) |-
        msteps _ _ (_, ?itr3) _ (_, ?itr4) =>
        replace itr4 with itr2
      end.
      { simpl_itree_goal.
        eapply MSTEPS_SRC. }
      simpl_itree_goal. ss.
    }
    { erewrite map_nth_error; eauto. }
    { ss. }
    i.
    eapply map_nth_error_iff in ES_LSTEP'. des.
    clarify.

    econs; ss. econs; ss.
    hexploit EVENT_OTHER; eauto.
  Qed.



  Lemma sim_step_itree
        tid tm
        lsts_tgt es_r outs lsts_tgt'
        (STEP: Forall4 (SNode.step sntz_msg num_tasks mcasts tm)
                       lsts_tgt es_r outs lsts_tgt')
        (TID: tid + length lsts_tgt = num_tasks)
    : forall R inbs lsts_src tes
        lsts_src_pre'
        (k: _ -> itree _ R)
        (MATCH: iForall3 (match_loc_state) tid
                         inbs lsts_src lsts_tgt)
        (FLT_LOC: DSys.filter_nb_sysstep
                    (map (fun es => (Z.of_nat tm, es)) es_r) =
                  Some tes)
        (LEN_PRE: length lsts_src_pre' = tid)
    ,
      exists lsts_src' n es_step,
      <<MATCH': iForall3 (match_loc_state) tid
                         (repeat (SNode.init_box num_tasks)
                                 (length lsts_tgt))
                         lsts_src' lsts_tgt'>> /\
      (* <<INBS': imap (fun tid _ => map (SNode.get_outbox_msg_by_dest tid) outs) 0 (repeat tt num_tasks) = inbs'>> /\ *)
      <<MSTEPS_SRC:
        msteps sys_src n (Z.of_nat tm,
                          interp_ainvk exec_sys _
                                       (x <- step_itree (Z.of_nat tm) tid inbs ;;
                                        k x)
                                       (lsts_src_pre' ++ lsts_src);;
                         Ret tt)
               es_step
               (Z.of_nat tm, interp_ainvk exec_sys _ (k outs)
                                          (lsts_src_pre' ++ lsts_src') ;; Ret tt)>> /\
      <<DONE_BEFORE:
          forall tid' tes'
            (TID_BEF: tid' < tid)
            (ES_STEP_N: nth_error es_step tid' = Some tes'),
            Forall (fun x => snd x = []) tes' >> /\
      <<EVENTS_AFTER:
              forall tid' tes' te'
                (TID_AFT: tid <= tid')
                (ES_STEP_N: nth_error es_step tid' = Some tes')
                (TES_N: nth_error tes (tid' - tid) = Some te')
              ,
                flatten_tes tes' = flatten_te te'>>.
  Proof.
    depgen tid.
    induction STEP; i; ss.
    { exists [], 0. eexists.
      guardH LEN_PRE.
      inv MATCH.
      unfold DSys.filter_nb_sysstep in *. ss. clarify.

      splits.
      - econs.
      - match goal with
        | |- context [interp_ainvk  _ _ ?tr]  =>
          remember tr as itr eqn:EQN
        end.
        symmetry in EQN.
        simpl_itree_hyp EQN.
        subst.
        rewrite app_nil_r.
        econs 1; eauto.
      - i. ss.
        eapply nth_error_In in ES_STEP_N.
        eapply repeat_spec in ES_STEP_N. subst tes'.
        econs.
      - i. ss.
        destruct (tid' - tid); ss.
    }
    guardH LEN_PRE.

    renames a b into st es.
    renames c d into out st'.
    renames l1 l2 into sts ess.
    renames l3 l4 into outs sts'.

    (* guardH LEN_OUTS_PREV. guardH INBOX. *)
    inv MATCH.
    renames ha ta into inb inbs.
    renames hb tb into lst_src lsts_src.
    renames FA P_HEAD into MATCH MATCH1.

    assert (TID_UBND: tid < num_tasks).
    { unguard. nia. }

    ss.
    match goal with
    | |- context[ interp_ainvk _ _ ?tr ] =>
      remember tr as itr eqn: ITR; symmetry in ITR
    end.
    simpl_itree_hyp ITR.
    simpl_itree_hyp ITR.
    subst itr.
    erewrite unfold_interp_ainvk_vis_invoke by ss.

    assert (exists es1 tes2,
               <<FLT_LOC1: DSys.filter_nb_localstep (Z.of_nat tm, es) =
                           Some (Z.of_nat tm, es1)>> /\
               <<FLT_SYS2: DSys.filter_nb_sysstep (map (fun es => (Z.of_nat tm, es)) ess) =
                           Some tes2>> /\
               <<TES_EQ: tes = (Z.of_nat tm, es1) :: tes2>>).
    { clear - FLT_LOC.
      unfold DSys.filter_nb_sysstep in FLT_LOC. ss. desf.

      match goal with
      | H: DSys.filter_nb_localstep (_, es) = Some ?y |- _ =>
        rename H into FLT_LOC; destruct y
      end.

      apply DSys_filter_nb_localstep_inv in FLT_LOC.
      des; ss. subst.

      esplits; eauto.
    }
    des. subst tes.

    rewrite nth_error_app2.
    2: { unguard. nia. }
    rewrite LEN_PRE.
    rewrite Nat.sub_diag. s.
    destruct lst_src as [app oast].
    simpl_itree_goal.
    simpl_itree_goal.

    hexploit (sim_run_period_itree tid); eauto.
    (* instantiate (1:= *)
    (*                (fun x: loc_state * list msgT? => *)
    (*                   ('(lsts', outb) <- *)
    (*                    (let (lst', outbox) := x in *)
    (*                     Ret (replace_nth (lsts_src_pre' ++ {| app_mod := app; app_state := oast |} :: lsts_src) tid lst', outbox));; *)
    (*                    (Tau *)
    (*                       (interp_ainvk *)
    (*                          exec_sys R *)
    (*                          (x <- *)
    (*                           (outbs' <- step_itree *)
    (*                                       (Z.of_nat tm) (S tid) inbs;; *)
    (*                            Ret (outb :: outbs'));; *)
    (*                           k x) *)
    (*                          lsts')));; *)
    (*                   Ret tt)). *)
    instantiate (1:= (fun r: loc_state * list msgT? =>

` r0 : list loc_state * list msgT ? <-
  (let (lst', outbox) := r in
   Ret (replace_nth (lsts_src_pre' ++ {| app_mod := app; app_state := oast |} :: lsts_src) tid lst', outbox));;
  (let (lsts', outb) := r0 in
   Tau
     (interp_ainvk exec_sys R
        (` x : list (list msgT ?) <-
         (` outs_t : list (list msgT ?) <- step_itree (Z.of_nat tm) (S tid) inbs;; Ret (outb :: outs_t));;
         k x) lsts'));; Ret tt)).

                   (* (fun x: loc_state * list msgT? => *)
                   (*    '(lsts', outb) <- *)
                   (*    (let (lst', outbox) := x in *)
                   (*     Ret (replace_nth (lsts_src_pre' ++ {| app_mod := app; app_state := oast |} :: lsts_src) tid lst', outbox));; *)
                   (*    (Tau *)
                   (*       (interp_ainvk *)
                   (*          exec_sys R *)
                   (*          (outbs' <- step_itree *)
                   (*                      (Z.of_nat tm) (S tid) inbs;; *)
                   (*           k (outb :: outbs')) *)
                   (*          lsts'));; *)
                   (*    Ret tt)). *)
    i. des.

    hexploit (IHSTEP (S tid)); eauto.
    { nia. }
    { instantiate (1:= lsts_src_pre' ++ [lst_src']).
      rewrite app_length. ss.
      unguard. nia. }

    instantiate (1:= fun outbs =>
                       x <- Ret (out :: outbs) ;;
                       k x).
    (* fun outbs: list (list msgT ?) => *)
    (*                    k outbs *)
    (*                    y <- (let (lsts_t', outs) := x in *)
    (*                         Ret (lst_src' :: lsts_t', out :: outs));; *)
    (*                    k y). *)
    i. des.

    hexploit msteps_concat.
    { eapply MSTEPS_SRC. }
    { simpl_itree_goal.
      simpl_itree_goal.

      econs 2; ss.
      - econs 2; ss.
      - unfold DSys.filter_nb_sysstep.
        apply deopt_list_Some_iff.
        do 2 rewrite map_repeat. ss.
      - erewrite replace_nth_exact by ss.
        rewrite <- app_assoc in MSTEPS_SRC0.
        match goal with
        | H: msteps _ _ (_, ?itr1) _ _ |-
          msteps _ _ (_, ?itr2) _ _ =>
          cut (itr1 = itr2)
        end.
        { intro REW. rewrite <- REW. eauto. }
        f_equal.
        f_equal.
        symmetry.
        simpl_itree_goal. ss.
      - ss. eapply cons_each_impl_rel.
        rewrite repeat_length.
        eapply msteps_num_sites_eq in MSTEPS_SRC0.
        ss. des. ss.
    }
    i. des.

    hexploit (cons_each_impl_rel
                _ (repeat (Z.of_nat tm, [])
                          (length app_mods)) es_step).
    { rewrite repeat_length.
      eapply msteps_num_sites_eq in MSTEPS_SRC0.
      ss. des; ss. }
    intro CONS_EACH_REL.

    esplits.
    - econs; eauto.
    - match goal with
      | H: msteps _ (_ + _) ?st ?es ?st' |-
        msteps _ _ ?st_g _ ?st_g' =>
        replace st_g' with st'
      end.
      2: { rewrite <- app_assoc. ss.
           f_equal. f_equal. f_equal.
           simpl_itree_goal. ss.
      }
      eauto.
      (* match goal with *)
      (* | H: msteps _ _ (_, ?itr1) _ _ |- *)
      (*   msteps _ _ (_, ?itr2) _ _ => *)
      (*   cut (itr1 = itr2) *)
      (* end. *)
      (* { intro ITR_EQ. *)
      (*   rewrite <- ITR_EQ. *)
      (*   eauto. } *)
      (* eauto. *)
    - i. eapply Forall3_nth3 in ES_CONCAT; eauto.
      des. subst.
      eapply Forall_app.
      + hexploit (EVENT_OTHER tid'); eauto.
        nia.
      + renames NTH1 NTH2 into LSTEP_TID' CONS_EACH_TID'.
        eapply Forall3_nth3 in CONS_EACH_REL; eauto.
        des. subst.
        apply repeat_spec_nth in NTH1. subst.
        econs; ss.
        hexploit (DONE_BEFORE tid'); eauto.

    - i. eapply Forall3_nth3 in ES_CONCAT; eauto.
      des. subst.
      renames NTH1 NTH2 into LSTEP_TID' EACH_TID'.
      renames e1 e2 into es_lstep1 es_lstep2.

      eapply Forall3_nth3 in CONS_EACH_REL; eauto.
      des. subst.
      renames e1 e2 into e1_nil e2_nil.

      assert (TID'_REL: tid = tid' \/ S tid <= tid') by nia.
      destruct TID'_REL.
      + subst tid'.
        rewrite Nat.sub_diag in TES_N. ss. clarify.
        rewrite flatten_tes_app.
        rewrite FLATTEN.

        hexploit (DONE_BEFORE tid); eauto.
        intros ES_NIL.

        assert (FLT_E2: flatten_tes e2_nil = []).
        { apply flatten_silent_local_trace_iff. ss. }
        unfold flatten_tes in *. ss.
        rewrite FLT_E2.
        rewrite app_nil_r.

        apply repeat_spec_nth in NTH1.
        subst e1_nil.
        unfold flatten_te. ss.
        rewrite app_nil_r. ss.

      + hexploit (EVENTS_AFTER tid').
        { nia. }
        { replace (tid' - tid) with (S (tid' - S tid)) in TES_N by nia.
          simpl in TES_N. eauto. }
        { replace (tid' - tid) with (S (tid' - S tid)) in TES_N by nia.
          simpl in TES_N. eauto. }
        intro RW.
        rewrite flatten_tes_app.
        (* unfold flatten_tes in *. ss. *)
        rewrite <- RW.

        hexploit (EVENT_OTHER tid'); eauto.
        { nia. }

        intro E1_NIL.
        eapply flatten_silent_local_trace_iff in E1_NIL.
        rewrite E1_NIL. ss.
        apply repeat_spec_nth in NTH1.
        subst e1_nil. ss.
  Qed.

  (* Lemma sync_sys_msteps_nosync_exists *)
  (*       n tm lsts st sytm *)
  (*       (* (MSTEPS: msteps sys_tgt n st tr st') *) *)
  (*       (STATE: st = SyncSys.State tm lsts) *)
  (*       (SYNC_TIME: Nat.divide period sytm) *)
  (*       (AFTER_SYNC: sytm < tm) *)
  (*       (BEFORE_NXT_SYNC: tm + n <= sytm + period) *)
  (*   : exists tr st', *)
  (*     msteps sys_tgt n st tr st'. *)
  (* Proof. *)
  (*   depgen st. depgen tm. *)
  (*   induction n as [| n' IH]; i; ss. *)
  (*   { esplits; eauto. *)
  (*     econs; eauto. } *)

  (*   subst. *)
  (*   assert (MSTEPS1: exists tr1, *)
  (*              msteps sys_tgt 1 *)
  (*                     (SyncSys.State tm lsts) *)
  (*                     tr1 (SyncSys.State (S tm) lsts)). *)
  (*   { esplits. *)
  (*     econs; ss. *)
  (*     3: { econs; eauto. } *)
  (*     - econs 1; eauto. *)
  (*       eapply in_btw_cant_divide; eauto. *)
  (*       nia. *)
  (*     - unfold DSys.filter_nb_sysstep. *)
  (*       instantiate (1:= repeat (Z.of_nat tm, []) (length lsts)). *)
  (*       apply deopt_list_Some_iff. *)
  (*       do 2 rewrite map_repeat. ss. *)
  (*     - ss. *)
  (*       unfold SyncSys.num_sites. ss. *)
  (*       eapply cons_each_impl_rel. *)
  (*       do 2 rewrite repeat_length. ss. *)
  (*   } *)
  (*   des. *)
  (*   hexploit (IH (S tm)); eauto. *)
  (*   { nia. } *)
  (*   intros (tr2 & st2 & MSTEPS2). *)

  (*   hexploit msteps_concat. *)
  (*   { apply MSTEPS1. } *)
  (*   { apply MSTEPS2. } *)
  (*   i. des. *)
  (*   esplits; eauto. *)
  (* Qed. *)

  Lemma sync_sys_msteps_nosync_impl
        n tm lsts st tr st' sytm
        (MSTEPS: msteps sys_tgt n st tr st')
        (STATE: st = SyncSys.State tm lsts)
        (SYNC_TIME: Nat.divide period sytm)
        (AFTER_SYNC: sytm < tm)
        (BEFORE_NXT_SYNC: tm + n <= sytm + period)
  : <<TRACE_NILS: Forall (Forall (fun tes => snd tes = [])) tr>> /\
    <<TGT'_EQ: st' = SyncSys.State (tm + n) lsts>>.
  Proof.
    depgen tm.
    induction MSTEPS; i; ss.
    { subst.
      esplits; eauto; ss.
      - eapply Forall_forall.
        intros x X_IN.
        apply repeat_spec in X_IN. subst x.
        econs.
      - f_equal. nia.
    }

    subst.
    inv STEP.
    2: {
      exfalso.
      clear - PERIOD_POS AFTER_SYNC BEFORE_NXT_SYNC
                         WAIT SYNC_TIME.
      r in WAIT. des. rename z into z_tm.
      r in SYNC_TIME. des. rename z into z_sytm.
      subst.

      assert (z_sytm < z_tm /\ z_tm <= z_sytm) by nia.
      nia.
    }

    hexploit IHMSTEPS; eauto.
    { nia. }
    i. des. subst.
    apply DSys_filter_nb_sysstep_inv in FILTER_NB.

    splits.
    2: { f_equal. nia. }

    apply Forall_nth. intro k.
    destruct (nth_error tr k) eqn: TR_K.
    2: { unfold events in *.
         rewrite TR_K. ss. }

    eapply Forall3_nth3 in CONS_EVENTS; eauto.
    des. subst.
    destruct e1 as [tm' es1_k].
    renames e2 NTH1 NTH2 into tr2_k ES1_K TR2_K.
    unfold events in *.
    rewrite TR_K. ss.
    econs; ss.
    - eapply Forall2_nth2 in FILTER_NB; eauto.
      des. ss.
      eapply nth_error_In in NTH1.
      apply repeat_spec in NTH1. subst.
      eapply DSys_filter_nb_localstep_inv in P_FA.
      des; ss.
      inv FILTERED_NB_EACH. ss.
    - eapply Forall_nth in TRACE_NILS.
      rewrite TR2_K in TRACE_NILS. ss.
  Qed.



  Lemma match_loc_state_new_inb
        tid lst nst
        inb outs
        (MATCH: match_loc_state
                  tid (SNode.init_box num_tasks) lst nst)
        (OUTS_INB_REL: map (SNode.get_outbox_msg_by_dest tid) outs = inb)
    : match_loc_state tid inb lst (SNode.accept_msgs outs nst).
  Proof.
    inv MATCH. s.
    econs. ss.
  Qed.


  Lemma iForall3_match_loc_state_new_inb
        inbs' lsts_src'
        lsts_tgt1 lsts_tgt' outs
        (MATCH' : iForall3 match_loc_state 0
                           (repeat (SNode.init_box num_tasks)
                                   num_tasks)
                           lsts_src' lsts_tgt1)
        (TGT': lsts_tgt' = map (SNode.accept_msgs outs)
                               lsts_tgt1)
        (INBS': inbs' = imap (fun tid _ =>
                                map (SNode.get_outbox_msg_by_dest tid) outs)
                             0 (repeat tt num_tasks))
    : iForall3 match_loc_state 0
               inbs' lsts_src' lsts_tgt'.
  Proof.
    eapply iForall3_nth. intro k. s.
    destruct (lt_ge_dec k num_tasks).
    2: {
      apply iForall3_length in MATCH'.
      rewrite repeat_length in MATCH'.
      des.
      rewrite nth_error_None2.
      2: { subst inbs'.
           rewrite imap_length. rewrite repeat_length. ss. }
      rewrite nth_error_None2 by nia.
      rewrite nth_error_None2.
      2: { subst. rewrite map_length. nia. }
      econs.
    }

    eapply iForall3_nth with (n:=k) in MATCH'. ss.
    rewrite repeat_nth_error_Some in MATCH' by nia.
    inv MATCH'.

    erewrite imap_nth_error1.
    2: { rewrite repeat_nth_error_Some; eauto. }
    erewrite map_nth_error; eauto.

    econs.
    eapply match_loc_state_new_inb; eauto.
  Qed.


  Lemma sim_period
    : forall tm tm_p inbs lsts_src lsts_tgt
        (SYNC_TIME: Nat.divide period tm)
        (NUM_TASKS: length lsts_tgt = num_tasks)
        (MATCH_LSTS: iForall3 match_loc_state 0
                              inbs lsts_src lsts_tgt),
      fmsim_states _ sys_src sys_tgt
                   (Z.of_nat tm_p,
                    (interp_ainvk exec_sys _
                                  (synch_itree_loop num_tasks (Z.of_nat period)
                                                    None (Z.of_nat tm) inbs)
                                  lsts_src);; Ret tt)
                   (SyncSys.State tm lsts_tgt).
  Proof.
    pcofix CIH. i.
    pfold. econs.
    { instantiate (1:= period). nia. }
    i.
    assert (PERIOD_DES: exists p', period = S p').
    { destruct period as [| p'] eqn: NPRD; ss.
      { exfalso. nia. }
      exists p'. ss. }
    des.
    guardH PERIOD_DES.
    rewrite PERIOD_DES in STEPS.

    inv STEPS.
    inv STEP; ss.

    assert (<<TRACE_NILS: Forall (Forall (fun tes => snd tes = [])) tr2>> /\
            <<TGT'_EQ: st_tgt' = SyncSys.State (tm + period)
                                               (map (SNode.accept_msgs outs) nsts1)>>).
    { replace (tm + period) with (S tm + p').
      2: { unguard. nia. }
      eapply sync_sys_msteps_nosync_impl; eauto.
      unguard. nia.
    }
    des.
    guardH TGT'_EQ.

    rewrite NUM_TASKS in STEPS.
    hexploit (sim_step_itree O); eauto.
    { instantiate (1:= []). ss. }
    i. des.

    pose (inbs' := imap (fun tid _ =>
                           map (SNode.get_outbox_msg_by_dest tid) outs)
                        0 (repeat tt num_tasks)).

    clear DONE_BEFORE.
    hexploit msteps_num_sites_eq; eauto. i. des. ss.
    clear NUM_SITES_EQ.

    assert (exists tr_src,
               <<MSTEPS_CONCAT:
                 msteps sys_src (S (S (S n)))
                        (Z.of_nat tm_p,
                         (interp_ainvk exec_sys _
                                       (synch_itree_loop
                                          num_tasks (Z.of_nat period)
                                          None (Z.of_nat tm) inbs)
                                       lsts_src);; Ret tt)
                        tr_src
                        (Z.of_nat tm,
                         (interp_ainvk exec_sys _
                                       (synch_itree_loop
                                          num_tasks (Z.of_nat period)
                                          None (Z.of_nat (tm + period)) inbs')
                                       lsts_src');; Ret tt)>> /\
               <<TRS_EQUIV: Forall2 tes_equiv tr_src es_step>>).
    { hexploit (msteps_concat _ sys_src 2 n
                              (Z.of_nat tm_p,
                               (interp_ainvk exec_sys _
                                             (synch_itree_loop
                                                num_tasks (Z.of_nat period)
                                                None (Z.of_nat tm) inbs)
                                             lsts_src);; Ret tt)).
      { econs; ss.
        - econs 3; eauto.
          rewrite unfold_synch_itree_loop. s.
          erewrite unfold_interp_ainvk_vis_tsp.
          { simpl_itree_goal. ss. }
          simpl_itree_goal. ss.
        - instantiate (1:= (repeat (Z.of_nat tm_p, []) num_tasks)).
          unfold DSys.filter_nb_sysstep.
          unfold DSys.filter_nb_localstep.
          apply deopt_list_Some_iff.
          fold num_tasks.
          do 2 rewrite map_repeat. ss.
        - econs; ss.
          + econs 2; eauto.
            simpl_itree_goal. ss.
          + unfold DSys.filter_nb_sysstep.
            unfold DSys.filter_nb_localstep.
            apply deopt_list_Some_iff.
            fold num_tasks.
            do 2 rewrite map_repeat. ss.
          + econs 1; ss.
          + instantiate (1:= repeat [(Z.of_nat tm, [])] num_tasks).
            apply Forall3_nth'.
            splits.
            { do 2 rewrite repeat_length. ss. }
            { do 2 rewrite repeat_length. ss. }
            i.
            apply repeat_spec_nth in NTH_A.
            apply repeat_spec_nth in NTH_B.
            apply repeat_spec_nth in NTH_C.
            subst. ss.
        - instantiate (1:= repeat [(Z.of_nat tm_p, []);
                                   (Z.of_nat tm, [])] num_tasks).
          apply Forall3_nth'.
          splits.
          { do 2 rewrite repeat_length. ss. }
          { do 2 rewrite repeat_length. ss. }
          i.
          apply repeat_spec_nth in NTH_A.
          apply repeat_spec_nth in NTH_B.
          apply repeat_spec_nth in NTH_C.
          subst. ss.
      }
      { apply MSTEPS_SRC. }
      i. des.

      hexploit (msteps_concat _ sys_src (2 + n) 1).
      { eauto. }
      { econs; ss.
        - econs 2; eauto.
          erewrite unfold_interp_ainvk_tau; eauto.
          { simpl_itree_goal. ss. }
          ss.
        - instantiate (1:= (repeat (Z.of_nat tm, []) num_tasks)).
          unfold DSys.filter_nb_sysstep.
          unfold DSys.filter_nb_localstep.
          apply deopt_list_Some_iff.
          fold num_tasks.
          do 2 rewrite map_repeat. ss.
        - econs; eauto.
        - s.
          instantiate (1:= repeat [(Z.of_nat tm, [])] num_tasks).
          apply Forall3_nth'.
          splits.
          { do 2 rewrite repeat_length. ss. }
          { do 2 rewrite repeat_length. ss. }
          i.
          apply repeat_spec_nth in NTH_A.
          apply repeat_spec_nth in NTH_B.
          apply repeat_spec_nth in NTH_C.
          subst. ss.
      }
      replace (2 + n + 1) with (S (S (S n))) by nia.
      renames es MSTEPS_CONCAT ES_CONCAT into
      es_step' MSTEPS_CONCAT1 ES_CONCAT1.
      i. des.

      match type of ES_CONCAT1 with
      | Forall3 _ ?c _ _ =>
        remember c as l_tmp1 eqn: L_TMP1
      end.
      match type of ES_CONCAT with
      | Forall3 _ _ ?c _ =>
        remember c as l_tmp2 eqn: L_TMP2
      end.

      (* assert (CONS_EACH_REL1: *)
      (*           cons_each_rel *)
      (*             (repeat (Z.of_nat tm_p, []) num_tasks) *)
      (*             (repeat [] num_tasks) l_tmp1). *)
      (* { subst l_tmp1. *)
      (*   eapply cons_each_impl_rel. *)
      (*   do 2 rewrite repeat_length. *)
      (*   ss. } *)
      (* clear L_TMP1. *)

      (* assert (CONS_EACH_REL2: *)
      (*           cons_each_rel *)
      (*             (repeat (Z.of_nat tm, []) num_tasks) *)
      (*             (repeat [] num_tasks) l_tmp2). *)
      (* { subst l_tmp2. *)
      (*   eapply cons_each_impl_rel. *)
      (*   do 2 rewrite repeat_length. *)
      (*   ss. } *)
      (* clear L_TMP2. *)

      esplits; eauto.
      { fold inbs' in MSTEPS_CONCAT.
        rewrite <- Nat2Z.inj_add in MSTEPS_CONCAT.
        eauto. }
      apply Forall2_tes_equiv_trans with (trsl2:= es_step').
      - eapply Forall2_nth.
        intro k. i. subst.
        destruct (lt_ge_dec k num_tasks).
        2: {
          apply Forall3_length in ES_CONCAT. des; ss.
          rewrite repeat_length in ES_CONCAT.
          rewrite nth_error_None2 by nia.
          rewrite nth_error_None2 by nia.
          econs.
        }

        eapply Forall3_nth2 with (n:= k) in ES_CONCAT.
        2: { apply repeat_nth_error_Some. ss. }
        des.
        subst e3.
        renames e1 NTH1 NTH3 into es_step'_k ES_STEP'_K ES_K.
        rewrite ES_K. rewrite ES_STEP'_K.
        econs. s.
        unfold tes_equiv.
        rewrite flatten_tes_app.

        unfold flatten_tes. s.
        rewrite app_nil_r. ss.
      - eapply Forall2_nth.
        intro k. subst.
        destruct (lt_ge_dec k num_tasks).
        2: {
          apply Forall3_length in ES_CONCAT1. des; ss.
          rewrite repeat_length in *.
          rewrite nth_error_None2 by nia.
          rewrite nth_error_None2 by nia.
          econs.
        }

        eapply Forall3_nth1 with (n:= k) in ES_CONCAT1.
        2: { apply repeat_nth_error_Some. ss. }
        des.
        subst e3.
        renames e2 NTH2 NTH3 into es_step_k ES_STEP_K ES_STEP'_K.
        rewrite ES_STEP_K. rewrite ES_STEP'_K.
        econs. s.
        unfold tes_equiv.
        unfold flatten_tes. ss.
    }
    des.

    exists (S (S (S n))).
    esplits; eauto.
    { nia. }
    { eapply Forall2_tes_equiv_trans; eauto.
      apply Forall2_nth. intro k.
      eapply DSys_filter_nb_sysstep_inv in FILTER_NB.

      hexploit Forall3_length; try apply CONS_EVENTS.
      intros (LEN_CE1 & LEN_CE2).
      hexploit Forall2_length; try apply FILTER_NB.
      rewrite map_length. intros LEN_FNB.
      hexploit Forall4_length; try apply STEPS.
      intros (LEN_STEP1 & LEN_STEP2 & LEN_STEP3). des.

      destruct (lt_ge_dec k num_tasks).
      2: {
        rewrite nth_error_None2 by nia.
        rewrite nth_error_None2 by nia.
        econs.
      }

      hexploit (nth_error_Some2 _ es_step k).
      { nia. }
      i. des.
      renames e1 NTH_EX into es_step_k ES_STEP_K.

      hexploit (nth_error_Some2 _ es1 k).
      { nia. }
      i. des.
      renames e1 NTH_EX into es1_k ES1_K.
      rewrite ES_STEP_K.

      eapply Forall3_nth1 in CONS_EVENTS; eauto.
      des. subst.
      renames e2 NTH2 NTH3 into tr2_k TR2_K TR_TGT_K.
      rewrite TR_TGT_K.

      econs.
      rewrite Forall_forall in TRACE_NILS.
      hexploit TRACE_NILS.
      { eapply nth_error_In. eauto. }
      intro TR2_K_SILENT.

      unfold tes_equiv.
      hexploit EVENTS_AFTER; try apply ES_STEP_K; eauto.
      { nia. }
      { replace (k - 0) with k by nia.
        eauto. }
      i. unfold flatten_tes at 2. ss.
      cut (flatten_tes tr2_k = []).
      { fold (flatten_tes tr2_k).
        intro R. rewrite R.
        rewrite app_nil_r. ss. }
      apply flatten_silent_local_trace_iff. ss.
    }

    right.
    unguard. subst st_tgt'.
    (* replace (Z.of_nat (tm + period))%Z with (Z.of_nat (tm + period)) by nia. *)

    eapply CIH; eauto.
    - eapply Nat.divide_add_r.
      + ss.
      + apply Nat.divide_refl.
    - rewrite map_length.
      eapply Forall4_length in STEPS. des. nia.
    - rewrite NUM_TASKS in MATCH'.
      eapply iForall3_match_loc_state_new_inb; eauto.
  Qed.

  Lemma fmsim_states_append_silent_prefix_tgt
        st_src
        n st_tgt_p st_tgt
        (FMSIM: fmsim_states _ sys_src sys_tgt st_src st_tgt)
        (MSTEPS_TGT:
           forall tr_tgt st_tgt'
             (MSTEPS: msteps sys_tgt n
                             st_tgt_p tr_tgt st_tgt'),
             <<TR_SILENT: Forall (Forall (fun tes => snd tes = [])) tr_tgt>> /\
             <<STATE_DET: st_tgt' = st_tgt>>)
    : fmsim_states _ sys_src sys_tgt st_src st_tgt_p.
  Proof.
    punfold FMSIM.
    2: { apply fmsim_states_monotone. }
    inv FMSIM.
    pfold. econs.
    { instantiate (1:= n + n_tgt). nia. }
    i.
    apply msteps_split in STEPS. des.
    hexploit MSTEPS_TGT; eauto. i. des. subst.

    hexploit STEPS_SIM; eauto. i. des.
    esplits; eauto.
    eapply Forall2_tes_equiv_trans; eauto.

    apply Forall2_nth. intro k.
    destruct (nth_error es2 k) eqn: ES2_K.
    2: {
      rewrite nth_error_None in ES2_K.
      apply Forall3_length in ES_DIV. des.
      rewrite nth_error_None2 by nia.
      econs.
    }

    eapply Forall3_nth2 in ES_DIV; eauto. des. subst.
    rewrite NTH3. econs.
    r.
    rewrite flatten_tes_app.

    cut (flatten_tes e1 = []).
    { intro R. rewrite R. ss. }
    apply flatten_silent_local_trace_iff.
    eapply Forall_nth in TR_SILENT.

    unfold events in *.
    rewrite NTH1 in TR_SILENT. ss.
  Qed.

  Lemma sync_exec_fmsim_states
        lsts_tgt
        (LSTS_TGT: lsts_tgt = imap (SNode.init_state (length nodes)) 0 nodes)
    : fmsim_states _ sys_src sys_tgt
                   (Z0, interp_ainvk exec_sys _
                                     (synch_itree num_tasks (Z.of_nat period)
                                                  (Z.of_nat tm_init) None)
                                     (init_loc_states exec_sys);;
                        Ret tt)
                   (SyncSys.State tm_init lsts_tgt).
  Proof.
    (* pose (m := (Z.to_nat tm_init) mod (Z.to_nat period)). *)
    pose (m := (tm_init mod period)).
    pose (n_pre := if m =? 0 then 0 else period - m).

    eapply fmsim_states_append_silent_prefix_tgt
      with (n:= n_pre).
    2: {
      instantiate (1:= SyncSys.State (tm_init + n_pre) lsts_tgt).
      destruct (Nat.eqb_spec m 0).
      { i.
        subst n_pre. inv MSTEPS.
        splits; ss.
        2: { f_equal. nia. }
        apply Forall_forall.
        intros x X_IN.
        apply repeat_spec in X_IN. subst x. econs.
      }
      i.
      eapply sync_sys_msteps_nosync_impl; eauto.
      { instantiate (1:= tm_init - m).
        r.
        hexploit (Nat.div_mod tm_init period).
        { nia. }
        i.
        exists (tm_init / period). nia.
      }
      { nia. }
      { subst n_pre.
        cut (m < period).
        { nia. }
        subst m.
        (* apply Z2Nat.inj_lt; try nia. *)
        apply Nat.mod_upper_bound. nia.
      }
    }

    unfold synch_itree. ss.
    fold m. fold n_pre.

    assert (LEN_LSTS_TGT: length lsts_tgt = num_tasks).
    { subst lsts_tgt.
      rewrite imap_length.
      subst nodes.
      rewrite map_length. ss. }

    match goal with
    | |- context[(Z.of_nat tm_init + ?x)%Z] =>
      replace x with (Z.of_nat n_pre)
    end.
    2: {
      assert (m < period).
      { subst m.
        apply Nat.mod_upper_bound. nia. }
      rewrite <- mod_Zmod by nia.
      fold m.
      replace (Z.of_nat m =? 0)%Z with
          (Z.of_nat m =? Z.of_nat O)%Z.
      2: { f_equal. }
      rewrite Nat2Z_inj_eqb.

      destruct (Nat.eqb_spec m O) as [EQ | NEQ].
      - ss.
      - nia.
    }

    replace 0%Z with (Z.of_nat 0) by nia.
    rewrite <- Nat2Z.inj_add.
    eapply sim_period.
    { destruct (Nat.eqb_spec m 0).
      - subst n_pre.
        rewrite Nat.add_0_r.
        eapply Nat.mod_divide; nia.
      - subst n_pre. subst m.
        hexploit (Nat.div_mod tm_init period).
        { nia. }
        i. r.
        exists ((tm_init / period) + 1)%nat.

        assert (tm_init mod period < period)%nat.
        { apply Nat.mod_upper_bound. nia. }
        nia.
    }
    { ss. }

    apply iForall3_nth. intro tid. ss.
    fold num_tasks.
    destruct (lt_ge_dec tid num_tasks).
    2: {
      rewrite nth_error_None2.
      2: { rewrite repeat_length. ss. }
      rewrite nth_error_None2.
      2: { unfold init_loc_states.
           rewrite map_length. ss. }
      rewrite nth_error_None2.
      2: { nia. }
      econs.
    }

    hexploit (nth_error_Some2 _ lsts_tgt tid).
    { nia. }
    i. des. renames e1 NTH_EX into lst_tgt LST_TGT.
    rewrite LST_TGT.
    subst lsts_tgt.
    rewrite imap_nth_error_iff in LST_TGT. ss.
    destruct (nth_error nodes tid) eqn: NODE_N; ss.
    clarify.

    unfold nodes in NODE_N.
    rewrite map_nth_error_iff in NODE_N. des. subst.

    match goal with
    | |- option_rel3 _ (nth_error ?x _) (nth_error ?y _) _ =>
      pose (l1:= x); pose (l2:= y)
    end.

    hexploit (nth_error_Some2 _ l1 tid).
    { subst l1.
      rewrite repeat_length. ss. }
    subst l1. i. des.
    rewrite NTH_EX.
    eapply nth_error_In in NTH_EX.
    apply repeat_spec in NTH_EX.
    subst e1.

    hexploit (nth_error_Some2 _ l2 tid).
    { subst l2.
      unfold init_loc_states.
      rewrite map_length. ss. }
    subst l2. i. des.
    rewrite NTH_EX.
    rename NTH_EX into LST1.
    apply map_nth_error_iff in LST1.
    des. subst.

    clarify.
    econs.
    replace (length nodes) with num_tasks.
    2: { subst nodes. rewrite map_length. ss. }

    s. subst exec_sys. ss. clarify.
  Qed.

End PROOF.
