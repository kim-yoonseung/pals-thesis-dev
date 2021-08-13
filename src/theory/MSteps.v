From Paco Require Import paco.
From ITree Require Import ITree.

Require Import Streams List Lia.

Require Import sflib.
Require Import StdlibExt.
Require Import SysSem.
Require Import IndefiniteDescription.

Set Nested Proofs Allowed.


Inductive msteps {sysE: Type -> Type} (sys: @DSys.t sysE)
  : nat -> sys.(DSys.state) ->
    list (list (tsp * events sysE)) ->
    sys.(DSys.state) -> Prop :=
| MSteps_Base
    st es
    (EVENTS: es = List.repeat [] (DSys.num_sites _ st))
  : msteps sys O st es st

| MSteps_Step
    n st0 es1_r es1 st1 tr2 st2 tr
    (STEP: DSys.step sys st0 es1_r st1)
    (FILTER_NB: DSys.filter_nb_sysstep es1_r = Some es1)
    (MSTEPS_REST: msteps sys n st1 tr2 st2)
    (CONS_EVENTS: cons_each_rel es1 tr2 tr)
  : msteps sys (S n) st0 tr st2.


Lemma msteps_num_sites_eq sysE
      (sys: @DSys.t sysE)
      n st ts st'
      (MSTEPS: msteps sys n st ts st')
  : <<NUM_SITES_EQ: DSys.num_sites _ st' = DSys.num_sites _ st>> /\
    <<EVENTS_LEN: DSys.num_sites _ st' = length ts>>.
Proof.
  induction MSTEPS; ss.
  { esplits; ss.
    subst. rewrite repeat_length. ss. }
  eapply DSys.step_prsv_num_sites in STEP. des.
  esplits.
  - congruence.
  - apply Forall3_length in CONS_EVENTS. des.
    congruence.
Qed.

Lemma msteps_trace_row_length sysE
      (sys: @DSys.t sysE)
      n st ts st'
      (MSTEPS: msteps sys n st ts st')
  : Forall (fun r => length r = n) ts.
Proof.
  induction MSTEPS; ss.
  { subst.
    apply Forall_forall.
    intros x IN.
    apply repeat_spec in IN. subst. ss.
  }
  apply Forall_nth. intro m.
  destruct (lt_ge_dec m (length tr)).
  2: { rewrite nth_error_None2 by ss. econs. }
  hexploit (nth_error_Some2 _ tr m); ss. i. des.
  renames e1 NTH_EX into tr_m TR_M.
  rewrite TR_M. r.

  eapply Forall3_nth3 in CONS_EVENTS; eauto. des.
  subst. ss.
  rewrite Forall_forall in IHMSTEPS.
  hexploit IHMSTEPS.
  { eapply nth_error_In; eauto. }
  i. nia.
Qed.


Lemma safe_state_mstep sysE
      (sys: @DSys.t sysE)
      n (st: DSys.state sys) ts st'
      (SAFE: DSys.safe_state st)
      (STEPS: msteps _ n st ts st')
  : DSys.safe_state st'.
Proof.
  induction STEPS; ss.
  punfold SAFE. inv SAFE.
  hexploit SAFE_NXT; eauto.
  { congruence. }
  i. pclearbot.
  eauto.
Qed.


Lemma msteps_concat sysE
      (sys: @DSys.t sysE)
      n1 n2
      st0 es1 st1 es2 st2
      (MSTEPS1: msteps sys n1 st0 es1 st1)
      (MSTEPS2: msteps sys n2 st1 es2 st2)
  : exists es,
    <<MSTEPS_CONCAT: msteps sys (n1 + n2) st0 es st2>> /\
    <<ES_CONCAT: Forall3 (fun e1 e2 e => e1 ++ e2 = e)
                         es1 es2 es>>.
Proof.
  induction MSTEPS1.
  { esplits; eauto.
    subst.
    apply Forall3_nth. i.
    eapply msteps_num_sites_eq in MSTEPS2. des.

    destruct (lt_ge_dec n (length es2)).
    - hexploit (nth_error_Some2 _ es2 n); eauto. i. des.
      rewrite NTH_EX.
      rewrite repeat_nth_error_Some by nia.
      econs. ss.
    - rewrite nth_error_None2.
      2: { rewrite repeat_length. nia. }
      rewrite nth_error_None2 by ss.
      econs.
  }

  specialize (IHMSTEPS1 MSTEPS2). des.

  hexploit (Forall_app_ex _ tr es2); eauto.
  { apply Forall3_length in CONS_EVENTS. des.
    apply Forall3_length in ES_CONCAT. des. nia. }
  intros [ls LS].

  exists ls.
  esplits; eauto.

  replace (S n + n2) with (S (n + n2)) by nia.
  econs; eauto.
  unfold cons_each_rel in *.

  apply Forall3_nth. intro k.
  rewrite Forall3_nth in *.
  specialize (CONS_EVENTS k).
  specialize (ES_CONCAT k).
  specialize (LS k).

  destruct (nth_error ls k) eqn:LS_K.
  - inv LS.
    destruct (nth_error es2 k); ss.
    destruct (nth_error tr k); ss.
    inv ES_CONCAT.
    inv CONS_EVENTS.
    repeat match goal with
           | H: _ = nth_error _ _ |- _ => symmetry in H
           end.
    clarify.
    econs. ss.
  - inv LS.
    destruct (nth_error es2 k); ss.
    destruct (nth_error tr k); ss.
    inv ES_CONCAT.
    inv CONS_EVENTS.
    econs.
Qed.

Lemma msteps_split sysE
      (sys: @DSys.t sysE)
      n1 n2 st es st'
      (MSTEPS: msteps sys (n1 + n2) st es st')
  : exists st1 es1 es2,
    <<MSTEPS1: msteps sys n1 st es1 st1>> /\
    <<MSTEPS2: msteps sys n2 st1 es2 st'>> /\
    <<ES_DIV: Forall3 (fun es1 es2 es => es1 ++ es2 = es)
                      es1 es2 es>>.
Proof.
  depgen st. revert es.
  induction n1 as [| n1 IH]; i; ss.
  { esplits; eauto.
    { econs; eauto. }
    apply Forall3_nth. i.
    hexploit msteps_num_sites_eq; eauto. i. des.
    rewrite <- NUM_SITES_EQ.
    rewrite EVENTS_LEN.
    destruct (lt_ge_dec n (length es)).
    - hexploit (nth_error_Some2 _ es n); eauto.
      i. des.
      rewrite NTH_EX.
      rewrite repeat_nth_error_Some by ss.
      econs. ss.
    - rewrite nth_error_None2.
      2: { rewrite repeat_length. ss. }
      rewrite nth_error_None2 by ss.
      econs.
  }

  inv MSTEPS.
  hexploit IH; eauto.
  intros (st2 & es2 & es3 & AUX). des.

  exists st2.

  hexploit (Forall_cons_ex _ es1 es2).
  { apply Forall3_length in CONS_EVENTS.
    apply Forall3_length in ES_DIV.
    des. nia. }
  intros (es1' & ES1').

  exists es1', es3.
  esplits; eauto.
  { econs; eauto. }

  apply Forall3_nth. i.

  r in CONS_EVENTS.
  rewrite Forall3_nth in ES_DIV, ES1', CONS_EVENTS.
  specialize (ES_DIV n).
  specialize (ES1' n).
  specialize (CONS_EVENTS n).

  destruct (nth_error es2 n); ss.
  2: {
    inv ES_DIV. inv ES1'.
    inv CONS_EVENTS.
    2: { congruence. }
    econs.
  }
  inv ES_DIV. inv ES1'.
  inv CONS_EVENTS.
  { congruence. }
  econs.

  ss. congruence.
Qed.


Lemma safe_exec_impl_msteps
      (sysE: Type -> Type)
      (sys: @DSys.t sysE)
      (st: DSys.state sys) exec
      (SAFE: DSys.safe_state st)
      (EXEC: DSys.exec_state _ st exec)
  : forall n, exists tr st' exec',
      <<EXEC_DIV: Forall3 (fun a b c => stream_app a b = c)
                          tr exec' exec>> /\
      <<MSTEPS: msteps _ n st tr st'>> /\
      <<SAFE: DSys.safe_state st'>> /\
      <<EXEC': DSys.exec_state _ st' exec'>>.
Proof.
  intros n.
  depgen st. revert exec.
  induction n as [| n' IH]; i; ss.
  { esplits; eauto.
    2: { econs 1; eauto. }
    eapply Forall3_nth. i.
    eapply exec_state_len in EXEC.
    destruct (lt_ge_dec n (length exec)).
    2: {
      rewrite nth_error_None2.
      2: { rewrite repeat_length. nia. }
      rewrite nth_error_None2 by ss.
      econs.
    }
    rewrite repeat_nth_error_Some by nia.
    hexploit (nth_error_Some2 _ exec n); ss.
    i. des.
    unfold lexec_t in *.
    rewrite NTH_EX. econs. ss.
  }
  punfold SAFE. inv SAFE.
  punfold EXEC. inv EXEC.
  { exfalso. eauto. }

  hexploit SAFE_NXT; eauto.
  { congruence. }
  intro SAFE'. pclearbot.

  hexploit IH; eauto.
  { inv EXEC_REST; ss. eauto. }
  intros (tr & st'' & exec'' & EXEC'' & MSTEPS'' & EXEC_ST'').
  i. des.

  assert (TR_TOT: exists tr_tot, cons_each_rel es_sysE tr tr_tot).
  { cut (forall n (N_UB: n < length tr),
            exists tr_tot_n,
              (fun n tr_tot_n =>
                 exists es_sysE_n tr_n,
                   nth_error es_sysE n = Some es_sysE_n /\
                   nth_error tr n = Some tr_n /\
                   es_sysE_n :: tr_n = tr_tot_n)
                n tr_tot_n).
    { intro AUX.
      apply exists_list in AUX. des.
      exists l.
      r. apply Forall3_nth. i.
      destruct (lt_ge_dec n (length l)).
      2: {
        apply Forall3_length in EXEC''.
        apply Forall3_length in BEH_CONS. des.
        rewrite nth_error_None2 by nia.
        rewrite nth_error_None2 by nia.
        rewrite nth_error_None2 by nia.
        econs.
      }
      hexploit (nth_error_Some2 _ l n); ss.
      i. des. rename NTH_EX into L_N.
      rewrite L_N.
      hexploit NTH_PROP; eauto.
      intros (? & ? & NTH1 & NTH2 & ?).
      rewrite NTH1, NTH2. econs. ss.
    }
    i.
    hexploit (nth_error_Some2 _ tr n); ss.
    i. des. rename NTH_EX into TR_N.
    eapply Forall3_nth1 in EXEC''; eauto. i. des.
    renames NTH2 NTH3 into EXEC''_N EXEC'_N. subst.
    eapply Forall3_nth2 in BEH_CONS; eauto. i. des.
    renames NTH1 NTH3 into ES_SYSE_N EXEC_N.
    esplits; eauto.
  }
  des.

  exists tr_tot, st'', exec''.
  splits.
  - apply Forall3_nth. i.
    destruct (lt_ge_dec n (length exec)).
    2: {
      eapply Forall3_length in TR_TOT. des.
      eapply Forall3_length in BEH_CONS. des.
      eapply Forall3_length in EXEC''. des.
      unfold lexec_t in *.
      rewrite nth_error_None2 by nia.
      rewrite nth_error_None2 by nia.
      rewrite nth_error_None2 by nia.
      econs.
    }
    hexploit (nth_error_Some2 _ exec n); eauto.
    i. des. rename NTH_EX into EXEC_N.
    eapply Forall3_nth3 in BEH_CONS; eauto. i. des.
    renames NTH1 NTH2 P_FA into ES_SYSE_N EXEC'_N CONS_EXEC.
    eapply Forall3_nth1 in TR_TOT; eauto. des.
    renames NTH2 NTH3 into TR_N TR_TOT_N. subst.
    eapply Forall3_nth1 in EXEC''; eauto. i. des.
    renames NTH2 NTH3 into EXEC''_N EXEC'_N_TMP.
    clarify.
    unfold lexec_t in *.
    rewrite EXEC''_N, TR_TOT_N, EXEC_N. econs.
    ss.
  - econs; eauto.
  - eauto.
  - ss.
Qed.


Lemma msteps_src_tl_aux {sysE: Type -> Type} sys_src
      (r: _ -> _ -> Prop)
      n_src st_src1 tr st_src' cstr_tl cstr'
      (STEPS_SRC: msteps sys_src n_src st_src1 tr st_src')
      (U_EXEC_ST: upaco2 (DSys._exec_state sys_src) r st_src' cstr')
      (NUM_SITES: DSys.num_sites sys_src st_src1 = length cstr')
      (CSTR_TL_LEN : length cstr_tl = length cstr')
      (CSTR_TL_PROP : forall (n : nat) (a : stream (tsp * events sysE)),
          nth_error cstr_tl n = Some a ->
          exists (tr_n : list (tsp * events sysE))
            (cstr'_n : lexec_t sysE),
        <<TR_N: nth_error tr n = Some tr_n >> /\
        <<CSTR'_N: nth_error cstr' n = Some cstr'_n >> /\
        <<STR_APP: a = stream_app tr_n cstr'_n >>)
  : upaco2 (DSys._exec_state sys_src) r st_src1 cstr_tl.
Proof.
  depgen cstr_tl. depgen cstr'.
  induction STEPS_SRC; i; ss.
  { subst.
    cut (cstr' = cstr_tl).
    { i. congruence. }

    apply nth_eq_list_eq. i.
    destruct (lt_ge_dec n (length cstr_tl)).
    2: { rewrite nth_error_None2 by nia.
         rewrite nth_error_None2 by ss. ss. }

    hexploit (nth_error_Some2 _ cstr_tl n); ss. i. des.
    hexploit CSTR_TL_PROP; eauto. i. des. subst.
    rewrite repeat_nth_error_Some in TR_N by nia.
    unfold lexec_t in *.
    rewrite NTH_EX, CSTR'_N. clarify.
  }
  left. rename n into m.

  assert (length es1 = length es1_r).
  { unfold DSys.filter_nb_sysstep in FILTER_NB.
    apply deopt_list_Some_iff in FILTER_NB.
    erewrite <- map_length.
    rewrite FILTER_NB. rewrite map_length. ss. }

  assert (exists cstr_tl',
             <<CSTR_TL_DIV: Cons_each_rel es1 cstr_tl' cstr_tl>>).
  { cut (forall n (RANGE_N: n < length es1),
            exists (tl'_n: stream (tsp * events sysE)),
              (fun n tl'_n =>
                 exists es1_n tl_n,
                   nth_error es1 n = Some es1_n /\
                   nth_error cstr_tl n = Some tl_n /\
                   Cons es1_n tl'_n = tl_n)
                n tl'_n).
    { intro AUX.
      apply exists_list in AUX. des.
      exists l.
      apply Forall3_nth. i.
      destruct (lt_ge_dec n (length l)).
      2: {
        apply DSys.step_prsv_num_sites in STEP. des.
        rewrite nth_error_None2 by nia.
        rewrite nth_error_None2 by ss.
        rewrite nth_error_None2 by nia.
        econs.
      }

      hexploit (nth_error_Some2 _ l n); ss. i. des.
      renames e1 NTH_EX into l_n L_N.
      hexploit NTH_PROP; eauto.
      intros (es1_n & tl_n & ES1_N & TL_N & ?). subst.
      rewrite ES1_N, L_N, TL_N. econs. ss.
    }

    assert (LEN_EQ: length es1 = length cstr_tl).
    { apply DSys.step_prsv_num_sites in STEP. des. nia. }

    i. hexploit (nth_error_Some2 _ cstr_tl n).
    { nia. }
    i. des.
    renames e1 NTH_EX into tl_n TL_N.
    hexploit CSTR_TL_PROP; eauto. i. des.

    eapply Forall3_nth3 in CONS_EVENTS; eauto. des.
    renames NTH1 NTH2 into ES1_N TR2_N. subst. ss.
    esplits; eauto.
  }
  des.

  hexploit IHSTEPS_SRC.
  { eauto. }
  { apply DSys.step_prsv_num_sites in STEP.
    des. nia. }
  { instantiate (1:= cstr_tl').
    apply Forall3_length in CSTR_TL_DIV. des. congruence. }
  { intros n tl_n TL_N.
    eapply Forall3_nth2 in CSTR_TL_DIV; eauto. des.
    r in P_FA. subst.
    hexploit CSTR_TL_PROP; eauto. i. des.
    eapply Forall3_nth3 in CONS_EVENTS; eauto. des. subst.
    ss. clarify.
    esplits; eauto.
  }
  intro IH.
  pfold.
  econs 2; eauto.
Qed.
