From Ordinal Require Import Ordinal Arithmetic.
From Paco Require Import paco.
From ITree Require Import ITree.

Require Import Streams List ZArith Lia.

Require Import sflib.
Require Import StdlibExt.

Require Import Axioms.
Require Import SysSem.
Require Import MSteps.

(* Require Import FMSim. *)

Set Nested Proofs Allowed.

(* General version of multi-step sim *)




Section EQUIV_EXEC.
  Context {E: Type -> Type}.

  Inductive _local_equiv_exec
            (leqv: lexec_t E -> lexec_t E -> Prop)
            (* (lexec_src lexec_tgt: lexec_t E) : Prop := *)
    : lexec_t E -> lexec_t E -> Prop :=
    LocalEquivExec
      lexec_src lexec_tgt
      ltr_src lexec_src'
      ltr_tgt lexec_tgt'
      (SAPP_SRC: stream_app ltr_src lexec_src' = lexec_src)
      (SAPP_TGT: stream_app ltr_tgt lexec_tgt' = lexec_tgt)
      (TR_POS_SRC: 0 < length ltr_src)
      (TR_POS_TGT: 0 < length ltr_tgt)
      (LTRS_EQV: tes_equiv ltr_src ltr_tgt)
      (LEQV_NEXT: leqv lexec_src' lexec_tgt')
    : _local_equiv_exec leqv lexec_src lexec_tgt.


  Hint Constructors _local_equiv_exec: paco.

  Lemma local_equiv_exec_monotone
    : monotone2 _local_equiv_exec.
  Proof. pmonauto. Qed.

  Hint Resolve local_equiv_exec_monotone: paco.

  Definition local_equiv_exec
    : lexec_t E -> lexec_t E -> Prop :=
    paco2 _local_equiv_exec bot2.

  Lemma local_equiv_exec_sym
    : forall lex1 lex2
        (LEQV: local_equiv_exec lex1 lex2),
      local_equiv_exec lex2 lex1.
  Proof.
    pcofix CIH. i.
    punfold LEQV. inv LEQV. pclearbot.
    pfold.
    symmetry in LTRS_EQV.
    econs; try apply LTRS_EQV; eauto.
  Qed.

  Lemma colist_eq_div A
        (l1: list A)
        (c1' c2: colist A)
        (CEQ: colist_eq (colist_app l1 c1') c2)
    : exists c2',
      <<C2_DIV: c2 = colist_app l1 c2'>> /\
      <<CEQ': colist_eq c1' c2'>>.
  Proof.
    depgen c2.
    induction l1 as [| h1 t1 IH]; i; ss.
    { exists c2. ss. }

    punfold CEQ.
    inv CEQ.
    pclearbot.
    hexploit IH; eauto. i. des.
    subst.
    exists c2'. esplits; eauto.
  Qed.


  Lemma local_exec_beh_colist_eq
    : forall lex (lbeh1 lbeh2: lbehav_t E)
        (CEQ: colist_eq lbeh1 lbeh2)
        (LEX_BEH: local_exec_behav lex lbeh1),
      local_exec_behav lex lbeh2.
  Proof.
    pcofix CIH.
    i.
    punfold LEX_BEH. inv LEX_BEH.
    - punfold CEQ.
      inv CEQ.
      pfold. econs 1. ss.
    - pclearbot.
      apply colist_eq_div in CEQ. des. subst.
      pfold. econs 2; eauto.
  Qed.


  Lemma local_equiv_exec_false_aux
        ts e es lex1
    : forall n,
      (fun n =>
         forall lex2 tr_tau,
           length tr_tau = n ->
           inftau_lexec lex2 ->
           local_equiv_exec (stream_app tr_tau (Cons (ts, e :: es) lex1)) lex2 -> False) n.
  Proof.
    apply nat_strong_ind.
    intros m SIH.
    intros lex2 tr_tau LEN LEX2_TAU LEQV.
    punfold LEQV.

    remember (stream_app tr_tau (Cons (ts, e :: es) lex1))
      as sapp eqn: SAPP.
    guardH SAPP.
    inv LEQV.
    pclearbot.

    apply inftau_lexec_pref_iff in LEX2_TAU. des.
    apply stream_app_3ways in SAPP. des.
    - subst lexec_src'.
      eapply SIH; eauto.
      subst tr_tau.
      rewrite app_length.
      unfold events in *.
      nia.
    - destruct l1r; ss.
      { nia. }
      clarify.
      apply silent_tes_equiv in LTRS_EQV; eauto.
      r in LTRS_EQV.
      apply Forall_app_inv in LTRS_EQV. des.
      inv LTRS_EQV0. ss.
    - subst ltr_src.
      hexploit (SIH 0); eauto.
      { instantiate (1:= []). ss. }
      ss. subst lexec_src'. ss.
  Qed.

  Lemma Forall_stream_ind_aux' A
        (r: stream A -> Prop)
        (P: A -> Prop)
        l s
        (P_L: Forall P l)
        (R_S: r s)
    : (length l = 0 /\ r s) \/
      (0 < length l /\
       paco1 (_Forall_stream P) r (stream_app l s)).
  Proof.
    induction l as [| h t IH]; i; ss.
    { left. ss. }
    right.
    split.
    { nia. }

    inv P_L.
    pfold. econs; eauto.
    hexploit IH; eauto.
    i. des.
    { destruct t; ss. right. ss. }
    { left. eauto. }
  Qed.

  Lemma Forall_stream_ind_aux A
        (r: stream A -> Prop)
        (P: A -> Prop)
        l s
        (P_L: Forall P l)
        (R_S: r s)
        (L_POS: 0 < length l)
    : paco1 (_Forall_stream P) r (stream_app l s).
  Proof.
    hexploit Forall_stream_ind_aux'; eauto.
    i. des; ss.
    nia.
  Qed.


  Lemma local_exec_behav_inftau
    : forall lex1 lex2
        (LEQV: local_equiv_exec lex1 lex2)
        (INFTAU1: inftau_lexec lex1),
      inftau_lexec lex2.
  Proof.
    pcofix CIH. i.
    punfold LEQV. inv LEQV. pclearbot.
    eapply inftau_lexec_pref_iff in INFTAU1. des.
    apply Forall_stream_ind_aux; eauto.
    eapply silent_tes_equiv; eauto.
    unfold tes_equiv. ss.
  Qed.

  Lemma local_exec_behav_div_until_tr
    : forall lex1 lex2 tr_x lex_x
        (LEQV: local_equiv_exec lex1 lex2)
        (INFTAU1: lex1 = stream_app tr_x lex_x),
      exists tr1 tr2 lex1' lex2' tr1',
        lex1 = stream_app tr1 lex1' /\
        lex2 = stream_app tr2 lex2' /\
        tes_equiv tr1 tr2 /\
        tr1 = tr_x ++ tr1' /\
        local_equiv_exec lex1' lex2'.
  Proof.
    cut(forall n,
           (fun n =>
              forall lex1 lex2 tr_x lex_x
                (LEN_TR_X: length tr_x = n)
                (LEQV: local_equiv_exec lex1 lex2)
                (INFTAU1: lex1 = stream_app tr_x lex_x),
              exists tr1 tr2 lex1' lex2' tr1',
                lex1 = stream_app tr1 lex1' /\
                lex2 = stream_app tr2 lex2' /\
                tes_equiv tr1 tr2 /\
                tr1 = tr_x ++ tr1' /\
                local_equiv_exec lex1' lex2') n).
    { i. eauto. }
    apply nat_strong_ind.
    i.
    destruct m as [| m'].
    { destruct tr_x; ss. subst.
      exists [], [].
      esplits; ss.
    }

    punfold LEQV. inv LEQV.
    pclearbot.

    eapply stream_app_3ways in SAPP_SRC. des.
    - subst tr_x.
      rewrite app_length in LEN_TR_X.
      hexploit (IH (length l2r)); eauto.
      { nia. }
      i. des. subst.

      rewrite stream_app_assoc.

      exists (ltr_src ++ l2r ++ tr1'), (ltr_tgt ++ tr2).
      esplits; eauto.
      { rewrite stream_app_assoc.
        f_equal.
        eauto. }
      { rewrite stream_app_assoc. ss. }
      { unfold tes_equiv in *.
        repeat rewrite flatten_tes_app in *.
        congruence. }
      { rewrite app_assoc. ss. }
    - exists ltr_src, ltr_tgt, lexec_src', lexec_tgt'.
      subst.
      esplits; eauto.
      rewrite stream_app_assoc. ss.
    - exists ltr_src, ltr_tgt, lexec_src', lexec_tgt'.
      subst.
      esplits; eauto.
      rewrite app_nil_r. ss.
  Qed.


  Lemma local_exec_behav_div_cases
        lex1 lex2
        (LEQV: local_equiv_exec lex1 lex2)
    : (<<INFTAU1: inftau_lexec lex1>> /\
       <<INFTAU2: inftau_lexec lex2>>) \/
      <<TR_POS_EX: exists tr1 tr2 lex1' lex2',
        <<DIV_LEX1: lex1 = stream_app tr1 lex1'>> /\
        <<DIV_LEX2: lex2 = stream_app tr2 lex2'>> /\
        <<TR_EQV: tes_equiv tr1 tr2>> /\
        <<FLATTEN_POS: 0 < length (flatten_tes tr1)>> /\
        <<EQV': local_equiv_exec lex1' lex2'>> >>.
  Proof.
    hexploit (exec_div_ex _ lex1). intros [ox1 OX1].

    destruct ox1 as [[[[tr_tau1 lex1'] ts1] es1]|].
    - right. r.
      destruct OX1 as [? [TR_TAU1 ES1]].
      replace (stream_app tr_tau1 (Cons (ts1, es1) lex1'))
        with (stream_app (tr_tau1 ++ [(ts1, es1)]) lex1') in *.
      2: { rewrite stream_app_assoc. ss. }

      hexploit local_exec_behav_div_until_tr; eauto. i. des.
      esplits; eauto.
      subst tr1.
      repeat rewrite flatten_tes_app.
      repeat rewrite app_length.
      cut (0 < length (flatten_tes [(ts1, es1)])).
      { nia. }
      destruct es1; ss.
      nia.
    - left. esplits; ss.
      eapply local_exec_behav_inftau; eauto.
  Qed.

  Lemma colist_eq_tr'
        (r: colist _ -> colist _ -> Prop)
        fb (beh1 beh2: lbehav_t E)
        (CEQ: r beh1 beh2)
    : (length fb = 0 /\ r beh1 beh2) \/
      (length fb <> 0 /\
       paco2 _colist_eq r
             (colist_app fb beh1)
             (colist_app fb beh2)).
  Proof.
    induction fb as [| h t IH]; ss.
    { left. eauto. }
    right. split; ss.
    pfold. econs.
    destruct t.
    - right. ss.
    - left.
      des; ss.
  Qed.

  Lemma colist_eq_tr
        (r: colist _ -> colist _ -> Prop)
        fb (beh1 beh2: lbehav_t E)
        (CEQ: r beh1 beh2)
        (FB_POS: length fb <> 0)
    : paco2 _colist_eq r
            (colist_app fb beh1)
            (colist_app fb beh2).
  Proof.
    hexploit (colist_eq_tr' r fb); eauto.
    i. des; ss.
  Qed.


  Lemma local_equiv_exec_lbeh_eq
    : forall lex1 lex2 beh
        (EQV: local_equiv_exec lex1 lex2)
        (LEX_BEH: local_exec_behav lex2 beh)
    ,
      local_exec_behav lex1 beh.
  Proof.
    cut (forall lex1 lex2 beh
           (EQV: local_equiv_exec lex1 lex2)
           (LEX_BEH: local_exec_behav lex2 beh)
          ,
            exists beh',
              colist_eq beh' beh /\
              local_exec_behav lex1 beh').
    { intro AUX. i.
      hexploit AUX; eauto. i. des.
      eapply local_exec_beh_colist_eq; eauto.
    }

    i.
    hexploit (local_exec_behav_ex _ lex1); eauto.
    destruct 1 as [beh1 LEX_BEH1].
    exists beh1.
    split; ss.

    depgen lex1. depgen lex2.
    revert beh1 beh.
    pcofix CIH. i.

    hexploit local_exec_behav_div_cases; eauto.
    i. des.
    - punfold LEX_BEH.
      inv LEX_BEH.
      2: { exfalso.
           eapply inftau_lexec_pref_iff in INFTAU2. des.
           punfold INFTAU. inv INFTAU; ss. }
      punfold LEX_BEH1.
      inv LEX_BEH1.
      2: { exfalso.
           eapply inftau_lexec_pref_iff in INFTAU1. des.
           punfold INFTAU. inv INFTAU; ss. }
      pfold. econs 1.
    - hexploit local_exec_beh_div; try apply DIV_LEX1; eauto.
      i. des.
      renames beh' BEH_DIV EBEH' into
              beh1' BEH_DIV1 EBEH1'.
      hexploit local_exec_beh_div; try apply DIV_LEX2; eauto.
      i. des.
      renames beh' BEH_DIV EBEH' into
              beh2' BEH_DIV2 EBEH2'.
      subst.
      rewrite TR_EQV.

      apply colist_eq_tr.
      2: { rewrite <- TR_EQV. nia. }
      eauto.
  Qed.


  Inductive _equiv_exec
            (eqv: exec_t E -> exec_t E -> Prop)
    : exec_t E -> exec_t E -> Prop :=
    EquivExec
      exec_src exec_tgt
      n_src tr_src exec_src'
      n_tgt tr_tgt exec_tgt'
      (SAPP_EACH_SRC: sapp_each_rel tr_src exec_src' exec_src)
      (SAPP_EACH_TGT: sapp_each_rel tr_tgt exec_tgt' exec_tgt)

      (TRS_EQV: Forall2 tes_equiv tr_src tr_tgt)
      (TR_SRC_LEN: Forall (fun ltr => length ltr = n_src) tr_src)
      (TR_TGT_LEN: Forall (fun ltr => length ltr = n_tgt) tr_tgt)
      (TR_SRC_POS: 0 < n_src)
      (TR_TGT_POS: 0 < n_tgt)

      (EQV_NEXT: eqv exec_src' exec_tgt')
    : _equiv_exec eqv exec_src exec_tgt.

  Hint Constructors _equiv_exec: paco.

  Lemma equiv_exec_monotone
    : monotone2 _equiv_exec.
  Proof. pmonauto. Qed.

  Hint Resolve equiv_exec_monotone: paco.

  Definition equiv_exec: exec_t E -> exec_t E -> Prop :=
    paco2 _equiv_exec bot2.

  Lemma equiv_exec_length_eq
    : forall ex1 ex2
        (EQV: equiv_exec ex1 ex2),
      length ex1 = length ex2.
  Proof.
    i. punfold EQV. inv EQV.
    apply Forall3_length in SAPP_EACH_SRC.
    apply Forall3_length in SAPP_EACH_TGT.
    apply Forall2_length in TRS_EQV.
    des.
    unfold lexec_t, events in *.
    nia.
  Qed.

  Lemma equiv_exec_global_local
        ex1 ex2
        (EQV: equiv_exec ex1 ex2)
    : Forall2 local_equiv_exec ex1 ex2.
  Proof.
    apply Forall2_nth'.
    split.
    { apply equiv_exec_length_eq. ss. }
    i.
    revert ex1 ex2 EQV a b NTH_A NTH_B.
    pcofix CIH. i.

    punfold EQV. inv EQV. pclearbot.
    eapply Forall3_nth3 in SAPP_EACH_SRC; eauto.
    des.
    renames e1 e2 into tr_src_n exec_src_n'.
    renames NTH1 NTH2 into TR_SRC_N EXEC_SRC_N'.
    eapply Forall3_nth3 in SAPP_EACH_TGT; eauto.
    des.
    renames e1 e2 into tr_tgt_n exec_tgt_n'.
    renames NTH1 NTH2 into TR_TGT_N EXEC_TGT_N'.
    subst.
    eapply Forall2_nth in TRS_EQV.
    rewrite TR_SRC_N in TRS_EQV.
    rewrite TR_TGT_N in TRS_EQV.
    inv TRS_EQV.

    eapply Forall_nth in TR_SRC_LEN.
    rewrite TR_SRC_N in TR_SRC_LEN. ss.
    eapply Forall_nth in TR_TGT_LEN.
    rewrite TR_TGT_N in TR_TGT_LEN. ss.

    pfold. econs; eauto; nia.
  Qed.


  Lemma equiv_exec_beh_eq
    : forall exec1 exec2 beh
        (EQV_EXEC: equiv_exec exec1 exec2)
        (BEH: exec_behav exec2 beh)
    , exec_behav exec1 beh.
  Proof.
    i.
    r in BEH. r.
    eapply equiv_exec_global_local in EQV_EXEC.
    apply Forall2_nth'.
    split.
    { apply Forall2_length in EQV_EXEC.
      apply Forall2_length in BEH.
      nia. }

    i. eapply Forall2_nth1 in EQV_EXEC; eauto. des.
    eapply Forall2_nth1 in BEH; eauto. des.
    clarify.
    eapply local_equiv_exec_lbeh_eq; eauto.
  Qed.

End EQUIV_EXEC.





Section GMSIM.
  Context {E: Type -> Type}.
  Variable sys_src sys_tgt: @DSys.t E.

  Inductive _gmsim_states
            (sim: Ord.t ->
                  (list (list (Z * events E)))? ->
                  DSys.state sys_src ->
                  DSys.state sys_tgt -> Prop)
            (ord: Ord.t)
            (otr_accum: (list (list (Z * events E)))? )
            (st_src: DSys.state sys_src)
            (st_tgt: DSys.state sys_tgt)
    : Prop :=
    GMSimStates
      (SAFE_TGT: exists tr st',
          DSys.step sys_tgt st_tgt tr st')
      (STEPS_SIM: forall tr_tgt_r st_tgt'
                    tr_tgt tr_accum'
                    (STEP_TGT: DSys.step sys_tgt st_tgt
                                         tr_tgt_r st_tgt')
                    (FILTER_NB: DSys.filter_nb_sysstep
                                  tr_tgt_r = Some tr_tgt)
                    (APP_EVENTS:
                       match otr_accum with
                       | None =>
                         tr_accum' = map (fun x => [x]) tr_tgt
                       | Some tr_accum =>
                         snoc_each_rel
                           tr_accum tr_tgt tr_accum'
                       end)
        ,
          ((* stutter *)
            exists ord',
              <<ORD_LT: Ord.lt ord' ord>> /\
              <<NEXT: sim ord' (Some tr_accum') st_src st_tgt' >>) \/
          ((* src step *)
            exists n_src tr_src st_src' ord',
              <<MSTEPS_SRC: msteps sys_src n_src st_src tr_src st_src'>> /\
              <<SCNT_SRC_POS: 0 < n_src>> /\
              <<TRS_EQV: Forall2 tes_equiv tr_src tr_accum' >> /\
              <<NEXT: sim ord' None st_src' st_tgt'>>
          ))
  .

  Hint Constructors _gmsim_states: paco.

  Lemma gmsim_states_monotone: monotone4 _gmsim_states.
  Proof.
    ii. inv IN. econs; eauto.
    i. hexploit STEPS_SIM; eauto. i. des.
    - left. esplits; eauto.
    - right. esplits; eauto.
  Qed.

  Hint Resolve gmsim_states_monotone: paco.

  Definition gmsim_states
    : Ord.t -> (list (list (Z * events E)))? ->
      sys_src.(DSys.state) -> sys_tgt.(DSys.state) -> Prop :=
    paco4 _gmsim_states bot4.

  Inductive gmsim: Prop :=
    GMSim
      (TGT_INIT_OK: exists st_tgt_i1, sys_tgt.(DSys.initial_state) st_tgt_i1)
      (SIM_INIT_STATES:
         forall st_tgt_i
           (INIT_TGT: sys_tgt.(DSys.initial_state) st_tgt_i),
         exists st_src_i ord_i,
           <<INIT_SRC: sys_src.(DSys.initial_state) st_src_i>> /\
           <<SIM_STATES: gmsim_states
                           ord_i None
                           st_src_i st_tgt_i>>)
  .

  Lemma gmsim_states_tgt_ind
        ord
    : forall st_src
        scnt1 (st_tgt0: DSys.state sys_tgt) tr1 st_tgt1 exec1
        (MSTEPS1: msteps _ scnt1 st_tgt0 tr1 st_tgt1)
        (SIM: gmsim_states ord (Some tr1) st_src st_tgt1)
        (SCNT1_POS: 0 < scnt1)
        (EXEC_ST1: DSys.exec_state _ st_tgt1 exec1)
    , exists scnt2 tr2 st_tgt2 tr_tgt exec2
        scnt_src tr_src st_src' ord'
    ,
      <<MSTEPS2: msteps _ scnt2 st_tgt1 tr2 st_tgt2>> /\
      <<MSTEPS_SRC: msteps _ scnt_src st_src tr_src st_src'>> /\
      <<SCNT_SRC_POS: 0 < scnt_src>> /\
      <<SAPP_TR_TGT: app_each_rel tr1 tr2 tr_tgt>> /\
      <<TRS_EQV: Forall2 tes_equiv tr_src tr_tgt>> /\
      <<EXEC_ST2: DSys.exec_state _ st_tgt2 exec2>> /\
      <<EXEC_DIV: sapp_each_rel tr2 exec2 exec1>> /\
      <<SIM_NEXT: gmsim_states ord' None
                               st_src' st_tgt2>>
  .
  Proof.
    pattern ord.
    revert ord.
    apply (well_founded_induction Ord.lt_well_founded).
    intros ord IH. i.

    punfold SIM. inv SIM.
    punfold EXEC_ST1. inv EXEC_ST1.
    { exfalso. ss. }
    renames es es_sysE st' into
    tr_tgt_step_raw tr_tgt_step st_tgt_step.
    renames exec' STEP into exec_step STEP_TGT.
    renames FILTER_NOBEH BEH_CONS EXEC_REST into
        FLT_TR_STEP EXEC1_DIV EXEC_ST_STEP.
    pclearbot.

    assert (exists tr_accum',
               <<MSTEPS_TGT_PAST':
                 msteps sys_tgt (S scnt1)
                        st_tgt0 tr_accum' st_tgt_step>> /\
               <<TR_ACCUM: snoc_each_rel tr1 tr_tgt_step tr_accum'>>).
    { hexploit msteps_concat.
      { eapply MSTEPS1. }
      { econs 2.
        { eauto. }
        { eauto. }
        { econs 1; eauto. }
        eapply cons_each_to_nils.

        apply DSys_filter_nb_sysstep_inv in FLT_TR_STEP.
        apply Forall2_length in FLT_TR_STEP.
        eapply DSys.step_prsv_num_sites in STEP_TGT.
        des. nia.
      }
      replace (scnt1 + 1) with (S scnt1) by nia.
      i. des.
      esplits; eauto.
      eapply snoc_each_tolist2. eauto.
    }
    des.

    hexploit STEPS_SIM; eauto. i. des.
    - r in NEXT.
      des.
      2: { exfalso. ss. }

      rename ord' into ord1.
      hexploit IH; eauto. i. des.

      assert (exists tr_tgt_past,
                 <<TR_TGT_PAST: cons_each_rel tr_tgt_step tr2 tr_tgt_past>> /\
                 <<TR_TGT_TOT: app_each_rel tr1 tr_tgt_past tr_tgt>>).
      { exists (cons_each tr_tgt_step tr2).
        assert (REL: cons_each_rel tr_tgt_step tr2
                                   (cons_each tr_tgt_step tr2)).
        { apply cons_each_impl_rel.
          apply DSys_filter_nb_sysstep_inv in FLT_TR_STEP.
          apply Forall2_length in FLT_TR_STEP.
          eapply DSys.step_prsv_num_sites in STEP_TGT.
          eapply msteps_num_sites_eq in MSTEPS2.
          des. nia.
        }

        esplits; ss.

        clear - REL TR_ACCUM SAPP_TR_TGT.

        apply Forall3_nth'.
        splits.
        { eapply Forall3_length in TR_ACCUM, SAPP_TR_TGT, REL.
          des; ss. nia. }
        { eapply Forall3_length in TR_ACCUM, SAPP_TR_TGT, REL.
          des; ss. nia. }

        i.
        eapply Forall3_nth3 in REL; eauto. des.
        clarify.
        renames e1 NTH1 into tr_tgt_step_n TR_TGT_STEP_N.
        renames e2 NTH2 into tr2_n TR2_N.

        eapply Forall3_nth2 in TR_ACCUM; eauto. i. des.
        clarify.
        renames NTH1 NTH3 into TR1_N TR_ACCCUM'_N.

        eapply Forall3_nth2 in SAPP_TR_TGT; eauto. i. des.
        clarify.
        rewrite <- app_assoc. ss.
      }
      des.

      exists (S scnt2), tr_tgt_past, st_tgt2, tr_tgt, exec2.
      esplits; eauto.
      + econs; eauto.
      + apply Forall3_nth'.
        splits.
        { eapply Forall3_length in TR_TGT_PAST, EXEC1_DIV, EXEC_DIV.
          des. nia. }
        { eapply Forall3_length in TR_TGT_PAST, EXEC1_DIV, EXEC_DIV.
          des. nia. }
        i.
        clear - TR_TGT_PAST EXEC1_DIV EXEC_DIV
                            NTH_A NTH_B NTH_C.
        eapply Forall3_nth3 in EXEC1_DIV; eauto. des.
        eapply Forall3_nth3 in EXEC_DIV; eauto. des.
        eapply Forall3_nth1 in TR_TGT_PAST; eauto. des.
        clarify.

    - r in NEXT. des; ss.
      esplits; eauto.
      + econs 2; eauto.
        { econs 1; eauto. }
        instantiate (1:= map (fun x => [x]) tr_tgt_step).

        apply cons_each_to_nils.
        eapply Forall3_length in EXEC1_DIV. des.
        apply exec_state_len in EXEC_ST_STEP. ss.
        rewrite EXEC1_DIV.
        rewrite <- EXEC_ST_STEP. ss.
      + apply snoc_each_tolist2. ss.
      + eapply Cons_each_tolist1; eauto.
  Qed.

  Record _gmsim_auxdata : Type :=
    GMSimAuxdata {
        aux_tr_h_src : list (tsp * events E) ;
        aux_tr_t_src : list (list (tsp * events E)) ;
        aux_st_src_nxt : DSys.state sys_src ;

        aux_tr_h_tgt : list (tsp * events E) ;
        aux_tr_t_tgt : list (list (tsp * events E)) ;
        aux_st_tgt_nxt : DSys.state sys_tgt ;
        aux_exec_tgt_nxt: @exec_t E;
        aux_ord: Ord.t ;

        AUX_EXEC_TGT_NXT: DSys.exec_state _ aux_st_tgt_nxt aux_exec_tgt_nxt ;
        AUX_GMSIM_NXT: gmsim_states
                         aux_ord None
                         aux_st_src_nxt aux_st_tgt_nxt ;
      }.

  Definition gmsim_states_ex
             ord st_src st_tgt exec_tgt
             (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt)
             (GMSIM: gmsim_states ord None st_src st_tgt)
    : exists ord' n_src tr_h_src_raw tr_h_src st_src1
        tr_t_src tr_src st_src'
        n_tgt tr_h_tgt_raw tr_h_tgt st_tgt1
        tr_t_tgt tr_tgt st_tgt' exec_tgt',
      DSys.step _ st_src tr_h_src_raw st_src1 /\
      DSys.filter_nb_sysstep tr_h_src_raw = Some tr_h_src /\
      msteps _ n_src st_src1 tr_t_src st_src' /\

      DSys.step _ st_tgt tr_h_tgt_raw st_tgt1 /\
      DSys.filter_nb_sysstep tr_h_tgt_raw = Some tr_h_tgt /\
      msteps _ n_tgt st_tgt1 tr_t_tgt st_tgt' /\

      cons_each_rel tr_h_src tr_t_src tr_src /\
      cons_each_rel tr_h_tgt tr_t_tgt tr_tgt /\
      Forall2 tes_equiv tr_src tr_tgt /\
      Forall3 (fun a b c => stream_app a b = c)
              tr_tgt exec_tgt' exec_tgt /\

      (* DSys.safe_state st_tgt' /\ *)
      DSys.exec_state _ st_tgt' exec_tgt' /\
      gmsim_states ord' None st_src' st_tgt'
  .
  Proof.
    punfold GMSIM. inv GMSIM.
    punfold EXEC_TGT. inv EXEC_TGT.
    { exfalso. eauto. }
    pclearbot.

    hexploit STEPS_SIM; eauto. i. des.
    - (* stutter *)
      r in NEXT. des.
      2: { exfalso. ss. }

      hexploit gmsim_states_tgt_ind; eauto.
      { econs; eauto.
        { econs 1; eauto. }
        apply Forall3_nth'.
        rewrite repeat_length.
        rewrite map_length.

        splits; ss.
        { eapply DSys.step_prsv_num_sites in STEP. des.
          apply exec_state_len in EXEC_REST.
          apply Forall3_length in BEH_CONS. des.
          rewrite BEH_CONS.
          ss.
        }

        i.
        apply repeat_spec_nth in NTH_B.
        apply map_nth_error_iff in NTH_C.
        des; ss. subst. clarify.
      }
      i. des.
      destruct scnt_src as [| scnt_src'].
      { exfalso. nia. }
      replace (S scnt_src') with (1 + scnt_src') in MSTEPS_SRC by nia.
      apply msteps_split in MSTEPS_SRC. des.

      inv MSTEPS1.
      inv MSTEPS_REST.

      esplits; eauto.
      + apply Forall3_nth'.
        splits.
        { apply Forall3_length in CONS_EVENTS.
          apply Forall3_length in ES_DIV.
          rewrite repeat_length in CONS_EVENTS.
          des. nia. }
        { apply Forall3_length in CONS_EVENTS.
          apply Forall3_length in ES_DIV.
          rewrite repeat_length in CONS_EVENTS.
          des. nia. }
        i.
        eapply Forall3_nth1 in CONS_EVENTS; eauto. des.
        subst.
        eapply repeat_spec_nth in NTH2. subst.
        rename NTH3 into ES1_N.
        eapply Forall3_nth2 in ES_DIV; eauto. des.
        subst. clarify.
      + apply Forall3_nth' in SAPP_TR_TGT.
        rewrite map_length in SAPP_TR_TGT.
        destruct SAPP_TR_TGT as [LEN1 [LEN2 AUX]].
        apply Forall3_nth'.
        splits; ss.
        i.
        hexploit AUX; eauto.
        { apply map_nth_error_iff.
          esplits; eauto. }
        ss.
      + apply Forall3_nth'.
        splits.
        { apply Forall3_length in SAPP_TR_TGT.
          apply Forall3_length in EXEC_DIV.
          des. nia. }
        { apply Forall3_length in SAPP_TR_TGT.
          apply Forall3_length in EXEC_DIV.
          apply Forall3_length in BEH_CONS.
          des. nia. }
        i.
        eapply Forall3_nth3 in SAPP_TR_TGT; eauto. des.
        subst.
        rewrite map_nth_error_iff in NTH1. des. subst.
        renames e2 NTH1 NTH2 into tr2_n ES_SYSE_N TR2_N. ss.

        eapply Forall3_nth1 in EXEC_DIV; eauto. des.
        clarify.
        renames NTH2 NTH3 into EXEC'_N EXEC2_N.

        eapply Forall3_nth3 in BEH_CONS; eauto. des.
        r in P_FA. subst.
        clarify.

    - destruct n_src as [| scnt_src'].
      { exfalso. nia. }
      replace (S scnt_src') with (1 + scnt_src') in MSTEPS_SRC by nia.
      apply msteps_split in MSTEPS_SRC. des.

      inv MSTEPS1.
      inv MSTEPS_REST.

      r in NEXT. des.
      2: { exfalso. ss. }

      esplits.
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { econs 1; eauto. }
      { instantiate (1:= tr_src).
        apply Forall3_nth'.
        splits; ss.
        { apply Forall3_length in ES_DIV.
          apply Forall3_length in CONS_EVENTS.
          nia. }
        { apply Forall3_length in ES_DIV.
          apply Forall3_length in CONS_EVENTS.
          nia. }
        i.
        eapply Forall3_nth2 in ES_DIV; eauto. des.
        subst. clarify.
        renames e1 NTH1 NTH3 into es1_n ES1_N TR_SRC_N.
        eapply Forall3_nth1 in CONS_EVENTS; eauto. des.
        clarify.
        apply repeat_spec_nth in NTH2. subst. ss.
      }
      { instantiate (1:= map (fun x => [x]) es_sysE).
        apply Forall3_nth'.
        rewrite repeat_length. rewrite map_length.
        splits; ss.
        { eapply DSys.step_prsv_num_sites in STEP. des.
          apply exec_state_len in EXEC_REST.
          apply Forall3_length in BEH_CONS. des.
          rewrite BEH_CONS.
          ss. }
        i.
        apply repeat_spec_nth in NTH_B. subst.
        apply map_nth_error_iff in NTH_C. des; ss.
        clarify.
      }
      { eauto. }
      { instantiate (1:= exec').
        apply Forall3_nth'.
        rewrite map_length.
        splits.
        { apply Forall3_length in BEH_CONS. des. nia. }
        { apply Forall3_length in BEH_CONS. des. nia. }
        i.
        rewrite map_nth_error_iff in NTH_A. des. clarify. s.
        eapply Forall3_nth in BEH_CONS.
        rewrite NTH_A, NTH_B, NTH_C in BEH_CONS.
        inv BEH_CONS. ss.
      }
      { eauto. }
      { eauto. }
  Qed.

  Definition gmsim_states_sig
        ord st_src st_tgt exec_tgt
        (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt)
        (GMSIM: gmsim_states ord None st_src st_tgt)
    : { aux: _gmsim_auxdata |
        exists n_src tr_h_src_raw st_src1 tr_src
          n_tgt tr_h_tgt_raw st_tgt1 tr_tgt,
      <<AUX_STEP1_SRC: DSys.step _ st_src tr_h_src_raw st_src1>> /\
      <<AUX_FLT1_SRC: DSys.filter_nb_sysstep tr_h_src_raw = Some (aux_tr_h_src aux)>> /\
      <<AUX_STEPS_SRC: msteps _ n_src st_src1 (aux_tr_t_src aux) (aux_st_src_nxt aux)>> /\

      <<AUX_STEP1_TGT: DSys.step _ st_tgt tr_h_tgt_raw st_tgt1>> /\
      <<AUX_FLT1_TGT: DSys.filter_nb_sysstep tr_h_tgt_raw = Some (aux_tr_h_tgt aux)>> /\
      <<AUX_STEPS_TGT: msteps _ n_tgt st_tgt1 (aux_tr_t_tgt aux) (aux_st_tgt_nxt aux)>> /\

      <<TR_SRC: cons_each_rel (aux_tr_h_src aux) (aux_tr_t_src aux) tr_src>> /\
      <<TR_TGT: cons_each_rel (aux_tr_h_tgt aux) (aux_tr_t_tgt aux) tr_tgt>> /\
      <<TRC_EQV: Forall2 tes_equiv tr_src tr_tgt>> /\
      <<EXEC_TGT_NXT:
        Forall3 (fun a b c => stream_app a b = c)
                tr_tgt (aux_exec_tgt_nxt aux) exec_tgt>>
      }.
  Proof.
    hexploit gmsim_states_ex; eauto.
    intro EX.

    pose (CID := constructive_indefinite_description).
    eapply CID in EX. destruct EX as [ord' EX].
    eapply CID in EX. destruct EX as [ns_src EX].
    eapply CID in EX. destruct EX as [tr_h_src_raw EX].
    eapply CID in EX. destruct EX as [tr_h_src EX].
    eapply CID in EX. destruct EX as [st_src1 EX].
    eapply CID in EX. destruct EX as [tr_t_src EX].
    eapply CID in EX. destruct EX as [tr_src EX].
    eapply CID in EX. destruct EX as [st_src' EX].
    eapply CID in EX. destruct EX as [n_tgt EX].
    eapply CID in EX. destruct EX as [tr_h_tgt_raw EX].
    eapply CID in EX. destruct EX as [tr_h_tgt EX].
    eapply CID in EX. destruct EX as [st_tgt1 EX].
    eapply CID in EX. destruct EX as [tr_t_tgt EX].
    eapply CID in EX. destruct EX as [tr_tgt EX].
    eapply CID in EX. destruct EX as [st_tgt' EX].
    eapply CID in EX. destruct EX as [exec_tgt' EX].
    des.

    eexists (GMSimAuxdata _ _ _ _ _ _ _ _ _ _).
    esplits; eauto.
    Unshelve.
    - eauto.
    - eauto.
    - eauto.
  Qed.

  CoFixpoint constr_local_exec_src
        ord st_src st_tgt exec_tgt
        (* (SAFE: DSys.safe_state st_tgt) *)
        (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt)
        (GMSIM: gmsim_states ord None st_src st_tgt)
        (n: nat) (cont: list (tsp * events E))
    : @lexec_t E.
  Proof.
    destruct cont as [| h t].
    2: { exact (Cons h (constr_local_exec_src
                          _ _ _ _ EXEC_TGT GMSIM n t)). }

    pose (C := proj1_sig (gmsim_states_sig
                            _ _ _ _ EXEC_TGT GMSIM)).
    econs.
    { exact (nth n (aux_tr_h_src C) (0%Z, [])). }
    { exact (constr_local_exec_src
               _ _ _ _
               (AUX_EXEC_TGT_NXT C)
               (AUX_GMSIM_NXT C) n
               (nth n (aux_tr_t_src C) [])).
    }
  Defined.

  Definition constr_exec_src
        ord st_src st_tgt exec_tgt
        (* (SAFE: DSys.safe_state st_tgt) *)
        (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt)
        (GMSIM: gmsim_states ord None st_src st_tgt)
    : @exec_t E :=
    imap (fun n _ => constr_local_exec_src
                    _ _ _ _ EXEC_TGT GMSIM n [])
         0 (List.repeat tt (DSys.num_sites _ st_src)).

  Lemma constr_exec_src_length
        ord st_src st_tgt exec_tgt
        (* (SAFE: DSys.safe_state st_tgt) *)
        (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt)
        (GMSIM: gmsim_states ord None st_src st_tgt)
    : length (constr_exec_src _ _ _ _ EXEC_TGT GMSIM) =
      DSys.num_sites _ st_src.
  Proof.
    unfold constr_exec_src.
    rewrite imap_length.
    rewrite repeat_length. ss.
  Qed.

  Lemma constr_local_exec_src_app_cont
        n ord es st_src st_tgt exec_tgt
        (* (SAFE: DSys.safe_state st_tgt) *)
        (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt)
        (GMSIM: gmsim_states ord None st_src st_tgt)
    : constr_local_exec_src
        _ _ _ _ EXEC_TGT GMSIM n es =
      stream_app es
                 (constr_local_exec_src
                    _ _ _ _ EXEC_TGT GMSIM n []).
  Proof.
    induction es as [| h t IH]; ss.
    match goal with
    | |- ?c = _ => rewrite (unfold_Stream c)
    end.
    ss. f_equal. ss.
  Qed.


  Lemma constr_exec_src_des_aux
        ord st_src st_tgt exec_tgt
        (* (SAFE: DSys.safe_state st_tgt) *)
        (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt)
        (GMSIM: gmsim_states ord None st_src st_tgt)
    : exists ord' n_src tr_h_src_raw tr_h_src st_src1
        tr_t_src tr_src st_src'
        n_tgt tr_h_tgt_raw tr_h_tgt st_tgt1
        tr_t_tgt tr_tgt st_tgt' exec_tgt'
        (* (SAFE': DSys.safe_state st_tgt') *)
        (EXEC_TGT': DSys.exec_state _ st_tgt' exec_tgt')
        (GMSIM': gmsim_states ord' None st_src' st_tgt')
    ,
      <<STEP1_SRC: DSys.step _ st_src tr_h_src_raw st_src1>> /\
      <<FLT1_SRC: DSys.filter_nb_sysstep tr_h_src_raw = Some tr_h_src>> /\
      <<STEPS_SRC: msteps _ n_src st_src1 tr_t_src st_src'>> /\

      <<STEP1_TGT: DSys.step _ st_tgt tr_h_tgt_raw st_tgt1>> /\
      <<FLT1_TGT: DSys.filter_nb_sysstep tr_h_tgt_raw = Some tr_h_tgt>> /\
      <<STEPS_TGT: msteps _ n_tgt st_tgt1 tr_t_tgt st_tgt'>> /\

      <<TR_SRC_DIV: cons_each_rel tr_h_src tr_t_src tr_src>> /\
      <<TR_TGT_DIV: cons_each_rel tr_h_tgt tr_t_tgt tr_tgt>> /\
      <<TES_EQUIV: Forall2 tes_equiv tr_src tr_tgt>> /\
      <<EXEC_TGT_DIV: Forall3 (fun a b c => stream_app a b = c)
                              tr_tgt exec_tgt' exec_tgt>> /\

      <<CONSTR_SRC_DIV:
        Forall3 (fun a b c => stream_app a b = c)
                tr_src
                (constr_exec_src _ _ _ _ EXEC_TGT' GMSIM')
                (constr_exec_src _ _ _ _ EXEC_TGT GMSIM)>>
  .
  Proof.
    destruct (gmsim_states_sig
                _ _ _ _ EXEC_TGT GMSIM) as [aux P] eqn: CONSTR.
    des.
    assert (AUX: proj1_sig (gmsim_states_sig
                              _ _ _ _ EXEC_TGT GMSIM) = aux).
    { rewrite CONSTR. ss. }
    clear CONSTR.

    esplits; eauto.
    instantiate (1:= AUX_GMSIM_NXT aux).
    instantiate (1:= AUX_EXEC_TGT_NXT aux).

    match goal with
    | |- Forall3 _ _ ?c' ?c =>
      pose (cstr' := c'); pose (cstr := c)
    end.
    fold cstr' cstr.

    apply Forall3_nth. i.

    (* for lengths *)
    assert (LEN_C': length cstr' = DSys.num_sites _ (aux_st_src_nxt aux)).
    { subst cstr'.
      apply constr_exec_src_length. }
    assert (LEN_C: length cstr = DSys.num_sites _ st_src).
    { subst cstr.
      apply constr_exec_src_length. }
    hexploit msteps_num_sites_eq; try apply AUX_STEPS_SRC.
    i. des.
    hexploit (DSys.step_prsv_num_sites sys_src).
    { apply AUX_STEP1_SRC. }
    i. des.
    hexploit Forall3_length; try apply TR_SRC. i. des.

    destruct (lt_ge_dec n (length tr_src)).
    2: {
      rewrite nth_error_None2 by ss.
      rewrite nth_error_None2.
      2: { unfold lexec_t in *. nia. }
      rewrite nth_error_None2.
      2: { unfold lexec_t in *. nia. }
      econs.
    }

    hexploit (nth_error_Some2 _ tr_src n); ss. i. des.
    renames e1 NTH_EX into src_n SRC_N.
    unfold constr_exec_src in *.
    rewrite SRC_N.

    subst cstr'.
    rewrite imap_nth_error_iff. ss.
    rewrite repeat_nth_error_Some.
    2: { unfold lexec_t in *. nia. }
    ss.
    subst cstr.
    rewrite imap_nth_error_iff. ss.
    rewrite repeat_nth_error_Some.
    2: { unfold lexec_t in *. nia. }
    ss.

    eapply Forall3_nth3 in TR_SRC; eauto. des. subst.
    econs. ss.
    match goal with
    | |- _ = ?c => rewrite (unfold_Stream c)
    end.
    ss.
    f_equal.
    - erewrite nth_error_nth; eauto.
    - erewrite nth_error_nth; eauto.
      symmetry.
      apply constr_local_exec_src_app_cont.
  Qed.

  Lemma constr_exec_src_des
        ord
        st_src st_tgt exec_tgt
        (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt)
        (GMSIM: gmsim_states ord None
                           st_src st_tgt)
    : exists tr_src tr_tgt
        n_src n_tgt
        ord' st_src' st_tgt' exec_tgt'
        (EXEC_TGT': DSys.exec_state _ st_tgt' exec_tgt')
        (GMSIM': gmsim_states ord' None st_src' st_tgt')
    ,
      <<SRC_DIV:
        sapp_each_rel tr_src
                      (constr_exec_src _ _ _ _ EXEC_TGT' GMSIM')
                      (constr_exec_src _ _ _ _ EXEC_TGT GMSIM)>>
      /\
      <<EXEC_TGT_DIV: sapp_each_rel tr_tgt exec_tgt' exec_tgt>> /\
      <<TES_EQV: Forall2 tes_equiv tr_src tr_tgt>> /\
      <<TR_LEN_SRC: Forall (fun tr' => length tr' = n_src) tr_src>> /\
      <<TR_LEN_TGT: Forall (fun tr' => length tr' = n_tgt) tr_tgt>> /\
      <<N_SRC_POS: 0 < n_src>> /\
      <<N_TGT_POS: 0 < n_tgt>>.
  Proof.
    hexploit (constr_exec_src_des_aux
                _ _ _ _ EXEC_TGT GMSIM); eauto.
    i. des.

    exists tr_src, tr_tgt.
    exists (1 + n_src), (1 + n_tgt).
    exists ord'.
    exists st_src', st_tgt'.
    exists exec_tgt'. exists EXEC_TGT', GMSIM'.
    esplits; eauto.
    - eapply Forall_forall.
      intros x IN.
      apply In_nth_error in IN. des.
      eapply Forall3_nth3 in TR_SRC_DIV; eauto.
      des. subst. ss.

      eapply msteps_trace_row_length in STEPS_SRC.
      rewrite Forall_nth in STEPS_SRC.
      specialize (STEPS_SRC n).
      rewrite NTH2 in STEPS_SRC. ss.
      nia.
    - eapply Forall_forall.
      intros x IN.
      apply In_nth_error in IN. des.
      eapply Forall3_nth3 in TR_TGT_DIV; eauto.
      des. subst. ss.

      eapply msteps_trace_row_length in STEPS_TGT.
      rewrite Forall_nth in STEPS_TGT.
      specialize (STEPS_TGT n).
      rewrite NTH2 in STEPS_TGT. ss.
      nia.
    - nia.
    - nia.
  Qed.

  Lemma gmsim_exec_eqv
    : forall st_src st_tgt
        ord
        exec_tgt
        (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt)
        (GMSIM: gmsim_states ord None st_src st_tgt)
    ,
      equiv_exec (constr_exec_src
                    _ _ _ _ EXEC_TGT GMSIM)
                 exec_tgt.
  Proof.
    pcofix CIH. i.
    hexploit (constr_exec_src_des _ _ _ _ EXEC_TGT GMSIM).
    i. des.
    pfold. econs; eauto.
  Qed.

  Lemma gmsim_exec_state_src
    : forall ord st_src st_tgt
        exec_tgt
        (EXEC_TGT : DSys.exec_state sys_tgt st_tgt exec_tgt)
        (GMSIM : gmsim_states ord None st_src st_tgt)
        (* (BEH_TGT : exec_behav exec_tgt beh) *),
      DSys.exec_state _ st_src
                      (constr_exec_src
                         _ _ _ _ EXEC_TGT GMSIM).
  Proof.
    pcofix CIH. i. pfold.
    hexploit (constr_exec_src_des_aux _ _ _ _ EXEC_TGT GMSIM).
    i. des.

    pose (cstr := constr_exec_src _ _ _ _ EXEC_TGT GMSIM).
    pose (cstr' := constr_exec_src _ _ _ _ EXEC_TGT' GMSIM').
    fold cstr.

    assert (AUX: forall n (N_UB: n < length cstr'),
               exists lexec',
                 (fun n lexec' =>
                    exists tr_t_src_n cstr'_n,
                      <<TR_T_SRC: nth_error tr_t_src n = Some tr_t_src_n>> /\
                      <<CSTR'_N: nth_error cstr' n = Some cstr'_n>> /\
                      <<LEXEC'_EQ: lexec' = stream_app tr_t_src_n cstr'_n>>)
                   n lexec').
    { fold cstr cstr' in CONSTR_SRC_DIV.
      i. hexploit (nth_error_Some2 _ cstr' n); ss. i. des.
      renames e1 NTH_EX into c'_n C'_N.

      eapply Forall3_nth2 in CONSTR_SRC_DIV; eauto. i. des.
      eapply Forall3_nth3 in TR_SRC_DIV; eauto. i. des.
      clarify.
      esplits; eauto.
    }

    apply exists_list in AUX. des.
    renames l LIST_LEN NTH_PROP into
            cstr_tl CSTR_TL_LEN CSTR_TL_PROP.

    econs 2.
    { eauto. }
    { eauto. }
    { instantiate (1:= cstr_tl).
      r. apply Forall3_nth. i.
      destruct (lt_ge_dec n (length cstr_tl)).
      2: {
        assert (length cstr' = DSys.num_sites _ st_src').
        { subst cstr'.
          apply constr_exec_src_length. }
        assert (length cstr = DSys.num_sites _ st_src).
        { subst cstr.
          apply constr_exec_src_length. }

        hexploit msteps_num_sites_eq; try apply STEPS_SRC.
        i. des.
        apply Forall3_length in TR_SRC_DIV. des.
        eapply DSys.step_prsv_num_sites in STEP1_SRC. des.

        rewrite nth_error_None2 by nia.
        rewrite nth_error_None2 by ss.
        rewrite nth_error_None2.
        2: { fold (@lexec_t E) in *. nia. }
        econs. }

      hexploit (nth_error_Some2 _ cstr_tl n).
      { ss. }
      i. des. renames e1 NTH_EX into cstr_tl_n CSTR_TL_N.
      rewrite CSTR_TL_N.
      hexploit CSTR_TL_PROP; eauto. i. des.
      r in TR_SRC_DIV.
      hexploit Forall3_nth2; try apply TR_SRC_DIV; eauto.
      i. des.
      renames e1 e3 into tr_h_src_n tr_src_n.
      renames NTH1 NTH3 P_FA into TR_HS_N TR_N TR_CONS.

      rewrite TR_HS_N.

      fold cstr cstr' in CONSTR_SRC_DIV.
      eapply Forall3_nth1 in CONSTR_SRC_DIV; eauto.
      des.
      renames e2 e3 into cstr'_n_tmp cstr_n.
      renames NTH2 NTH3 P_FA into CSTR'_N_TMP CSTR_N CSTR_N_DIV.

      fold (lexec_t E) in *.
      rewrite CSTR'_N in CSTR'_N_TMP.
      symmetry in CSTR'_N_TMP. inv CSTR'_N_TMP.
      rewrite CSTR_N.

      econs. ss.
    }

    eapply (msteps_src_tl_aux sys_src) with (cstr':= cstr'); eauto.
    subst cstr'.
    rewrite constr_exec_src_length.
    apply msteps_num_sites_eq in STEPS_SRC. des. ss.
  Qed.


  Lemma gmsim_state_adequacy
        ord st_src st_tgt
        (GMSIM: gmsim_states ord None st_src st_tgt)
    : DSys.behav_state _ st_tgt <1= DSys.behav_state _ st_src.
  Proof.
    intros beh BEH_TGT.
    r in BEH_TGT. des.
    renames exec EXEC_ST EXEC_BEH into exec_tgt EXEC_TGT BEH_TGT.
    r. exists (constr_exec_src _ _ _ _ EXEC_TGT GMSIM).
    splits.
    - apply gmsim_exec_state_src.
    - eapply equiv_exec_beh_eq; eauto.
      apply gmsim_exec_eqv.
  Qed.


  Lemma gmsim_adequacy
        (GMSIM: gmsim)
    : DSys.behav_sys sys_tgt <1= DSys.behav_sys sys_src.
  Proof.
    intros beh BEH_SYS_TGT.
    inv GMSIM.

    red in BEH_SYS_TGT. desH BEH_SYS_TGT.
    { exfalso. eauto. }
    (* clear dependent st_i. *)
    clear TGT_INIT_OK.

    econs 2.
    hexploit SIM_INIT_STATES; eauto. i. des.
    hexploit gmsim_state_adequacy; eauto.
  Qed.

  Lemma gmsim_states_append_silent_prefix_src_Some
    : forall ord tr st_src st_tgt
        st_src_p scnt_p tr_p
        (GMSIM: gmsim_states ord (Some tr) st_src st_tgt)
        (MSTEPS_PREF: msteps _ scnt_p st_src_p tr_p st_src)
        (SILENT_PREF: Forall (@silent_local_trace _) tr_p)
    , gmsim_states ord (Some tr) st_src_p st_tgt.
  Proof.
    intro ord.
    pattern ord.
    revert ord.
    apply (well_founded_induction Ord.lt_well_founded).
    intros ord IH. i.

    punfold GMSIM. inv GMSIM.
    pfold. econs; eauto.
    i. hexploit STEPS_SIM; eauto.
    i. des.
    2: {
      right.
      hexploit msteps_concat.
      { eapply MSTEPS_PREF. }
      { eauto. }
      i. des.
      esplits; eauto.
      { nia. }
      apply Forall2_nth'.
      split.
      { eapply Forall3_length in ES_CONCAT. des.
        apply Forall2_length in TRS_EQV.
        congruence.
      }

      intros n es_n tr_tgt_n' ES_N TR_TGT_N.
      eapply Forall3_nth3 in ES_CONCAT; eauto.
      des. clarify.
      renames e1 NTH1 into tr_p_n TR_P_N.
      renames e2 NTH2 into tr_src_n TR_SRC_N.

      eapply Forall2_nth1 in TRS_EQV; eauto. des.
      clarify.
      renames NTH2 P_FA into TR_TGT_N TR_EQV2.

      unfold tes_equiv in *.
      rewrite flatten_tes_app.
      rewrite <- TR_EQV2.

      cut (flatten_tes tr_p_n = []).
      { intro R. rewrite R. ss. }

      apply flatten_silent_local_trace_iff.
      rewrite Forall_forall in SILENT_PREF.
      apply SILENT_PREF.
      eapply nth_error_In; eauto.
    }

    pclearbot.
    hexploit IH; eauto. intro GMSIM'.
    left. exists ord'.
    splits; eauto.
  Qed.


  Lemma gmsim_states_append_silent_prefix_src
        ord st_src st_tgt
        st_src_p scnt_p tr_p
        (GMSIM: gmsim_states ord None st_src st_tgt)
        (MSTEPS_PREF: msteps _ scnt_p st_src_p tr_p st_src)
        (SILENT_PREF: Forall (@silent_local_trace _) tr_p)
    : gmsim_states ord None st_src_p st_tgt.
  Proof.
    punfold GMSIM.
    inv GMSIM.

    pfold.
    econs; eauto.

    i. hexploit STEPS_SIM; eauto.
    i. des.
    2: {
      right.
      hexploit msteps_concat.
      { eapply MSTEPS_PREF. }
      { eauto. }
      i. des.
      esplits; eauto.
      { nia. }
      apply Forall2_nth'.
      split.
      { eapply Forall3_length in ES_CONCAT. des.
        subst tr_accum'.
        rewrite map_length.
        apply Forall2_length in TRS_EQV.
        rewrite map_length in TRS_EQV.
        congruence.
      }

      subst tr_accum'.
      intros n es_n tr_tgt_n' ES_N TR_TGT_N.
      apply map_nth_error_iff in TR_TGT_N. des. clarify.
      destruct a as [tr_tgt_n1 tr_tgt_n2].

      eapply Forall3_nth3 in ES_CONCAT; eauto.
      des. clarify.
      renames e1 NTH1 into tr_p_n TR_P_N.
      renames e2 NTH2 into tr_src_n TR_SRC_N.

      eapply Forall2_nth1 in TRS_EQV; eauto. des.
      eapply map_nth_error_iff in NTH2. des. subst.
      clarify.
      renames NTH2 P_FA into TR_TGT_N TR_EQV2.

      unfold tes_equiv in *.
      rewrite flatten_tes_app.
      rewrite <- TR_EQV2.

      cut (flatten_tes tr_p_n = []).
      { intro R. rewrite R. ss. }

      apply flatten_silent_local_trace_iff.
      rewrite Forall_forall in SILENT_PREF.
      apply SILENT_PREF.
      eapply nth_error_In; eauto.
    }

    left.
    pclearbot.
    hexploit gmsim_states_append_silent_prefix_src_Some; eauto.
    i.
    exists ord'.
    esplits; eauto.
  Qed.

End GMSIM.
