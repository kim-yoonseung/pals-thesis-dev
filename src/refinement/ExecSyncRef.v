From ITree Require Import ITree Eq EqAxiom.
From compcert Require Coqlib.
From Paco Require Import paco.
From Ordinal Require Import Ordinal Arithmetic.

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
Require Import GMSim.

Require Import SyncExecRef.

(* move some lemmas in this to StdlibExt *)
Require Import CompcertLemmas.

Set Nested Proofs Allowed.

Import ITreeNotations.
Import ExecutableSpec.



Lemma sub_mod_divide
      p n
      (P_POS: 0 < p)
  : Nat.divide p (n - n mod p).
Proof.
  r.
  hexploit (Nat.div_mod n p).
  { nia. }
  intro N_EQ.
  exists (n / p).
  rewrite N_EQ at 1.
  nia.
Qed.

Section PROOF.
  Context {sysE: Type -> Type}.
  Context {msgT: Set}.
  Context `{EventRetInhabit sysE}.

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

  Let sys_src := SyncSys.as_dsys
                   sync_sys (* (tm_init + max_clock_skew). *)
                   tm_init.

  Let sys_tgt := ExecutableSpec.as_dsys exec_sys (Z.of_nat tm_init) None.

  Let ord_prd : Ord.t :=
    (* (10 + (Ord.omega + 5) * num_tasks)%ord. *)
    (5 + (Ord.omega + 5) * num_tasks + 5)%ord.

  Lemma gmsim_red_idx
        (r: _ -> _ -> _ -> _ -> Prop)
        ord2
    : forall ord1
        otr_acc st_src st_tgt
        (ORD_LE: (ord1 <= ord2)%ord)
        (SIM_LESS: paco4 (_gmsim_states sys_src sys_tgt) r
                         ord1 otr_acc st_src st_tgt)
    , paco4 (_gmsim_states sys_src sys_tgt)
            r ord2 otr_acc st_src st_tgt.
  Proof.
    pattern ord2. revert ord2.
    apply (well_founded_induction Ord.lt_well_founded).
    intros ord IH. i.

    punfold SIM_LESS.
    2: { apply gmsim_states_monotone. }
    inv SIM_LESS.

    pfold. econs.
    { eauto. }
    i. hexploit STEPS_SIM; eauto. i. des.
    2: { right. esplits; eauto. }

    r in NEXT. des; ss.
    2: { left. esplits; eauto.
         eapply Ord.lt_le_lt; eauto. }
    left. exists ord'.
    esplits; eauto.
    eapply Ord.lt_le_lt; eauto.
  Qed.

  Lemma sync_sys_msteps_nosync_exists
        n tm lsts st sytm
        (STATE: st = SyncSys.State tm lsts)
        (SYNC_TIME: Nat.divide period sytm)
        (AFTER_SYNC: sytm < tm)
        (BEFORE_NXT_SYNC: tm + n <= sytm + period)
    : exists tr st',
      <<MSTEPS_NOSYNC: msteps sys_src n st tr st'>> /\
      <<TRACE_NILS: Forall (Forall (fun tes => snd tes = [])) tr>> /\
      <<STATE': st' = SyncSys.State (tm + n) lsts>>.
  Proof.
    assert (MSTEPS_EX: exists tr st',
               msteps sys_src n st tr st').
    { depgen st. depgen tm.
      induction n as [| n' IH]; i; ss.
      { esplits; eauto.
        econs; eauto. }

      subst.
      assert (MSTEPS1: exists tr1,
                 msteps sys_src 1
                        (SyncSys.State tm lsts)
                        tr1 (SyncSys.State (S tm) lsts)).
      { esplits.
        econs; ss.
        3: { econs; eauto. }
        - econs 1; eauto.
          eapply in_btw_cant_divide; eauto.
          nia.
        - unfold DSys.filter_nb_sysstep.
          instantiate (1:= repeat (Z.of_nat tm, []) (length lsts)).
          apply deopt_list_Some_iff.
          do 2 rewrite map_repeat. ss.
        - ss.
          unfold SyncSys.num_sites. ss.
          eapply cons_each_impl_rel.
          do 2 rewrite repeat_length. ss.
      }
      des.
      hexploit (IH (S tm)); eauto.
      { nia. }
      intros (tr2 & st2 & MSTEPS2).

      hexploit msteps_concat.
      { apply MSTEPS1. }
      { apply MSTEPS2. }
      i. des.
      esplits; eauto.
    }
    des.
    pose proof MSTEPS_EX as MSTEPS_EX'.
    eapply sync_sys_msteps_nosync_impl in MSTEPS_EX; eauto.
  Qed.

  Lemma sync_msteps_exists
        tm lsts tr_r outs lsts1
        tr1 lsts'
        (TM_LB: period <= tm)
        (TM_SYNC: Nat.divide period tm)
        (LEN_LSTS: length lsts = num_tasks)
        (STEPS: Forall4 (SNode.step sntz_msg num_tasks mcasts tm)
                        lsts tr_r outs lsts1)
        (FLT: DSys.filter_nb_sysstep
                (map (fun es => (Z.of_nat tm, es)) tr_r) =
              Some tr1)
        (ACCEPT_MSGS: List.map (SNode.accept_msgs outs) lsts1 = lsts')
        (* (TRACE: cons_each_rel tr1  *)
        (*    tr = tolist_each tr1) *)
    : exists tr,
      Forall2 tes_equiv (tolist_each tr1) tr /\
      msteps sys_src period
             (SyncSys.State tm lsts) tr
             (SyncSys.State (tm + period) lsts').
  Proof.
    assert (SCNT: exists scnt, scnt = period).
    { esplits; eauto. }
    des. guardH SCNT.
    rewrite <- SCNT.

    destruct scnt as [| scnt'].
    { exfalso. unguard. nia. }

    hexploit sync_sys_msteps_nosync_exists; eauto.
    { instantiate (1:= scnt').
      unguard. nia. }
    instantiate (1:= lsts').
    i. des. subst.

    exists (cons_each tr1 tr).
    assert (LEN_TRS_EQ: length tr1 = length tr).
    { apply DSys_filter_nb_sysstep_inv in FLT.
      apply Forall2_length in FLT.
      rewrite map_length in FLT.
      apply Forall4_length in STEPS. des; ss.
      rewrite <- FLT.
      apply msteps_num_sites_eq in MSTEPS_NOSYNC. ss.
      unfold SyncSys.num_sites in MSTEPS_NOSYNC. ss.
      rewrite map_length in MSTEPS_NOSYNC.
      des; ss.
      congruence.
    }
    hexploit cons_each_impl_rel; eauto.
    intro CONS_EACH_REL.

    splits.
    { apply Forall2_nth'.
      split.
      { unfold tolist_each.
        rewrite map_length.
        apply Forall3_length in CONS_EACH_REL.
        des; ss. }

      unfold tolist_each. i.
      eapply Forall3_nth3 in CONS_EACH_REL; eauto.
      des. subst.
      apply map_nth_error_iff in NTH_A. des. clarify.
      r.
      rewrite (rw_cons_app _ a0 e2).
      rewrite flatten_tes_app.

      cut (flatten_tes e2 = []).
      { intro R. rewrite R.
        rewrite app_nil_r. ss. }
      apply flatten_silent_local_trace_iff.
      r.
      rewrite Forall_forall in TRACE_NILS.
      apply TRACE_NILS.
      eapply nth_error_In; eauto.
    }

    econs; eauto.
    - ss.
      econs 2; eauto.
      rewrite LEN_LSTS.
      eauto.
    - replace (tm + S scnt') with (S tm + scnt') by nia.
      eauto.
  Qed.


  Lemma sim_run_with_fuel
        (r: _ -> _ -> _ -> _ -> Prop)
        k (ord': Ord.t)
        (app: AppMod.t)
        tm tid inb tr_acc_p
        lsts_src1 lst_src lsts_src2 ast
        (LST_SRC: lst_src = SNode.State tid (ITrSNode.to_snode app) inb (Some (Ret ast)))
        (REST:
           forall (oitr': (itree _ _)?) oast'
             outb es_src_r tr_src
             tr_acc_c tr_acc_c_n tr_acc_tot
             (ISTAR: SNode.istar sntz_msg num_tasks mcasts
                                 (ITrSNode.to_snode app)
                                 (AppMod.job_itree app (Z.of_nat tm) inb ast,
                                  repeat None num_tasks)
                                 es_src_r (oitr', outb))
             (PRD_END: option_map (fun ast => Ret ast) oast' = oitr')
             (FLT_SRC: DSys.filter_nb_localstep (Z.of_nat tm, es_src_r) =
                       Some tr_src)
             (TR_EQV: tes_equiv [tr_src] tr_acc_c_n)
             (TR_ACC_N: nth_error tr_acc_c tid = Some tr_acc_c_n)
             (TR_ACC_OTHER:
                forall tid' tr_acc_c_n'
                  (TID_NEQ: tid' <> tid)
                  (NTH': nth_error tr_acc_c tid' = Some tr_acc_c_n')
                ,
                  silent_local_trace _ tr_acc_c_n')
             (TR_ACC_TOT: app_each_rel tr_acc_p tr_acc_c
                                       tr_acc_tot)
           ,
             paco4 (_gmsim_states sys_src sys_tgt) r
                   (ord' + 1)%ord
                   (Some tr_acc_tot)
                   (SyncSys.State
                      tm (lsts_src1 ++ lst_src :: lsts_src2))
                   (Z.of_nat tm,
                    k ({| app_mod := app;
                          app_state := oast' |}, outb)))
    : forall (fuel: nat)
        tr_acc tr_acc_n tr_acc_tot
        es_src1_r itr outb tr_src1
        (TID_UBND: tid < num_tasks)
        (LEN1: length lsts_src1 = tid)
        (ISTAR: SNode.istar sntz_msg num_tasks mcasts
                            (ITrSNode.to_snode app)
                            (AppMod.job_itree app (Z.of_nat tm) inb ast,
                             repeat None num_tasks)
                            es_src1_r (Some itr, outb))
        (FLT_SRC: DSys.filter_nb_localstep (Z.of_nat tm, es_src1_r) =
                  Some tr_src1)
        (TR_EQV: tes_equiv [tr_src1] tr_acc_n)
        (TR_ACC_N: nth_error tr_acc tid = Some tr_acc_n)
        (TR_ACC_OTHER:
           forall tid' tr_acc_n'
             (TID_NEQ: tid' <> tid)
             (NTH': nth_error tr_acc tid' = Some tr_acc_n')
           ,
             silent_local_trace _ tr_acc_n')
        (TR_ACC_TOT: app_each_rel tr_acc_p tr_acc
                                  tr_acc_tot)

      , paco4 (_gmsim_states sys_src sys_tgt) r
              (ord' + (1 + fuel))%ord
              (Some tr_acc_tot)
              (SyncSys.State
                 tm (lsts_src1 ++ lst_src :: lsts_src2))
              (Z.of_nat tm,
               `x : (_)? * list msgT? <-
                    run_with_fuel
                      num_tasks mcasts sntz_msg
                      app (length lsts_src1) fuel outb
                      itr ;;
               y <- (let (oast', out) := x in
                    Ret ({| app_mod := app;
                            app_state := oast' |}, out));;
               k y).
  Proof.
    induction fuel as [| fuel' IH]; i; ss.
    { simpl_itree_goal.
      simpl_itree_goal.
      apply gmsim_red_idx with (ord1:= (ord' + 1)%ord).
      { apply OrdArith.le_add_r.
        setoid_rewrite OrdArith.add_O_r.
        reflexivity. }

      eapply REST.
      { eapply SNode.istar_snoc_fail; eauto. }
      { ss. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
    }

    destruct (observe itr) eqn: OBS_ITR.
    - (* RET *)
      simpl_itree_goal.
      simpl_itree_goal.

      apply gmsim_red_idx with (ord1:= (ord' + 1)%ord).
      { apply OrdArith.le_add_r.
        setoid_rewrite <- OrdArith.add_O_r at 1.
        apply OrdArith.le_add_r.
        apply Ord.O_bot. }

      eapply REST.
      { eauto. }
      { ss.
        rewrite (itree_eta_ itr).
        rewrite <- OBS_ITR. ss. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
    - (* Tau *)
      simpl_itree_goal.

      pfold. econs.
      { ss. esplits.
        econs 2; ss. }

      i. left.
      exists (ord' + (1 + fuel'))%ord.
      esplits.
      { apply OrdArith.lt_add_r.
        apply OrdArith.lt_add_r.
        apply Ord.S_lt. }

      left.
      inv STEP_TGT; ss.
      clarify.
      assert (TR_TGT_EQ: tr_tgt = repeat (Z.of_nat tm, []) num_tasks).
      { apply DSys_filter_nb_sysstep_inv in FILTER_NB.
        apply nth_eq_list_eq'.
        { rewrite repeat_length.
          apply Forall2_length in FILTER_NB.
          rewrite repeat_length in FILTER_NB.
          nia. }
        i. apply repeat_spec_nth in NTH2. subst.
        renames a NTH1 into tr_tgt_n TR_TGT_N.
        eapply Forall2_nth2 in FILTER_NB; eauto. des.
        apply repeat_spec_nth in NTH1. subst.
        unfold DSys.filter_nb_localstep in P_FA.
        ss. clarify.
      }

      assert (exists tr_acc_new,
                 <<TR_ACC_NEW:
                   snoc_each_rel tr_acc tr_tgt tr_acc_new>>).
      { hexploit (Forall_app_ex _ tr_acc (tolist_each tr_tgt)).
        { unfold tolist_each.
          rewrite map_length.
          subst tr_tgt. rewrite repeat_length.
          apply Forall3_length in APP_EVENTS.
          apply Forall3_length in TR_ACC_TOT.
          rewrite repeat_length in APP_EVENTS.
          des. nia. }
        intros [ls LS].

        exists ls.
        apply snoc_each_tolist2. ss.
      }
      des.

      assert (exists tr_acc_new_n,
                 nth_error tr_acc_new (length lsts_src1) = Some tr_acc_new_n /\
                 tes_equiv [tr_src1] tr_acc_new_n).
      { hexploit (nth_error_Some2 _ tr_acc_new (length lsts_src1)).
        { apply Forall3_length in TR_ACC_NEW.
          subst tr_tgt.
          rewrite repeat_length in TR_ACC_NEW.
          des. nia. }
        i. des.
        esplits; eauto.
        eapply tes_equiv_trans; eauto.
        r.
        eapply Forall3_nth3 in TR_ACC_NEW; eauto.
        i. des. subst.
        apply repeat_spec_nth in NTH2. subst.
        rewrite flatten_tes_app.
        clarify.
        unfold flatten_tes. ss.
        rewrite app_nil_r. ss.
      }
      des.

      eapply IH.
      { nia. }
      { ss. }
      { instantiate (1:= es_src1_r).
        replace es_src1_r with (es_src1_r ++ []).
        2: { apply app_nil_r. }
        eapply SNode.istar_app.
        - eauto.
        - econs 3.
          { econs 1. ss.
            econs; eauto. }
          { eauto. }
          { econs 2. }
          { ss. }
      }
      { eauto. }
      { eauto. }
      { eauto. }
      { i.
        eapply Forall3_nth3 in TR_ACC_NEW; eauto. des.
        subst.
        eapply repeat_spec_nth in NTH2. subst.
        hexploit TR_ACC_OTHER; eauto. i.
        apply Forall_app; eauto.
      }
      { apply Forall3_nth'.
        splits.
        { apply Forall3_length in TR_ACC_NEW.
          apply Forall3_length in TR_ACC_TOT.
          des. nia. }
        { apply Forall3_length in TR_ACC_NEW.
          apply Forall3_length in TR_ACC_TOT.
          apply Forall3_length in APP_EVENTS.
          des. nia. }

        intro m. i.
        eapply Forall3_nth1 in TR_ACC_TOT; eauto. des.
        subst.
        renames e2 NTH2 NTH3 into tr_acc_m TR_ACC_M TR_ACC_TOT_M.
        eapply Forall3_nth1 in APP_EVENTS; eauto. des.
        subst.
        apply repeat_spec_nth in NTH2. subst.
        clarify.
        eapply Forall3_nth3 in TR_ACC_NEW; eauto. des.
        subst.
        apply repeat_spec_nth in NTH2. subst.
        clarify.
        rewrite app_assoc. ss.
      }
    - (* Vis *)
      simpl_itree_goal.
      destruct e as [sys_e | send_e].
      + (* syse *)
        ss.
        simpl_itree_goal.
        simpl_itree_goal.

        pfold. econs.
        { generalize (event_return_inhabit _ sys_e).
          intros (x & _).
          esplits; ss.
          eapply Step_SystemEvent with (ret:= x); eauto.
          ss. }

        i. left.
        exists (ord' + (1+ fuel'))%ord.
        esplits.
        { apply OrdArith.lt_add_r.
          apply OrdArith.lt_add_r.
          apply Ord.S_lt. }

        left.
        inv STEP_TGT; ss.
        clarify. existT_elim. subst. clear_tt.

        match goal with
        | |- context[ (Z.of_nat tm, ?t) ] =>
          remember t as itr_tmp eqn: ITR
        end.
        symmetry in ITR.
        simpl_itree_hyp ITR.
        subst itr_tmp.

        assert (exists es_src1,
                   tr_src1 = (Z.of_nat tm, es_src1)).
        { apply DSys_filter_nb_localstep_inv in FLT_SRC.
          des. ss.
          destruct tr_src1; ss. subst.
          esplits; eauto. }
        des. subst tr_src1.

        assert (exists tr_acc_new,
                   <<TR_ACC_NEW:
                     snoc_each_rel tr_acc tr_tgt tr_acc_new>>).
        { hexploit (Forall_app_ex _ tr_acc (tolist_each tr_tgt)).
          { unfold tolist_each.
            rewrite map_length.
            apply Forall3_length in APP_EVENTS.
            apply Forall3_length in TR_ACC_TOT.
            des. nia.
          }
          intros [ls LS].

          exists ls.
          apply snoc_each_tolist2. ss.
        }
        des.

        assert (exists tr_acc_new_n,
                   nth_error tr_acc_new (length lsts_src1) = Some tr_acc_new_n /\
                   tes_equiv [(Z.of_nat tm, es_src1 ++ [Event syse ret])] tr_acc_new_n).
        { hexploit (nth_error_Some2 _ tr_acc_new (length lsts_src1)).
          { apply Forall3_length in TR_ACC_NEW.
            eapply DSys_filter_nb_sysstep_inv in FILTER_NB.
            apply Forall2_length in FILTER_NB.
            rewrite replace_nth_length in FILTER_NB.
            rewrite repeat_length in FILTER_NB.
            des. nia. }
          i. des.
          esplits; eauto.
          eapply Forall3_nth3 in TR_ACC_NEW; eauto.
          des. subst. clarify.
          renames e2 NTH1 NTH2 into tr_tgt_n TR_ACC_N TR_TGT_N.

          eapply DSys_filter_nb_sysstep_inv in FILTER_NB.
          eapply Forall2_nth2 in FILTER_NB; eauto.
          i. des.

          rewrite replace_nth_gss in NTH1.
          2: { rewrite repeat_length. nia. }
          clarify.

          r.
          rewrite flatten_tes_app.
          rewrite <- TR_EQV.
          apply DSys_filter_nb_localstep_inv in P_FA.
          des; ss.
          destruct tr_tgt_n as [? ?]. ss.
          inv FILTERED_NB_EACH.
          match goal with
          | H: Forall2 _ [] _ |- _ => inv H
          end.
          ss. clarify.
          unf_resum.
          unfold flatten_tes. ss.
          do 2 rewrite app_nil_r.
          unfold flatten_te. ss.
          rewrite map_app. ss.
        }
        des.

        eapply IH.
        { nia. }
        { ss. }
        { instantiate (1:= es_src1_r ++ [embed (Event syse ret)]).
          eapply SNode.istar_app.
          - eauto.
          - econs 3.
            { econs 2; eauto.
              - econs; eauto.
              - econs; eauto.
            }
            { eauto. }
            { econs 2. }
            { ss. }
        }
        { apply filter_nb_localstep_app; eauto. }
        { s. eauto. }
        { eauto. }
        { i.
          eapply Forall3_nth3 in TR_ACC_NEW; eauto. des.
          subst.
          hexploit TR_ACC_OTHER; eauto. i.
          apply Forall_app; eauto.
          renames NTH1 NTH2 into TR_ACC TR_TGT.

          eapply DSys_filter_nb_sysstep_inv in FILTER_NB.
          eapply Forall2_nth2 in FILTER_NB; eauto.
          des.
          rewrite replace_nth_gso in NTH1 by nia.
          apply repeat_spec_nth in NTH1. subst.
          unfold DSys.filter_nb_localstep in P_FA. ss.
          clarify.
          econs; ss.
        }
        { apply Forall3_nth'.
          splits.
          { apply Forall3_length in TR_ACC_NEW.
            apply Forall3_length in TR_ACC_TOT.
            des. nia. }
          { apply Forall3_length in TR_ACC_NEW.
            apply Forall3_length in TR_ACC_TOT.
            apply Forall3_length in APP_EVENTS.
            des. nia. }

          intro m. i.
          eapply Forall3_nth1 in TR_ACC_TOT; eauto. des.
          subst.
          renames e2 NTH2 NTH3 into tr_acc_m TR_ACC_M TR_ACC_TOT_M.
          eapply Forall3_nth1 in APP_EVENTS; eauto. des.
          subst. clarify.
          eapply Forall3_nth3 in TR_ACC_NEW; eauto. des.
          subst. clarify.
          rewrite app_assoc. ss.
        }
      + (* send *)
        ss.
        destruct send_e.
        simpl_itree_goal.

        pfold. econs.
        { esplits; ss.
          econs 2; eauto. ss. }

        i. left.
        exists (ord' + (1 + fuel'))%ord.
        esplits.
        { apply OrdArith.lt_add_r.
          apply OrdArith.lt_add_r.
          apply Ord.S_lt. }

        left.
        inv STEP_TGT; ss.
        clarify.

        assert (TR_TGT_EQ: tr_tgt = repeat (Z.of_nat tm, []) num_tasks).
        { apply DSys_filter_nb_sysstep_inv in FILTER_NB.
          apply nth_eq_list_eq'.
          { rewrite repeat_length.
            apply Forall2_length in FILTER_NB.
            rewrite repeat_length in FILTER_NB.
            nia. }
          i. apply repeat_spec_nth in NTH2. subst.
          renames a NTH1 into tr_tgt_n TR_TGT_N.
          eapply Forall2_nth2 in FILTER_NB; eauto. des.
          apply repeat_spec_nth in NTH1. subst.
          unfold DSys.filter_nb_localstep in P_FA.
          ss. clarify.
        }

        assert (exists tr_acc_new,
                   <<TR_ACC_NEW:
                     snoc_each_rel tr_acc tr_tgt tr_acc_new>>).
        { hexploit (Forall_app_ex _ tr_acc (tolist_each tr_tgt)).
          { unfold tolist_each.
            rewrite map_length.
            subst tr_tgt. rewrite repeat_length.
            apply Forall3_length in APP_EVENTS.
            apply Forall3_length in TR_ACC_TOT.
            rewrite repeat_length in APP_EVENTS.
            des. nia. }
          intros [ls LS].

          exists ls.
          apply snoc_each_tolist2. ss.
        }
        des.

        assert (exists tr_acc_new_n,
                   nth_error tr_acc_new (length lsts_src1) = Some tr_acc_new_n /\
                   tes_equiv [tr_src1] tr_acc_new_n).
        { hexploit (nth_error_Some2 _ tr_acc_new (length lsts_src1)).
          { apply Forall3_length in TR_ACC_NEW.
            subst tr_tgt.
            rewrite repeat_length in TR_ACC_NEW.
            des. nia. }
          i. des.
          esplits; eauto.
          eapply tes_equiv_trans; eauto.
          r.
          eapply Forall3_nth3 in TR_ACC_NEW; eauto.
          i. des. subst.
          apply repeat_spec_nth in NTH2. subst.
          rewrite flatten_tes_app.
          clarify.
          unfold flatten_tes. ss.
          rewrite app_nil_r. ss.
        }
        des.
        match goal with
        | |- context[ (Z.of_nat tm, ?t) ] =>
          remember t as itr_tmp eqn: ITR
        end.
        symmetry in ITR.
        simpl_itree_hyp ITR.
        subst itr_tmp.

        eapply IH.
        { nia. }
        { ss. }
        { instantiate (1:= es_src1_r).
          replace es_src1_r with (es_src1_r ++ []).
          2: { apply app_nil_r. }
          eapply SNode.istar_app.
          - eauto.
          - econs 3.
            { econs 3; ss.
              - econs; eauto.
              - econs; eauto.
            }
            { eauto. }
            { econs 2. }
            { ss. }
        }
        { eauto. }
        { eauto. }
        { eauto. }
        { i.
          eapply Forall3_nth3 in TR_ACC_NEW; eauto. des.
          subst.
          eapply repeat_spec_nth in NTH2. subst.
          hexploit TR_ACC_OTHER; eauto. i.
          apply Forall_app; eauto.
        }
        { apply Forall3_nth'.
          splits.
          { apply Forall3_length in TR_ACC_NEW.
            apply Forall3_length in TR_ACC_TOT.
            des. nia. }
          { apply Forall3_length in TR_ACC_NEW.
            apply Forall3_length in TR_ACC_TOT.
            apply Forall3_length in APP_EVENTS.
            des. nia. }

          intro m. i.
          eapply Forall3_nth1 in TR_ACC_TOT; eauto. des.
          subst.
          renames e2 NTH2 NTH3 into tr_acc_m TR_ACC_M TR_ACC_TOT_M.
          eapply Forall3_nth1 in APP_EVENTS; eauto. des.
          subst.
          apply repeat_spec_nth in NTH2. subst.
          clarify.
          eapply Forall3_nth3 in TR_ACC_NEW; eauto. des.
          subst.
          apply repeat_spec_nth in NTH2. subst.
          clarify.
          rewrite app_assoc. ss.
        }
  Qed.

  Lemma sim_run_period
        (r: _ -> _ -> _ -> _ -> Prop)
        ord' k tr_tgt1 tm
        lsts_src1 lst_src lsts_src2
        tid inb lst_tgt
        (TID_EQ: length lsts_src1 = tid)
        (TID_UBND: tid < num_tasks)
        (LEN_TR_TGT1: length tr_tgt1 = num_tasks)
        (MATCH: match_loc_state tid inb
                                lst_tgt lst_src)
        (REST: forall lst_src' tr_tgt1' lst_tgt' out
                 tr_tgt_c tr_tgt_c_n
                 tr_src_cr tr_src_c
                 (STEP: SNode.step
                          sntz_msg num_tasks mcasts tm
                          lst_src tr_src_cr out lst_src')
                 (FLT: DSys.filter_nb_localstep
                         (Z.of_nat tm, tr_src_cr) =
                       Some tr_src_c)
                 (TR_TGT_C_N: nth_error tr_tgt_c tid = Some tr_tgt_c_n)
                 (TR_N_EQV: tes_equiv tr_tgt_c_n [tr_src_c])
                 (SILENT_OTHER:
                    forall tid' tr_n'
                      (TID_NEQ: tid' <> tid)
                      (NTH: nth_error tr_tgt_c tid' =
                            Some tr_n'),
                      silent_local_trace _ tr_n')

                 (MATCH_DONE:
                    match_loc_state
                      tid (SNode.init_box num_tasks)
                      lst_tgt' lst_src')
                 (APP_TR_TGT: app_each_rel tr_tgt1 tr_tgt_c tr_tgt1')
          ,
            paco4 (_gmsim_states sys_src sys_tgt) r
                  (ord' + 1)%ord (Some tr_tgt1')
                  (SyncSys.State tm (lsts_src1 ++ lst_src :: lsts_src2))
                  (Z.of_nat tm, k (lst_tgt', out)))
    : paco4 (_gmsim_states sys_src sys_tgt) r
            (ord' + (Ord.omega + 5))%ord
            (Some tr_tgt1)
            (SyncSys.State tm (lsts_src1 ++ lst_src :: lsts_src2))
            (Z.of_nat tm,
             x <- run_period_itree
                   num_tasks mcasts sntz_msg
                   (Z.of_nat tm) tid inb lst_tgt;;
             k x)
  .
  Proof.
    unfold run_period_itree.
    destruct lst_tgt as [app [oast|]].
    2: {
      simpl_itree_goal.
      simpl_itree_goal.

      pfold. econs.
      { esplits; ss.
        eapply Step_RandomEvent with (ret:= true); ss.
      }
      i. left.
      exists (ord' + (Ord.omega + 4))%ord.
      esplits.
      { apply OrdArith.lt_add_r.
        apply OrdArith.lt_add_r.
        apply OrdArith.lt_from_nat. nia.
      }
      left.

      apply gmsim_red_idx with (ord1 := (ord' + 1)%ord).
      { apply OrdArith.le_add_r.
        etransitivity.
        { apply Ord.lt_le.
          apply Ord.omega_upperbound. }
        apply OrdArith.add_base_l.
      }

      inv STEP_TGT; ss.
      clarify.
      existT_elim. subst. clear_tt.
      apply DSys_filter_nb_sysstep_inv in FILTER_NB.
      inv MATCH. existT_elim. subst.

      destruct ret.
      - simpl_itree_goal.
        assert (TR_TGT_N: nth_error (tolist_each tr_tgt) (length lsts_src1) =
                          Some [(Z.of_nat tm, [])]).
        { eapply Forall2_nth1 with (n:=length lsts_src1) in FILTER_NB.
          2: { erewrite repeat_nth_error_Some by nia.
               eauto. }
          des; ss.
          unfold DSys.filter_nb_localstep in P_FA. ss.
          clarify.
          unfold tolist_each.
          apply map_nth_error_iff.
          esplits; eauto.
        }

        eapply REST.
        + s. econs 2; eauto.
          ss. econs; eauto.
        + ss.
        + apply TR_TGT_N.
        + ss.
        + i.
          unfold tolist_each in NTH.
          apply map_nth_error_iff in NTH. des. subst.
          eapply Forall2_nth2 in FILTER_NB; eauto.
          des.
          eapply repeat_spec_nth in NTH1. subst.
          unfold DSys.filter_nb_localstep in P_FA. ss.
          clarify.
          r. econs; ss.
        + econs 1; ss.
        + apply snoc_each_tolist2. ss.
      - simpl_itree_goal.
        assert (TR_TGT_N: nth_error (tolist_each tr_tgt) (length lsts_src1) =
                          Some [(Z.of_nat tm, [])]).
        { eapply Forall2_nth1 with (n:=length lsts_src1) in FILTER_NB.
          2: { erewrite repeat_nth_error_Some by nia.
               eauto. }
          des; ss.
          unfold DSys.filter_nb_localstep in P_FA. ss.
          clarify.
          unfold tolist_each.
          apply map_nth_error_iff.
          esplits; eauto.
        }

        eapply REST.
        + s. econs 1; eauto.
        + ss.
        + apply TR_TGT_N.
        + ss.
        + i.
          unfold tolist_each in NTH.
          apply map_nth_error_iff in NTH. des. subst.
          eapply Forall2_nth2 in FILTER_NB; eauto.
          des.
          eapply repeat_spec_nth in NTH1. subst.
          unfold DSys.filter_nb_localstep in P_FA. ss.
          clarify.
          r. econs; ss.
        + econs 1; ss.
        + apply snoc_each_tolist2. ss.
    }

    simpl_itree_goal.
    simpl_itree_goal.

    pfold. econs.
    { esplits; ss.
      eapply Step_RandomEvent with (ret:= true); ss.
    }
    i. left.
    exists (ord' + (Ord.omega + 4))%ord.
    esplits.
    { apply OrdArith.lt_add_r.
      apply OrdArith.lt_add_r.
      apply OrdArith.lt_from_nat. nia.
    }
    left.

    inv STEP_TGT; ss.
    clarify.
    existT_elim. subst. clear_tt.
    apply DSys_filter_nb_sysstep_inv in FILTER_NB.
    inv MATCH. existT_elim. subst.

    destruct ret.
    2: {
      simpl_itree_goal.

      (* failed *)
      apply gmsim_red_idx with (ord1 := (ord' + 1)%ord).
      { apply OrdArith.le_add_r.
        etransitivity.
        { apply Ord.lt_le.
          apply Ord.omega_upperbound. }
        apply OrdArith.add_base_l.
      }

      assert (TR_TGT_N: nth_error (tolist_each tr_tgt) (length lsts_src1) =
                        Some [(Z.of_nat tm, [])]).
      { eapply Forall2_nth1 with (n:=length lsts_src1) in FILTER_NB.
        2: { erewrite repeat_nth_error_Some by nia.
             eauto. }
        des; ss.
        unfold DSys.filter_nb_localstep in P_FA. ss.
        clarify.
        unfold tolist_each.
        apply map_nth_error_iff.
        esplits; eauto.
      }

      eapply REST.
      + s. econs 3.
        2: { eauto. }
        econs 1.
      + ss.
      + apply TR_TGT_N.
      + ss.
      + i.
        unfold tolist_each in NTH.
        apply map_nth_error_iff in NTH. des. subst.
        eapply Forall2_nth2 in FILTER_NB; eauto.
        des.
        eapply repeat_spec_nth in NTH1. subst.
        unfold DSys.filter_nb_localstep in P_FA. ss.
        clarify.
        r. econs; ss.
      + econs 1; ss.
      + apply snoc_each_tolist2. ss.
    }

    (* fuel *)
    simpl_itree_goal.
    simpl_itree_goal.

    renames tr_tgt tr_accum' into tr_pre1 tr_acc_pre1.
    renames FILTER_NB APP_EVENTS into
            TR_PRE1_SILENT APP_PRE1.

    pfold. econs.
    { esplits; ss.
      eapply Step_RandomEvent with (ret:= O); ss.
    }
    i. left.
    exists (ord' + (Ord.omega + 3))%ord.
    esplits.
    { apply OrdArith.lt_add_r.
      apply OrdArith.lt_add_r.
      apply OrdArith.lt_from_nat. nia.
    }
    left.

    inv STEP_TGT; ss.
    clarify.
    existT_elim. subst. clear_tt.
    apply DSys_filter_nb_sysstep_inv in FILTER_NB.

    renames tr_tgt tr_accum' into tr_pre2 tr_acc_pre2.
    renames FILTER_NB APP_EVENTS into
            TR_PRE2_SILENT APP_PRE2.

    rename ret into fuel.

    match goal with
    | |- context[(Z.of_nat _, ?t)] =>
      remember t as itr eqn: ITR
    end.
    symmetry in ITR.
    simpl_itree_hyp ITR.
    subst itr.

    eapply gmsim_red_idx with (ord1:= (ord' + (1 + fuel))%ord).
    { apply OrdArith.le_add_r.
      etransitivity.
      - instantiate (1:= (Ord.omega)%ord).
        apply Ord.lt_le.
        eapply Ord.le_lt_lt.
        2: { instantiate (1:= Ord.from_nat (1 + fuel)).
             apply Ord.omega_upperbound. }
        setoid_rewrite OrdArith.add_from_nat.
        reflexivity.
      - apply OrdArith.add_base_l.
    }

    assert (exists tr_pre,
               <<TR_PRE_EQ: tr_pre = (repeat [(Z.of_nat tm, []); (Z.of_nat tm, [])]
                num_tasks)>> /\
               <<TR_PRE_APP: app_each_rel tr_tgt1 tr_pre tr_acc_pre2>> /\
               <<APP_PRES: cons_each_rel tr_pre1 (tolist_each tr_pre2) tr_pre>>).
    { esplits.
      - eauto.
      - apply Forall3_nth'.
        rewrite repeat_length.
        splits.
        { apply Forall2_length in TR_PRE1_SILENT.
          rewrite repeat_length in TR_PRE1_SILENT.
          apply Forall3_length in APP_PRE1.
          des; ss. }
        { apply Forall3_length in APP_PRE1.
          apply Forall3_length in APP_PRE2.
          des; ss. nia. }
        i.
        apply repeat_spec_nth in NTH_B. subst.
        eapply Forall3_nth1 in APP_PRE1; eauto. des.
        clarify.
        eapply Forall3_nth3 in APP_PRE2; eauto. des.
        clarify.
        eapply Forall2_nth2 in TR_PRE1_SILENT; eauto. des.
        apply repeat_spec_nth in NTH3. clarify.
        unfold DSys.filter_nb_localstep in P_FA. ss.
        inv P_FA.
        eapply Forall2_nth2 in TR_PRE2_SILENT; eauto. des.
        apply repeat_spec_nth in NTH3. clarify.
        unfold DSys.filter_nb_localstep in P_FA. ss.
        inv P_FA.
        rewrite <- app_assoc. ss.
      - apply Forall3_nth'.
        unfold tolist_each.
        rewrite map_length, repeat_length.
        splits.
        { apply Forall3_length in APP_PRE2.
          apply Forall3_length in APP_PRE1.
          des. nia. }
        { apply Forall3_length in APP_PRE2.
          apply Forall3_length in APP_PRE1.
          des. nia. }
        i.
        apply repeat_spec_nth in NTH_C. subst.
        apply map_nth_error_iff in NTH_B. des. subst.
        eapply Forall2_nth2 in TR_PRE1_SILENT; eauto. des.
        apply repeat_spec_nth in NTH1. subst.
        eapply Forall2_nth2 in TR_PRE2_SILENT; eauto. des.
        apply repeat_spec_nth in NTH1. subst.

        unfold DSys.filter_nb_localstep in *. ss.
        clarify.
    }
    des.

    hexploit (nth_error_Some2 _ tr_pre (length lsts_src1)).
    { subst. rewrite repeat_length. nia. }
    i. des. guardH TR_PRE_EQ.
    renames e1 NTH_EX into tr_pre_n TR_PRE_N.

    eapply sim_run_with_fuel; cycle 2.
    { instantiate (1:= length lsts_src1). nia. }
    { ss. }
    { econs 2. }
    { ss. }
    { instantiate (1:= tr_pre_n). ss.
      rewrite TR_PRE_EQ in TR_PRE_N.
      apply repeat_spec_nth in TR_PRE_N. subst.
      ss. }
    { eauto. }
    { i. r.
      rewrite TR_PRE_EQ in NTH'.
      apply repeat_spec_nth in NTH'. subst.
      econs; ss. econs; ss. }
    { instantiate (1:= tr_tgt1). eauto. }
    { ss. }

    i.
    eapply REST.
    { econs 3; eauto.
      econs 2; eauto.
      - econs; eauto. ss.
      - ss. subst.
        destruct oast'; ss.
    }
    { eauto. }
    { eauto. }
    { eapply tes_equiv_sym. ss. }
    { i. eauto. }
    { econs; ss. }
    { eauto. }
  Qed.


  Lemma sim_step_itree
        (r: _ -> _ -> _ -> _ -> Prop)
        (tm: nat)
        k lsts_src
        (REST: forall tr_src_r outs lsts_src'
                 tr_src tr_tgt lsts_tgt'
                 (STEPS_SRC2: Forall4
                                (SNode.step sntz_msg num_tasks mcasts tm)
                                lsts_src tr_src_r outs lsts_src')
                 (FLT_ES2: DSys.filter_nb_sysstep
                             (map (fun es => (Z.of_nat tm, es))
                                  tr_src_r) = Some tr_src)
                 (TR_EQV: Forall2 tes_equiv
                                  (tolist_each tr_src)
                                  tr_tgt)
                 (MATCH_LSTS_DONE:
                    iForall3 match_loc_state O
                             (repeat (SNode.init_box num_tasks)
                                     num_tasks)
                             lsts_tgt' lsts_src')
          ,
            paco4 (_gmsim_states sys_src sys_tgt) r
                  5%ord (Some tr_tgt)
                  (SyncSys.State tm lsts_src)
                  (Z.of_nat tm,
                   interp_ainvk exec_sys unit
                                (k outs)
                                (lsts_tgt') ;;
                   Ret tt))
    : forall n_left n_done
        lsts_src1 lsts_src2
        ord_steps
        inbs2
        tr_src_r1 tr_src1 outs1 lsts_src1'
        lsts_tgt1' tr_tgt1 lsts_tgt2
        (LEFT_UBND: n_done + n_left = num_tasks)
        (LSTS_SRC_DIV: lsts_src = lsts_src1 ++ lsts_src2)
        (N_DONE: length lsts_src1 = n_done)
        (LEN_INBS: length inbs2 = n_left)
        (ORD_EQ: ord_steps =
                 (5 + (Ord.omega + 5) * n_left)%ord)
        (DONE: Forall4 (SNode.step sntz_msg num_tasks mcasts tm)
                       lsts_src1 tr_src_r1 outs1 lsts_src1')
        (FLT_SRC1: DSys.filter_nb_sysstep
                     (map (fun es => (Z.of_nat tm, es))
                          tr_src_r1) = Some tr_src1)
        (LEN_TR_TGT1: length tr_tgt1 = num_tasks)
        (TES_DONE_EQV: Forall2 tes_equiv
                               (tolist_each tr_src1)
                               (firstn n_done tr_tgt1))
        (SILENT_REST: Forall (@silent_local_trace _)
                             (skipn n_done tr_tgt1))
        (MATCH_LSTS_DONE: iForall3 match_loc_state 0
                                   (repeat (SNode.init_box num_tasks) n_done)
                                   lsts_tgt1' lsts_src1')

        (MATCH_LSTS: iForall3 match_loc_state n_done
                              inbs2 lsts_tgt2 lsts_src2)
    ,
      paco4 (_gmsim_states sys_src sys_tgt) r
            ord_steps (Some tr_tgt1)
            (SyncSys.State tm (lsts_src1 ++ lsts_src2))
            (Z.of_nat tm,
             interp_ainvk exec_sys unit
                          (r <- step_itree (Z.of_nat tm) n_done inbs2;; k (outs1 ++ r))
                          (lsts_tgt1' ++ lsts_tgt2);;
             Ret tt).
  Proof.
    induction n_left as [|n_left' IH]; i; ss.
    { eapply gmsim_red_idx with (ord1 := 5).
      { subst ord_steps.
        setoid_rewrite OrdArith.mult_O_r.
        setoid_rewrite OrdArith.add_O_r.
        reflexivity.
      }

      destruct inbs2; ss.
      match goal with
      | |- context[interp_ainvk _ _ ?t] =>
        remember t as itr' eqn: ITR
      end.
      symmetry in ITR.
      simpl_itree_hyp ITR. subst itr'.
      rewrite Nat.add_0_r in LEFT_UBND.

      inv MATCH_LSTS.
      eapply REST.
      { apply Forall4_app; eauto.
        econs. }
      { rewrite app_nil_r. eauto. }
      { rewrite <- LEN_TR_TGT1 in TES_DONE_EQV.
        rewrite firstn_all in TES_DONE_EQV.
        ss.
      }
      { do 2 rewrite app_nil_r. eauto. }
    }

    destruct inbs2 as [| inb_cur inbs2'].
    { exfalso. ss. }

    destruct lsts_tgt2 as [| lst_tgt lsts_tgt2_tl].
    { exfalso. inv MATCH_LSTS. }
    destruct lsts_src2 as [| lst_src lsts_src2_tl].
    { exfalso. inv MATCH_LSTS. }
    inv MATCH_LSTS.
    rename FA into MATCH_LSTS'.

    (* unfold step_itree *)
    s.
    erewrite unfold_interp_ainvk_vis_invoke.
    2: { simpl_itree_goal.
         simpl_itree_goal. ss. }

    hexploit iForall3_length; try apply MATCH_LSTS_DONE.
    rewrite repeat_length.
    intros [LEN1 LEN2].

    rewrite nth_error_app2 by nia.
    rewrite <- LEN1.
    rewrite Nat.sub_diag. s.
    simpl_itree_goal.
    simpl_itree_goal.
    fold num_tasks.

    eapply gmsim_red_idx with
        (ord1:= ((5 + (Ord.omega + 5) * n_left') +
                 (Ord.omega + 5))%ord).
    { setoid_rewrite OrdArith.add_assoc.
      eapply OrdArith.le_add_r.
      assert (EQ1: Ord.eq (S n_left') (n_left' + 1)%ord).
      { replace (S n_left') with (n_left' + 1) by nia.
        setoid_rewrite OrdArith.add_from_nat.
        reflexivity. }
      setoid_rewrite EQ1.
      setoid_rewrite OrdArith.mult_dist.
      setoid_rewrite OrdArith.mult_1_r.
      reflexivity.
    }

    eapply sim_run_period; eauto.
    { nia. }
    i. erewrite replace_nth_exact by ss.
    simpl_itree_goal.
    simpl_itree_goal.

    pfold. econs.
    { esplits. ss.
      econs 2; ss. }

    i. left.
    exists (5 + (Ord.omega + 5) * n_left')%ord.
    esplits.
    { apply OrdArith.add_lt_l.
      apply Ord.S_lt. }

    left.
    inv STEP_TGT; ss.
    clarify.
    rewrite DSys_filter_nb_sysstep_repeat_nil in FILTER_NB.
    inv FILTER_NB.

    match goal with
    | |- context[interp_ainvk _ _ ?t] =>
      remember t as itr' eqn: ITR
    end.
    symmetry in ITR.
    simpl_itree_hyp ITR. subst itr'.

    replace (lsts_src1 ++ lst_src :: lsts_src2_tl) with
        (snoc lsts_src1 lst_src ++ lsts_src2_tl).
    2: { unfold snoc. rewrite <- app_assoc. ss. }
    replace (lsts_tgt1' ++ lst_tgt' :: lsts_tgt2_tl) with
        (snoc lsts_tgt1' lst_tgt' ++ lsts_tgt2_tl).
    2: { unfold snoc. rewrite <- app_assoc. ss. }

    match goal with
    | |- context[ interp_ainvk _ _ ?t] =>
      remember t as itr eqn: ITR
    end.

    assert (ITR2: itr =
                  r <- step_itree (Z.of_nat tm) (S (length lsts_src1)) inbs2' ;;
                  k (snoc outs1 out ++ r)).
    { rewrite ITR.
      apply bisimulation_is_eq.
      eapply eqit_bind.
      - ii. simpl_itree_goal.
        unfold snoc.
        rewrite <- app_assoc. ss.
        reflexivity.
      - reflexivity.
    }
    clear ITR.
    subst itr.

    eapply IH.
    { nia. }
    { unfold snoc.
      rewrite <- app_assoc. ss. }
    { rewrite snoc_length. ss. }
    { ss. }
    { ss. }
    { unfold snoc.
      eapply Forall4_app.
      { eauto. }
      econs.
      2: { econs. }
      eauto.
    }
    { instantiate (1:= snoc tr_src1 tr_src_c).
      unfold snoc.

      unfold DSys.filter_nb_sysstep.
      apply deopt_list_Some_iff.
      symmetry.
      rewrite map_app.
      rewrite map_app.
      rewrite map_app.

      unfold DSys.filter_nb_sysstep in FLT_SRC1.
      apply deopt_list_Some_iff in FLT_SRC1.
      rewrite <- FLT_SRC1.
      ss.
      do 2 f_equal.
      ss.
    }
    { apply Forall3_length in APP_EVENTS.
      rewrite repeat_length in APP_EVENTS.
      des; ss. nia. }
    { unfold snoc.
      unfold tolist_each.
      rewrite map_app.

      assert (LT: length lsts_src1 < length tr_accum').
      { apply Forall3_length in APP_EVENTS.
        rewrite repeat_length in APP_EVENTS. des.
        nia. }

      hexploit (nth_error_Some2 _ tr_accum' (length lsts_src1)).
      { ss. }
      i. des.
      renames e1 NTH_EX into tr_acc_c TR_ACC_C.

      replace (firstn (S (length lsts_src1)) tr_accum')
        with (firstn (length lsts_src1) tr_accum' ++
                     [tr_acc_c]).
      2: {
        erewrite firstn_snoc_nth.
        { unfold snoc. eauto. }
        { apply Forall3_length in APP_EVENTS.
          rewrite repeat_length in APP_EVENTS. des.
          nia. }
        instantiate (1:= []).
        eapply nth_error_nth. eauto.
      }
      apply Forall2_app.
      - apply Forall2_nth'.
        rewrite map_length.

        replace (S (length lsts_src1)) with
            (length lsts_src1 + 1) by nia.
        rewrite firstn_length.
        splits.
        { apply Forall3_length in APP_EVENTS.
          rewrite repeat_length in APP_EVENTS.
          des.
          apply Forall2_length in TES_DONE_EQV.
          unfold tolist_each in TES_DONE_EQV.
          rewrite map_length in TES_DONE_EQV.
          rewrite firstn_length in TES_DONE_EQV.
          nia.
        }

        i. rewrite map_nth_error_iff in NTH_A. des.
        subst.

        apply nth_error_firstn in NTH_B. des.
        rename NTH_ERR into TR_ACC_N.

        eapply Forall2_nth1 in TES_DONE_EQV.
        2: {
          unfold tolist_each.
          apply map_nth_error_iff.
          esplits; eauto.
        }
        des; ss.
        renames e2 NTH2 P_FA into tr_tgt1_n TR_TGT1_N EQV1.
        apply nth_error_firstn in TR_TGT1_N. des.
        rename NTH_ERR into TR_TGT1_N.

        eapply Forall3_nth1 in APP_TR_TGT; eauto.
        des. subst.
        renames e2 NTH2 NTH3 into
                tr_tgt_cn TR_TGT_CN TR_TGT1'_N.
        eapply Forall3_nth1 in APP_EVENTS; eauto.
        des. clarify.
        eapply repeat_spec_nth in NTH2. subst.

        hexploit SILENT_OTHER.
        { instantiate (1:= n). nia. }
        { eauto. }
        intro SILENT.
        eapply flatten_silent_local_trace_iff in SILENT.
        r. do 2 rewrite flatten_tes_app.
        rewrite SILENT.
        rewrite EQV1.
        unfold flatten_tes. ss.
        do 2 rewrite app_nil_r. ss.
      - econs.
        2: { econs. }
        eapply tes_equiv_trans.
        { eapply tes_equiv_sym. eauto. }

        eapply Forall3_nth3 in APP_EVENTS; eauto.
        des. clarify.
        apply repeat_spec_nth in NTH2. subst.
        renames e1 NTH1 into tr_tgt1'_n TR_TGT1'_N.

        eapply Forall3_nth3 in APP_TR_TGT; eauto.
        des. clarify.
        renames e1 NTH1 NTH2 into
                tr_tgt1_n TR_TGT1_N TR_TGT_C_N.

        rewrite Forall_forall in SILENT_REST.
        hexploit SILENT_REST.
        { instantiate (1:= tr_tgt1_n).

          eapply nth_error_In.
          rewrite skipn_nth_error.
          instantiate (1:= O). ss.
        }
        intro SILENT.
        apply flatten_silent_local_trace_iff in SILENT.
        r.
        repeat rewrite flatten_tes_app.
        rewrite SILENT. s.
        unfold flatten_tes. ss.
        rewrite app_nil_r. ss.
    }
    { apply Forall_nth. intro n.
      rewrite skipn_nth_error.
      r. desf.
      eapply Forall3_nth3 in APP_EVENTS; eauto. des.
      subst.
      renames e1 NTH1 into tr_tgt1'_m TR_TGT1'_M.
      apply repeat_spec_nth in NTH2. subst.

      eapply Forall3_nth3 in APP_TR_TGT; eauto. des.
      clarify.

      rewrite Forall_forall in SILENT_REST.
      hexploit SILENT_REST.
      { eapply nth_error_In.
        rewrite skipn_nth_error.
        replace (n + S (length lsts_src1)) with
            (S n + length lsts_src1) in NTH1 by nia.
        apply NTH1.
      }
      intro SILENT1.

      hexploit (SILENT_OTHER (n + S (length lsts_src1))).
      { nia. }
      { eauto. }
      intro SILENT2.

      unfold silent_local_trace.
      apply Forall_app.
      2: { econs; ss. }
      apply Forall_app; ss.
    }
    { replace (S (length lsts_src1)) with (length lsts_src1 + 1) by nia.
      rewrite repeat_app. s.
      unfold snoc.
      eapply iForall3_app; eauto.
      rewrite repeat_length. s.
      econs; eauto.
      econs.
    }
    { ss. }
  Qed.



  Lemma sim_period
    : forall tm tm_p inbs lsts_src lsts_tgt
        (TM_UBND: period <= tm)
        (SYNC_TIME: Nat.divide period tm)
        (NUM_TASKS: length lsts_src = num_tasks)
        (MATCH_LSTS: iForall3 match_loc_state 0
                              inbs lsts_tgt lsts_src),
      gmsim_states sys_src sys_tgt
                   ord_prd None
                   (SyncSys.State tm lsts_src)
                   (Z.of_nat tm_p,
                    (interp_ainvk exec_sys _
                                  (synch_itree_loop num_tasks (Z.of_nat period)
                                                    None (Z.of_nat tm) inbs)
                                  lsts_tgt);; Ret tt).
  Proof.
    pcofix CIH. i.

    pfold.
    erewrite unfold_interp_ainvk_vis_tsp.
    2: { rewrite unfold_synch_itree_loop.
         ss. simpl_itree_goal. ss. }
    simpl_itree_goal.
    unf_resum.

    econs; ss.
    { esplits.
      econs 3; ss. }

    i. subst.

    inv STEP_TGT; ss.
    clarify.
    existT_elim. subst.
    rewrite DSys_filter_nb_sysstep_repeat_nil
      in FILTER_NB.
    inv FILTER_NB.

    left.
    pose (ord_m1 := (5 + (Ord.omega + 5) * num_tasks + 4)%ord).

    exists ord_m1.
    splits.
    { subst ord_m1 ord_prd.
      apply OrdArith.lt_add_r.
      apply OrdArith.lt_from_nat. nia. }
    left.
    simpl_itree_goal.

    pfold.
    econs.
    { esplits; ss.
      econs 2; ss. }

    i. left.
    inv STEP_TGT; ss.
    clarify.
    rewrite DSys_filter_nb_sysstep_repeat_nil
      in FILTER_NB.
    inv FILTER_NB.

    assert (TR_ACCUM_EQ:
              (* tr_accum' = *)
              (* repeat [(Z.of_nat tm_p, []); *)
              (*         (Z.of_nat tm, [])] num_tasks). *)
              Forall (@silent_local_trace _) tr_accum').
    { apply Forall_nth. i.
      destruct (nth_error tr_accum' n) eqn:NTH; ss.
      eapply Forall3_nth3 in APP_EVENTS; eauto.
      des. subst.
      rewrite map_nth_error_iff in NTH1. des.
      apply repeat_spec_nth in NTH1, NTH2.
      clarify.
      ss. r. econs; ss. econs; ss.
    }
    assert (LEN_ACC: length tr_accum' = num_tasks).
    { apply Forall3_length in APP_EVENTS.
      rewrite map_length, repeat_length in APP_EVENTS.
      des; ss. }
    clear APP_EVENTS.

    pose (ord_m2 := (5 + (Ord.omega + 5) * num_tasks)%ord).

    exists ord_m2.
    splits.
    { setoid_rewrite <- OrdArith.add_O_r at 1.
      subst ord_m1 ord_m2.
      apply OrdArith.lt_add_r.
      replace Ord.O with (Ord.from_nat O) by ss.
      apply OrdArith.lt_from_nat. nia. }
    left.

    replace lsts_src with ([] ++ lsts_src) by ss.
    replace lsts_tgt with ([] ++ lsts_tgt) by ss.
    rewrite <- Nat2Z.inj_add.

    pose (k := fun x: list (list msgT?) =>
                 Tau (synch_itree_loop num_tasks (Z.of_nat period) None (Z.of_nat (tm + period))
                                       (imap (fun (tid : nat) (_ : unit) => map (SNode.get_outbox_msg_by_dest tid) x) 0 (repeat tt num_tasks)))).

    hexploit (sim_step_itree r tm k); cycle 1.
    { assert (AUX: 0 + num_tasks = num_tasks) by ss.
      apply AUX. }
    { assert (AUX: lsts_src = [] ++ lsts_src) by ss.
      apply AUX. }
    { ss. }
    { instantiate (1:= inbs).
      apply iForall3_length in MATCH_LSTS.
      des; ss. congruence. }
    { reflexivity. }
    { econs. }
    { ss. }
    { instantiate (1:= tr_accum'). ss. }
    { ss. }
    { ss. }
    { ss. econs 1. }
    { eauto. }
    { eauto. }

    subst k. i. pfold.
    erewrite unfold_interp_ainvk_tau by ss.
    simpl_itree_goal.
    econs.
    { esplits; ss.
      econs 2; ss. }

    renames tr_accum' tr_tgt into tr_acc_done tr_tgt_done.
    s. i.
    inv STEP_TGT; ss.
    clarify.
    rewrite DSys_filter_nb_sysstep_repeat_nil
      in FILTER_NB.
    inv FILTER_NB.

    hexploit sync_msteps_exists;
      try apply STEPS_SRC2; eauto.
    i. des.

    right.
    exists period.
    do 2 eexists.
    exists ord_prd.

    esplits; eauto.
    { eapply Forall2_tes_equiv_trans.
      { eapply Forall2_tes_equiv_trans.
        - eapply Forall2_tes_equiv_sym; eauto.
        - eapply TR_EQV.
      }
      clear - APP_EVENTS.
      apply Forall2_nth'.
      split.
      { apply Forall3_length in APP_EVENTS.
        des; ss. }
      i.
      eapply Forall3_nth1 in APP_EVENTS; eauto.
      des; ss.
      apply repeat_spec_nth in NTH2.
      clarify.
      unfold tes_equiv.
      rewrite flatten_tes_app.
      unfold flatten_tes. ss.
      rewrite app_nil_r. ss.
    }

    right.
    (* rewrite <- Nat2Z.inj_add. *)
    eapply CIH.
    - nia.
    - apply Nat.divide_add_r; eauto.
      apply Nat.divide_refl.
    - rewrite map_length.
      apply Forall4_length in STEPS_SRC2. des; ss.
      nia.
    - eapply iForall3_match_loc_state_new_inb.
      { instantiate (1:= period). ss. }
      { instantiate (1:= (tm + period)).
        nia. }
      { instantiate (1:= lsts_src').
        instantiate (1:= app_mods).
        fold num_tasks. ss. }
      { eauto. }
      eauto.
  Qed.


  Lemma exec_sync_gmsim_states
        lsts_src
        (LSTS_SRC: lsts_src = imap (SNode.init_state
                                      (length nodes)) 0 nodes)
    : gmsim_states
        sys_src sys_tgt ord_prd None
        (SyncSys.State tm_init lsts_src)
        (Z0, interp_ainvk exec_sys _
                          (synch_itree num_tasks (Z.of_nat period)
                                       (Z.of_nat tm_init) None)
                          (init_loc_states exec_sys);;
             Ret tt).
  Proof.
    pose (m := (tm_init mod period)).
    pose (n_pre := if m =? 0 then 0 else period - m).

    assert (exists tr_pre,
               <<MSTEPS_SRC_PRE:
                 msteps sys_src n_pre
                        {| SyncSys.time := tm_init;
                           SyncSys.node_states := lsts_src |}
                        tr_pre
                        {| SyncSys.time := tm_init + n_pre;
                           SyncSys.node_states := lsts_src |}>> /\
               <<TR_PRE_SILENT:
                   Forall (@silent_local_trace _) tr_pre>>).
    {
      destruct (Nat.eqb_spec m 0).
      { subst m n_pre.
        rewrite Nat.add_0_r.
        esplits.
        { econs 1; eauto. }
        ss.
        apply Forall_forall.
        intros x IN.
        apply repeat_spec in IN. subst. ss.
      }

      assert (tm_init mod period < period).
      { apply Nat.mod_upper_bound. nia. }

      assert(Nat.divide period (tm_init - m)).
      { r. subst m.
        apply sub_mod_divide. ss. }

      hexploit sync_sys_msteps_nosync_exists.
      { eauto. }
      { eauto. }
      (* { reflexivity. } *)
      (* { instantiate (1:= tm_init - m). ss. } *)
      { instantiate (1:= tm_init). nia. }
      { instantiate (1:= n_pre).
        subst n_pre.
        subst m.
        nia. }
      intros [tr_pre [st1 MSTEPS_PRE]].
      pose proof MSTEPS_PRE as MSTEPS_PRE'.
      (* eapply sync_sys_msteps_nosync_impl in MSTEPS_PRE'; *)
      (*   eauto; cycle 1. *)
      (* { nia. } *)
      (* { nia. } *)

      des. subst.
      esplits; eauto.
    }
    des.

    eapply gmsim_states_append_silent_prefix_src; eauto.

    unfold synch_itree. ss.
    fold m. fold n_pre.

    assert (LEN_LSTS_SRC: length lsts_src = num_tasks).
    { subst lsts_src.
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
    { nia. }
    { destruct (Nat.eqb_spec m 0).
      - subst n_pre.
        rewrite Nat.add_0_r. ss.
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

    hexploit (nth_error_Some2 _ lsts_src tid).
    { nia. }
    i. des. renames e1 NTH_EX into lst_src LST_SRC.
    rewrite LST_SRC.
    subst lsts_src.
    rewrite imap_nth_error_iff in LST_SRC. ss.
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
