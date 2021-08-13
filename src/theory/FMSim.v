From Paco Require Import paco.
From ITree Require Import ITree.
From Ordinal Require Import Ordinal Arithmetic.

Require Import IndefiniteDescription.
Require Import ZArith Streams List Lia.

Require Import sflib.
Require Import StdlibExt.
Require Import SysSem.
Require Import MSteps.

Require Import GMSim.


Set Nested Proofs Allowed.

(* fixed-length multistep simulation *)



(* Definition tes_equiv {sysE: Type -> Type} *)
(*            (ftr1 ftr2: list (nat * events sysE)): Prop := *)
(*   flatten_tes ftr1 = flatten_tes ftr2. *)

Section SIM.
  Variable sysE: Type -> Type.
  Variable sys_src sys_tgt: @DSys.t sysE.

  Inductive _fmsim_states
            (sim: sys_src.(DSys.state) ->
                  sys_tgt.(DSys.state) -> Prop)
            (st_src: sys_src.(DSys.state))
            (st_tgt: sys_tgt.(DSys.state)): Prop :=
    FMSimStates
      (n_tgt: nat)
      (N_TGT_POS: 0 < n_tgt)
      (STEPS_SIM:
         forall tr_tgt st_tgt'
           (STEPS: msteps sys_tgt n_tgt st_tgt tr_tgt st_tgt')
         ,
         exists n_src tr_src st_src',
           <<N_SRC_POS: 0 < n_src>> /\
           <<STEPS_SRC: msteps sys_src n_src st_src tr_src st_src'>> /\
           <<TRACE_EQUIV: Forall2 tes_equiv tr_src tr_tgt>> /\
           <<SIM_NXT: sim st_src' st_tgt'>>)
  .

  Hint Constructors _fmsim_states: paco.

  Lemma fmsim_states_monotone: monotone2 _fmsim_states.
  Proof.
    ii. inv IN. econs; eauto.
    i. hexploit STEPS_SIM; eauto. i. des.
    esplits; eauto.
  Qed.

  Hint Resolve fmsim_states_monotone: paco.

  Definition fmsim_states
    : sys_src.(DSys.state) -> sys_tgt.(DSys.state) -> Prop :=
    paco2 _fmsim_states bot2.

  Inductive fmsim: Prop :=
    FMSim
      (* (TGT_INIT_OK: exists st_tgt_i1, sys_tgt.(DSys.initial_state) st_tgt_i1) *)
      (SIM_INIT_STATES:
         forall st_tgt_i
           (INIT_TGT: sys_tgt.(DSys.initial_state) st_tgt_i),
         exists st_src_i,
           <<INIT_SRC: sys_src.(DSys.initial_state) st_src_i>> /\
           <<SIM_STATES: fmsim_states st_src_i st_tgt_i>>)
  .


  Lemma fmsim_gmsim_states_aux
        (r: _ -> _ -> _ -> _ -> Prop)
        (CIH : forall (st_src : DSys.state sys_src) (st_tgt : DSys.state sys_tgt),
            DSys.safe_state st_tgt -> fmsim_states st_src st_tgt ->
            r Ord.omega None st_src st_tgt)
        n_tgt2'
    : forall st_src st_tgt
        n_tgt1
        tr_tgt1 st_tgt1
        (SAFE1: DSys.safe_state st_tgt1)
        (MSTEPS1: msteps sys_tgt n_tgt1 st_tgt tr_tgt1 st_tgt1)
        (STEPS_SIM: forall tr_tgt2 st_tgt' tr_tgt
                      (MSTEPS2: msteps sys_tgt (S n_tgt2') st_tgt1 tr_tgt2 st_tgt')
                      (TR_TGT: app_each_rel tr_tgt1 tr_tgt2 tr_tgt)
          ,
            exists n_src tr_src st_src',
              0 < n_src /\
              msteps sys_src n_src st_src tr_src st_src' /\
              Forall2 tes_equiv tr_src tr_tgt /\
              paco2 _fmsim_states bot2 st_src' st_tgt')
    ,
      paco4 (_gmsim_states sys_src sys_tgt) r (S n_tgt2') (Some tr_tgt1)
             st_src st_tgt1.
  Proof.
    induction n_tgt2' as [| n_tgt2'' IH]; i; ss.
    { pfold.
      punfold SAFE1. inv SAFE1.
      econs.
      { eauto. }

      i. right.

      hexploit STEPS_SIM; eauto.
      { econs 2; eauto.
        { econs 1; eauto. }
        apply cons_each_to_nils.
        apply DSys.step_prsv_num_sites in STEP_TGT. des.
        apply Forall3_length in APP_EVENTS. des.

        apply DSys_filter_nb_sysstep_inv in FILTER_NB.
        apply Forall2_length in FILTER_NB.
        nia.
      }
      { instantiate (1:= tr_accum').
        apply snoc_each_tolist2 in APP_EVENTS. ss.
      }

      i. des.
      esplits; eauto.
      right. apply CIH; eauto.
      hexploit SAFE_NXT; eauto.
      { congruence. }
      i. pclearbot. ss.
    }

    punfold SAFE1. inv SAFE1.
    pfold. econs; eauto.
    i. left.
    exists (S n_tgt2'').
    esplits.
    { apply OrdArith.lt_from_nat. nia. }
    left.

    assert (MSTEPS_CC: msteps _ (n_tgt1 + 1) st_tgt tr_accum' st_tgt').
    { hexploit msteps_concat.
      { eauto. }
      { econs 2; eauto.
        { econs 1; eauto. }
        apply cons_each_impl_rel.
        rewrite repeat_length.

        apply DSys_filter_nb_sysstep_inv in FILTER_NB.
        apply Forall2_length in FILTER_NB.
        apply Forall3_length in APP_EVENTS.
        apply DSys.step_prsv_num_sites in STEP_TGT. des.
        nia.
      }
      i. des.

      rewrite cons_each_nil_eq_tolist_each in ES_CONCAT.
      2: {
        apply DSys_filter_nb_sysstep_inv in FILTER_NB.
        apply Forall2_length in FILTER_NB.
        apply Forall3_length in APP_EVENTS.
        apply DSys.step_prsv_num_sites in STEP_TGT. des.
        nia.
      }

      replace tr_accum' with es.
      { eauto. }

      eapply app_each_rel_det; eauto.
      apply snoc_each_tolist2 in APP_EVENTS.
      ss.
    }

    eapply IH.
    { hexploit SAFE_NXT; eauto.
      { congruence. }
      i. pclearbot. ss.
    }
    { eauto. }

    i.
    hexploit STEPS_SIM.
    { econs 2; try apply MSTEPS2; eauto.
      eapply cons_each_impl_rel.
      apply Forall3_length in APP_EVENTS.
      apply Forall3_length in TR_TGT.
      des; ss. nia. }
    { instantiate (1:= tr_tgt0).
      apply Forall3_nth'.

      hexploit Forall3_length; try apply TR_TGT.
      hexploit Forall3_length; try apply APP_EVENTS.
      i. des.

      hexploit (cons_each_impl_rel _ tr_tgt tr_tgt2).
      { nia. }
      intro CONS_EACH.
      hexploit Forall3_length; try apply CONS_EACH.
      i. des.

      splits.
      { nia. }
      { nia. }

      i.
      eapply Forall3_nth1 in APP_EVENTS; eauto. i. des.
      subst.
      renames e2 NTH2 NTH3 into tr_tgt_n TR_TGT_N TR_ACC_N.
      eapply Forall3_nth3 in CONS_EACH; eauto. i. des.
      clarify.
      renames e2 NTH1 NTH2 into tr_tgt2_n TR_TGT_N TR_TGT2_N.
      eapply Forall3_nth3 in TR_TGT; eauto. i. des.
      clarify.
      rewrite <- app_assoc. ss.
    }

    i. des.
    esplits; eauto.
  Qed.


  Lemma fmsim_states_impl_gmsim_states
    : forall st_src st_tgt
        (SAFE: DSys.safe_state st_tgt)
        (FMSIM: fmsim_states st_src st_tgt),
      gmsim_states _ _ Ord.omega None st_src st_tgt.
  Proof.
    pcofix CIH. i.
    punfold FMSIM.
    inv FMSIM.

    pfold. econs.
    { r in SAFE. punfold SAFE.
      inv SAFE.
      eauto. }

    i.
    destruct n_tgt as [| [ |n_tgt]].
    { nia. }
    { right.
      hexploit STEPS_SIM; eauto.
      { econs 2; eauto.
        { econs 1; eauto. }
        apply cons_each_to_nils.
        apply DSys_filter_nb_sysstep_inv in FILTER_NB.
        apply Forall2_length in FILTER_NB.
        apply DSys.step_prsv_num_sites in STEP_TGT. des.
        nia.
      }
      i. des.
      esplits; eauto.
      { subst tr_accum'.
        eauto. }
      right.
      apply CIH.
      - punfold SAFE.
        inv SAFE.
        hexploit SAFE_NXT; eauto.
        { congruence. }
        i. pclearbot. ss.
      - pclearbot. ss.
    }

    left. exists (S n_tgt).
    esplits.
    { apply Ord.omega_upperbound. }

    left.
    punfold SAFE. inv SAFE.
    hexploit SAFE_NXT; eauto.
    { congruence. }
    i. pclearbot.

    eapply fmsim_gmsim_states_aux; eauto.
    { econs 2; eauto.
      { econs 1; eauto. }
      apply cons_each_to_nils.

      apply DSys.step_prsv_num_sites in STEP_TGT. des.
      apply DSys_filter_nb_sysstep_inv in FILTER_NB.
      apply Forall2_length in FILTER_NB. nia.
    }

    i.
    hexploit msteps_concat.
    2: { eauto. }
    { econs 2; eauto.
      { econs 1; eauto. }
      apply cons_each_to_nils.
      apply DSys.step_prsv_num_sites in STEP_TGT. des.
      apply DSys_filter_nb_sysstep_inv in FILTER_NB.
      apply Forall2_length in FILTER_NB. nia.
    }

    replace (1 + S n_tgt) with (S (S n_tgt)) by nia. i. des.

    hexploit STEPS_SIM; eauto.
    i. des.
    esplits; eauto.
    - fold (tolist_each tr_tgt) in TR_TGT.
      apply cons_each_hd_tolist in TR_TGT.
      apply cons_each_hd_tolist in ES_CONCAT.
      apply cons_each_rel_det in TR_TGT.
      apply cons_each_rel_det in ES_CONCAT.
      clarify.
    - r in SIM_NXT. inv SIM_NXT; ss.
  Qed.

  Lemma fmsim_impl_gmsim
        (SAFE_SYS: DSys.safe sys_tgt)
        (FMSIM: fmsim)
    : gmsim sys_src sys_tgt.
  Proof.
    inv FMSIM.
    econs.
    { inv SAFE_SYS. eauto. }
    i.
    hexploit SIM_INIT_STATES; eauto. i. des.
    esplits; eauto.
    apply fmsim_states_impl_gmsim_states; eauto.
    inv SAFE_SYS. eauto.
  Qed.



  Lemma fmsim_num_sites_eq
        st_src st_tgt exec_tgt
        (SAFE: DSys.safe_state st_tgt)
        (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt)
        (FMSIM: fmsim_states st_src st_tgt)
    : DSys.num_sites _ st_src = DSys.num_sites _ st_tgt.
  Proof.
    punfold FMSIM. inv FMSIM.
    hexploit safe_exec_impl_msteps; eauto. i. des.
    hexploit msteps_num_sites_eq; eauto. i. des.

    hexploit STEPS_SIM; eauto. i. des.
    hexploit msteps_num_sites_eq; eauto. i. des.
    apply Forall2_length in TRACE_EQUIV; eauto. nia.
  Qed.


  (* Record _fmsim_auxdata : Type := *)
  (*   FMSimAuxdata { *)
  (*       aux_tr_h_src : list (tsp * events sysE) ; *)
  (*       aux_tr_t_src : list (list (tsp * events sysE)) ; *)
  (*       aux_st_src_nxt : DSys.state sys_src ; *)

  (*       aux_tr_h_tgt : list (tsp * events sysE) ; *)
  (*       aux_tr_t_tgt : list (list (tsp * events sysE)) ; *)
  (*       aux_st_tgt_nxt : DSys.state sys_tgt ; *)
  (*       aux_exec_tgt_nxt: @exec_t sysE; *)

  (*       AUX_SAFE_NXT: DSys.safe_state aux_st_tgt_nxt ; *)
  (*       AUX_EXEC_TGT_NXT: DSys.exec_state _ aux_st_tgt_nxt aux_exec_tgt_nxt ; *)
  (*       AUX_FMSIM_NXT: fmsim_states aux_st_src_nxt aux_st_tgt_nxt ; *)
  (*     }. *)

  (* Lemma fmsim_states_ex_src *)
  (*       st_src st_tgt exec_tgt *)
  (*       (SAFE: DSys.safe_state st_tgt) *)
  (*       (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt) *)
  (*       (FMSIM: fmsim_states st_src st_tgt) *)
  (*   : exists n_src tr_h_src_raw tr_h_src st_src1 *)
  (*       tr_t_src tr_src st_src' *)
  (*       n_tgt tr_h_tgt_raw tr_h_tgt st_tgt1 *)
  (*       tr_t_tgt tr_tgt st_tgt' exec_tgt', *)
  (*     DSys.step _ st_src tr_h_src_raw st_src1 /\ *)
  (*     DSys.filter_nb_sysstep tr_h_src_raw = Some tr_h_src /\ *)
  (*     msteps _ n_src st_src1 tr_t_src st_src' /\ *)

  (*     DSys.step _ st_tgt tr_h_tgt_raw st_tgt1 /\ *)
  (*     DSys.filter_nb_sysstep tr_h_tgt_raw = Some tr_h_tgt /\ *)
  (*     msteps _ n_tgt st_tgt1 tr_t_tgt st_tgt' /\ *)

  (*     cons_each_rel tr_h_src tr_t_src tr_src /\ *)
  (*     cons_each_rel tr_h_tgt tr_t_tgt tr_tgt /\ *)
  (*     Forall2 tes_equiv tr_src tr_tgt /\ *)
  (*     Forall3 (fun a b c => stream_app a b = c) *)
  (*             tr_tgt exec_tgt' exec_tgt /\ *)

  (*     DSys.safe_state st_tgt' /\ *)
  (*     DSys.exec_state _ st_tgt' exec_tgt' /\ *)
  (*     fmsim_states st_src' st_tgt' *)
  (* . *)
  (* Proof. *)
  (*   punfold FMSIM. inv FMSIM. *)
  (*   hexploit safe_exec_impl_msteps; eauto. *)
  (*   instantiate (1:= n_tgt). *)
  (*   i. des. *)
  (*   hexploit STEPS_SIM; eauto. *)
  (*   i. des. *)
  (*   pclearbot. *)

  (*   destruct n_src as [| n_src']; ss. *)
  (*   { exfalso. nia. } *)
  (*   destruct n_tgt as [| n_tgt']; ss. *)
  (*   { exfalso. nia. } *)
  (*   inv MSTEPS. *)
  (*   inv STEPS_SRC. *)

  (*   esplits; eauto. *)

  (*   (* punfold SAFE. inv SAFE. *) *)
  (*   (* hexploit SAFE_NXT; eauto. *) *)
  (*   (* { congruence. } *) *)
  (*   (* i. pclearbot. *) *)


  (*   (* eapply safe_state_mstep; eauto. *) *)
  (* Qed. *)

  (* Definition fmsim_states_constr_src1 *)
  (*       st_src st_tgt exec_tgt *)
  (*       (SAFE: DSys.safe_state st_tgt) *)
  (*       (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt) *)
  (*       (FMSIM: fmsim_states st_src st_tgt) *)
  (*   : { aux: _fmsim_auxdata | *)
  (*       exists n_src tr_h_src_raw st_src1 tr_src *)
  (*         n_tgt tr_h_tgt_raw st_tgt1 tr_tgt, *)
  (*     <<AUX_STEP1_SRC: DSys.step _ st_src tr_h_src_raw st_src1>> /\ *)
  (*     <<AUX_FLT1_SRC: DSys.filter_nb_sysstep tr_h_src_raw = Some (aux_tr_h_src aux)>> /\ *)
  (*     <<AUX_STEPS_SRC: msteps _ n_src st_src1 (aux_tr_t_src aux) (aux_st_src_nxt aux)>> /\ *)

  (*     <<AUX_STEP1_TGT: DSys.step _ st_tgt tr_h_tgt_raw st_tgt1>> /\ *)
  (*     <<AUX_FLT1_TGT: DSys.filter_nb_sysstep tr_h_tgt_raw = Some (aux_tr_h_tgt aux)>> /\ *)
  (*     <<AUX_STEPS_TGT: msteps _ n_tgt st_tgt1 (aux_tr_t_tgt aux) (aux_st_tgt_nxt aux)>> /\ *)

  (*     <<TR_SRC: cons_each_rel (aux_tr_h_src aux) (aux_tr_t_src aux) tr_src>> /\ *)
  (*     <<TR_TGT: cons_each_rel (aux_tr_h_tgt aux) (aux_tr_t_tgt aux) tr_tgt>> /\ *)
  (*     <<TRC_EQV: Forall2 tes_equiv tr_src tr_tgt>> /\ *)
  (*     <<EXEC_TGT_NXT: *)
  (*       Forall3 (fun a b c => stream_app a b = c) *)
  (*               tr_tgt (aux_exec_tgt_nxt aux) exec_tgt>> *)
  (*     }. *)
  (* Proof. *)
  (*   hexploit fmsim_states_ex_src; eauto. *)
  (*   intro EX. *)

  (*   pose (CID := constructive_indefinite_description). *)
  (*   eapply CID in EX. destruct EX as [ns_src EX]. *)
  (*   eapply CID in EX. destruct EX as [tr_h_src_raw EX]. *)
  (*   eapply CID in EX. destruct EX as [tr_h_src EX]. *)
  (*   eapply CID in EX. destruct EX as [st_src1 EX]. *)
  (*   eapply CID in EX. destruct EX as [tr_t_src EX]. *)
  (*   eapply CID in EX. destruct EX as [tr_src EX]. *)
  (*   eapply CID in EX. destruct EX as [st_src' EX]. *)
  (*   eapply CID in EX. destruct EX as [n_tgt EX]. *)
  (*   eapply CID in EX. destruct EX as [tr_h_tgt_raw EX]. *)
  (*   eapply CID in EX. destruct EX as [tr_h_tgt EX]. *)
  (*   eapply CID in EX. destruct EX as [st_tgt1 EX]. *)
  (*   eapply CID in EX. destruct EX as [tr_t_tgt EX]. *)
  (*   eapply CID in EX. destruct EX as [tr_tgt EX]. *)
  (*   eapply CID in EX. destruct EX as [st_tgt' EX]. *)
  (*   eapply CID in EX. destruct EX as [exec_tgt' EX]. *)
  (*   des. *)

  (*   eexists (FMSimAuxdata _ _ _ _ _ _ _ _ _ _). *)
  (*   esplits; eauto. *)
  (*   Unshelve. *)
  (*   - eauto. *)
  (*   - eauto. *)
  (*   - eauto. *)
  (* Qed. *)

  (* CoFixpoint constr_local_exec_src *)
  (*       st_src st_tgt exec_tgt *)
  (*       (SAFE: DSys.safe_state st_tgt) *)
  (*       (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt) *)
  (*       (FMSIM: fmsim_states st_src st_tgt) *)
  (*       (n: nat) (cont: list (tsp * events sysE)) *)
  (*   : @lexec_t sysE. *)
  (* Proof. *)
  (*   destruct cont as [| h t]. *)
  (*   2: { exact (Cons h (constr_local_exec_src *)
  (*                         _ _ _ SAFE EXEC_TGT FMSIM n t)). } *)

  (*   pose (C := proj1_sig (fmsim_states_constr_src1 *)
  (*                           _ _ _ SAFE EXEC_TGT FMSIM)). *)
  (*   econs. *)
  (*   { exact (nth n (aux_tr_h_src C) (0%Z, [])). } *)
  (*   { exact (constr_local_exec_src *)
  (*              _ _ _ *)
  (*              (AUX_SAFE_NXT C) (AUX_EXEC_TGT_NXT C) *)
  (*              (AUX_FMSIM_NXT C) n *)
  (*              (nth n (aux_tr_t_src C) [])). *)
  (*   } *)
  (* Defined. *)

  (* Definition constr_exec_src *)
  (*       st_src st_tgt exec_tgt *)
  (*       (SAFE: DSys.safe_state st_tgt) *)
  (*       (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt) *)
  (*       (FMSIM: fmsim_states st_src st_tgt) *)
  (*   : @exec_t sysE := *)
  (*   imap (fun n _ => constr_local_exec_src *)
  (*                   _ _ _ SAFE EXEC_TGT FMSIM n []) *)
  (*        0 (List.repeat tt (DSys.num_sites _ st_src)). *)

  (* Lemma constr_exec_src_length *)
  (*       st_src st_tgt exec_tgt *)
  (*       (SAFE: DSys.safe_state st_tgt) *)
  (*       (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt) *)
  (*       (FMSIM: fmsim_states st_src st_tgt) *)
  (*   : length (constr_exec_src _ _ _ SAFE EXEC_TGT FMSIM) = *)
  (*     DSys.num_sites _ st_src. *)
  (* Proof. *)
  (*   unfold constr_exec_src. *)
  (*   rewrite imap_length. *)
  (*   rewrite repeat_length. ss. *)
  (* Qed. *)

  (* Lemma constr_local_exec_src_app_cont *)
  (*       n es st_src st_tgt exec_tgt *)
  (*       (SAFE: DSys.safe_state st_tgt) *)
  (*       (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt) *)
  (*       (FMSIM: fmsim_states st_src st_tgt) *)
  (*   : constr_local_exec_src *)
  (*       _ _ _ SAFE EXEC_TGT FMSIM n es = *)
  (*     stream_app es *)
  (*                (constr_local_exec_src *)
  (*                   _ _ _ SAFE EXEC_TGT FMSIM n []). *)
  (* Proof. *)
  (*   induction es as [| h t IH]; ss. *)
  (*   match goal with *)
  (*   | |- ?c = _ => rewrite (unfold_Stream c) *)
  (*   end. *)
  (*   ss. f_equal. ss. *)
  (* Qed. *)



  (* Lemma constr_exec_src_des *)
  (*       st_src st_tgt exec_tgt *)
  (*       (SAFE: DSys.safe_state st_tgt) *)
  (*       (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt) *)
  (*       (FMSIM: fmsim_states st_src st_tgt) *)
  (*   : exists n_src tr_h_src_raw tr_h_src st_src1 *)
  (*       tr_t_src tr_src st_src' *)
  (*       n_tgt tr_h_tgt_raw tr_h_tgt st_tgt1 *)
  (*       tr_t_tgt tr_tgt st_tgt' exec_tgt' *)
  (*       (SAFE': DSys.safe_state st_tgt') *)
  (*       (EXEC_TGT': DSys.exec_state _ st_tgt' exec_tgt') *)
  (*       (FMSIM': fmsim_states st_src' st_tgt') *)
  (*   , *)
  (*     <<STEP1_SRC: DSys.step _ st_src tr_h_src_raw st_src1>> /\ *)
  (*     <<FLT1_SRC: DSys.filter_nb_sysstep tr_h_src_raw = Some tr_h_src>> /\ *)
  (*     <<STEPS_SRC: msteps _ n_src st_src1 tr_t_src st_src'>> /\ *)

  (*     <<STEP1_TGT: DSys.step _ st_tgt tr_h_tgt_raw st_tgt1>> /\ *)
  (*     <<FLT1_TGT: DSys.filter_nb_sysstep tr_h_tgt_raw = Some tr_h_tgt>> /\ *)
  (*     <<STEPS_TGT: msteps _ n_tgt st_tgt1 tr_t_tgt st_tgt'>> /\ *)

  (*     <<TR_SRC_DIV: cons_each_rel tr_h_src tr_t_src tr_src>> /\ *)
  (*     <<TR_TGT_DIV: cons_each_rel tr_h_tgt tr_t_tgt tr_tgt>> /\ *)
  (*     <<TES_EQUIV: Forall2 tes_equiv tr_src tr_tgt>> /\ *)
  (*     <<EXEC_TGT_DIV: Forall3 (fun a b c => stream_app a b = c) *)
  (*                             tr_tgt exec_tgt' exec_tgt>> /\ *)

  (*     <<CONSTR_SRC_DIV: *)
  (*       Forall3 (fun a b c => stream_app a b = c) *)
  (*               tr_src *)
  (*               (constr_exec_src _ _ _ SAFE' EXEC_TGT' FMSIM') *)
  (*               (constr_exec_src _ _ _ SAFE EXEC_TGT FMSIM)>> *)
  (* . *)
  (* Proof. *)
  (*   destruct (fmsim_states_constr_src1 *)
  (*               _ _ _ SAFE EXEC_TGT FMSIM) as [aux P] eqn: CONSTR. *)
  (*   des. *)
  (*   assert (AUX: proj1_sig (fmsim_states_constr_src1 *)
  (*                             _ _ _ SAFE EXEC_TGT FMSIM) = aux). *)
  (*   { rewrite CONSTR. ss. } *)
  (*   clear CONSTR. *)

  (*   esplits; eauto. *)
  (*   instantiate (1:= AUX_FMSIM_NXT aux). *)
  (*   instantiate (1:= AUX_EXEC_TGT_NXT aux). *)
  (*   instantiate (1:= AUX_SAFE_NXT aux). *)

  (*   match goal with *)
  (*   | |- Forall3 _ _ ?c' ?c => *)
  (*     pose (cstr' := c'); pose (cstr := c) *)
  (*   end. *)
  (*   fold cstr' cstr. *)

  (*   apply Forall3_nth. i. *)

  (*   (* for lengths *) *)
  (*   assert (LEN_C': length cstr' = DSys.num_sites _ (aux_st_src_nxt aux)). *)
  (*   { subst cstr'. *)
  (*     apply constr_exec_src_length. } *)
  (*   assert (LEN_C: length cstr = DSys.num_sites _ st_src). *)
  (*   { subst cstr. *)
  (*     apply constr_exec_src_length. } *)
  (*   hexploit msteps_num_sites_eq; try apply AUX_STEPS_SRC. *)
  (*   i. des. *)
  (*   hexploit (DSys.step_prsv_num_sites sys_src). *)
  (*   { apply AUX_STEP1_SRC. } *)
  (*   i. des. *)
  (*   hexploit Forall3_length; try apply TR_SRC. i. des. *)

  (*   destruct (lt_ge_dec n (length tr_src)). *)
  (*   2: { *)
  (*     rewrite nth_error_None2 by ss. *)
  (*     rewrite nth_error_None2. *)
  (*     2: { unfold lexec_t in *. nia. } *)
  (*     rewrite nth_error_None2. *)
  (*     2: { unfold lexec_t in *. nia. } *)
  (*     econs. *)
  (*   } *)

  (*   hexploit (nth_error_Some2 _ tr_src n); ss. i. des. *)
  (*   renames e1 NTH_EX into src_n SRC_N. *)
  (*   unfold constr_exec_src in *. *)
  (*   rewrite SRC_N. *)

  (*   subst cstr'. *)
  (*   rewrite imap_nth_error_iff. ss. *)
  (*   rewrite repeat_nth_error_Some. *)
  (*   2: { unfold lexec_t in *. nia. } *)
  (*   ss. *)
  (*   subst cstr. *)
  (*   rewrite imap_nth_error_iff. ss. *)
  (*   rewrite repeat_nth_error_Some. *)
  (*   2: { unfold lexec_t in *. nia. } *)
  (*   ss. *)

  (*   eapply Forall3_nth3 in TR_SRC; eauto. des. subst. *)
  (*   econs. ss. *)
  (*   match goal with *)
  (*   | |- _ = ?c => rewrite (unfold_Stream c) *)
  (*   end. *)
  (*   ss. *)
  (*   f_equal. *)
  (*   - erewrite nth_error_nth; eauto. *)
  (*   - erewrite nth_error_nth; eauto. *)
  (*     symmetry. *)
  (*     apply constr_local_exec_src_app_cont. *)
  (* Qed. *)




  (* Lemma exec_state_src *)
  (*   : forall st_src st_tgt *)
  (*       exec_tgt *)
  (*       (SAFE : DSys.safe_state st_tgt) *)
  (*       (EXEC_TGT : DSys.exec_state sys_tgt st_tgt exec_tgt) *)
  (*       (FMSIM : fmsim_states st_src st_tgt) *)
  (*       (* (BEH_TGT : exec_behav exec_tgt beh) *), *)
  (*     DSys.exec_state _ st_src *)
  (*                     (constr_exec_src *)
  (*                        _ _ _ SAFE EXEC_TGT FMSIM). *)
  (* Proof. *)
  (*   pcofix CIH. i. pfold. *)
  (*   hexploit (constr_exec_src_des _ _ _ SAFE EXEC_TGT FMSIM). *)
  (*   i. des. *)

  (*   pose (cstr := constr_exec_src _ _ _ SAFE EXEC_TGT FMSIM). *)
  (*   pose (cstr' := constr_exec_src _ _ _ SAFE' EXEC_TGT' FMSIM'). *)
  (*   fold cstr. *)

  (*   assert (AUX: forall n (N_UB: n < length cstr'), *)
  (*              exists lexec', *)
  (*                (fun n lexec' => *)
  (*                   exists tr_t_src_n cstr'_n, *)
  (*                     <<TR_T_SRC: nth_error tr_t_src n = Some tr_t_src_n>> /\ *)
  (*                     <<CSTR'_N: nth_error cstr' n = Some cstr'_n>> /\ *)
  (*                     <<LEXEC'_EQ: lexec' = stream_app tr_t_src_n cstr'_n>>) *)
  (*                  n lexec'). *)
  (*   { fold cstr cstr' in CONSTR_SRC_DIV. *)
  (*     i. hexploit (nth_error_Some2 _ cstr' n); ss. i. des. *)
  (*     renames e1 NTH_EX into c'_n C'_N. *)

  (*     eapply Forall3_nth2 in CONSTR_SRC_DIV; eauto. i. des. *)
  (*     eapply Forall3_nth3 in TR_SRC_DIV; eauto. i. des. *)
  (*     clarify. *)
  (*     esplits; eauto. *)
  (*   } *)

  (*   apply exists_list in AUX. des. *)
  (*   renames l LIST_LEN NTH_PROP into *)
  (*           cstr_tl CSTR_TL_LEN CSTR_TL_PROP. *)

  (*   econs 2. *)
  (*   { eauto. } *)
  (*   { eauto. } *)
  (*   { instantiate (1:= cstr_tl). *)
  (*     r. apply Forall3_nth. i. *)
  (*     destruct (lt_ge_dec n (length cstr_tl)). *)
  (*     2: { *)
  (*       assert (length cstr' = DSys.num_sites _ st_src'). *)
  (*       { subst cstr'. *)
  (*         apply constr_exec_src_length. } *)
  (*       assert (length cstr = DSys.num_sites _ st_src). *)
  (*       { subst cstr. *)
  (*         apply constr_exec_src_length. } *)

  (*       hexploit msteps_num_sites_eq; try apply STEPS_SRC. *)
  (*       i. des. *)
  (*       apply Forall3_length in TR_SRC_DIV. des. *)
  (*       eapply DSys.step_prsv_num_sites in STEP1_SRC. des. *)

  (*       rewrite nth_error_None2 by nia. *)
  (*       rewrite nth_error_None2 by ss. *)
  (*       rewrite nth_error_None2. *)
  (*       2: { fold (@lexec_t sysE) in *. nia. } *)
  (*       econs. } *)

  (*     hexploit (nth_error_Some2 _ cstr_tl n). *)
  (*     { ss. } *)
  (*     i. des. renames e1 NTH_EX into cstr_tl_n CSTR_TL_N. *)
  (*     rewrite CSTR_TL_N. *)
  (*     hexploit CSTR_TL_PROP; eauto. i. des. *)
  (*     r in TR_SRC_DIV. *)
  (*     hexploit Forall3_nth2; try apply TR_SRC_DIV; eauto. *)
  (*     i. des. *)
  (*     renames e1 e3 into tr_h_src_n tr_src_n. *)
  (*     renames NTH1 NTH3 P_FA into TR_HS_N TR_N TR_CONS. *)

  (*     rewrite TR_HS_N. *)

  (*     fold cstr cstr' in CONSTR_SRC_DIV. *)
  (*     eapply Forall3_nth1 in CONSTR_SRC_DIV; eauto. *)
  (*     des. *)
  (*     renames e2 e3 into cstr'_n_tmp cstr_n. *)
  (*     renames NTH2 NTH3 P_FA into CSTR'_N_TMP CSTR_N CSTR_N_DIV. *)

  (*     fold (lexec_t sysE) in *. *)
  (*     rewrite CSTR'_N in CSTR'_N_TMP. *)
  (*     symmetry in CSTR'_N_TMP. inv CSTR'_N_TMP. *)
  (*     rewrite CSTR_N. *)

  (*     econs. ss. *)
  (*   } *)

  (*   eapply (msteps_src_tl_aux sys_src) with (cstr':= cstr'); eauto. *)
  (*   subst cstr'. *)
  (*   rewrite constr_exec_src_length. *)
  (*   apply msteps_num_sites_eq in STEPS_SRC. des. ss. *)
  (* Qed. *)


  (* Lemma fmsim_merged_inv *)
  (*       st_src st_tgt exec_tgt *)
  (*       (SAFE: DSys.safe_state st_tgt) *)
  (*       (EXEC: DSys.exec_state _ st_tgt exec_tgt) *)
  (*       (FMSIM: fmsim_states st_src st_tgt) *)
  (*   : forall n_min, *)
  (*     exists n_tgt tr_tgt exec_tgt' st_tgt' *)
  (*       tr_src st_src' *)
  (*       (SAFE': DSys.safe_state st_tgt') *)
  (*       (EXEC': DSys.exec_state _ st_tgt' exec_tgt') *)
  (*       (FMSIM': fmsim_states st_src' st_tgt') *)
  (*     , *)
  (*       <<N_TGT_GE: n_min <= n_tgt>> /\ *)
  (*       <<EXEC_TGT_DIV: Forall3 (fun a b c => stream_app a b = c) *)
  (*                               tr_tgt exec_tgt' exec_tgt>> /\ *)
  (*       <<TR_TGT_ROW_LEN: Forall (fun r => length r = n_tgt) tr_tgt>> /\ *)
  (*       (* <<STEPS_TGT: msteps _ n_tgt st_tgt tr_tgt st_tgt'>> /\ *) *)

  (*       <<TRACE_EQUIV: Forall2 tes_equiv tr_src tr_tgt>> /\ *)

  (*       <<CONSTR_SRC_DIV: *)
  (*         Forall3 (fun a b c => stream_app a b = c) *)
  (*                 tr_src *)
  (*                 (constr_exec_src _ _ _ SAFE' EXEC' FMSIM') *)
  (*                 (constr_exec_src _ _ _ SAFE EXEC FMSIM)>> *)
  (* . *)
  (* Proof. *)
  (*   i. revert st_src st_tgt exec_tgt SAFE EXEC FMSIM. *)
  (*   induction n_min as [| n_min' IH]; i; ss. *)
  (*   { exists 0. *)
  (*     exists (repeat [] (length exec_tgt)). *)
  (*     exists exec_tgt, st_tgt. *)
  (*     exists (repeat [] (length exec_tgt)). *)
  (*     exists st_src, SAFE, EXEC, FMSIM. *)
  (*     hexploit fmsim_num_sites_eq; eauto. intro NUM_SITES_EQ. *)
  (*     hexploit exec_state_len; eauto. intro EXEC_TGT_LEN. *)

  (*     splits; ss. *)
  (*     - apply Forall3_nth. i. *)
  (*       destruct (lt_ge_dec n (length exec_tgt)). *)
  (*       2: { *)
  (*         rewrite nth_error_None2. *)
  (*         2: { rewrite repeat_length. ss. } *)
  (*         rewrite nth_error_None2 by ss. *)
  (*         econs. *)
  (*       } *)
  (*       rewrite repeat_nth_error_Some by ss. *)
  (*       hexploit (nth_error_Some2 _ exec_tgt n); ss. *)
  (*       i. des. *)
  (*       unfold lexec_t in *. rewrite NTH_EX. *)
  (*       econs. ss. *)
  (*     - apply Forall_forall. *)
  (*       intros x IN. *)
  (*       apply repeat_spec in IN. subst. ss. *)
  (*     - apply Forall2_tes_equiv_refl. *)
  (*     - remember (constr_exec_src _ _ _ SAFE EXEC FMSIM) as cstr. *)

  (*       assert (CSTR_LEN: length cstr = DSys.num_sites _ st_src). *)
  (*       { subst cstr. *)
  (*         apply constr_exec_src_length. } *)

  (*       clear Heqcstr. *)
  (*       apply Forall3_nth. i. *)

  (*       destruct (lt_ge_dec n (length exec_tgt)). *)
  (*       2: { *)
  (*         rewrite nth_error_None2. *)
  (*         2: { rewrite repeat_length. ss. } *)
  (*         unfold lexec_t in *. *)
  (*         rewrite nth_error_None2 by nia. *)
  (*         econs. *)
  (*       } *)

  (*       rewrite repeat_nth_error_Some by ss. *)
  (*       hexploit (nth_error_Some2 _ cstr n). *)
  (*       { unfold lexec_t in *. nia. } *)
  (*       i. des. *)

  (*       unfold lexec_t in *. *)
  (*       rewrite NTH_EX. econs. ss. *)
  (*   } *)

  (*   generalize (constr_exec_src_des _ _ _ SAFE EXEC FMSIM). *)
  (*   i. des. *)

  (*   remember (constr_exec_src _ _ _ SAFE EXEC FMSIM) *)
  (*     as cstr eqn: CSTR. *)
  (*   clear CSTR. *)
  (*   clear SAFE EXEC FMSIM. *)
  (*   renames SAFE' EXEC_TGT' FMSIM' into SAFE1 EXEC1 FMSIM1. *)


  (*   hexploit (IH _ _ _ SAFE1 EXEC1 FMSIM1); eauto. *)
  (*   i. des. *)
  (*   exists (S n_tgt + n_tgt0). *)

  (*   assert (exists tr_tgt_tot, *)
  (*              <<TR_TGT_TOT: Forall3 (fun a b c => app a b = c) *)
  (*                                    tr_tgt tr_tgt0 tr_tgt_tot>>). *)
  (*   { cut (forall n (RANGE_N: n < length tr_tgt), *)
  (*             exists (tot_n: list (tsp * events sysE)), *)
  (*               (fun n tot_n => *)
  (*                  exists tgt_n tgt0_n, *)
  (*                    nth_error tr_tgt n = Some tgt_n /\ *)
  (*                    nth_error tr_tgt0 n = Some tgt0_n /\ *)
  (*                    tgt_n ++ tgt0_n = tot_n) *)
  (*                 n tot_n). *)
  (*     { intro AUX. *)
  (*       apply exists_list in AUX. des. *)
  (*       exists l. *)
  (*       apply Forall3_nth. i. *)
  (*       destruct (lt_ge_dec n (length l)). *)
  (*       2: { *)
  (*         apply Forall3_length in EXEC_TGT_DIV. *)
  (*         apply Forall3_length in EXEC_TGT_DIV0. des. *)
  (*         rewrite nth_error_None2 by nia. *)
  (*         rewrite nth_error_None2 by nia. *)
  (*         rewrite nth_error_None2 by ss. *)
  (*         econs. *)
  (*       } *)

  (*       hexploit (nth_error_Some2 _ l n); ss. *)
  (*       i. des. renames e1 NTH_EX into l_n L_N. *)
  (*       hexploit NTH_PROP; eauto. *)
  (*       intros (tgt_n & tgt0_n & NTH & NTH0 & APP_EQ). *)
  (*       subst. *)
  (*       rewrite L_N, NTH, NTH0. econs. ss. *)
  (*     } *)

  (*     i. *)
  (*     hexploit (nth_error_Some2 _ tr_tgt n); ss. i. des. *)
  (*     renames e1 NTH_EX into tgt_n TGT_N. *)

  (*     eapply Forall3_nth1 in EXEC_TGT_DIV; eauto. i. des. *)
  (*     renames e2 e3 into e'_n e_n. *)
  (*     renames NTH2 NTH3 into E'_N E_N. subst. *)

  (*     eapply Forall3_nth3 in EXEC_TGT_DIV0; eauto. i. des. *)
  (*     renames e1 e2 into tgt0_n e'0_n. *)
  (*     renames NTH1 NTH2 into TGT0_N E'0_N. subst. *)
  (*     esplits; eauto. *)
  (*   } *)

  (*   remember (constr_exec_src *)
  (*               _ _ _ SAFE' EXEC' FMSIM') as cstr'. *)
  (*   remember (constr_exec_src *)
  (*               _ _ _ SAFE1 EXEC1 FMSIM1) as cstr1. *)
  (*   guardH Heqcstr'. guardH Heqcstr1. *)

  (*   assert (exists tr_src_tot, *)
  (*              <<TR_SRC_TOT: Forall3 (fun a b c => app a b = c) *)
  (*                                    tr_src tr_src0 tr_src_tot>>). *)
  (*   { cut (forall n (RANGE_N: n < length tr_src), *)
  (*             exists (tot_n: list (tsp * events sysE)), *)
  (*               (fun n tot_n => *)
  (*                  exists src_n src0_n, *)
  (*                    nth_error tr_src n = Some src_n /\ *)
  (*                    nth_error tr_src0 n = Some src0_n /\ *)
  (*                    src_n ++ src0_n = tot_n) *)
  (*                 n tot_n). *)
  (*     { intro AUX. *)
  (*       apply exists_list in AUX. des. *)
  (*       exists l. *)
  (*       apply Forall3_nth. i. *)
  (*       destruct (lt_ge_dec n (length l)). *)
  (*       2: { *)
  (*         apply Forall3_length in CONSTR_SRC_DIV. *)
  (*         apply Forall3_length in CONSTR_SRC_DIV0. des. *)
  (*         rewrite nth_error_None2 by nia. *)
  (*         rewrite nth_error_None2 by nia. *)
  (*         rewrite nth_error_None2 by ss. *)
  (*         econs. *)
  (*       } *)

  (*       hexploit (nth_error_Some2 _ l n); ss. *)
  (*       i. des. renames e1 NTH_EX into l_n L_N. *)
  (*       hexploit NTH_PROP; eauto. *)
  (*       intros (src_n & src0_n & NTH & NTH0 & APP_EQ). *)
  (*       subst. *)
  (*       rewrite L_N, NTH, NTH0. econs. ss. *)
  (*     } *)

  (*     i. *)
  (*     hexploit (nth_error_Some2 _ tr_src n); ss. i. des. *)
  (*     renames e1 NTH_EX into src_n SRC_N. *)

  (*     eapply Forall3_nth1 in CONSTR_SRC_DIV; eauto. i. des. *)
  (*     renames e2 e3 into e'_n e_n. *)
  (*     renames NTH2 NTH3 into E'_N E_N. subst. *)

  (*     eapply Forall3_nth3 in CONSTR_SRC_DIV0; eauto. i. des. *)
  (*     renames e1 e2 into src0_n e'0_n. *)
  (*     renames NTH1 NTH2 into SRC0_N E'0_N. subst. *)
  (*     esplits; eauto. *)
  (*   } *)
  (*   des. *)

  (*   eexists tr_tgt_tot, _, _, tr_src_tot, _, *)
  (*   SAFE', EXEC', FMSIM'. *)
  (*   esplits; ss. *)
  (*   - nia. *)
  (*   - apply Forall3_nth. i. *)
  (*     destruct (lt_ge_dec n (length tr_tgt_tot)). *)
  (*     2: { *)
  (*       apply Forall3_length in TR_TGT_TOT. des. *)
  (*       apply Forall3_length in EXEC_TGT_DIV. des. *)
  (*       apply Forall3_length in EXEC_TGT_DIV0. des. *)
  (*       rewrite nth_error_None2 by ss. *)
  (*       rewrite nth_error_None2 by nia. *)
  (*       rewrite nth_error_None2 by nia. *)
  (*       econs. *)
  (*     } *)
  (*     hexploit (nth_error_Some2 _ tr_tgt_tot n); ss. i. des. *)
  (*     renames e1 NTH_EX into tr_tgt_tot_n TR_TGT_TOT_N. *)
  (*     eapply Forall3_nth3 in TR_TGT_TOT; eauto. i. des. *)
  (*     renames e1 e2 into tr_tgt_n tr_tgt0_n. *)
  (*     renames NTH1 NTH2 into TR_TGT_N TR_TGT0_N. *)
  (*     subst tr_tgt_tot_n. *)
  (*     eapply Forall3_nth1 in EXEC_TGT_DIV; eauto. i. des. *)
  (*     renames e2 e3 into exec_tgt'_n exec_tgt_n. *)
  (*     renames NTH2 NTH3 into EXEC_TGT'_N EXEC_TGT_N. *)
  (*     subst exec_tgt_n. *)
  (*     eapply Forall3_nth1 in EXEC_TGT_DIV0; eauto. i. des. *)
  (*     renames e2 e3 into exec_tgt'0_n exec_tgt'_n_tmp. *)
  (*     renames NTH2 NTH3 into EXEC_TGT'0_N EXEC_TGT'_N_TMP. *)
  (*     clarify. *)
  (*     rename EXEC_TGT'_N_TMP into EXEC_TGT'_N. *)

  (*     rewrite TR_TGT_TOT_N, EXEC_TGT'0_N, EXEC_TGT_N. *)
  (*     econs. apply stream_app_assoc. *)

  (*   - apply Forall_forall. *)
  (*     intros tr_tgt_tot_n TOT_N. *)
  (*     eapply In_nth_error in TOT_N. des. *)
  (*     eapply Forall3_nth3 in TR_TGT_TOT; eauto. i. des. *)
  (*     renames e1 e2 into tr_tgt_n tr_tgt0_n. *)
  (*     renames NTH1 NTH2 into TR_TGT_N TR_TGT0_N. subst. *)
  (*     rewrite app_length. *)

  (*     cut (length tr_tgt_n = S n_tgt). *)
  (*     { i. rewrite Forall_forall in TR_TGT_ROW_LEN. *)
  (*       hexploit TR_TGT_ROW_LEN. *)
  (*       { eapply nth_error_In. eauto. } *)
  (*       i. nia. *)
  (*     } *)

  (*     eapply Forall3_nth3 in TR_TGT_DIV; eauto. i. des. *)
  (*     renames e1 e2 into h_n t_n. *)
  (*     renames NTH1 NTH2 into H_N T_N. subst. ss. *)
  (*     hexploit msteps_trace_row_length; eauto. *)
  (*     rewrite Forall_forall. intro A. *)
  (*     hexploit A. *)
  (*     { eapply nth_error_In. eauto. } *)
  (*     i. nia. *)

  (*   - apply Forall2_nth. i. *)
  (*     destruct (lt_ge_dec n (length tr_src_tot)). *)
  (*     2: { *)
  (*       apply Forall3_length in TR_SRC_TOT. des. *)
  (*       apply Forall3_length in TR_TGT_TOT. des. *)
  (*       apply Forall2_length in TES_EQUIV. *)
  (*       rewrite nth_error_None2 by ss. *)
  (*       rewrite nth_error_None2 by nia. *)
  (*       econs. *)
  (*     } *)

  (*     hexploit (nth_error_Some2 _ tr_src_tot n); ss. i. des. *)
  (*     renames e1 NTH_EX into src_tot_n SRC_TOT_N. *)
  (*     eapply Forall3_nth3 in TR_SRC_TOT; eauto. i. des. *)
  (*     renames e1 e2 into src_n src0_n. *)
  (*     renames NTH1 NTH2 into SRC_N SRC0_N. subst. *)
  (*     eapply Forall2_nth1 in TES_EQUIV; eauto. i. des. *)
  (*     renames e2 NTH2 P_FA into tgt_n TGT_N EQV1. *)
  (*     eapply Forall3_nth1 in TR_TGT_TOT; eauto. i. des. *)
  (*     renames e2 NTH2 NTH3 into tgt0_n TGT0_N TGT_TOT_N. subst. *)
  (*     rewrite Forall2_nth in TRACE_EQUIV. *)
  (*     specialize (TRACE_EQUIV n). *)

  (*     assert (EQV2: tes_equiv src0_n tgt0_n). *)
  (*     { rewrite SRC0_N, TGT0_N in TRACE_EQUIV. *)
  (*       inv TRACE_EQUIV. ss. } *)

  (*     rewrite SRC_TOT_N, TGT_TOT_N. econs. *)
  (*     unfold tes_equiv, flatten_tes in *. *)
  (*     repeat rewrite map_app. repeat rewrite concat_app. *)
  (*     congruence. *)

  (*   - rewrite <- Heqcstr'. *)
  (*     clear Heqcstr1 Heqcstr'. *)
  (*     apply Forall3_nth. i. *)
  (*     destruct (lt_ge_dec n (length tr_src_tot)). *)
  (*     2: { *)
  (*       rewrite nth_error_None2 by ss. *)
  (*       apply Forall3_length in TR_SRC_TOT. *)
  (*       apply Forall3_length in CONSTR_SRC_DIV0. des. *)
  (*       apply Forall3_length in CONSTR_SRC_DIV. des. *)
  (*       rewrite nth_error_None2 by nia. *)
  (*       rewrite nth_error_None2 by nia. *)
  (*       econs. *)
  (*     } *)

  (*     hexploit (nth_error_Some2 _ tr_src_tot n); ss. i. des. *)
  (*     renames e1 NTH_EX into src_tot_n SRC_TOT_N. *)
  (*     eapply Forall3_nth3 in TR_SRC_TOT; eauto. i. des. *)
  (*     renames e1 e2 into src_n src0_n. *)
  (*     renames NTH1 NTH2 into SRC_N SRC0_N. subst. *)
  (*     eapply Forall3_nth1 in CONSTR_SRC_DIV0; eauto. i. des. *)
  (*     renames e2 e3 into c'_n c_n. *)
  (*     renames NTH2 NTH3 into C'_N C_N. subst. *)
  (*     eapply Forall3_nth1 in CONSTR_SRC_DIV; eauto. i. des. *)
  (*     renames e2 e3 into c1_n c_n_tmp. *)
  (*     renames NTH2 NTH3 into C1_N C_N_TMP. *)
  (*     clarify. rename C_N_TMP into C_N. *)
  (*     rewrite SRC_TOT_N, C'_N, C_N. *)
  (*     econs. apply stream_app_assoc. *)
  (* Qed. *)

  (* (* Lemma inftau_lexec_Cons *) *)
  (* (*       (lexec: @lexec_t sysE) ts *) *)
  (* (*   : inftau_lexec lexec <-> *) *)
  (* (*     inftau_lexec (Cons (ts, []) lexec). *) *)
  (* (* Proof. *) *)
  (* (*   split. *) *)
  (* (*   - i. pfold. econs; ss. *) *)
  (* (*     left. ss. *) *)
  (* (*   - intro CONS. punfold CONS. inv CONS. ss. pclearbot. ss. *) *)
  (* (* Qed. *) *)



  (* Lemma constr_local_src_exec_inftau *)
  (*   : forall st_src st_tgt exec_tgt *)
  (*       n exec_tgt_n *)
  (*       (SAFE: DSys.safe_state st_tgt) *)
  (*       (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt) *)
  (*       (FMSIM: fmsim_states st_src st_tgt) *)
  (*       (EXEC_TGT_N: nth_error exec_tgt n = Some exec_tgt_n) *)
  (*       (EXBEH_N: inftau_lexec exec_tgt_n) *)
  (*   , *)
  (*     inftau_lexec *)
  (*       (constr_local_exec_src *)
  (*          _ _ _ SAFE EXEC_TGT FMSIM n []). *)
  (* Proof. *)
  (*   pcofix CIH. i. *)
  (*   match goal with *)
  (*   | |- _ _ _ ?c => rewrite (unfold_Stream c) *)
  (*   end. *)
  (*   ss. *)

  (*   pose (CSTR1:= fmsim_states_constr_src1 *)
  (*                   st_src st_tgt exec_tgt SAFE EXEC_TGT FMSIM). *)
  (*   fold CSTR1. *)
  (*   destruct CSTR1. ss. des. *)
  (*   destruct x. ss. *)
  (*   pfold. *)

  (*   eapply Forall3_nth3 in EXEC_TGT_NXT; eauto. i. des. *)
  (*   renames e1 e2 into tr_tgt_n exec_tgt'_n. *)
  (*   renames NTH1 NTH2 into TR_TGT_N EXEC_TGT'_N. *)
  (*   subst exec_tgt_n. *)
  (*   apply inftau_lexec_pref_iff in EXBEH_N. des. *)

  (*   eapply Forall2_nth2 in TRC_EQV; eauto. i. des. *)
  (*   renames e1 NTH1 P_FA into tr_src_n TR_SRC_N EQV_N. *)
  (*   eapply silent_tes_equiv in EQV_N; eauto. *)

  (*   eapply Forall3_nth3 in TR_SRC; eauto. i. des. *)
  (*   renames e1 e2 into tr_h_src_n tr_t_src_n. *)
  (*   renames NTH1 NTH2 into TR_H_SRC_N TR_T_SRC_N. *)
  (*   subst tr_src_n. *)
  (*   erewrite nth_error_nth; eauto. *)
  (*   erewrite nth_error_nth; eauto. *)

  (*   econs; ss. *)
  (*   { inv EQV_N. ss. } *)
  (*   { assert (SILENT: silent_local_trace _ tr_t_src_n). *)
  (*     { inv EQV_N. ss. } *)

  (*     clear - CIH SILENT EXEC_TGT'_N INFTAU. *)
  (*     (* depgen aux_tr_t_src0. *) *)

  (*     induction tr_t_src_n as [| h t IH]; i; ss. *)
  (*     { eauto. } *)
  (*     left. *)
  (*     match goal with *)
  (*     | |- _ _ _ ?c => rewrite (unfold_Stream c) *)
  (*     end. *)
  (*     ss. *)
  (*     pfold. econs. *)
  (*     { inv SILENT. ss. } *)
  (*     eapply IH; eauto. *)
  (*     inv SILENT. ss. *)
  (*   } *)
  (* Qed. *)


  (* Lemma constr_local_src_exec_behav *)
  (*   : forall st_src st_tgt exec_tgt *)
  (*       n exec_tgt_n beh_n (* tes *) *)
  (*       pref_src beh_pref *)
  (*       (SAFE: DSys.safe_state st_tgt) *)
  (*       (EXEC_TGT: DSys.exec_state _ st_tgt exec_tgt) *)
  (*       (FMSIM: fmsim_states st_src st_tgt) *)
  (*       (EXEC_TGT_N: nth_error exec_tgt n = Some exec_tgt_n) *)
  (*       (EXBEH_N: local_exec_behav exec_tgt_n beh_n) *)
  (*       (PREF_EQUIV: flatten_tes pref_src = beh_pref) *)
  (*   , *)
  (*     local_exec_behav *)
  (*       (stream_app pref_src *)
  (*                   (constr_local_exec_src *)
  (*                      _ _ _ SAFE EXEC_TGT FMSIM n [])) *)
  (*       (colist_app beh_pref beh_n). *)
  (* Proof. *)
  (*   pcofix CIH. i. subst. *)

  (*   induction pref_src as [| h_pref t_pref IH]. *)
  (*   - ss. *)
  (*     punfold EXBEH_N. inv EXBEH_N. *)
  (*     + pfold. econs 1. *)
  (*       eapply constr_local_src_exec_inftau; eauto. *)
  (*     + pclearbot. *)
  (*       hexploit (fmsim_merged_inv _ _ _ SAFE EXEC_TGT FMSIM *)
  (*                                  (S (length tr_tau))). *)
  (*       i. des. *)
  (*       eapply Forall3_nth3 in EXEC_TGT_DIV; eauto. des. *)
  (*       renames e1 e2 into tr_tgt_n exec_tgt'_n. *)
  (*       renames NTH1 NTH2 P_FA into TR_TGT_N EXEC_TGT'_N SAPP_EQ. *)
  (*       eapply Forall_nth with (n:=n) in TR_TGT_ROW_LEN. *)
  (*       rewrite TR_TGT_N in TR_TGT_ROW_LEN. ss. *)
  (*       guardH TR_TGT_ROW_LEN. *)
  (*       eapply Forall2_nth2 in TRACE_EQUIV; eauto. des. *)
  (*       renames e1 NTH1 P_FA into tr_src_n TR_SRC_N EQV_N. *)
  (*       eapply Forall3_nth1 in CONSTR_SRC_DIV; eauto. des. *)
  (*       renames e2 e3 into cstr' cstr. *)
  (*       renames NTH2 NTH3 P_FA into CSTR' CSTR CSTR_DIV. *)
  (*       guardH CSTR_DIV. *)

  (*       unfold constr_exec_src in CSTR', CSTR. *)
  (*       rewrite imap_nth_error_iff in CSTR', CSTR. *)
  (*       rewrite repeat_nth_error_Some in CSTR'. *)
  (*       2: { *)
  (*         cut (nth_error (repeat tt (DSys.num_sites sys_src st_src')) n <> None). *)
  (*         { intro AUX. *)
  (*           apply nth_error_Some in AUX. *)
  (*           rewrite repeat_length in AUX. ss. } *)
  (*         intro NONE. rewrite NONE in CSTR'. ss. *)
  (*       } *)
  (*       rewrite repeat_nth_error_Some in CSTR. *)
  (*       2: { *)
  (*         cut (nth_error (repeat tt (DSys.num_sites sys_src st_src)) n <> None). *)
  (*         { intro AUX. *)
  (*           apply nth_error_Some in AUX. *)
  (*           rewrite repeat_length in AUX. ss. } *)
  (*         intro NONE. rewrite NONE in CSTR. ss. *)
  (*       } *)
  (*       ss. clarify. *)
  (*       rewrite <- CSTR_DIV. *)

  (*       assert (exists pref_tgt', *)
  (*                  <<TR_TGT_N_DIV: tr_tgt_n = tr_tau ++ [(ts, es)] ++ pref_tgt'>> /\ *)
  (*                  <<LEXEC'_DIV: lexec' = stream_app pref_tgt' exec_tgt'_n>>). *)
  (*       { clear - TRACE_TAU SAPP_EQ N_TGT_GE TR_TGT_ROW_LEN. *)
  (*         destruct tr_tgt_n as [| h_tr t_tr]; ss. *)
  (*         { unguardH TR_TGT_ROW_LEN. subst n_tgt. *)
  (*           exfalso. inv N_TGT_GE. } *)
  (*         assert (LEN_CMP: length tr_tau <= length t_tr). *)
  (*         { unguard. *)
  (*           subst n_tgt. *)
  (*           clear - N_TGT_GE. *)
  (*           apply Le.le_S_n. ss. *)
  (*         } *)

  (*         clear N_TGT_GE TR_TGT_ROW_LEN n_tgt. *)
  (*         depgen t_tr. revert h_tr. *)

  (*         induction tr_tau as [| h t IH]; i; ss. *)
  (*         - clarify. *)
  (*           esplits; eauto. *)
  (*         - assert (h = h_tr /\ *)
  (*                   <<STR_EQ: stream_app t_tr exec_tgt'_n = *)
  (*                             stream_app t (Cons (ts, es) lexec')>>). *)
  (*           { clarify. } *)
  (*           des. subst h. *)

  (*           inv TRACE_TAU. *)
  (*           destruct h_tr as [ts_h []]; ss. *)
  (*           destruct t_tr; ss. *)
  (*           { inv LEN_CMP. } *)

  (*           hexploit IH; eauto. *)
  (*           { apply Le.le_S_n. ss. } *)
  (*           i. des. *)
  (*           esplits; eauto. *)
  (*           rewrite <- TR_TGT_N_DIV. ss. *)
  (*       } *)

  (*       des. *)
  (*       guardH TR_TGT_N_DIV. guardH LEXEC'_DIV. *)

  (*       eapply local_exec_beh_div in LOCAL_EXEC_BEHAV_REST; eauto. *)
  (*       des. renames beh'0 EBEH' into beh_nxt EBEH_NXT. *)
  (*       guardH BEH_DIV. *)

  (*       rewrite BEH_DIV. *)
  (*       rewrite <- colist_app_assoc. *)

  (*       assert (exists tr_tau_src es_src pref_src', *)
  (*                  <<TR_SRC_N_DIV: tr_src_n = tr_tau_src ++ [(ts, es_src)] ++ pref_src'>> /\ *)
  (*                  <<TAU_SRC: silent_local_trace sysE tr_tau_src>> /\ *)
  (*                  <<ES_SRC_NONNIL: es_src <> []>>). *)
  (*       { clear - EQV_N TR_TGT_N_DIV EVENTS_NONNIL TRACE_TAU. *)
  (*         rewrite TR_TGT_N_DIV in EQV_N. clear TR_TGT_N_DIV. *)
  (*         unfold tes_equiv in EQV_N. ss. *)
  (*         depgen tr_tau. *)
  (*         clear tr_tgt_n. *)

  (*         induction tr_src_n as [| h t IH]; i; ss. *)
  (*         { exfalso. *)
  (*           unfold flatten_tes in EQV_N. ss. *)
  (*           rewrite map_app in EQV_N. ss. *)
  (*           rewrite concat_app in EQV_N. *)
  (*           fold (flatten_tes tr_tau) in EQV_N. *)

  (*           assert (AUX: flatten_tes tr_tau = []). *)
  (*           { apply flatten_silent_local_trace_iff. ss. } *)
  (*           rewrite AUX in EQV_N. ss. *)
  (*           destruct es; ss. *)
  (*         } *)

  (*         destruct h as [tstamp [|e_h e_t]]; ss. *)
  (*         { unfold flatten_tes at 1 in EQV_N. ss. *)
  (*           hexploit IH; eauto. i. des. *)
  (*           exists ((tstamp, [])::tr_tau_src). *)
  (*           esplits; eauto; ss. *)
  (*           - f_equal. eauto. *)
  (*           - econs; ss. *)
  (*         } *)
  (*         assert (tstamp = ts). *)
  (*         { clear - EQV_N EVENTS_NONNIL TRACE_TAU. *)
  (*           depgen tr_tau. *)
  (*           induction tr_tau; i; ss. *)
  (*           { unfold flatten_tes in EQV_N. ss. *)
  (*             destruct es; ss. clarify. } *)
  (*           inv TRACE_TAU. *)
  (*           destruct a; ss. clarify. *)
  (*           eapply IHtr_tau; ss. *)
  (*         } *)
  (*         subst tstamp. *)

  (*         exists []. esplits; ss. *)
  (*       } *)
  (*       des. guardH TR_SRC_N_DIV. *)
  (*       rewrite TR_SRC_N_DIV. *)

  (*       rewrite stream_app_assoc. ss. *)
  (*       rewrite colist_app_assoc. *)

  (*       pfold. econs 2; try reflexivity; ss. *)
  (*       2: { instantiate (1:= colist_app *)
  (*                               (flatten_tes pref_src') beh_nxt). *)
  (*            rewrite <- colist_app_assoc. *)
  (*            rewrite <- colist_app_assoc. *)

  (*            rewrite TR_SRC_N_DIV in EQV_N. *)
  (*            rewrite TR_TGT_N_DIV in EQV_N. *)
  (*            unfold tes_equiv, flatten_tes in EQV_N. *)
  (*            repeat rewrite map_app in EQV_N. *)
  (*            do 2 rewrite concat_app in EQV_N. *)

  (*            replace (concat (map flatten_te tr_tau_src)) *)
  (*              with (@nil (tsp * event sysE)) in EQV_N. *)
  (*            2: { symmetry. *)
  (*                 apply flatten_silent_local_trace_iff. ss. } *)
  (*            replace (concat (map flatten_te tr_tau)) *)
  (*              with (@nil (tsp * event sysE)) in EQV_N. *)
  (*            2: { symmetry. *)
  (*                 apply flatten_silent_local_trace_iff. ss. } *)
  (*            ss. *)
  (*            unfold flatten_tes. *)
  (*            rewrite EQV_N. ss. *)
  (*       } *)
  (*       { eauto. } *)

  (*   - i. *)
  (*     match goal with *)
  (*     | |- paco2 _ _ ?c1 _ => *)
  (*       rewrite (unfold_Stream c1) *)
  (*     end. ss. *)
  (*     unfold flatten_tes. ss. *)

  (*     rewrite colist_app_assoc. *)
  (*     destruct h_pref as [ts_h es_h]. *)

  (*     destruct es_h as [| h_e t_e]; ss. *)
  (*     + punfold IH. inv IH. *)
  (*       * fold (flatten_tes t_pref). *)
  (*         match goal with *)
  (*         | H: cnil = _ |- _ => rewrite <- H *)
  (*         end. *)
  (*         pfold. econs 1. *)
  (*         apply inftau_lexec_Cons. ss. *)
  (*       * rewrite LOCAL_EXEC_PREFIX. *)
  (*         match goal with *)
  (*         | |- _ _ _ (Cons ?a (stream_app ?l ?c)) _ => *)
  (*           replace (Cons a (stream_app l c)) with *)
  (*               (stream_app (a::l) c) by ss *)
  (*         end. *)
  (*         pfold. econs 2; try reflexivity; eauto. *)
  (*         r. econs; ss. *)

  (*     + pfold. *)
  (*       match goal with *)
  (*       | |- _ _ _ ?c _ => *)
  (*         replace c with (stream_app [] c) by ss *)
  (*       end. *)
  (*       econs 2; try reflexivity; ss. *)
  (*       left. eauto. *)
  (* Qed. *)

  Lemma fmsim_state_adequacy
        st_src st_tgt
        (SAFE: DSys.safe_state st_tgt)
        (FMSIM: fmsim_states st_src st_tgt)
    : DSys.behav_state _ st_tgt <1= DSys.behav_state _ st_src.
  Proof.
    eapply fmsim_states_impl_gmsim_states in FMSIM; eauto.
    eapply gmsim_state_adequacy. eauto.
  Qed.
  (*   intros beh BEH_TGT. *)
  (*   r in BEH_TGT. des. *)
  (*   renames exec EXEC_ST EXEC_BEH into exec_tgt EXEC_TGT BEH_TGT. *)
  (*   r. exists (constr_exec_src _ _ _ SAFE EXEC_TGT FMSIM). *)
  (*   splits. *)
  (*   - eapply exec_state_src. *)
  (*   - r. *)
  (*     apply Forall2_nth. *)
  (*     i. destruct (lt_ge_dec n (DSys.num_sites _ st_src)). *)
  (*     2: { *)
  (*       rewrite nth_error_None2. *)
  (*       2: { rewrite constr_exec_src_length. ss. } *)
  (*       rewrite nth_error_None2. *)
  (*       2: { *)
  (*         eapply fmsim_num_sites_eq in FMSIM; eauto. *)
  (*         eapply exec_state_len in EXEC_TGT. *)
  (*         r in BEH_TGT. apply Forall2_length in BEH_TGT. *)
  (*         nia. *)
  (*       } *)
  (*       econs. *)
  (*     } *)

  (*     r in BEH_TGT. *)
  (*     hexploit (nth_error_Some2 _ beh n). *)
  (*     { apply Forall2_length in BEH_TGT. *)
  (*       eapply fmsim_num_sites_eq in FMSIM; eauto. *)
  (*       apply exec_state_len in EXEC_TGT. *)
  (*       nia. } *)
  (*     i. des. renames e1 NTH_EX into beh_n BEH_N. *)
  (*     eapply Forall2_nth2 in BEH_TGT; eauto. *)
  (*     i. des. *)
  (*     renames e1 NTH1 P_FA into exec_tgt_n EXEC_TGT_N EXBEH_N. *)
  (*     rewrite BEH_N. *)

  (*     unfold constr_exec_src. *)
  (*     rewrite imap_nth_error_iff. ss. *)
  (*     rewrite repeat_nth_error_Some. *)
  (*     2: { eapply fmsim_num_sites_eq in FMSIM; eauto. } *)
  (*     ss. econs. *)
  (*     replace beh_n with (colist_app [] beh_n) by ss. *)
  (*     match goal with *)
  (*     | |- _ ?c _ => *)
  (*       replace c with (stream_app [] c) by ss *)
  (*     end. *)
  (*     eapply constr_local_src_exec_behav; eauto. *)
  (* Qed. *)

  Lemma fmsim_adequacy
        (SAFE_SYS: DSys.safe sys_tgt)
        (FMSIM: fmsim)
    : DSys.behav_sys sys_tgt <1= DSys.behav_sys sys_src.
  Proof.
    eapply fmsim_impl_gmsim in FMSIM; eauto.
    apply gmsim_adequacy. ss.
  Qed.
  (*   intros beh BEH_SYS_TGT. *)
  (*   inv FMSIM. inv SAFE_SYS. *)

  (*   red in BEH_SYS_TGT. des. *)
  (*   { exfalso. eauto. } *)
  (*   clear dependent st_i. *)

  (*   econs 2. *)
  (*   hexploit SIM_INIT_STATES; eauto. i. des. *)
  (*   hexploit fmsim_state_adequacy; eauto. *)
  (* Qed. *)

End SIM.
