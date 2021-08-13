From Paco Require Import paco.
From ITree Require Import ITree.

Require Import Arith List Lia.

Require Import sflib.
Require Import StdlibExt.
Require Import SysSem.

Require Import DiscreteTimeModel IPModel.

Require Import NWSysModel.
(* Require Import ProgSem OSModel OSNodes. *)

(* Require Import SyncSysModel. *)
(* Require Import NWSyncNode. *)

Require Import MSteps.
Require Import FMSim.

Set Nested Proofs Allowed.

(* Definition flatten_tes {E} (tes: tsp * events E) *)
(*   : list (tsp * event E) := *)
(*   let (ts, es) := tes in *)
(*   List.map (fun e => (ts, e)) es. *)

(* Fixpoint flatten_ftrace {E} (tr: list (tsp * events E)) *)
(*   : list (tsp * event E) := *)
(*   match tr with *)
(*   | [] => [] *)
(*   | h::t => flatten_tes h ++ flatten_ftrace t *)
(*   end. *)

(* Definition ftrace_equiv {E} *)
(*            (tr1 tr2: list (tsp * events E)): Prop := *)
(*   flatten_ftrace tr1 = flatten_ftrace tr2. *)


Lemma Forall_safe_state (E: Type -> Type)
      tm (nsts: list (@Node.state E))
      tes ops nsts' dpms
      (WF_DPMS: Forall (fun dm => Packet.msg_wf (snd dm)) dpms)
      (SAFE_STATES: Forall (Node.safe_state tm) nsts)
      (STEPS: Forall4 (Node.step tm dpms) nsts tes ops nsts')
: <<SAFE_STATES': Forall (Node.safe_state (DTime.succ tm)) nsts'>> /\
  <<WF_OPS: Forall (option_rel1 Packet.wf) ops>>.
Proof.
  hexploit Forall4_length; try apply STEPS. i. des.

  cut (forall n (N_UB: n < length nsts),
          exists nst' op,
            nth_error nsts' n = Some nst' /\
            nth_error ops n = Some op /\
            Node.safe_state (DTime.succ tm) nst' /\
            option_rel1 Packet.wf op).
  { intro X.
    esplits.
    - apply Forall_nth. i.
      destruct (lt_ge_dec n (length nsts)).
      2: { rewrite nth_error_None2 by nia. ss. }
      hexploit X; eauto. i. des.

      match goal with
      | H: nth_error nsts' n = Some _ |- _ =>
        rewrite H in *; ss
      end.
    - apply Forall_nth. i.
      destruct (lt_ge_dec n (length nsts)).
      2: { rewrite nth_error_None2 by nia. ss. }
      hexploit X; eauto. i. des.

      match goal with
      | H: nth_error ops n = Some _ |- _ =>
        rewrite H in *; ss
      end.
  }
  i.
  hexploit (nth_error_Some2 _ nsts n); eauto.
  i. des. renames e1 NTH_EX into nst NST.
  eapply Forall4_nth1 in STEPS; eauto. des.
  renames e2 e3 e4 into te op nst'.
  inv P_FA.

  rewrite Forall_nth in SAFE_STATES.
  specialize (SAFE_STATES n).
  rewrite NST in SAFE_STATES. ss.
  inv SAFE_STATES. existT_elim. subst.
  punfold SAFE_ISTATE.
  2: { apply Node.safe_istate_monotone. }
  inv SAFE_ISTATE.
  hexploit SAFE_NEXT; eauto.
  { unfold Node.distr_msgs_to.
    apply Forall_forall.
    rewrite Forall_forall in WF_DPMS.
    intros pm IN_F.
    apply filtermap_in in IN_F.
    destruct IN_F as (dpm & IN_DPMS & CHGET).
    destruct dpm as (ip_dest & pm').
    hexploit WF_DPMS; eauto. i. ss.
    unfold Node.chget_pm_by_dest in CHGET. ss.
    desf.
  }
  i. des. pclearbot.
  esplits; eauto.
  econs. eauto.
Qed.


Section NODE_LOCAL_STEPS.
  Context {sysE: Type -> Type}.
  Variable node: @Node.t sysE.

  Inductive node_local_steps (gtm: DTime.t)
    : list (list Packet.msg_t) ->
      node.(Node.istate) ->
      list (tsp * events sysE) -> list (Packet.t ?) ->
      node.(Node.istate) -> Prop :=
  | NodeLocalStep_Base nst
    : node_local_steps gtm [] nst [] [] nst
  | NodeLocalStep_Step
      nst nst1 te_r1 te1 opkt1 pm1
      pms2 tess2 opkts2 nst'
      (STEP: Node.istep node gtm pm1 nst te_r1 opkt1 nst1)
      (NOT_NB: DSys.filter_nb_localstep te_r1 = Some te1)
      (* (ACCEPT: Node.accept_packets node gtm pm1 nst1 nst2) *)
      (REST_STEPS: node_local_steps (DTime.succ gtm) pms2
                                    nst1 tess2 opkts2 nst')
    : node_local_steps gtm (pm1::pms2)
                       nst (te1::tess2) (opkt1::opkts2) nst'.

End NODE_LOCAL_STEPS.


Section NWSYS_CONCRETE_STEPS.
  Context {sysE: Type -> Type}.
  Context `{rnws_params}.

  Variable nwsys: @NWSys.t sysE.
  Variable tm_init: nat.
  Let state: Type := @NWSys.state sysE.
  Let sys: @DSys.t sysE:= NWSys.as_dsys nwsys tm_init.

  Inductive nwsys_csteps
    : state -> list (list (ip_t * Packet.msg_t)) ->
      list (list (tsp * events sysE)) ->
      list (list Packet.t?) -> list state -> Prop :=
  | CSteps_Base st
    : nwsys_csteps st [] [] [] []
  | CSteps_Step
      tm nw nsts
      nw1 dpms
      tes1_r ops1 nsts1 nw' tes1 st1
      dpmss tess opss sts
      (NW_DISTR: NW.distr nw = (nw1, dpms))
      (LOCAL_STEPS: Forall4 (Node.step tm dpms)
                            nsts tes1_r ops1 nsts1)
      (NW_STEP: NW.gather nw1 (filtermap id ops1) nw')

      (FNB_OK: DSys.filter_nb_sysstep tes1_r = Some tes1)
      (STATE1: st1 = NWSys.State (DTime.succ tm) nw' nsts1)
      (REST_CSTEPS: nwsys_csteps st1 dpmss tess opss sts)
    : nwsys_csteps (NWSys.State tm nw nsts)
                   (dpms :: dpmss) (tes1::tess)
                   (ops1::opss) (st1::sts)
  .

  Lemma csteps_length
        st dms tess opss sts
        (CSTEPS: nwsys_csteps st dms tess opss sts)
    : length dms = length tess /\
      length dms = length opss /\
      length dms = length sts.
  Proof.
    induction CSTEPS; ss.
    des.
    splits; eauto.
  Qed.

  Lemma msteps_csteps
        n st tr st'
        (MSTEPS: msteps sys n st tr st')
    : exists dpmss trs_conc ops sts,
      <<CSTEPS: nwsys_csteps st dpmss trs_conc ops sts>> /\
      (* <<LEN_TRS_CONC: length trs_conc = n>> /\ *)
      (* <<LEN_STATES: length sts = n>> /\ *)
      <<TRACE_TRANSPOSE: transpose (DSys.num_sites _ st) n
                                   tr trs_conc>> /\
      <<LAST_STATE: last' sts st = st'>>
  .
  Proof.
    induction MSTEPS; ss.
    { subst es.
      esplits; ss.
      - econs 1.
      - eapply transpose_column. ss.
      - ss.
    }
    des.

    hexploit transpose_cons_each; eauto. intro TRANSP_TR.
    hexploit (DSys.step_prsv_num_sites sys); eauto. i. des.
    ss.
    rewrite NUM_SITES_AFTER in TRANSP_TR.

    inv STEP.

    esplits; eauto.
    - econs; eauto.
    - ss.
  Qed.

End NWSYS_CONCRETE_STEPS.


Section NWSYS_CONC_STEP_TO_LOCAL.
  Context {sysE: Type -> Type}.
  Context `{rnws_params}.

  Variable nsys: @NWSys.t sysE.
  Let state: Type := @NWSys.state sysE.

  Lemma nwsys_cstep_to_local
        (st: state) dmss trs_c opss sts nd ip_n
        (CONC_STEPS: nwsys_csteps st dmss trs_c opss sts)
        (NODE_IP: Node.ip_addr nd = ip_n)
    : forall tm nw nsts idx ist
        (STATE: st = NWSys.State tm nw nsts)
        (NODE_STATE: nth_error nsts idx =
                     Some (Node.State nd ist))
        (NODES_SAFE: Forall (Node.safe_state tm) nsts)
        (WF_NW: NW.wf nw)
    ,
      exists dmss_f tes ops ist',
      <<DMSGS_TO: Forall2 (fun dms dms_f =>
                             Node.distr_msgs_to ip_n dms = dms_f)
                          dmss dmss_f>> /\
      <<WF_DMSGS_F: Forall (Forall Packet.msg_wf) dmss_f>> /\
      <<TRACE_N: Forall2 (fun tes te => nth_error tes idx = Some te)
                         trs_c tes>> /\
      <<OUTPKTS_N: Forall2 (fun ops op => nth_error ops idx =
                                       Some op)
                           opss ops>> /\
      <<STATE'_N: nth_error (NWSys.nodes (last' sts st)) idx =
                  Some (Node.State nd ist')>> /\
      <<LOCAL_STEPS: node_local_steps nd tm dmss_f
                                      ist tes ops ist'>>.
  Proof.
    induction CONC_STEPS.
    { i. exists [], [], [], ist.
      subst st.
      esplits; ss.
      econs. }

    i. symmetry in STATE. clarify.

    hexploit NW.wf_distr_preserve; eauto. i. des.
    hexploit (Forall_safe_state); eauto. i. des.

    eapply Forall4_nth1 in LOCAL_STEPS; eauto. des.
    renames e2 e3 e4 into te_r op nst'.
    renames NTH2 NTH3 NTH4 into TE OP NST'.
    inv P_FA. existT_elim. subst.

    assert (exists te, <<TE: nth_error tes1 idx = Some te>> /\
                  <<FLT_TE_R: DSys.filter_nb_localstep te_r = Some te>>).
    { unfold DSys.filter_nb_sysstep in FNB_OK.
      apply deopt_list_Some_iff in FNB_OK.

      hexploit (nth_error_Some2 _ tes1 idx).
      { cut (length tes1 = length tes1_r).
        { intro R. rewrite R.
          apply nth_error_Some. congruence. }
        apply f_equal with (f:=(@length _)) in FNB_OK.
        do 2 rewrite map_length in FNB_OK. ss.
      }
      i. des.
      esplits; eauto.

      cut (nth_error (map DSys.filter_nb_localstep tes1_r) idx =
           Some (Some e1)).
      { intro NTH_MAP.
        apply map_nth_error_iff in NTH_MAP. des.
        clarify. }

      rewrite <- FNB_OK.
      apply map_nth_error_iff.
      esplits; eauto.
    }
    des.

    hexploit IHCONC_STEPS.
    { reflexivity. }
    { eauto. }
    { ss. }
    { eapply NW.wf_gather_preserve; eauto.
      apply Forall_filter_id. ss. }
    i. des.
    esplits; eauto.
    - econs; eauto.
      unfold Node.distr_msgs_to.
      apply Forall_forall.
      intros pm IN_F.
      apply filtermap_in in IN_F. des.
      unfold Node.chget_pm_by_dest in *. desf.
      rewrite Forall_forall in DMSGS_WF.
      hexploit DMSGS_WF; eauto.
    - econs; eauto.
  Qed.

End NWSYS_CONC_STEP_TO_LOCAL.



Section SIM.
  Context `{rnws_params}.
  Context {sysE: Type -> Type}.

  Hint Resolve Node.safe_istate_monotone: paco.

  Section SIM_NODES.

    Variable node_src node_tgt: @Node.t sysE.
    Let ip: ip_t := Node.ip_addr node_src.

    Inductive _fmsim_nstates
              (sim: DTime.t -> node_src.(Node.istate) ->
                    node_tgt.(Node.istate) -> Prop)
              (gtm: DTime.t)
              (nst_src: node_src.(Node.istate))
              (nst_tgt: node_tgt.(Node.istate)): Prop :=
      FMSim_NodeStates
        n (N_POS: 0 < n)
        (SIM: forall nst_tgt'
                ftr_tgt opkts
                (dmss: list (list Packet.msg_t))
                (POS: length dmss = n)
                (WF_DMSS: List.Forall (List.Forall Packet.msg_wf) dmss)
                (STEPS_TGT: node_local_steps
                              node_tgt gtm dmss nst_tgt
                              ftr_tgt opkts nst_tgt'),
            exists ftr_src nst_src',
              <<STEPS_SRC: node_local_steps
                             node_src gtm dmss nst_src
                             ftr_src opkts nst_src'>> /\
              <<FTR_EQUIV: tes_equiv ftr_src ftr_tgt>> /\
              <<WF_OUT_PKTS: List.Forall
                               (option_rel1 Packet.wf) opkts >> /\
              <<SIM: sim (DTime.uadd gtm n)
                         nst_src' nst_tgt'>>)
    .

    Hint Constructors _fmsim_nstates: paco.

    Lemma fmsim_nstates_monotone
      : monotone3 _fmsim_nstates.
    Proof.
      ii. inv IN. econs; eauto.
      ii. hexploit SIM; eauto. i. des.
      esplits; eauto.
    Qed.

    Hint Resolve fmsim_nstates_monotone: paco.

    Definition fmsim_nstates
      : DTime.t -> node_src.(Node.istate) ->
        node_tgt.(Node.istate) -> Prop :=
      paco3 _fmsim_nstates bot3.

    Definition fmsim_nodes: Prop :=
      <<NODE_IPS_EQ: Node.ip_addr node_src = Node.ip_addr node_tgt>> /\
      forall (gtm_init: DTime.t) ist_tgt
        (INIT_TGT: node_tgt.(Node.init_istate) ist_tgt),
        exists ist_src,
          <<INIT_SRC: node_src.(Node.init_istate) ist_src>> /\
          <<SIM_STATES: fmsim_nstates gtm_init ist_src ist_tgt>>
    .

    (* simple sim *)
    Inductive _sim_nstates
              (sim: DTime.t -> node_src.(Node.istate) ->
                    node_tgt.(Node.istate) -> Prop)
              (gtm: DTime.t)
              (nst_src: node_src.(Node.istate))
              (nst_tgt: node_tgt.(Node.istate)): Prop :=
      Sim_NodeStates
        (SIM: forall nst_tgt'
                te_r_tgt te_tgt opkt
                (dms: list Packet.msg_t)
                (WF_DMS: List.Forall Packet.msg_wf dms)
                (STEP_TGT: Node.istep node_tgt gtm dms
                                      nst_tgt te_r_tgt opkt nst_tgt')
                (NOT_NB_TGT: DSys.filter_nb_localstep te_r_tgt = Some te_tgt)
          ,
            exists te_r_src te_src nst_src',
              <<STEP_SRC: Node.istep node_src gtm dms
                                     nst_src te_r_src opkt nst_src'>> /\
              <<NOT_NB_SRC: DSys.filter_nb_localstep te_r_src = Some te_src>> /\
              <<TES_EQUIV: flatten_te te_src = flatten_te te_tgt>> /\
              <<WF_OUT_PKTS: option_rel1 Packet.wf opkt >> /\
              <<SIM: sim (DTime.succ gtm) nst_src' nst_tgt'>>)
    .

    Hint Constructors _sim_nstates: paco.

    Lemma sim_nstates_monotone: monotone3 _sim_nstates.
    Proof.
      ii. inv IN. econs.
      i. hexploit SIM; eauto.
      i. des.
      esplits; eauto.
    Qed.

    Hint Resolve sim_nstates_monotone: paco.

    Definition sim_nstates
      : DTime.t -> node_src.(Node.istate) ->
        node_tgt.(Node.istate) -> Prop :=
      paco3 _sim_nstates bot3.

    Lemma sim_nstates_impl_fmsim
      : sim_nstates <3= fmsim_nstates.
    Proof.
      pcofix CIH. i.
      pfold. econs; eauto.
      i. destruct dmss as [| dms []]; ss.
      inv STEPS_TGT; ss.
      inv REST_STEPS; ss.
      inv WF_DMSS.

      punfold PR.
      inv PR.
      hexploit SIM; try apply STEP; eauto.
      i. des.
      pclearbot.

      esplits; eauto.
      { econs; eauto.
        econs. }
      (*   { clear - NOT_NB TES_EQUIV. *)
      (*     unfold DSys.filter_nb_localstep in *. *)
      (*     destruct te_r1 as [tsp1 es_r1]. *)
      (*     destruct te_r_src as [tsp2 es_r2]. ss. *)

      (*     destruct (deopt_list (map DSys.filter_nb1 es_r1)) eqn: ES1_FNB; ss. *)
      (*     apply deopt_list_Some_iff in ES1_FNB. *)

      (*     cut (deopt_list (map DSys.filter_nb1 es_r2) = Some l). *)
      (*     { intro R. rewrite R. ss. } *)

      (*     apply deopt_list_Some_iff. *)
      (*     rewrite ES1_FNB. *)
      (*     clear - TES_EQUIV. *)

      (*     depgen es1. *)
      (*     induction es2; i; ss. *)
      (*     - destruct es1; ss. *)
      (*     - destruct es1; ss. *)
      (*       clarify. f_equal. eauto. *)
      (*   } *)
      (*   econs. *)
      (* } *)
      { r. unfold flatten_tes. ss.
        congruence. }

      right.
      apply CIH.
      rewrite DTime_uadd_one. eauto.
    Qed.

  End SIM_NODES.


  Section SWITCH.
    Variable gtm_init_ns: nat.
    Variable nds1 nds2: list (@Node.t sysE).
    Variable nd_src nd_tgt: @Node.t sysE.

    Hypothesis SIM_NODES: fmsim_nodes nd_src nd_tgt.
    Hypothesis SAFE_NODES1: Forall Node.safe nds1.
    Hypothesis SAFE_NODES2: Forall Node.safe nds2.
    (* Hypothesis SAFE_ND_SRC: Node.safe nd_src. *)
    Hypothesis SAFE_ND_TGT: Node.safe nd_tgt.

    Let sys_src: NWSys.t := nds1 ++ [nd_src] ++ nds2.
    Let sys_tgt: NWSys.t := nds1 ++ [nd_tgt] ++ nds2.

    Let dsys_src := NWSys.as_dsys sys_src gtm_init_ns.
    Let dsys_tgt := NWSys.as_dsys sys_tgt gtm_init_ns.

    (* Hypothesis SAFE_SYS_TGT: DSys.safe dsys_tgt. *)


    Lemma constr_srcsteps_aux
          st dpmss trs_c opss sts ip_n idx nsites
          (CSTEPS: nwsys_csteps st dpmss trs_c opss sts)
          (NODE_IP: Node.ip_addr nd_tgt = ip_n)
          (IDX: idx = length nds1)
          (NUM_SITES: nsites = length sys_tgt)
      : forall tr_src_p tr_tgt_p
          tm nw nsts scnt
          ist_tgt (nsts_l nsts_r: list Node.state)
          trs_tgt trs_l trs_r tr_tgt
          dmss_f ist_src tr_src ops ist_src'

          (TRANSPOSE_TRS: transpose nsites scnt trs_tgt trs_c)
          (STEP_COUNTS: length trs_c = scnt)
          (STATE: st = NWSys.State tm nw nsts)
          (SAFE_NODES: Forall (Node.safe_state tm) nsts)
          (* (SAFE_NODE_SRC: Node.safe_istate _ tm ist_src) *)
          (WF_NW: NW.wf nw)

          (NODE_STATES: nsts = nsts_l ++ [Node.State nd_tgt ist_tgt] ++ nsts_r)
          (DMSGS_TO : Forall2
                        (fun dms dms_f =>
                           Node.distr_msgs_to ip_n dms = dms_f)
                        dpmss dmss_f)
          (WF_DMSGS_F : Forall (Forall Packet.msg_wf) dmss_f)
          (LOCAL_STEPS_SRC: node_local_steps
                              nd_src tm dmss_f ist_src
                              tr_src ops ist_src')
          (TES_EQUIV : tes_equiv (tr_src_p ++ tr_src)
                                       (tr_tgt_p ++ tr_tgt))
          (TR_TGT: trs_tgt = trs_l ++ [tr_tgt] ++ trs_r)
          (* Forall2 *)
          (*          (fun tes te => nth_error tes idx = Some te) *)
          (*          trs_c tr_tgt) *)
          (OUTPKTS_N : Forall2 (fun ops op =>
                                  nth_error ops idx = Some op)
                               opss ops)
          (WF_OUT_PKTS : Forall (option_rel1 Packet.wf) ops)
          (LEN_NSTS: length nsts = length sys_tgt)
          (LEN_TRS_L: length trs_l = idx)
          (LEN_NSTS_L: length nsts_l = idx)
      ,
        exists (st_src' : NWSys.state)
          (nw': NW.t) (nsts_l' nsts_r': list (@Node.state sysE))
          (ist_tgt': Node.istate nd_tgt)
          (tm': DTime.t)
      ,
        <<MSTEPS_SRC: msteps dsys_src scnt
                             (NWSys.State tm nw
                                          (nsts_l ++ [Node.State nd_src ist_src] ++ nsts_r))
                             (trs_l ++ [tr_src] ++ trs_r)
                             st_src'>> /\
        (* <<FTRL_EQUIV: Forall2 ftrl_equiv trs_src trs_tgt>> /\ *)
        <<TM': tm' = DTime.uadd tm (length trs_c)>> /\
        <<ST_SRC': st_src' =
                   NWSys.State tm' nw'
                               (nsts_l' ++ [Node.State nd_src ist_src'] ++ nsts_r')>> /\
        <<ST_TGT': last' sts st =
                   NWSys.State tm' nw'
                               (nsts_l' ++ [Node.State nd_tgt ist_tgt'] ++ nsts_r')>> /\
        <<NODES_SAFE1: Forall (Node.safe_state tm') nsts_l'>> /\
        <<NODES_SAFE2: Forall (Node.safe_state tm') nsts_r'>> /\
        (* <<IST_SRC_SAFE1: Node.safe_istate _ tm' ist_src'>> /\ *)
        <<IST_TGT_SAFE1: Node.safe_istate _ tm' ist_tgt'>> /\
        <<WF_NW': NW.wf nw'>> /\
        <<LEN_NSTS1': length nsts_l' = length nsts_l>> /\
        <<LEN_NSTS2': length nsts_r' = length nsts_r>>
    .
    Proof.
      guardH NODE_IP. guardH IDX. guardH NUM_SITES.
      induction CSTEPS.
      { i. ss. clarify.
        rewrite DTime_uadd_zero.
        inv DMSGS_TO. inv OUTPKTS_N.
        inv LOCAL_STEPS_SRC.
        rename ist_src' into ist_src.

        (* assert (trs_tgt = repeat [] nsites). *)
        (* { hexploit transpose_dims; eauto. i. des. *)
        (*   apply nth_eq_list_eq. i. *)
        (*   destruct (lt_ge_dec n nsites); ss. *)
        (*   2: { rewrite nth_error_None2 by nia. *)
        (*        rewrite nth_error_None2. *)
        (*        2: { rewrite repeat_length. ss. } *)
        (*        ss. *)
        (*   } *)
        (*   hexploit (nth_error_Some2 _ trs_tgt n). *)
        (*   { nia. } *)
        (*   i. des. *)
        (*   rewrite Forall_nth in NUM_COLS; eauto. *)
        (*   specialize (NUM_COLS n). *)
        (*   rewrite NTH_EX in NUM_COLS. ss. *)
        (*   destruct e1; ss. *)
        (*   rewrite NTH_EX. ss. *)
        (*   rewrite repeat_nth_error_Some by ss. *)
        (*   ss. *)
        (* } *)
        (* subst trs_tgt. *)

        apply Forall_app_inv in SAFE_NODES.
        destruct SAFE_NODES as (SAFE_NSTS_L & SAFE_NODES').

        assert (<<SAFE_X: Node.safe_state tm (Node.State nd_tgt ist_tgt)>> /\
                <<SAFE_NSTS_R: Forall (Node.safe_state tm) nsts_r>>).
        { inv SAFE_NODES'. ss. }
        des.

        assert (trs_l = repeat [] (length nsts_l) /\
                trs_r = repeat [] (length nsts_r) /\
                tr_tgt = []).
        {
          hexploit transpose_dims; eauto. i. des.
          rewrite Forall_forall in NUM_COLS.

          splits.
          - apply constr_repeat; eauto.
            apply Forall_forall.
            intros x IN.
            hexploit NUM_COLS.
            { apply in_or_app. left. eauto. }
            destruct x; ss.
          - apply constr_repeat; eauto.
            { rewrite app_length in LEN_NSTS.
              rewrite app_length in NUM_ROWS. ss.
              unguardH NUM_SITES. nia. }
            apply Forall_forall.
            intros x IN.
            hexploit NUM_COLS.
            { apply in_or_app. right.
              ss. right. eauto. }
            destruct x; ss.
          - hexploit (NUM_COLS tr_tgt).
            { apply in_or_app. right. ss. eauto. }
            destruct tr_tgt; ss.
        }
        des. subst.

        esplits; eauto.
        { econs 1; eauto.
          ss. rewrite app_length. ss.
          rewrite repeat_app. ss. }
        { inv SAFE_X. existT_elim. clarify. }
      }

      intros tr_src_p tr_tgt_p tm_tmp nw_tmp nsts_tmp
      scnt ist_tgt nsts_l_tmp nsts_r_tmp.
      i. guardH STEP_COUNTS. guardH LEN_TRS_L. guardH LEN_NSTS_L.
      clarify.

      renames nw_tmp tm_tmp into nw tm.
      renames nsts_l_tmp nsts_r_tmp into nsts_l nsts_r.
      rename tes1_r into tes1_raw.

      assert (exists tes1_l tes1_r trs_l' trs_r' te1 tr_tgt',
                 <<TRS_L_DIV: cons_each_rel tes1_l trs_l' trs_l>> /\
                 <<TRS_R_DIV: cons_each_rel tes1_r trs_r' trs_r>> /\
                 <<TR_TGT_DIV: tr_tgt = te1 :: tr_tgt'>> /\
                 <<TES1_DIV: tes1 = tes1_l ++ [te1] ++ tes1_r>> /\
                 <<TRANSPOSE_TRS':
                   transpose nsites (length tess)
                             (trs_l' ++ [tr_tgt'] ++ trs_r') tess>>).
      { rewrite <- STEP_COUNTS in TRANSPOSE_TRS. ss.
        hexploit transpose_des_col; eauto. i. des.
        clarify.
        apply Forall3_app_inv3 in DES_M. des.
        inv DES_M2.
        esplits; eauto.
      }
      des. subst tr_tgt. subst tes1. clear TRANSPOSE_TRS.

      assert (exists dms_f1 dmss_f',
                 <<DMS_DIV: dmss_f = dms_f1 :: dmss_f'>> /\
                 <<DMSGS_TO': Forall2 (fun dms dms_f =>
                                         Node.distr_msgs_to ip_n dms = dms_f)
                                      dpmss dmss_f'>> /\
                 <<DMS_F1: Node.distr_msgs_to ip_n dpms = dms_f1>> /\
                 <<WF_DMSS_F: Forall (Forall Packet.msg_wf) dmss_f'>> /\
                 <<WF_DMS_F1: Forall Packet.msg_wf dms_f1>>).
      { destruct dmss_f as [|dms_f1 dmss_f']; inv DMSGS_TO.
        inv WF_DMSGS_F.
        esplits; eauto. }
      clear DMSGS_TO WF_DMSGS_F. des.
      subst dmss_f. guardH DMS_F1.

      assert (exists nsts_l' ist_tgt' nsts_r'
                tes1_raw_l te1_raw tes1_raw_r
                ops1_l op1 ops' ops1_r,
                 <<STEPS_L: Forall4 (Node.step tm dpms)
                                    nsts_l tes1_raw_l ops1_l nsts_l'>> /\
                 <<STEPS_R: Forall4 (Node.step tm dpms)
                                    nsts_r tes1_raw_r ops1_r nsts_r'>> /\
                 <<STEP_TGT: Node.step tm dpms
                                       (Node.State nd_tgt ist_tgt)
                                       te1_raw op1
                                       (Node.State nd_tgt ist_tgt')>> /\
                 <<SAFE_NODES_L: Forall (Node.safe_state (DTime.succ tm)) nsts_l'>> /\
                 <<SAFE_NODES_R: Forall (Node.safe_state (DTime.succ tm)) nsts_r'>> /\
                 <<SAFE_NODE: Node.safe_istate _ (DTime.succ tm) ist_tgt'>> /\

                 <<TES_RAW_DIV: tes1_raw = tes1_raw_l ++ [te1_raw] ++ tes1_raw_r>> /\
                 <<NSTS1_DIV: nsts1 = nsts_l' ++ [Node.State nd_tgt ist_tgt'] ++ nsts_r'>> /\
                 <<OPS_DIV: ops = op1 :: ops'>> /\
                 <<OPS1_DIV: ops1 = ops1_l ++ [op1] ++ ops1_r>> /\
                 <<OUTPKTS1: nth_error ops1 idx = Some op1>> /\
                 <<WF_OUTPKT: option_rel1 Packet.wf op1>> /\
                 <<WF_OPS1_L: Forall (option_rel1 Packet.wf) ops1_l>> /\
                 <<WF_OPS1_R: Forall (option_rel1 Packet.wf) ops1_r>> /\
                 <<OUTPKTS_N': Forall2 (fun ops op =>
                                          nth_error ops idx = Some op) opss ops'>> /\
                 <<WF_OUT_PKTS': Forall (option_rel1 Packet.wf) ops'>> /\
                 <<LEN_LSTS_L': length nsts_l' = length nsts_l>> /\
                 <<LEN_LSTS_R': length nsts_r' = length nsts_r>> /\
                 <<LEN_OPS1_L: length ops1_l = length nsts_l>> /\
                 <<LEN_OPS1_R: length ops1_r = length nsts_r>>).
      { destruct ops as [|op1 ops']; inv OUTPKTS_N.
        inv WF_OUT_PKTS.

        apply Forall4_app_inv1 in LOCAL_STEPS.
        destruct LOCAL_STEPS as
            (tes1_raw_l & tes1_raw' & ops1_l & ops1' &
             nsts1_l & nsts1' & ? & ? & ? &
             STEPS_L & STEPS').
        subst.
        inv STEPS'.

        hexploit Forall4_length; try apply STEPS_L. i. des.

        assert (LEN_OPS1_L: length ops1_l = idx).
        { rewrite <- LEN_NSTS_L. ss. }

        assert (c = op1).
        { match goal with
          | H: nth_error (_ ++ _) idx = Some op1 |- _ =>
            rename H into OP1
          end.
          rewrite nth_error_app2 with (l:= ops1_l) in OP1 by nia.
          rewrite LEN_OPS1_L in OP1.
          rewrite Nat.sub_diag in OP1. ss. clarify.
        }
        subst c.
        inv P_HOLDS. existT_elim. subst.
        rename FORALL_T into STEPS_R.
        hexploit Forall4_length; try apply STEPS_R. i. des.

        apply Forall_app_inv in SAFE_NODES.
        destruct SAFE_NODES as [SAFE_L SAFE'].
        apply Forall_app_inv in SAFE'.
        destruct SAFE' as [SAFE_X SAFE_R].
        (* rewrite Forall_nth in SAFE_L, SAFE_X, SAFE_R. *)

        hexploit NW.wf_distr_preserve; eauto. i. des.

        hexploit Forall_safe_state; try apply STEPS_L; eauto.
        i. des.
        hexploit Forall_safe_state; try apply STEPS_R; eauto.
        i. des.

        esplits; eauto; ss.
        - econs; eauto.
        - assert (SAFE_X': Node.safe_state
                             tm (Node.State nd_tgt ist_tgt)).
          { inv SAFE_X. ss. }
          inv SAFE_X'. existT_elim. subst.
          punfold SAFE_ISTATE. inv SAFE_ISTATE.
          hexploit SAFE_NEXT; eauto.
          { rewrite NODE_IP.
            rewrite DMS_F1. ss. }
          i. des. pclearbot.
          eauto.
      }

      des. subst. clear OUTPKTS_N WF_OUT_PKTS LOCAL_STEPS.

      inv LOCAL_STEPS_SRC.
      renames te_r1 te0 into te1_raw_src te1_src.
      renames tess2 nst1 into tr_src' ist_src1.

      assert (NODE_STEPS_SRC:
                  Forall4 (Node.step tm dpms)
                          (nsts_l ++ [Node.State nd_src ist_src] ++ nsts_r)
                          (tes1_raw_l ++ [te1_raw_src] ++ tes1_raw_r)
                          (ops1_l ++ [op1] ++ ops1_r)
                          (nsts_l' ++ [Node.State nd_src ist_src1] ++ nsts_r')(*  /\ *)
             (* <<WF_OPS1: Forall Packet.wf (filtermap id ops1)>>). *)
             ).
      { apply Forall4_app; eauto.
        apply Forall4_app; eauto.
        econs.
        2: { econs. }

        econs; eauto.
        replace (Node.ip_addr nd_src) with ip_n.
        2: { inv SIM_NODES. des.
             congruence. }
        rewrite DMS_F1. ss.
      }

      assert (FLT_SYS_SRC_OK:
                DSys.filter_nb_sysstep
                  (tes1_raw_l ++ [te1_raw_src] ++ tes1_raw_r) =
                Some (tes1_l ++ [te1_src] ++ tes1_r)).
      { move FNB_OK at bottom.
        hexploit Forall4_length; try apply STEPS_L. i. des.
        hexploit Forall3_length; try apply TRS_L_DIV. i. des.

        unfold DSys.filter_nb_sysstep in *.
        apply deopt_list_Some_iff in FNB_OK.
        apply deopt_list_Some_iff.
        repeat rewrite map_app in FNB_OK.
        repeat rewrite map_app.

        apply app_eqlen_inv in FNB_OK.
        2: { do 2 rewrite map_length. congruence. }
        destruct FNB_OK as (FNB_L & FNB').
        ss. clarify.
        f_equal; eauto.
        f_equal; eauto.
      }

      assert (TES_EQUIV':
                tes_equiv (snoc tr_src_p te1_src ++ tr_src')
                             (snoc tr_tgt_p te1 ++ tr_tgt')).
      { unfold snoc.
        do 2 rewrite <- app_assoc. ss. }
      clear TES_EQUIV.

      hexploit IHCSTEPS; try apply REST_STEPS; eauto.
      { apply Forall_app; eauto.
        econs; eauto.
        econs. eauto. }
      (* { punfold SAFE_NODE_SRC. *)
      (*   inv SAFE_NODE_SRC. *)
      (*   hexploit SAFE_NEXT; eauto. *)
      (*   i. des. pclearbot. ss. } *)
      { eapply NW.wf_gather_preserve; eauto.
        eapply NW.wf_distr_preserve; eauto.
        apply Forall_filter_id.
        apply Forall_app; eauto.
        econs; eauto.
      }
      { rewrite <- LEN_NSTS. ss.
        repeat rewrite app_length. ss. nia. }
      { apply Forall3_length in TRS_L_DIV. des.
        congruence. }
      { apply Forall3_length in TRS_R_DIV. des.
        congruence. }
      i. des. clarify.

      assert (TM_RW: DTime.uadd tm (S (length tess)) =
                     DTime.uadd (DTime.succ tm) (length tess)).
      { rewrite <- DTime_uadd_one.
        rewrite DTime_uadd_assoc. ss. }

      esplits.
      { ss. rewrite <- STEP_COUNTS.
        econs; ss.
        { econs; eauto. }
        { eauto. }
        { apply MSTEPS_SRC. }
        { apply Forall3_app; eauto.
          econs; eauto. }
      }
      { eauto. }
      { rewrite <- TM_RW. ss. }
      { ss. rewrite ST_TGT'.
        rewrite <- TM_RW. ss. }
      { ss. rewrite TM_RW. ss. }
      { ss. rewrite TM_RW. ss. }
      { ss. rewrite TM_RW. ss. }
      { ss. }
      { congruence. }
      { congruence. }
    Qed.


    Lemma fmsim_nstates_impl_states
      : forall tm nw
          (nsts1 nsts2: list Node.state)
          (ist_src: Node.istate nd_src)
          (ist_tgt: Node.istate nd_tgt)
          (WF_NW: NW.wf nw)
          (NODE_SAFE1: Forall (Node.safe_state tm) nsts1)
          (NODE_SAFE2: Forall (Node.safe_state tm) nsts2)
          (NODE_SAFE_X: Node.safe_istate nd_tgt tm ist_tgt)
          (FMSIM_NST: fmsim_nstates _ _ tm ist_src ist_tgt)
          (LEN1: length nsts1 = length nds1)
          (LEN2: length nsts2 = length nds2)
      ,
        fmsim_states
          _ dsys_src dsys_tgt
          (NWSys.State
             tm nw
             (nsts1 ++ [Node.State nd_src ist_src] ++ nsts2))
          (NWSys.State
             tm nw
             (nsts1 ++ [Node.State nd_tgt ist_tgt] ++ nsts2)).
    Proof.
      pcofix CIH. i. pfold.
      punfold FMSIM_NST.
      2: { apply fmsim_nstates_monotone. }
      inv FMSIM_NST.

      econs.
      { apply N_POS. }
      i. exists n.

      exploit (msteps_csteps sys_tgt); eauto. i. des.
      hexploit (@nwsys_cstep_to_local sysE); eauto.
      { ss.
        rewrite nth_error_app2.
        2: { reflexivity. }
        rewrite Nat.sub_diag. ss. }
      { eapply Forall_app; eauto.
        eapply Forall_app; eauto.
        econs.
        2: { econs. }
        ss. }
      rename ops into opss.
      i. des.

      hexploit transpose_dims; eauto. i. des. ss.
      hexploit SIM; eauto.
      { replace (length dmss_f) with (length dpmss).
        2: { eapply Forall2_length. try apply DMSGS_TO. }
        replace (length dpmss) with (length trs_conc).
        2: { eapply csteps_length in CSTEPS.
             des. congruence. }
        ss.
      }

      i. des. rename SIM0 into SIM_NEXT. pclearbot.

      assert (NUM_SITES_EQ: length (nsts1 ++ Node.State nd_tgt ist_tgt :: nsts2) = length sys_tgt).
      { subst sys_tgt.
        do 2 rewrite app_length. ss. nia. }

      assert (exists trs_l trs_r,
                 <<TR_TGT_DIV: tr_tgt = trs_l ++ [tes] ++ trs_r>> /\
                 <<LEN_TRS_L: length trs_l = length nsts1>>).
      { clear - TRACE_TRANSPOSE TRACE_N.
        depgen trs_conc.
        revert tr_tgt tes.
        induction nsts1 as [|h1 t1 IH]; i; ss.
        { destruct tr_tgt as [| h_tgt t_tgt]; ss.
          { inv TRACE_TRANSPOSE. }
          inv TRACE_TRANSPOSE.
          exists [], t_tgt.
          esplits; ss. f_equal.
          apply nth_eq_list_eq. intro m.

          destruct (lt_ge_dec m (length h_tgt)).
          2: { rewrite nth_error_None2 by ss.
               rewrite nth_error_None2.
               2: { apply Forall2_length in TRACE_N.
                    apply Forall3_length in CONS_EACH.
                    des. congruence. }
               ss.
          }
          rewrite Forall2_nth in TRACE_N.
          r in CONS_EACH.
          rewrite Forall3_nth in CONS_EACH.
          specialize (TRACE_N m). specialize (CONS_EACH m).

          hexploit (nth_error_Some2 _ h_tgt m); ss.
          intros [te1 TE1]. r in TE1.
          rewrite TE1 in *.

          assert (TM_INV: exists T'm Tm,
                     nth_error trT m = Some T'm /\
                     nth_error trs_conc m = Some Tm /\
                     te1 :: T'm = Tm).
          { inv CONS_EACH. esplits; eauto. }
          destruct TM_INV as (T'm & Tm & T'M_N & TM_N & TM_EQ).
          clear CONS_EACH.
          subst Tm.

          rewrite TM_N in TRACE_N.
          destruct (nth_error tes m) as [te|]; inv TRACE_N.
          clarify.
        }

        destruct tr_tgt as [| h_tgt t_tgt]; inv TRACE_TRANSPOSE.
        hexploit IH; eauto.
        { instantiate (1:= tes).
          apply Forall2_nth.
          intro m.
          destruct (lt_ge_dec m (length trT)).
          2: {
            rewrite nth_error_None2 by ss.
            rewrite nth_error_None2.
            2: { apply Forall2_length in TRACE_N.
                 apply Forall3_length in CONS_EACH. des.
                 congruence. }
            econs.
          }
          hexploit (nth_error_Some2 _ trT m); ss.
          intros (trTm & TR_T_M). r in TR_T_M.
          eapply Forall3_nth2 in CONS_EACH; eauto.
          i. des.
          renames e1 e3 into h_tgt_m trs_conc_m.
          renames NTH1 NTH3 into H_TGT_M TRS_CONC_M.
          subst trs_conc_m.

          eapply Forall2_nth1 in TRACE_N; eauto.
          i. des.
          rewrite NTH2. rewrite TR_T_M. econs.
          eauto.
        }
        intros (trs_l' & trs_r' & T_TGT & LEN_EQ).
        exists (h_tgt::trs_l'), trs_r'.
        rewrite T_TGT.
        esplits; eauto.
        ss. rewrite LEN_EQ. ss.
      }
      des.

      hexploit constr_srcsteps_aux; eauto.
      { apply Forall_app; eauto.
        econs; eauto.
        econs. eauto. }
      { reflexivity. }
      { do 2 rewrite app_nil_l. eauto. }
      i. des.

      esplits; eauto.
      { subst tr_tgt.
        apply Forall2_app.
        { apply Forall2_tes_equiv_refl. }
        apply Forall2_app.
        { econs; eauto. }
        { apply Forall2_tes_equiv_refl. }
      }

      right. subst. rewrite ST_TGT'.
      eapply CIH; eauto; cycle 1.
      { nia. }
      { nia. }

      replace ist_tgt' with ist'.
      { eauto. }

      rewrite ST_TGT' in STATE'_N. ss.
      rewrite nth_error_app2 in STATE'_N.
      2: { rewrite LEN_NSTS1'. ss. }
      rewrite LEN_NSTS1' in STATE'_N.
      rewrite Nat.sub_diag in STATE'_N.
      clear - STATE'_N. ss.
      clarify. existT_elim. ss.
    Qed.


    Lemma sim_switch_sys
      : fmsim _ dsys_src dsys_tgt.
    Proof.
      econs. i.
      inv INIT_TGT.
      unfold sys_tgt in INIT_NODE_STATES.
      apply Forall2_app_inv_l in INIT_NODE_STATES.
      destruct INIT_NODE_STATES as
          (nsts1 & nsts' & INIT1 & INIT' & NSTS_EQ).
      apply Forall2_app_inv_l in INIT'.
      destruct INIT' as
          (nsts_x & nsts2 & INIT_XL & INIT2 & NSTS'_EQ).
      subst nsts'.
      assert (exists nst_x, nsts_x = [nst_x] /\
                       <<INIT_X: Node.init nd_tgt nst_x>>).
      { inv INIT_XL. esplits; eauto.
        match goal with
        | H: Forall2 _ [] _ |- _ => inv H
        end. ss. }
      des. clear INIT_XL. subst nsts_x.
      inv INIT_X.

      r in SIM_NODES.
      destruct SIM_NODES as [IP_EQ SIM_NODES'].
      hexploit (SIM_NODES' (DTime.of_ns gtm_init_ns)); eauto.
      destruct 1 as (ist_src & INIT_SRC & FMSIM').
      esplits; ss.
      { econs.
        instantiate (1:= nsts1 ++ [_] ++ nsts2).
        subst sys_src.
        apply Forall2_app; eauto.
        ss. econs; eauto.
        econs. eauto.
      }
      apply fmsim_nstates_impl_states; eauto.
      - apply NW.wf_init.
      - apply Forall_nth. i.
        destruct (lt_ge_dec n (length nds1)).
        + rewrite Forall_nth in SAFE_NODES1.
          rewrite Forall2_nth in INIT1.
          hexploit (nth_error_Some2 _ nds1 n); eauto.
          intros (nd1 & ND1).
          specialize (SAFE_NODES1 n).
          specialize (INIT1 n).
          rewrite ND1 in SAFE_NODES1.
          rewrite ND1 in INIT1. ss.
          destruct (nth_error nsts1 n) as [nst1|]; ss.
          inv SAFE_NODES1.
          assert (INIT: Node.init nd1 nst1).
          { inv INIT1. ss. }
          inv INIT.
          econs. eauto.
        + rewrite nth_error_None2.
          2: { apply Forall2_length in INIT1. congruence. }
          ss.
      -  apply Forall_nth. i.
         destruct (lt_ge_dec n (length nds2)).
         + rewrite Forall_nth in SAFE_NODES2.
           rewrite Forall2_nth in INIT2.
           hexploit (nth_error_Some2 _ nds2 n); eauto.
           intros (nd2 & ND2).
           specialize (SAFE_NODES2 n).
           specialize (INIT2 n).
           rewrite ND2 in SAFE_NODES2.
           rewrite ND2 in INIT2. ss.
           destruct (nth_error nsts2 n) as [nst2|]; ss.
           inv SAFE_NODES2.
           assert (INIT: Node.init nd2 nst2).
           { inv INIT2. ss. }
           inv INIT.
           econs. eauto.
         + rewrite nth_error_None2.
           2: { apply Forall2_length in INIT2. congruence. }
           ss.
      - inv SAFE_ND_TGT. eauto.
      - apply Forall2_length in INIT1. ss.
      - apply Forall2_length in INIT2. ss.
    Qed.

  End SWITCH.

  Section SWITCH_ALL_AUX.
    Variable gtm_init_ns: nat.
    Variable nds1: list (@Node.t sysE).
    Variable nds_src nds_tgt: list (@Node.t sysE).

    Hypothesis SIM_NODES: Forall2 fmsim_nodes nds_src nds_tgt.
    (* Hypothesis SAFE_NODES1: Forall Node.safe nds1. *)
    Hypothesis SAFE_NODES1: Forall Node.safe nds1.
    Hypothesis SAFE_NODES_SRC: Forall Node.safe nds_src.
    Hypothesis SAFE_NODES_TGT: Forall Node.safe nds_tgt.

    (* Let sys_src: NWSys.t := nds1 ++ [nd_src] ++ nds2. *)
    (* Let sys_tgt: NWSys.t := nds1 ++ [nd_tgt] ++ nds2. *)

    Let dsys_src := NWSys.as_dsys (nds1 ++ nds_src) gtm_init_ns.
    Let dsys_tgt := NWSys.as_dsys (nds1 ++ nds_tgt) gtm_init_ns.

    Lemma ref_switch_all_aux
      : DSys.behav_sys dsys_tgt <1= DSys.behav_sys dsys_src.
    Proof.
      depgen nds1.
      clear nds1 SAFE_NODES1 dsys_src dsys_tgt.
      induction SIM_NODES; i; ss.

      pose (dsys' := NWSys.as_dsys (nds1 ++ x :: l') gtm_init_ns).

      cut (DSys.behav_sys dsys_tgt <1= DSys.behav_sys dsys').
      { intro REF'.
        subst dsys_src.
        rewrite rw_cons_app.
        rewrite app_assoc.

        inv SIM_NODES.
        inv SAFE_NODES_SRC. inv SAFE_NODES_TGT.
        eapply IHf; eauto.
        { apply Forall_app; eauto. }

        rewrite <- app_assoc. ss.
        fold dsys'. eauto.
      }

      apply fmsim_adequacy.
      { subst dsys_tgt.
        apply NWSys.safe_nodes_safe.
        apply Forall_app; eauto. }

      inv SAFE_NODES_TGT.
      apply sim_switch_sys; eauto.
    Qed.

  End SWITCH_ALL_AUX.

  Lemma ref_switch_all
        (gtm_init_ns: nat)
        (nds_src nds_tgt: list (@Node.t sysE))
        (SIM_NODES: Forall2 fmsim_nodes nds_src nds_tgt)
        (SAFE_NODES_SRC: Forall Node.safe nds_src)
        (SAFE_NODES_TGT: Forall Node.safe nds_tgt)
    : DSys.behav_sys
        (NWSys.as_dsys nds_tgt gtm_init_ns) <1=
      DSys.behav_sys
        (NWSys.as_dsys nds_src gtm_init_ns)
  .
  Proof.
    replace nds_src with ([] ++ nds_src) by ss.
    replace nds_tgt with ([] ++ nds_tgt) by ss.
    i. eapply ref_switch_all_aux; eauto.
  Qed.

End SIM.
