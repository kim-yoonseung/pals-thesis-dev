From ITree Require Import
     ITree Core.ITreeDefinition Eq.Eq.
From compcert Require Coqlib.
From Paco Require Import paco.

Require Import Logic.FunctionalExtensionality.
Require Import List.
Require Import Arith ZArith Lia.

Require Import sflib ITreeTac.
Require Import Axioms StdlibExt IntegersExt.

Require Import SysSem.
Require Import IPModel DiscreteTimeModel.
Require Import NWSysModel OSModel OSNodes ProgSem.
Require Import RTSysEnv.
Require Import SyncSysModel MWITree AbstMW.
Require Import CProgEventSem.

Require Import FMSim FMSim_Switch.

Import ITreeNotations.

Set Nested Proofs Allowed.
(* Generalizable Variable sysE. *)

Local Opaque Int64.max_unsigned Int.max_unsigned Int.max_signed.


Ltac condtac :=
  match goal with
  | [|- context[if ?c then _ else _]] =>
    let COND := fresh "COND" in
    destruct c eqn:COND
  end.

Ltac update_times :=
  match goal with
  | H: valid_clock_skew ?gtm ?ltm |-
    context[paco3 _ _ ?gtm'] =>
    let tmp := fresh in
    let Htmp := fresh "GTM_UPD" in
    remember gtm' as tmp eqn: Htmp ;
    renames gtm ltm tmp into gtm_p ltm_p gtm;
    clear H
  end.

Ltac refl := reflexivity.
Ltac etrans := etransitivity.
Ltac congr := congruence.


Lemma sub_mod_divide
      a b
      (B: b <> 0):
  Nat.divide b (a - a mod b).
Proof.
  rewrite (Nat.div_mod a b) at 1; ss.
  replace (b * (a / b) + a mod b - a mod b) with (b * (a / b)) by nia.
  apply Nat.divide_factor_l.
Qed.

Lemma divide_range_eq
      p a b
      (P: p <> 0)
      (DIVA: Nat.divide p a)
      (DIVB: Nat.divide p b)
      (RANGE: a <= b < a + p):
  a = b.
Proof.
  rewrite <- Nat.mod_divide in *; try nia.
  rewrite (Nat.div_mod a p) in RANGE; ss.
  rewrite (Nat.div_mod b p) in RANGE; ss.
  rewrite DIVA, DIVB in *.
  repeat rewrite Nat.add_0_r in *.
  replace (p * (a / p) + p) with (p * ((a / p) + 1)) in * by nia.
  inv RANGE.
  rewrite <- Nat.mul_le_mono_pos_l in H; try nia.
  rewrite <- Nat.mul_lt_mono_pos_l in H0; try nia.
  assert (a / p = b / p) by nia.
  rewrite (Nat.div_mod a p); ss.
  rewrite (Nat.div_mod b p); ss.
  rewrite DIVA, DIVB.
  congr.
Qed.

Lemma sub_mod_range
      p a b
      (P: p <> 0)
      (DIVA: Nat.divide p a)
      (RANGE: a <= b):
  a <= b - b mod p.
Proof.
  rewrite <- Nat.mod_divide in *; ss.
  rewrite (Nat.div_mod b p) at 1; ss.
  replace (p * (b / p) + b mod p - b mod p) with (p * (b / p)) by nia.
  eapply Nat.div_le_mono in RANGE; try eapply P.
  rewrite (Nat.div_mod a p); ss.
  rewrite DIVA, Nat.add_0_r.
  nia.
Qed.

Lemma le_sub_mod
      p a b
      (P: p <> 0)
      (LE: a <= b):
  a - a mod p <= b - b mod p.
Proof.
  rewrite (Nat.div_mod a p) at 1; auto.
  rewrite (Nat.div_mod b p) at 1; auto.
  exploit Nat.div_le_mono; try exact LE; try exact P. i. nia.
Qed.

Lemma itree_event_eq
      E R (itr itr1 itr2: itree E R)
      (TAU1: itree_tau_star itr itr1)
      (TAU2: itree_tau_star itr itr2)
      (OBS1: forall itr', observe itr1 <> TauF itr')
      (OBS2: forall itr', observe itr2 <> TauF itr'):
  itr1 = itr2.
Proof.
  revert TAU2. induction TAU1.
  - i. inv TAU2; try congr.
  - i. apply IHTAU1; auto. inv TAU2; try congr.
Qed.

Lemma itree_tau_star_until_observe
      E R
      (itr itr1 itr2: itree E R)
      (TAU1: itree_tau_star itr itr1)
      (TAU2: itree_tau_star itr itr2)
      (AT_EVENT2: forall itr', observe itr2 <> TauF itr'):
  itree_tau_star itr1 itr2.
Proof.
  revert itr1 TAU1. induction TAU2; i.
  - inv TAU1; try by econs 1. rewrite STEP in *. congr.
  - inv TAU1.
    + econs 2; eauto.
    + rewrite STEP0 in *. inv STEP. eauto.
Qed.

Lemma itree_tau_star2
      E R
      (itr itr1 itr2: itree E R)
      (TAU1: itree_tau_star itr itr1)
      (TAU2: itree_tau_star itr itr2):
  itree_tau_star itr1 itr2 \/
  (exists itr', observe itr2 = TauF itr' /\ itree_tau_star itr' itr1).
Proof.
  revert itr1 TAU1. induction TAU2; i.
  - inv TAU1.
    + left. econs 1.
    + right. eauto.
  - inv TAU1.
    + left. econs 2; eauto.
    + rewrite STEP0 in *. inv STEP. eauto.
Qed.

Lemma itree_cases
      E R (itr1: itree E R):
  (<<INF: itr1 ≅ ITree.spin>>) \/
  (exists itr2,
      (<<TAU: itree_tau_star itr1 itr2>>) /\
      __guard__ (
          (exists r, (<<OBS: observe itr2 = RetF r>>)) \/
          (exists X (e: E X) k,
              (<<OBS: observe itr2 = VisF e k>>)))).
Proof.
  match goal with
  | [|- ?a \/ ?b] => destruct (classic b); eauto
  end.
  left. revert itr1 H. unguard.
  pcofix CIH. i.
  pfold. unfold eqit_.
  destruct (observe itr1) eqn:OBS.
  - exfalso. apply H0. esplits; try by econs 1; eauto.
  - replace (observe ITree.spin) with (@TauF E R (itree E R) ITree.spin) by ss.
    econs 2. right. eapply CIH; eauto.
    ii. des; apply H0; esplits; eauto; econs 2; eauto.
  - exfalso. apply H0. esplits; try by econs 1. right. esplits; eauto.
Qed.

Lemma itree_tau_star_spin
      E R (itr: itree E R)
      (TAU: itree_tau_star itr ITree.spin):
  itr = ITree.spin.
Proof.
  apply EqAxiom.bisimulation_is_eq.
  revert itr TAU. pcofix CIH. i.
  pfold. unfold eqit_.
  inv TAU.
  - replace (observe ITree.spin) with (@TauF E R (itree E R) ITree.spin) by ss.
    econs 2. right. eapply CIH. econs 1.
  - rewrite STEP.
    replace (observe ITree.spin) with (@TauF E R (itree E R) ITree.spin) by ss.
    econs 2. right. eapply CIH. auto.
Qed.

Lemma spin_itree_tau_star
      E R (itr: itree E R)
      (TAU: itree_tau_star ITree.spin itr):
  itr = ITree.spin.
Proof.
  remember ITree.spin as itr0.
  revert Heqitr0.
  induction TAU; ss; i; subst.
  inv STEP. eauto.
Qed.


Section PROOF.
  (* Context `{sysE: Type -> Type}. *)
  Context `{SystemEnv}.

  Notation obsE := (extcallE +' errE).
  Let sendE: Type -> Type := @abst_sendE bytes.
  Let appE: Type -> Type := (* (extcallE +' errE) *) obsE +' sendE.
  (* Let progE: Type -> Type := osE +' tlimE +' sysE. *)

  Variable tid: Tid.
  Variable ip: ip_t.

  (* Variable astate_t: Type. *)
  (* Variable init_astate: astate_t. *)
  (* Variable job_itree: *)
  (*   nat(*sync_time*) -> list bytes? -> astate_t -> *)
  (*   itree appE astate_t. *)

  Variable app_mod: @AppMod.t obsE bytes.

  Hypothesis TASK_ID_IP: task_id_ip tid ip.

  Let snode : SNode.t := ITrSNode.to_snode app_mod.

  Let spec_itree: itree progE unit :=
    MWITree.main_itree tid app_mod.
  Let prog := prog_of_itree _ spec_itree.

  Let node_src: Node.t :=
    AbstMW.as_node tid snode.
  Let node_tgt: Node.t :=
    OSNode.as_node ip prog
                   (fun tm => Z.of_nat (base_time period tm)).


  Lemma tau_steps_itree_tau_star
        st1 st2
        (TAU: Prog.tau_steps prog st1 st2):
    itree_tau_star (snd st1) (snd st2).
  Proof.
    induction TAU; try by econs 1.
    inv STEP1; ss. econs 2; eauto.
  Qed.

  Lemma bind_ret_l_eq
        {E R S} (r : R) (k : R -> itree E S):
    ITree.bind (Ret r) k = (k r).
  Proof.
    eapply EqAxiom.bisimulation_is_eq.
    eapply Eq.bind_ret_l.
  Qed.

  Lemma bind_bind_eq
        {E R S T}
        (s : itree E R) (k : R -> itree E S) (h : S -> itree E T):
    ITree.bind (ITree.bind s k) h = ITree.bind s (fun r => ITree.bind (k r) h).
  Proof.
    eapply EqAxiom.bisimulation_is_eq.
    eapply Eq.bind_bind.
  Qed.

  Lemma iprog_observe_eq
        pst1 pst2
        (TAU: Prog.tau_steps prog pst1 pst2):
    (exists itr', observe (snd pst1) = TauF itr') \/
    (observe (snd pst1) = observe (snd pst2)).
  Proof.
    induction TAU; eauto.
    inv STEP1; eauto.
  Qed.


  Lemma AbstMW_accept_packets_nil
        (node: @SNode.t obsE _)
        (ist: @AbstMW.istate_t _ node)
    : AbstMW.accept_packets [] ist = ist.
  Proof.
    destruct ist; ss.
    - rewrite app_nil_r. ss.
    - rewrite app_nil_r. ss.
  Qed.

  Lemma AbstMW_accept_packets_acc
        (node: @SNode.t obsE _)
        (ist: @AbstMW.istate_t _ node)
        pms1 pms2
    : AbstMW.accept_packets pms2 (AbstMW.accept_packets pms1 ist) =
      AbstMW.accept_packets (pms1 ++ pms2) ist.
  Proof.
    destruct ist; ss.
    - unfold AbstMW.filter_port.
      rewrite filter_app.
      rewrite app_assoc. ss.
    - unfold AbstMW.filter_port.
      rewrite filter_app.
      rewrite app_assoc. ss.
  Qed.

  Lemma socket_accept_msgs_nil skt:
    Socket.accept_msgs [] skt = skt.
  Proof.
    unfold Socket.accept_msgs.
    des_ifs; ss. unfold Socket.insert_msgs.
    destruct skt. rewrite List.app_nil_r. ss.
  Qed.

  Lemma sockets_accept_msgs_nil skts:
    Socket.set_accept_msgs [] skts = skts.
  Proof.
    induction skts; ss.
    rewrite IHskts, socket_accept_msgs_nil. ss.
  Qed.

  Lemma socket_accept_msgs_cons
        skt m dms:
    Socket.accept_msgs (m :: dms) skt =
    Socket.accept_msgs dms (Socket.accept_msgs [m] skt).
  Proof.
    unfold Socket.accept_msgs.
    destruct (Socket.bound_port skt) eqn:SKT; try rewrite SKT; ss.
    condtac; ss.
    - destruct skt; ss. rewrite SKT. f_equal.
      rewrite rw_cons_app. rewrite app_assoc. ss.
    - destruct skt; ss. rewrite SKT. f_equal.
      rewrite app_nil_r. ss.
  Qed.

  Lemma sockets_accept_msgs_acc
        skts dms1 dms2:
    Socket.set_accept_msgs dms2 (Socket.set_accept_msgs dms1 skts) =
    Socket.set_accept_msgs (dms1 ++ dms2) skts.
  Proof.
    induction skts; ss.
    rewrite IHskts. clear IHskts. f_equal.
    revert a dms2. induction dms1; ss; i.
    - rewrite socket_accept_msgs_nil. ss.
    - rewrite socket_accept_msgs_cons.
      rewrite (socket_accept_msgs_cons a0 a (dms1 ++ dms2)).
      auto.
  Qed.

  Definition is_recv_socket (skt: Socket.t): bool :=
    match skt.(Socket.bound_port) with
    | Some pn => pn =? port
    | None => false
    end.

  Definition sockets_of (txs rxs: nat) (inbp: list Packet.msg_t): Socket.set_t :=
    Socket.new_socket txs :: Socket.mk rxs (Some port) inbp :: [].

  Lemma sockets_of_accept_msgs
        txs rxs inbp1 skts1 dms
        (SOCKETS1: skts1 = sockets_of txs rxs inbp1):
    Socket.set_accept_msgs dms skts1 =
    sockets_of txs rxs (inbp1 ++ AbstMW.filter_port dms).
  Proof.
    subst. ss.
  Qed.


  Section LEMMAS.
    Lemma cskew_time_not_over
          tlim gtm ltm
          (TLIM: tlim >= period)
          (CSKEW: valid_clock_skew gtm ltm)
          (LTM: ltm < tlim - DELTA):
      gtm < DTime.of_ns (tlim - max_clock_skew - max_nw_delay).
    Proof.
      specialize DTime.units_per_ns_pos. i.
      unfold DTime.of_ns. s.
      unfold valid_clock_skew, nat_diff, DTime.to_ns_rd in *.
      unfold DELTA in *.
      revert CSKEW. condtac; ss; i.
      - apply Nat.leb_le in COND.
        assert (ltm + max_clock_skew < tlim - max_clock_skew - max_nw_delay) by nia.
        eapply Nat.le_lt_trans; [|rewrite <- Nat.mul_lt_mono_pos_r; try eapply H1]; eauto.
        rewrite (Nat.div_mod gtm DTime.units_per_ns); [|nia].
        etrans; [eapply Nat.add_le_mono|].
        + eapply Nat.mul_le_mono_l; eauto.
        + apply Nat.lt_le_incl. apply Nat.mod_upper_bound. nia.
        + specialize max_clock_skew_pos. nia.
      - apply Nat.leb_gt in COND.
        assert (gtm / DTime.units_per_ns < ltm + max_clock_skew) by nia.
        assert (gtm / DTime.units_per_ns < tlim - max_clock_skew - max_nw_delay) by nia.
        apply div_ub_inv; nia.
    Qed.

    Lemma sim_latency
          (r: DTime.t -> Node.istate node_src ->
              Node.istate node_tgt -> Prop)
          gtm lat ltm tlim
          ist_amw skts tmr ost pst
          (CSKEW: valid_clock_skew gtm ltm)
          (CIH_OFF:
             forall gtm,
               r gtm
                 (AbstMW.State tid ip snode AbstMW.Off)
                 (OSNode.Off prog))
          (SILENT_SRC:
             forall gtm' ltm' dms ist_amw'
               (TIME_NOT_OVER: OSNode.is_time_limit_over ltm' tlim = false)
               (CSKEW: valid_clock_skew gtm' ltm')
               (ACCEPT: ist_amw' = AbstMW.accept_packets dms ist_amw),
               AbstMW.istep
                 gtm' tid ip snode
                 ist_amw' (Z0, []) None ist_amw')
          (LAT_ZERO:
             forall gtm0 ltm0
               dms ist_amw0 skts0
               (CSKEW: valid_clock_skew gtm0 ltm0)
               (GTM: gtm <= gtm0)
               (LTM: ltm <= ltm0)
               (ACCEPT_AMW: ist_amw0 = AbstMW.accept_packets dms ist_amw)
               (ACCEPT_SOCKETS: skts0 = Socket.set_accept_msgs dms skts),
               paco3 (_sim_nstates _ _) r gtm0
                     (AbstMW.State tid ip snode ist_amw0)
                     (OSNode.On prog ltm0 0
                                (OSNode.Proc prog (OS.State skts0 tmr tlim ost) pst))):
      paco3 (_sim_nstates _ _) r gtm
            (AbstMW.State tid ip snode ist_amw)
            (OSNode.On prog ltm lat
                       (OSNode.Proc prog (OS.State skts tmr tlim ost) pst)).
    Proof.
      rewrite <- (AbstMW_accept_packets_nil _ ist_amw).
      rewrite <- (sockets_accept_msgs_nil skts).
      remember (@nil Packet.msg_t) as dms. clear Heqdms.
      revert dms gtm ltm lat CSKEW LAT_ZERO.

      pcofix CIH_TMP. i.
      destruct lat as [| lat].
      { i. eapply paco3_mon; eauto. }
      pfold. econs. i. ss.
      inv STEP_TGT.
      inv ESTEP; ss; cycle 1.
      { inv IST_ADV_LCLOCK.
        esplits; ss.
        { econs; eauto. econs 1. }
        { ss. }
        right.
        eapply CIH_TMP0.
        eapply CIH_OFF.
      }
      inv IST_ADV_LCLOCK.
      esplits.
      { econs; eauto.
        rewrite AbstMW_accept_packets_acc.
        eapply SILENT_SRC; eauto.
      }
      { ss. }
      { inv NOT_NB_TGT. ss. }
      { ss. }
      right.
      inv ADV_LCLOCK.
      rewrite sockets_accept_msgs_acc.
      eapply CIH_TMP; eauto.
      i. eapply LAT_ZERO; eauto.
      - etrans; try exact GTM. ss. nia.
      - etrans; eauto.
    Qed.

    Lemma sim_ose_call
          (r: DTime.t -> Node.istate node_src ->
              Node.istate node_tgt -> Prop)
          gtm ltm lat
          ist_amw idx tlim skts tmr
          (itr itr_act: itree progE unit)
          R (ose: osE R) k
          (CSKEW: valid_clock_skew gtm ltm)
          (CIH_OFF:
             forall gtm,
               r gtm
                 (AbstMW.State tid ip snode AbstMW.Off)
                 (OSNode.Off prog))
          (ITREE_STAR: itree_tau_star itr itr_act)
          (OBS_OSE: observe itr_act = VisF (subevent _ ose) k)
          (SILENT_SRC:
             forall gtm' ltm' dms ist_amw'
               (TIME_NOT_OVER: OSNode.is_time_limit_over ltm' tlim = false)
               (CSKEW: valid_clock_skew gtm' ltm')
               (ACCEPT: ist_amw' = AbstMW.accept_packets dms ist_amw),
               AbstMW.istep
                 gtm' tid ip snode
                 ist_amw' (Z0, []) None ist_amw')
          (STEP_SRC_SIM:
             forall gtm0 ltm0 gtm1 ltm1 lat
               dms ist_amw0 os0
               (CSKEW: valid_clock_skew gtm0 ltm0)
               (GTM1: gtm1 = DTime.succ gtm0)
               (GTM: gtm <= gtm1)
               (LTM: ltm <= ltm1)
               (ADV_LCLOCK: adv_local_clock gtm0 ltm0 ltm1)
               (TLIM_NOT_OVER: OSNode.is_time_limit_over ltm0 tlim = false)
               (ACCEPT_AMW: ist_amw0 = AbstMW.accept_packets dms ist_amw)
               (OS: os0 = OS.State (Socket.set_accept_msgs dms skts) tmr tlim (OS.Proc ose)),
             exists ts ist_amw1,
               AbstMW.istep
                 gtm0 tid ip snode
                 ist_amw0 (ts, []) None ist_amw1 /\
               paco3 (_sim_nstates _ _) r gtm1
                     (AbstMW.State tid ip snode ist_amw1)
                     (OSNode.On prog ltm1 lat
                                (OSNode.Proc prog os0 (0, itr_act)))):
      paco3 (_sim_nstates _ _) r gtm
            (AbstMW.State tid ip snode ist_amw)
            (OSNode.On prog ltm lat
                       (OSNode.Proc prog (OS.State skts tmr tlim OS.Idle) (idx, itr))).
    Proof.
      rewrite <- (AbstMW_accept_packets_nil _ ist_amw).
      rewrite <- (sockets_accept_msgs_nil skts).
      remember (@nil Packet.msg_t) as dms. clear Heqdms.
      revert gtm lat ltm itr itr_act k CSKEW ITREE_STAR OBS_OSE STEP_SRC_SIM.
      revert idx dms.

      pcofix CIH_TMP. i.
      eapply sim_latency; eauto.
      { i. subst. rewrite AbstMW_accept_packets_acc. eauto. }
      i. subst.
      pfold. econs. i.
      inv STEP_TGT; ss. inv ESTEP; ss; cycle 1.
      { (* off *)
        esplits.
        { econs; eauto. econs 1. }
        { ss. }
        { inv NOT_NB_TGT. ss. }
        { ss. }
        inv IST_ADV_LCLOCK.
        right. eapply CIH_TMP0. eapply CIH_OFF.
      }

      (* proc step *)
      inv PROC_STEP; cycle 1.
      { inv OS_STEP. }
      { inv OS_RET. ss. }

      inv PEFF_STEP; ss; cycle 1.
      { (* sys event *)
        exploit (iprog_itree_tau_star_until_zero spec_itree); eauto. i.
        exploit (@iprog_at_event_eq progE); [exact x0| |exact PROG_SILENT_STEPS|..]; eauto.
        { econs; eauto. }
        destruct pst_m. s. i. des. subst.
        inv AT_EVT. existT_elim. subst.
        rewrite OBS in *. ss.
      }
      { (* itree step *)
        esplits.
        { econs; eauto.
          do 2 rewrite AbstMW_accept_packets_acc.
          eapply SILENT_SRC; eauto.
        }
        { ss. }
        { inv NOT_NB_TGT. ss. }
        { ss. }
        do 2 rewrite sockets_accept_msgs_acc in *.
        inv IST_ADV_LCLOCK. destruct pst'.
        right. eapply CIH_TMP; eauto.
        - inv ADV_LCLOCK. ss.
        - move ITREE_STAR at bottom.
          exploit tau_steps_itree_tau_star.
          { eapply Prog.tau_steps_app; [eauto|].
            econs 2; eauto. econs 1. }
          i. eapply itree_tau_star_until_observe; eauto. congr.
        - i. subst. eapply STEP_SRC_SIM; eauto.
          + unfold DTime.succ in *. ss. nia.
          + inv ADV_LCLOCK. nia.
      }
      { (* final *)
        exploit tau_steps_itree_tau_star; try exact PROG_SILENT_STEPS. s. i.
        exploit itree_tau_star_until_observe; [exact x0|exact ITREE_STAR|congr|].
        i. inv APP_STEP. inv x1; ss; try congr.
      }
      { (* UB *)
        exfalso.
        exploit tau_steps_itree_tau_star; try exact PROG_SILENT_STEPS. s. i.
        exploit itree_tau_star_until_observe; [exact x0|exact ITREE_STAR|congr|].
        i. inv PROG_STUCK. inv x1; ss.
        - destruct pst_m. destruct n.
          + apply NOT_AT_EVENT. esplits. econs; eauto.
          + apply STUCK_STEP. esplits. econs; eauto.
        - destruct pst_m. destruct n.
          + apply STUCK_STEP. esplits. econs; eauto.
          + apply STUCK_STEP. esplits. econs; eauto.
      }
      { (* os call *)
        exploit (iprog_itree_tau_star_until_zero spec_itree); eauto. i.
        exploit (@iprog_at_event_eq progE); [exact x0| |exact PROG_SILENT_STEPS|..]; eauto.
        { econs; eauto. }
        destruct pst_m. s. i. des. subst.
        inv AT_EVT. rewrite OBS in *. inv OBS_OSE. existT_elim. subst.
        inv IST_ADV_LCLOCK.
        exploit (@STEP_SRC_SIM gtm0 ltm0 (DTime.succ gtm0) ltm' lat' (dms ++ dms0 ++ dms1)); eauto.
        { unfold DTime.succ. ss. nia. }
        { inv ADV_LCLOCK. nia. }
        i. des. esplits.
        { econs; eauto.
          do 2 rewrite AbstMW_accept_packets_acc. eauto.
        }
        { ss. }
        { inv NOT_NB_TGT. ss. }
        { ss. }
        destruct os_ec.
        revert H3. unfold embed, embed_event_call. i. inv H3. existT_elim.
        unfold resum, ReSum_id, id_, Id_IFun in *. subst.
        inv OS_CALL. existT_elim. subst.
        left. eapply paco3_mon; eauto.
        do 2 rewrite sockets_accept_msgs_acc. ss.
      }
      Unshelve.
      auto.
    Qed.

    Lemma sim_ose_ret
          (r: DTime.t -> Node.istate node_src ->
              Node.istate node_tgt -> Prop)
          gtm ltm lat
          ist_amw tlim skts tmr
          (itr_act: itree progE unit)
          R (ose: osE R) (retv: R) k
          (CSKEW: valid_clock_skew gtm ltm)
          (CIH_OFF:
             forall gtm,
               r gtm
                 (AbstMW.State tid ip snode AbstMW.Off)
                 (OSNode.Off prog))
          (OBS_OSE: observe itr_act = VisF (subevent _ ose) k)
          (SILENT_SRC:
             forall gtm' ltm' dms ist_amw'
               (TIME_NOT_OVER: OSNode.is_time_limit_over ltm' tlim = false)
               (CSKEW: valid_clock_skew gtm' ltm')
               (ACCEPT: ist_amw' = AbstMW.accept_packets dms ist_amw),
               AbstMW.istep
                 gtm' tid ip snode
                 ist_amw' (Z0, []) None ist_amw')
          (STEP_SRC_SIM:
             forall gtm0 ltm0 gtm1 ltm1 lat
               dms ist_amw0 os0 idx0 itr0
               (CSKEW: valid_clock_skew gtm0 ltm0)
               (GTM1: gtm1 = DTime.succ gtm0)
               (GTM: gtm <= gtm1)
               (LTM: ltm <= ltm1)
               (ADV_LCLOCK: adv_local_clock gtm0 ltm0 ltm1)
               (TLIM_NOT_OVER: OSNode.is_time_limit_over ltm0 tlim = false)
               (ACCEPT_AMW: ist_amw0 = AbstMW.accept_packets dms ist_amw)
               (OS: os0 = OS.State (Socket.set_accept_msgs dms skts) tmr tlim OS.Idle)
               (RET_CONT: k retv = itr0),
             exists ts ist_amw1,
               AbstMW.istep
                 gtm0 tid ip snode
                 ist_amw0 (ts, []) None ist_amw1 /\
               upaco3 (_sim_nstates _ _) r gtm1
                      (AbstMW.State tid ip snode ist_amw1)
                      (OSNode.On prog ltm1 lat
                                 (OSNode.Proc prog os0 (idx0, itr0)))):
      paco3 (_sim_nstates _ _) r
            gtm
            (AbstMW.State tid ip snode ist_amw)
            (OSNode.On prog ltm lat
                       (OSNode.Proc
                          prog (OS.State skts tmr tlim (OS.Ret ose retv)) (0, itr_act))).
    Proof.
      rewrite <- (AbstMW_accept_packets_nil _ ist_amw).
      rewrite <- (sockets_accept_msgs_nil skts).
      remember (@nil Packet.msg_t) as dms. clear Heqdms.
      revert gtm lat ltm itr_act k dms CSKEW OBS_OSE STEP_SRC_SIM.

      pcofix CIH_TMP. i.
      eapply sim_latency; eauto.
      { i. subst. rewrite AbstMW_accept_packets_acc. eauto. }
      i. subst.
      pfold. econs. i.
      inv STEP_TGT; ss. inv ESTEP; ss; cycle 1.
      { (* off *)
        esplits.
        { econs; eauto. econs 1. }
        { ss. }
        { inv NOT_NB_TGT. ss. }
        { ss. }
        inv IST_ADV_LCLOCK.
        right. eapply CIH_TMP0. eapply CIH_OFF.
      }

      (* proc step *)
      inv PROC_STEP; ss.
      { inv OS_STEP. }
      inv OS_RET. inv RET_STATUS. existT_elim. subst.
      inv IST_ADV_LCLOCK.
      destruct pst'.
      exploit (@STEP_SRC_SIM gtm0 ltm0 (DTime.succ gtm0) ltm' lat' (dms ++ dms0 ++ dms1)); eauto.
      { unfold DTime.succ. ss. nia. }
      { inv ADV_LCLOCK. nia. }
      i. des. esplits.
      { econs; eauto.
        do 2 rewrite AbstMW_accept_packets_acc. eauto.
      }
      { ss. }
      { inv NOT_NB_TGT. ss. }
      { ss. }
      inv AFT_EVT. existT_elim. subst.
      rewrite OBS in *. inv OBS_OSE. existT_elim. subst.
      do 2 rewrite sockets_accept_msgs_acc.
      eapply upaco3_mon; eauto.
    Qed.

    Lemma sim_wait_timer
          (r: DTime.t -> Node.istate node_src ->
              Node.istate node_tgt -> Prop)
          gtm ltm lat
          ist_amw tlim skts itr
          ose tm
          (CSKEW: valid_clock_skew gtm ltm)
          (CIH_OFF:
             forall gtm,
               r gtm
                 (AbstMW.State tid ip snode AbstMW.Off)
                 (OSNode.Off prog))
          (OSE: ose = OSWaitTimer tm)
          (TLIM: tlim <= tm - DELTA)
          (SILENT_SRC:
             forall gtm' ltm' dms ist_amw'
               (TIME_NOT_OVER: OSNode.is_time_limit_over ltm' (Some tlim) = false)
               (CSKEW: valid_clock_skew gtm' ltm')
               (ACCEPT: ist_amw' = AbstMW.accept_packets dms ist_amw),
               AbstMW.istep
                 gtm' tid ip snode
                 ist_amw' (Z0, []) None ist_amw')
          (STEP_SRC_SIM:
             forall gtm ltm lat
               dms ist_amw0 os0 tlim'
               (CSKEW: valid_clock_skew gtm ltm)
               (EXPIRED: tm < ltm)
               (ACCEPT_AMW: ist_amw0 = AbstMW.accept_packets dms ist_amw)
               (OS: os0 = OS.State (Socket.set_accept_msgs dms skts)
                                   Timer.Init (Some tlim') (OS.Ret ose Z0))
               (TLIM: tlim' <= tm + period - DELTA),
               upaco3 (_sim_nstates _ _) r gtm
                      (AbstMW.State tid ip snode ist_amw0)
                      (OSNode.On prog ltm lat
                                 (OSNode.Proc prog os0 (0, itr)))):
      paco3 (_sim_nstates _ _) r gtm
            (AbstMW.State tid ip snode ist_amw)
            (OSNode.On prog ltm lat
                       (OSNode.Proc prog (OS.State skts Timer.Init (Some tlim) (OS.Proc ose)) (0, itr))).
    Proof.
      eapply sim_latency; eauto. i. subst.
      clear gtm ltm lat CSKEW GTM LTM.
      rename gtm0 into gtm, ltm0 into ltm, CSKEW0 into CSKEW.

      pfold. econs. i.
      inv STEP_TGT. inv ESTEP; ss; cycle 1.
      { inv IST_ADV_LCLOCK.
        esplits; ss; eauto.
        econs; eauto. econs.
      }
      rename lat' into lat.
      inv PROC_STEP; ss.
      2: { inv OS_RET. ss. }

      inv OS_STEP; ss; cycle 1.
      { (* ret *)
        existT_elim. inv H4.
        rewrite Nat.leb_gt in TLIM_OK. nia.
      }

      existT_elim. inv H4.
      inv IST_ADV_LCLOCK. inv ADV_LCLOCK.
      esplits.
      { econs; eauto.
        rewrite AbstMW_accept_packets_acc.
        eapply SILENT_SRC; eauto.
      }
      { ss. }
      { inv NOT_NB_TGT. ss. }
      { ss. }
      left.
      remember (DTime.succ gtm) as gtm'.
      clear gtm ltm te_tgt CSKEW Heqgtm' NOT_NB_TGT TLIM_OK WAIT H1.
      rewrite sockets_accept_msgs_acc.
      remember (dms ++ dms0) as dms'.
      clear dms dms0 Heqdms' WF_DMS.
      rename gtm' into gtm, ltm' into ltm, dms' into dms, H2 into CSKEW.

      revert gtm ltm lat dms CSKEW.
      pcofix CIH_WAITING. i.

      eapply sim_latency; eauto.
      { s. i. subst.
        rewrite AbstMW_accept_packets_acc.
        eapply SILENT_SRC; eauto.
      }
      i. subst.
      clear gtm ltm lat CSKEW GTM LTM.
      rewrite sockets_accept_msgs_acc, AbstMW_accept_packets_acc.
      remember (dms ++ dms0) as dms'.
      clear dms dms0 Heqdms'.
      rename gtm0 into gtm, ltm0 into ltm, dms' into dms, CSKEW0 into CSKEW.

      pfold. econs. i.
      inv STEP_TGT. inv ESTEP; ss; cycle 1.
      { inv IST_ADV_LCLOCK.
        esplits; ss; eauto.
        econs; eauto. econs.
      }
      rename lat' into lat.
      inv PROC_STEP; ss.
      2: { inv OS_RET. ss. }

      inv OS_STEP; ss.
      { (* waiting *)
        inv IST_ADV_LCLOCK. inv ADV_LCLOCK.
        esplits.
        { econs; eauto.
          rewrite AbstMW_accept_packets_acc.
          eapply SILENT_SRC; eauto.
        }
        { ss. }
        { inv NOT_NB_TGT. ss. }
        { ss. }
        right.
        rewrite sockets_accept_msgs_acc.
        eapply CIH_WAITING; eauto.
      }

      clear CIH_WAITING.
      inv IST_ADV_LCLOCK. inv ADV_LCLOCK.
      esplits.
      { econs; eauto.
        rewrite AbstMW_accept_packets_acc.
        eapply SILENT_SRC; eauto.
      }
      { ss. }
      { inv NOT_NB_TGT. ss. }
      { ss. }

      rewrite sockets_accept_msgs_acc.
      eapply upaco3_mon; eauto.
      eapply STEP_SRC_SIM; eauto.
      { eapply Nat.lt_le_trans; eauto. }
      { nia. }
    Qed.

    Fixpoint mcast_join (rxs: nat) (tids: list Tid): itree progE unit :=
      match tids with
      | [] => Ret tt
      | tid :: tids =>
        trigger (OSJoinSocket rxs (tid2ip tid));;
        mcast_join rxs tids
      end.

    Lemma mcast_join_equiv n rxs:
      MWITree.mcast_join tid rxs n (map snd mcasts) =
      mcast_join rxs (map fst
                          (ifilter (fun _ mc_mems => existsb (Nat.eqb tid) (snd mc_mems))
                                   n mcasts)).
    Proof.
      revert n.
      induction mcasts; ss; i. condtac; ss.
      - f_equal. rewrite IHl. ss.
      - erewrite bind_ret_l_eq. auto.
    Qed.

    Lemma sim_mcast_join
          (r: DTime.t -> Node.istate node_src ->
              Node.istate node_tgt -> Prop)
          gtm lat ltm
          tlim tlim_tgt
          inbp ast idx skts txs rxs tids k
          (CSKEW: valid_clock_skew gtm ltm)
          (ID_NEQ: txs <> rxs)
          (SOCKETS: skts = sockets_of txs rxs inbp)
          (TLIM: forall gtm' ltm'
                   (TIME_NOT_OVER: OSNode.is_time_limit_over ltm' tlim_tgt = false)
                   (CSKEW: valid_clock_skew gtm' ltm'),
              gtm' < DTime.of_ns tlim)
          (TIDS: List.Forall (fun tid => IP.mcast_ip (tid2ip tid)) tids)
          (CIH_OFF:
             forall gtm,
               r gtm
                 (AbstMW.State tid ip snode AbstMW.Off)
                 (OSNode.Off prog))
          (DONE:
             forall gtm0 ltm0 lat idx inbp0 skts0
               (CSKEW: valid_clock_skew gtm0 ltm0)
               (GTM: gtm <= gtm0)
               (LTM: ltm <= ltm0)
               (SOCKETS: skts0 = sockets_of txs rxs inbp0),
               paco3 (_sim_nstates _ _) r gtm0
                     (AbstMW.State tid ip snode (AbstMW.Prep [] tlim inbp0 ast))
                     (OSNode.On prog ltm0 lat
                                (OSNode.Proc prog
                                             (OS.State skts0 Timer.Init tlim_tgt OS.Idle)
                                             (idx, k)))):
      paco3 (_sim_nstates _ _) r gtm
            (AbstMW.State tid ip snode (AbstMW.Prep tids tlim inbp ast))
            (OSNode.On prog ltm lat
                       (OSNode.Proc prog
                                    (OS.State skts Timer.Init tlim_tgt OS.Idle)
                                    (idx, mcast_join rxs tids ;; k))).
    Proof.
      revert gtm ltm lat idx inbp skts tids CSKEW SOCKETS TIDS DONE.
      pcofix CIH_TMP. i.
      destruct tids as [|tid_j tids]; ss.
      { replace (Ret tt;; k) with k by (symmetry; apply bind_ret_l_eq).
        eapply paco3_mon; eauto.
      }

      (* call OSJoinSocket *)
      eapply sim_ose_call; eauto.
      { econs 1. }
      { simpl_itree_goal. unfold mcast_join. simpl_itree_goal. ss. }
      { i. ss. subst. econs 3. eauto. }
      i. ss. subst.
      esplits.
      { econs 3; eauto. }
      erewrite sockets_of_accept_msgs; eauto.
      inv ADV_LCLOCK.
      remember (inbp ++ AbstMW.filter_port dms) as inbp0.
      remember (DTime.succ gtm0) as gtm1.
      clear gtm0 ltm0 inbp dms lat idx CSKEW CSKEW0 H1 Heqgtm1 Heqinbp0 TLIM_NOT_OVER.
      rename gtm1 into gtm0, ltm1 into ltm0, inbp0 into inbp, H2 into CSKEW.

      (* latency *)
      eapply sim_latency; eauto.
      { i. ss. subst. econs 3. eauto. }
      i. subst.
      erewrite sockets_of_accept_msgs; eauto. ss.
      remember (inbp ++ AbstMW.filter_port dms) as inbp0.
      rewrite GTM0 in GTM. rewrite LTM0 in LTM.
      clear inbp dms gtm0 ltm0 lat0 CSKEW Heqinbp0 GTM0 LTM0.
      rename inbp0 into inbp, CSKEW0 into CSKEW.

      (* proc OSJoinSocket *)
      pfold. econs. i.
      inv STEP_TGT. inv ESTEP; ss; cycle 1.
      { inv IST_ADV_LCLOCK.
        esplits.
        { econs; eauto. econs 1. }
        { ss. }
        { inv NOT_NB_TGT. ss. }
        { ss. }
        right. eapply CIH_TMP0; eauto.
      }

      inv PROC_STEP; ss; cycle 1.
      { inv OS_RET. ss. }
      inv OS_STEP; ss. existT_elim. inv H5.
      inv IST_ADV_LCLOCK. inv JOIN_PKT.
      unfold Socket.make_mcast_pkt. ss.
      destruct (IP.mcast_ip (tid2ip tid_j)) eqn:MCAST_IP; cycle 1; ss.
      { exfalso. inv TIDS. rewrite MCAST_IP in *. ss. }
      destruct (txs =? rxs) eqn:ID_EQ.
      { rewrite Nat.eqb_eq in *. subst. ss. }
      rewrite Nat.eqb_refl in *.

      esplits.
      { econs; eauto. econs 4; eauto. }
      { ss. }
      { inv NOT_NB_TGT. ss. }
      { ss. econs. econs; eauto.
        move TASK_ID_IP at bottom.
        unfold task_id_ip, RTSysEnv.task_ips in *.
        specialize task_ips_local_ip. i.
        clear - TASK_ID_IP H1.
        eapply nth_error_In in TASK_ID_IP.
        rewrite Forall_forall in H1.
        exploit H1; eauto.
      }

      left.
      exploit (sockets_of_accept_msgs txs rxs inbp); eauto.
      unfold Socket.set_accept_msgs. ss. i.
      rewrite x0. clear x0.
      remember (inbp ++ AbstMW.filter_port dms) as inbp0.
      clear inbp dms Heqinbp0 WF_DMS.
      inv ADV_LCLOCK. rewrite H1 in LTM.
      assert (GTM0: gtm <= DTime.succ gtm1).
      { unfold DTime.succ. ss. nia. }
      remember (DTime.succ gtm1) as gtm0.
      clear gtm1 ltm1 te_tgt CSKEW Heqgtm0 GTM NOT_NB_TGT TLIM_OK H1.
      rename ltm' into ltm0, lat' into lat, inbp0 into inbp, H2 into CSKEW, GTM0 into GTM.

      (* latency *)
      eapply sim_latency; eauto.
      { i. ss. subst. econs 3. eauto. }
      i. subst.
      erewrite sockets_of_accept_msgs; eauto. ss.
      remember (inbp ++ AbstMW.filter_port dms) as inbp0.
      rewrite GTM0 in GTM. rewrite LTM0 in LTM.
      clear inbp dms gtm0 ltm0 lat CSKEW Heqinbp0 GTM0 LTM0.
      rename inbp0 into inbp, CSKEW0 into CSKEW.

      (* ret *)
      eapply sim_ose_ret; eauto.
      { unfold mcast_join. do 2 simpl_itree_goal. ss. }
      { s. i. subst. econs; eauto. }
      i. subst. fold mcast_join.
      esplits.
      { econs 3; eauto. }
      right. eapply CIH_TMP; eauto.
      { inv ADV_LCLOCK. ss. }
      { inv TIDS. ss. }
      { i. subst. eapply DONE; eauto.
        - unfold DTime.succ in *. ss. nia.
        - nia.
      }
    Qed.

    Lemma sim_final
          (r: DTime.t -> Node.istate node_src ->
              Node.istate node_tgt -> Prop)
          gtm ltm lat
          ist_amw idx tlim skts tmr
          (itr itr_act: itree progE unit)
          (CSKEW: valid_clock_skew gtm ltm)
          (CIH_OFF:
             forall gtm,
               r gtm
                 (AbstMW.State tid ip snode AbstMW.Off)
                 (OSNode.Off prog))
          (ITREE_STAR: itree_tau_star itr itr_act)
          (OBS_OSE: observe itr_act = RetF tt)
          (SILENT_SRC:
             forall gtm' ltm' dms ist_amw'
               (TIME_NOT_OVER: OSNode.is_time_limit_over ltm' tlim = false)
               (CSKEW: valid_clock_skew gtm' ltm')
               (ACCEPT: ist_amw' = AbstMW.accept_packets dms ist_amw),
               AbstMW.istep
                 gtm' tid ip snode
                 ist_amw' (Z0, []) None ist_amw'):
      paco3 (_sim_nstates _ _) r
            gtm
            (AbstMW.State tid ip snode ist_amw)
            (OSNode.On prog ltm lat
                       (OSNode.Proc prog (OS.State skts tmr tlim OS.Idle) (idx, itr))).
    Proof.
      rewrite <- (AbstMW_accept_packets_nil _ ist_amw).
      rewrite <- (sockets_accept_msgs_nil skts).
      remember (@nil Packet.msg_t) as dms. clear Heqdms.
      revert gtm lat ltm itr idx dms CSKEW ITREE_STAR OBS_OSE.

      pcofix CIH_TMP. i.
      eapply sim_latency; eauto.
      { i. subst. rewrite AbstMW_accept_packets_acc. eauto. }
      i. subst.
      pfold. econs. i.
      inv STEP_TGT; ss. inv ESTEP; ss; cycle 1.
      { (* off *)
        esplits.
        { econs; eauto. econs 1. }
        { ss. }
        { inv NOT_NB_TGT. ss. }
        { ss. }
        inv IST_ADV_LCLOCK.
        right. eapply CIH_OFF.
      }

      (* proc step *)
      inv PROC_STEP; cycle 1.
      { inv OS_STEP. }
      { inv OS_RET. ss. }

      inv PEFF_STEP; ss; cycle 1.
      { (* sys event *)
        inv AT_EVT. existT_elim. subst.
        exploit (iprog_itree_tau_star_until_zero spec_itree); eauto. i.
        exploit (@iprog_two_taus_det progE); [exact PROG_SILENT_STEPS|exact x0|]. i. des.
        - exploit iprog_observe_eq; try exact x1. s. i. des; try congr.
        - exploit iprog_observe_eq; try exact x1. s. i. des; try congr.
      }
      { (* itree step *)
        esplits.
        { econs; eauto.
          do 2 rewrite AbstMW_accept_packets_acc.
          eapply SILENT_SRC; eauto.
        }
        { ss. }
        { inv NOT_NB_TGT. ss. }
        { ss. }
        do 2 rewrite sockets_accept_msgs_acc in *.
        inv IST_ADV_LCLOCK. destruct pst'.
        right. eapply CIH_TMP; eauto.
        - inv ADV_LCLOCK. ss.
        - move ITREE_STAR at bottom.
          exploit tau_steps_itree_tau_star.
          { eapply Prog.tau_steps_app; [eauto|].
            econs 2; eauto. econs 1. }
          i. eapply itree_tau_star_until_observe; eauto. congr.
      }
      { (* final *)
        esplits.
        { econs; eauto.
          do 2 rewrite AbstMW_accept_packets_acc.
          eapply SILENT_SRC; eauto.
        }
        { ss. }
        { inv NOT_NB_TGT. ss. }
        { ss. }
        do 2 rewrite sockets_accept_msgs_acc in *.
        inv IST_ADV_LCLOCK. destruct pst_m.
        right. eapply CIH_TMP; eauto.
        - inv ADV_LCLOCK. ss.
        - move ITREE_STAR at bottom.
          exploit tau_steps_itree_tau_star; eauto. s. i.
          eapply itree_tau_star_until_observe; eauto. congr.
      }
      { (* UB *)
        exfalso.
        exploit tau_steps_itree_tau_star; try exact PROG_SILENT_STEPS. s. i.
        exploit itree_tau_star_until_observe; [exact x0|exact ITREE_STAR|congr|].
        i. inv PROG_STUCK. inv x1; ss.
        - destruct pst_m. destruct n.
          + apply NOT_FINAL. esplits. econs; eauto.
          + apply STUCK_STEP. esplits. econs; eauto.
        - destruct pst_m. destruct n.
          + apply STUCK_STEP. esplits. econs; eauto.
          + apply STUCK_STEP. esplits. econs; eauto.
      }
      { (* os call *)
        inv AT_EVT. existT_elim. subst.
        exploit (iprog_itree_tau_star_until_zero spec_itree); eauto. i.
        exploit (@iprog_two_taus_det progE); [exact PROG_SILENT_STEPS|exact x0|]. i. des.
        - exploit iprog_observe_eq; try exact x1. s. i. des; try congr.
        - exploit iprog_observe_eq; try exact x1. s. i. des; try congr.
      }
      Unshelve.
      auto.
    Qed.

    Lemma process_firstn_end
          S A (f: A -> S -> S) l s0
          m n
          (M: length l <= m)
          (N: length l <= n):
      process_firstn f l s0 m = process_firstn f l s0 n.
    Proof.
      do 2 rewrite process_firstn_spec.
      do 2 (rewrite firstn_all2; auto).
      do 2 (rewrite skipn_all2; auto).
    Qed.

    Lemma process_firstn_app
          S A (f: A -> S -> S) l1 l2 s0 n s l
          (LEN: length l1 >= n)
          (FIRSTN1: (s, l) = process_firstn f l1 s0 n):
      (s, l ++ l2) = process_firstn f (l1 ++ l2) s0 n.
    Proof.
      rewrite process_firstn_spec in *.
      rewrite firstn_app, skipn_app.
      replace (n - length l1) with 0 by nia. ss.
      rewrite app_nil_r.
      inv FIRSTN1. ss.
    Qed.

    Lemma process_one
          sytm inbp inbc inbn n
          inbc0 inbn0 inbp0
          inbc1 inbn1 inbp1
          l
          (LEN: length inbp >= n)
          (FETCHN0: (inbc0, inbn0, inbp0) =
                    process_firstn (AbstMW.fetch_one_msg sytm) inbp
                                   (inbc, inbn) n)
          (FETCHN1: (inbc1, inbn1, inbp1) =
                    process_firstn (AbstMW.fetch_one_msg sytm) (inbp ++ l)
                                   (inbc, inbn) (S n)):
      (inbp0 = [] /\ l = [] /\ inbp1 = [] /\ inbc1 = inbc0 /\ inbn1 = inbn0) \/
      (exists pkt,
          inbp0 ++ l = pkt :: inbp1 /\
          (inbc1, inbn1) = AbstMW.fetch_one_msg sytm pkt (inbc0, inbn0)).
    Proof.
      rewrite process_firstn_spec in *.
      destruct (inbp0 ++ l) as [|pkt inbp1'] eqn:INBP.
      - left.
        destruct inbp0, l; [|ss|ss|ss].
        rewrite app_nil_r in *. inv FETCHN0.
        exploit skipn_nil_implies; eauto. i.
        rewrite firstn_all2 in *; try nia.
        rewrite skipn_all2 in *; try nia.
        inv FETCHN1. rewrite <- H2 in *. inv H4. eauto.
      - right.
        replace (firstn (S n) (inbp ++ l)) with (firstn n inbp ++ [pkt]) in *; cycle 1.
        { inv FETCHN0.
          specialize (firstn_skipn n inbp). i.
          rewrite <- H1 at 2.
          rewrite <- app_assoc.
          rewrite firstn_app.
          rewrite firstn_length.
          rewrite min_l; auto.
          replace (S n - n) with 1 by nia.
          rewrite INBP.
          rewrite firstn_all2 with (n := S n); cycle 1.
          { etrans; try eapply firstn_le_length. nia. }
          ss.
        }
        replace (skipn (S n) (inbp ++ l)) with inbp1' in *; cycle 1.
        { specialize (firstn_skipn n inbp). i.
          replace inbp0 with (skipn n inbp) in * by (inv FETCHN0; ss).
          rewrite <- H1.
          rewrite <- app_assoc.
          rewrite INBP.
          rewrite skipn_app.
          rewrite firstn_length.
          rewrite min_l; auto.
          replace (S n - n) with 1 by nia.
          rewrite skipn_all2; ss.
          etrans; try eapply firstn_le_length. nia.
        }
        inv FETCHN0. inv FETCHN1.
        rewrite fold_left_app in H3.
        rewrite <- H2 in H3. ss. unfold flip in H3.
        esplits; eauto.
    Qed.

    Lemma recvfrom_inv
          sytm inbp inbc inbn n
          inbc0 inbn0 inbp0
          inbc1 inbn1 inbp1
          txs rxs l skts' obs
          (ID: txs =? rxs = false)
          (LEN: length inbp >= n)
          (FETCHN0: (inbc0, inbn0, inbp0) =
                    process_firstn (AbstMW.fetch_one_msg sytm) inbp
                                   (inbc, inbn) n)
          (FETCHN1: (inbc1, inbn1, inbp1) =
                    process_firstn (AbstMW.fetch_one_msg sytm) (inbp ++ l)
                                   (inbc, inbn) (S n))
          (RECV: Socket._recvfrom_skts (sockets_of txs rxs (inbp0 ++ l)) rxs = (skts', obs)):
      match obs with
      | None =>
        inbp0 = [] /\
        l = [] /\
        skts' = sockets_of txs rxs [] /\
        inbc1 = inbc0 /\
        inbn1 = inbn0 /\
        inbp1 = []
      | Some pld =>
        exists pkt,
        pld = pkt.(Packet.payload) /\
        inbp0 ++ l = pkt :: inbp1 /\
        skts' = sockets_of txs rxs inbp1 /\
        (inbc1, inbn1) = AbstMW.fetch_one_msg sytm pkt (inbc0, inbn0)
      end.
    Proof.
      revert RECV. unfold sockets_of, Socket._recvfrom_skts, repl_byid. ss.
      condtac; ss. rewrite Nat.eqb_refl. ss.
      exploit process_one; eauto. i. des; subst; ss.
      - inv RECV. esplits; eauto.
      - revert RECV. unfold Socket._recvfrom_skt. ss.
        rewrite x0. ss. i. inv RECV.
        esplits; eauto.
    Qed.

    Lemma fetch_msg_eq
          sytm pkt (inbc inbn: list bytes?):
      MWITree.fetch_msg sytm (firstn pld_size (Packet.payload pkt)) (inbc, inbn) =
      AbstMW.fetch_one_msg sytm pkt (inbc, inbn).
    Proof.
      unfold MWITree.fetch_msg, AbstMW.fetch_one_msg.
      unfold AbstMW.parse_pld.
      condtac; ss.
      - condtac; ss.
        rewrite Bool.negb_true_iff in COND. rewrite Nat.eqb_neq in COND.
        rewrite Nat.ltb_ge in COND0.
        specialize (firstn_length pld_size (Packet.payload pkt)). i.
        rewrite min_l in H1; ss.
      - rewrite Bool.negb_false_iff in COND. rewrite Nat.eqb_eq in COND.
        destruct (length (Packet.payload pkt) <? pld_size) eqn:COND0.
        { rewrite Nat.ltb_lt in COND0.
          specialize (firstn_length pld_size (Packet.payload pkt)). i.
          rewrite min_r in H1; nia.
        }
        cut (forall inbc tid_s msg,
                MWITree.insert_msg inbc tid_s msg = AbstMW.update_msg inbc tid_s msg).
        { i. des_ifs; f_equal; eauto. }
        clear.
        unfold AbstMW.update_msg.
        induction inbc; i; ss.
        destruct tid_s; ss. rewrite <- IHinbc. refl.
    Qed.

    Lemma fetch_one_msg_length
          sytm pm inbc_init inbn_init
          inbc inbn
          (FETCH: (inbc, inbn) = AbstMW.fetch_one_msg sytm pm (inbc_init, inbn_init)):
      (<<INBC: length inbc = length inbc_init>>) /\
      (<<INBN: length inbn = length inbn_init>>).
    Proof.
      revert FETCH. unfold AbstMW.fetch_one_msg.
      des_ifs; i; inv FETCH; split; ss.
      - unfold AbstMW.update_msg.
        specialize (replace_nth_spec _ inbc_init n0 (Some b)). i. des.
        + unnw. rewrite <- H2 at 2. ss.
        + rewrite H3, H1. repeat rewrite app_length. ss.
      - unfold AbstMW.update_msg.
        specialize (replace_nth_spec _ inbn_init n0 (Some b)). i. des.
        + unnw. rewrite <- H2 at 2. ss.
        + rewrite H3, H1. repeat rewrite app_length. ss.
    Qed.

    Lemma process_firstn_length
          sytm inbp_init inbc_init inbn_init n
          inbc inbn inbp
          (FETCHN: (inbc, inbn, inbp) =
                   process_firstn (AbstMW.fetch_one_msg sytm) inbp_init (inbc_init, inbn_init) n):
      (<<INBC: length inbc = length inbc_init>>) /\
      (<<INBN: length inbn = length inbn_init>>).
    Proof.
      rewrite process_firstn_spec in FETCHN. inv FETCHN.
      remember (firstn n inbp_init) as l. clear n inbp_init Heql.
      revert inbc_init inbn_init inbc inbn H2.
      induction l; ss; i.
      { inv H2. ss. }
      destruct (flip (AbstMW.fetch_one_msg sytm) (inbc_init, inbn_init) a) as [inbc' inbn'] eqn:FETCH.
      exploit fetch_one_msg_length; eauto. i. des.
      rewrite <- INBC, <- INBN. eauto.
    Qed.

    Lemma sim_fetch_msgs
          (r: DTime.t -> Node.istate node_src ->
              Node.istate node_tgt -> Prop)
          gtm ltm lat
          sytm inbp inbm
          tlim tmr txs rxs idx ast
          itr_pe
          n fetchn
          (CSKEW: valid_clock_skew gtm ltm)
          (SYTM_DIV: Nat.divide period sytm)
          (SYTM_MIN: sytm > period)
          (SYTM_MAX: sytm < MAX_TIME)
          (EXPIRED: sytm < ltm)
          (TLIM: tlim <= sytm + period - DELTA)
          (CIH_OFF:
             forall gtm,
               r gtm
                 (AbstMW.State tid ip snode AbstMW.Off)
                 (OSNode.Off prog))
          (ID_NEQ: txs =? rxs = false)
          (APP_ITR_OBS_RET: observe itr_pe = RetF ast)
          (N: n < num_tasks * 4)
          (LEN: n <= length inbp)
          (FETCHN : __guard__
                      (fetchn = process_firstn (AbstMW.fetch_one_msg sytm)
                                               inbp (inbm, repeat None num_tasks) n))
          (DONE:
             forall gtm0 ltm0 lat idx inbp0 n0 inbc1 inbn1 inbp1 inbp' itr_pe0
               (CSKEW: valid_clock_skew gtm0 ltm0)
               (EXPIRED: sytm < ltm0)
               (N: n0 <= num_tasks * 4)
               (FETCHN : (inbc1, inbn1, inbp1) =
                         process_firstn (AbstMW.fetch_one_msg sytm)
                                        inbp0 (inbm, repeat None num_tasks) n0)
               (PERIOD_BEGIN: snode.(SNode.period_begin) (Z.of_nat sytm) inbc1 itr_pe itr_pe0),
               paco3 (_sim_nstates _ _) r gtm0
                     (AbstMW.State tid ip snode
                                   (AbstMW.On (node:=snode) sytm inbp' inbn1
                                              (AbstMW.Running (List.repeat false num_tasks)) itr_pe0))
                     (OSNode.On prog ltm0 lat
                                (OSNode.Proc
                                   prog
                                   (OS.State (sockets_of txs rxs inbp') tmr
                                             (Some tlim) OS.Idle)
                                   (idx,
                                    '(mst', ast') <-
                                    ('(_, ast') <- MWITree.interp_send
                                                     tid app_mod txs sytm
                                                     (repeat false num_tasks)
                                                     ast inbc1 ;;
                                     Ret (inbn1, MWITree.reset_inbox inbc1, ast'));;
                                    Tau (MWITree.main_loop tid app_mod MWITree.ltb_max_time
                                                           txs rxs mst' ast' (sytm + period)))))):
      paco3 (_sim_nstates node_src node_tgt) r gtm
            (AbstMW.State tid ip snode
                          (AbstMW.On (node:=snode) sytm inbp inbm AbstMW.Ready itr_pe))
            (OSNode.On prog ltm lat
                       (OSNode.Proc
                          prog
                          (OS.State (sockets_of txs rxs (snd fetchn)) tmr
                                    (Some tlim) OS.Idle)
                          (idx,
                           '(mst', ast') <-
                           ('(inbc', inbn') <-
                            MWITree.fetch_msg_loop rxs sytm (num_tasks * 4 - n)
                                                   (fst (fst fetchn), snd (fst fetchn)) ;;
                            '(_, ast') <- MWITree.interp_send
                                           tid app_mod txs sytm
                                           (repeat false num_tasks)
                                           ast inbc' ;;
                            Ret ((inbn', MWITree.reset_inbox inbc'), ast'));;
                           Tau (MWITree.main_loop tid app_mod MWITree.ltb_max_time
                                                  txs rxs mst' ast' (sytm + period))))).
    Proof.
      revert gtm ltm lat idx inbp n fetchn CSKEW EXPIRED N LEN FETCHN.
      pcofix CIH_FETCH_MSGS. i.

      destruct (num_tasks * 4 - n) eqn:NLEFT; ss; try nia.
      eapply sim_ose_call; eauto.
      { econs 1. }
      { do 3 simpl_itree_goal. ss. }
      { i. subst. econs 6.
        eapply cskew_time_not_over; eauto; try nia. ss.
        rewrite Nat.leb_gt in *. nia.
      }
      i. subst.
      esplits.
      { match goal with
        | [|- AbstMW.istep _ _ _ _ ?ist_amw _ _ _] =>
          instantiate (1:=ist_amw)
        end.
        econs 6.
        eapply cskew_time_not_over; eauto; try nia. ss.
        rewrite Nat.leb_gt in *. nia.
      }
      exploit Nat.lt_le_trans; try exact EXPIRED; eauto.
      inv ADV_LCLOCK.
      remember (DTime.succ gtm0) as gtm1.
      clear gtm ltm lat idx CSKEW GTM LTM EXPIRED.
      clear gtm0 ltm0 CSKEW0 Heqgtm1 TLIM_NOT_OVER H1.
      rename gtm1 into gtm, ltm1 into ltm, lat0 into lat, H2 into CSKEW.
      intro EXPIRED.

      eapply sim_latency; eauto.
      { i. subst. econs 6.
        eapply cskew_time_not_over; eauto; try nia. ss.
        rewrite Nat.leb_gt in *. nia.
      }
      i. subst.
      rewrite AbstMW_accept_packets_acc.
      rewrite sockets_accept_msgs_acc.
      remember (dms ++ dms0) as dms'.
      erewrite sockets_of_accept_msgs; eauto.
      exploit Nat.lt_le_trans; try exact EXPIRED; eauto.
      clear dms dms0 Heqdms'. rename dms' into dms.
      clear gtm ltm lat CSKEW GTM LTM EXPIRED.
      rename gtm0 into gtm, ltm0 into ltm, CSKEW0 into CSKEW.
      intro EXPIRED.

      (* fetch one msg *)
      pfold. econs; i.
      inv STEP_TGT; ss. inv ESTEP; ss; cycle 1.
      { inv IST_ADV_LCLOCK.
        esplits; ss; eauto.
        econs; eauto. econs.
      }
      inv PROC_STEP; ss; cycle 1.
      { inv OS_RET. ss. }

      inv OS_STEP; ss.
      existT_elim. inv H5. inv RECVFROM.
      exploit (sockets_of_accept_msgs txs rxs (snd fetchn ++ AbstMW.filter_port dms)); eauto.
      ss. i. rewrite x0 in *. clear x0.

      move FETCHN at bottom. unguardH FETCHN.
      remember (process_firstn (AbstMW.fetch_one_msg sytm)
                               (inbp ++ AbstMW.filter_port dms ++ AbstMW.filter_port dms0)
                               (inbm, repeat None num_tasks) (S n)) as fetchn1.
      rename FETCHN into FETCHN0, Heqfetchn1 into FETCHN1.
      destruct fetchn as [[inbc0 inbn0] inbp0], fetchn1 as [[inbc1 inbn1] inbp1]. ss.
      rewrite <- app_assoc in RECVFROM0.
      exploit recvfrom_inv; try eapply RECVFROM0; try exact FETCHN0; try exact FETCHN1; auto. i.
      destruct obs0; cycle 1.
      { (* inbp empty *)
        clear CIH_FETCH_MSGS.
        des. subst. rewrite x1 in *. rewrite app_nil_r in *.
        esplits.
        { econs; eauto. econs 7; eauto.
          - move TLIM at bottom.
            move TLIM_OK at bottom.
            move SYTM_DIV at bottom.
            move SYTM_MIN at bottom.
            move EXPIRED at bottom.
            move CSKEW at bottom.
            clear - TLIM TLIM_OK SYTM_DIV SYTM_MIN EXPIRED CSKEW.
            apply Nat.leb_gt in TLIM_OK.
            unfold get_skwd_base_time, base_time.
            unfold valid_clock_skew, nat_diff, DTime.to_ns_rd, DELTA in *.
            eapply divide_range_eq; try eapply SYTM_DIV; try nia.
            { apply sub_mod_divide. nia. }
            revert CSKEW. condtac; i.
            + apply Nat.leb_le in COND.
              split; try nia.
              assert (ltm < gtm / DTime.units_per_ns + max_clock_skew) by nia.
              exploit (sub_mod_range period sytm ltm); try nia; auto. i.
              exploit (le_sub_mod period); try eapply Nat.lt_le_incl; try exact H1; nia.
            + apply Nat.leb_gt in COND.
              split; try nia.
              exploit (sub_mod_range period sytm ltm); try nia; auto. i.
              exploit (le_sub_mod period); try eapply Nat.lt_le_incl; try exact COND; try nia. i.
              etrans; try exact x0.
              etrans; try exact x1.
              eapply le_sub_mod; nia.
          - move TLIM at bottom.
            move TLIM_OK at bottom.
            move SYTM_DIV at bottom.
            move SYTM_MIN at bottom.
            move EXPIRED at bottom.
            move CSKEW at bottom.
            clear - TLIM TLIM_OK SYTM_DIV SYTM_MIN EXPIRED CSKEW.
            apply Nat.leb_gt in TLIM_OK.
            unfold valid_clock_skew, nat_diff, DTime.to_ns_rd, DTime.of_ns, DELTA in *. s.
            specialize DTime.units_per_ns_pos. i.
            revert CSKEW. condtac; i.
            + apply Nat.leb_le in COND. split.
              * assert (ltm - max_clock_skew < gtm / DTime.units_per_ns) by nia.
                rewrite (Nat.div_mod gtm DTime.units_per_ns); nia.
              * assert ((ltm + max_clock_skew) * DTime.units_per_ns <
                        (sytm + period - max_clock_skew - max_nw_delay) * DTime.units_per_ns) by nia.
                eapply Nat.le_lt_trans; try eapply H2.
                rewrite (Nat.div_mod gtm DTime.units_per_ns); [|nia].
                specialize max_clock_skew_pos. i.
                exploit (Nat.mod_upper_bound gtm DTime.units_per_ns); [nia|]. i.
                clear CSKEW H2 TLIM TLIM_OK SYTM_DIV SYTM_MIN EXPIRED. nia.
            + apply Nat.leb_gt in COND. split.
              * assert ((sytm - max_clock_skew) * DTime.units_per_ns <
                        (ltm - max_clock_skew) * DTime.units_per_ns) by nia.
                etrans; try eapply H2.
                rewrite (Nat.div_mod gtm DTime.units_per_ns); nia.
              * assert ((ltm + max_clock_skew) * DTime.units_per_ns <
                        (sytm + period - max_clock_skew - max_nw_delay) * DTime.units_per_ns) by nia.
                eapply Nat.le_lt_trans; try eapply H2.
                rewrite (Nat.div_mod gtm DTime.units_per_ns); [|nia].
                specialize max_clock_skew_pos. i.
                exploit (Nat.mod_upper_bound gtm DTime.units_per_ns); [nia|]. i.
                clear H2 TLIM TLIM_OK SYTM_DIV SYTM_MIN EXPIRED. nia.
          - rewrite FETCHN0.
            rewrite <- app_assoc, x1, app_nil_r.
            unfold AbstMW.fetch_msgs.
            rewrite process_firstn_spec in FETCHN0. inv FETCHN0.
            exploit skipn_nil_implies; eauto. i.
            unfold num_tasks in *.
            eapply process_firstn_end; try nia.
          - econs; eauto.
        }
        { ss. }
        { inv NOT_NB_TGT. ss. }
        { ss. }

        inv IST_ADV_LCLOCK. left.
        eapply sim_ose_ret; eauto.
        { inv ADV_LCLOCK. ss. }
        { do 3 simpl_itree_goal. ss. }
        { s. i. subst. econs 6.
          eapply cskew_time_not_over; eauto; try nia. ss.
          rewrite Nat.leb_gt in *. nia.
        }
        i. subst.
        esplits.
        { econs 6.
          eapply cskew_time_not_over; eauto; try nia. ss.
          rewrite Nat.leb_gt in *. nia.
        }
        left.
        erewrite sockets_of_accept_msgs; eauto. s.
        rewrite bind_ret_l_eq.

        inv ADV_LCLOCK0.
        eapply paco3_mon; eauto. eapply DONE; eauto.
        - inv ADV_LCLOCK. unfold DTime.succ in *. ss. nia.
        - econs; eauto.
      }

      des. subst. rewrite x1 in *.
      destruct n0.
      { (* last fetch *)
        clear CIH_FETCH_MSGS.
        esplits.
        { econs; eauto. econs 7; eauto.
          - move TLIM at bottom.
            move TLIM_OK at bottom.
            move SYTM_DIV at bottom.
            move SYTM_MIN at bottom.
            move EXPIRED at bottom.
            move CSKEW at bottom.
            clear - TLIM TLIM_OK SYTM_DIV SYTM_MIN EXPIRED CSKEW.
            apply Nat.leb_gt in TLIM_OK.
            unfold get_skwd_base_time, base_time.
            unfold valid_clock_skew, nat_diff, DTime.to_ns_rd, DELTA in *.
            eapply divide_range_eq; try eapply SYTM_DIV; try nia.
            { apply sub_mod_divide. nia. }
            revert CSKEW. condtac; i.
            + apply Nat.leb_le in COND.
              split; try nia.
              assert (ltm < gtm / DTime.units_per_ns + max_clock_skew) by nia.
              exploit (sub_mod_range period sytm ltm); try nia; auto. i.
              exploit (le_sub_mod period); try eapply Nat.lt_le_incl; try exact H1; nia.
            + apply Nat.leb_gt in COND.
              split; try nia.
              exploit (sub_mod_range period sytm ltm); try nia; auto. i.
              exploit (le_sub_mod period); try eapply Nat.lt_le_incl; try exact COND; try nia. i.
              etrans; try exact x0.
              etrans; try exact x1.
              eapply le_sub_mod; nia.
          - move TLIM at bottom.
            move TLIM_OK at bottom.
            move SYTM_DIV at bottom.
            move SYTM_MIN at bottom.
            move EXPIRED at bottom.
            move CSKEW at bottom.
            clear - TLIM TLIM_OK SYTM_DIV SYTM_MIN EXPIRED CSKEW.
            apply Nat.leb_gt in TLIM_OK.
            unfold valid_clock_skew, nat_diff, DTime.to_ns_rd, DTime.of_ns, DELTA in *. s.
            specialize DTime.units_per_ns_pos. i.
            revert CSKEW. condtac; i.
            + apply Nat.leb_le in COND. split.
              * assert (ltm - max_clock_skew < gtm / DTime.units_per_ns) by nia.
                rewrite (Nat.div_mod gtm DTime.units_per_ns); nia.
              * assert ((ltm + max_clock_skew) * DTime.units_per_ns <
                        (sytm + period - max_clock_skew - max_nw_delay) * DTime.units_per_ns) by nia.
                eapply Nat.le_lt_trans; try eapply H2.
                rewrite (Nat.div_mod gtm DTime.units_per_ns); [|nia].
                specialize max_clock_skew_pos. i.
                exploit (Nat.mod_upper_bound gtm DTime.units_per_ns); [nia|]. i. nia.
            + apply Nat.leb_gt in COND. split.
              * assert ((sytm - max_clock_skew) * DTime.units_per_ns <
                        (ltm - max_clock_skew) * DTime.units_per_ns) by nia.
                etrans; try eapply H2.
                rewrite (Nat.div_mod gtm DTime.units_per_ns); nia.
              * assert ((ltm + max_clock_skew) * DTime.units_per_ns <
                        (sytm + period - max_clock_skew - max_nw_delay) * DTime.units_per_ns) by nia.
                eapply Nat.le_lt_trans; try eapply H2.
                rewrite (Nat.div_mod gtm DTime.units_per_ns); [|nia].
                specialize max_clock_skew_pos. i.
                exploit (Nat.mod_upper_bound gtm DTime.units_per_ns); [nia|]. i. nia.
          - rewrite FETCHN1.
            rewrite <- app_assoc.
            unfold AbstMW.fetch_msgs.
            replace (length task_ips * 4) with (S n); ss.
            unfold num_tasks in *. nia.
          - econs; eauto.
        }
        { ss. }
        { inv NOT_NB_TGT. ss. }
        { ss. }

        inv IST_ADV_LCLOCK. left.
        eapply sim_ose_ret; eauto.
        { inv ADV_LCLOCK. ss. }
        { do 3 simpl_itree_goal. ss. }
        { s. i. subst. econs 6.
          eapply cskew_time_not_over; eauto; try nia. ss.
          rewrite Nat.leb_gt in *. nia.
        }
        i. subst.
        esplits.
        { econs 6.
          eapply cskew_time_not_over; eauto; try nia. ss.
          rewrite Nat.leb_gt in *. nia.
        }
        left.
        erewrite sockets_of_accept_msgs; eauto. s.
        rewrite fetch_msg_eq. rewrite <- x3.
        rewrite bind_ret_l_eq.

        inv ADV_LCLOCK0.
        eapply paco3_mon; eauto. eapply DONE; eauto.
        - inv ADV_LCLOCK. nia.
        - econs; eauto.
      }

      (* list non-empty and fetch left *)
      clear DONE.
      esplits.
      { econs; eauto. econs 6.
        eapply cskew_time_not_over; eauto; try nia. ss.
        rewrite Nat.leb_gt in *. nia.
      }
      { ss. }
      { inv NOT_NB_TGT. ss. }
      { ss. }

      replace (S n0) with (num_tasks * 4 - (S n)) in IST_ADV_LCLOCK by nia.
      inv IST_ADV_LCLOCK. left.
      eapply sim_ose_ret; eauto.
      { inv ADV_LCLOCK. ss. }
      { do 3 simpl_itree_goal. ss. }
      { s. i. subst. econs 6.
        eapply cskew_time_not_over; eauto; try nia. ss.
        rewrite Nat.leb_gt in *. nia.
      }
      i. subst.
      esplits.
      { econs 6.
        eapply cskew_time_not_over; eauto; try nia. ss.
        rewrite Nat.leb_gt in *. nia.
      }
      erewrite sockets_of_accept_msgs; eauto. s.
      rewrite fetch_msg_eq. rewrite <- x3.
      rewrite <- (app_assoc inbp).

      right.
      rewrite <- bind_bind_eq.
      exploit process_firstn_app; try eapply FETCHN1.
      { rewrite process_firstn_spec in FETCHN0. inv FETCHN0.
        rewrite <- (firstn_skipn n inbp).
        rewrite <- app_assoc.
        rewrite x1.
        rewrite app_length.
        rewrite firstn_length.
        rewrite min_l; try nia. ss. nia.
      }
      instantiate (1 := AbstMW.filter_port dms1). i.
      inv ADV_LCLOCK0.
      exploit CIH_FETCH_MSGS; try eapply x0; [..|eauto]; eauto; try nia.
      { eapply Nat.lt_le_trans; eauto.
        inv ADV_LCLOCK. etrans; eauto. }
      { rewrite process_firstn_spec in FETCHN0. inv FETCHN0.
        rewrite <- (firstn_skipn n inbp).
        rewrite <- (app_assoc (firstn n inbp)).
        rewrite x1.
        do 2 rewrite app_length. ss.
        rewrite firstn_length.
        rewrite min_l; try nia. }
    Qed.

    Lemma unfold_interp_cases
          txs sytm sh
          (itr: itree (obsE +' abst_sendE) app_mod.(AppMod.abst_state_t)):
      (exists ast,
          (<<OBS_RET: observe itr = RetF ast>>) /\
          (<<UNFOLD: interp (MWITree.send_handler tid txs sytm) itr sh =
                     Ret (sh, ast)>>)) \/
      (exists itr',
          (<<OBS_TAU: observe itr = TauF itr'>>) /\
          (<<UNFOLD: interp (MWITree.send_handler tid txs sytm) itr sh =
                     Tau (interp (MWITree.send_handler tid txs sytm) itr' sh)>>)) \/
      (exists R (sys_ec: obsE R) k,
          (<<OBS_SYS: observe itr = VisF (inl1 sys_ec) k>>) /\
          (<<UNFOLD: interp (MWITree.send_handler tid txs sytm) itr sh =
                     Vis (subevent _ sys_ec)
                         (fun r => Tau (interp (MWITree.send_handler tid txs sytm) (k r) sh))>>)) \/
      (exists tid_d bs k,
          (<<OBS_SEND: observe itr = VisF (inr1 (BSendEvent tid_d bs)) k>>) /\
          (<<UNFOLD: interp (MWITree.send_handler tid txs sytm) itr sh =
                     x <- MWITree.send_handler tid txs sytm _ (inr1 (BSendEvent tid_d bs)) sh ;;
                       Tau (interp (MWITree.send_handler tid txs sytm) (k (snd x)) (fst x))>>)).
    Proof.
      destruct (observe itr) eqn:OBS.
      - left. esplits; eauto.
        eapply MWITree.unfold_interp_ret; eauto.
      - right. left. esplits; eauto.
        eapply MWITree.unfold_interp_tau; eauto.
      - destruct e.
        + do 2 right. left. esplits; eauto.
          destruct s.
          * eapply MWITree.unfold_interp_vis_sys; eauto.
          * eapply MWITree.unfold_interp_vis_sys; eauto.
        + destruct a; ss.
          do 3 right. esplits; eauto.
          eapply MWITree.unfold_interp_vis_send; eauto.
    Qed.

    Lemma app_cases
          txs rxs sytm inbn inbc itr_app sh
          itr1
          (ITR1: itr1 =
                 '(mst', ast') <-
                 ('(_, ast') <- interp (MWITree.send_handler tid txs sytm) itr_app sh ;;
                  Ret ((inbn, MWITree.reset_inbox inbc), ast')) ;;
                 Tau (MWITree.main_loop tid app_mod MWITree.ltb_max_time txs rxs mst' ast' (sytm + period))):
      (<<INF: itr1 = ITree.spin>>) \/
      (exists itr2 itr_app',
          (<<TAU: itree_tau_star itr1 itr2>>) /\
          (<<TAU_APP: itree_tau_star
                        (interp (MWITree.send_handler tid txs sytm) itr_app sh)
                        (interp (MWITree.send_handler tid txs sytm) itr_app' sh)>>) /\
          (<<TAU_SNODE: AbstAsyncSysModel.AANode.sh_tau_steps sh snode itr_app itr_app'>>) /\
          ((exists ast,
               (<<ITR2: itr2 =
                        (MWITree.main_loop tid app_mod MWITree.ltb_max_time txs rxs
                                           (inbn, MWITree.reset_inbox inbc) ast (sytm + period))>>) /\
               (<<OBS_APP: observe itr_app' = RetF ast>>) /\
               (<<APP: interp (MWITree.send_handler tid txs sytm) itr_app' sh =
                       (Ret (sh, ast))>>)) \/
           ((<<ITR2: itr2 =
                     '(mst', ast') <-
                     ('(_, ast') <- interp (MWITree.send_handler tid txs sytm) itr_app' sh ;;
                      Ret ((inbn, MWITree.reset_inbox inbc), ast')) ;;
                     Tau (MWITree.main_loop tid app_mod MWITree.ltb_max_time txs rxs mst' ast' (sytm + period))>>) /\
            __guard__ (
                (exists R (sys_ec: obsE R) k,
                    (<<OBS_APP: observe itr_app' = VisF (inl1 sys_ec) k>>) /\
                    (<<APP: interp (MWITree.send_handler tid txs sytm) itr_app' sh =
                            Vis (subevent _ sys_ec)
                                (fun r => Tau (interp (MWITree.send_handler tid txs sytm) (k r) sh))>>)) \/
                (exists tid_d sh' bs k,
                    (<<OBS_APP: observe itr_app' = VisF (inr1 (BSendEvent tid_d bs)) k>>) /\
                    (<<CHECK: check_send_hist sh tid_d = Some sh'>>) /\
                    (<<APP: interp (MWITree.send_handler tid txs sytm) itr_app' sh =
                            x <- (trigger
                                   (OSSendto txs (serialize_msg (sytm + period) tid
                                                                (resize_bytes msg_size bs))
                                             (tid2ip tid_d) port);;
                                 Ret (sh', tt)) ;;
                            Tau (interp (MWITree.send_handler tid txs sytm) (k (snd x)) (fst x))>>)))))).
    Proof.
      exploit itree_cases. i. des.
      { left. apply EqAxiom.bisimulation_is_eq. eapply INF. }
      right. revert itr_app ITR1.
      induction TAU; i.
      { subst.
        specialize (unfold_interp_cases txs sytm sh itr_app). i. des.
        - exfalso. rewrite UNFOLD in *. unguard. des; ss.
        - exfalso. rewrite UNFOLD in *. unguard. des; ss.
        - esplits; (try by econs 1).
          right. split; eauto. left. esplits; eauto.
        - ss. revert UNFOLD.
          unfold MWITree.bsendE_itree.
          destruct (check_send_hist sh tid_d) eqn:CHECK; i.
          + esplits; (try by econs 1).
            right. split; auto. right. esplits; eauto.
          + exfalso. rewrite UNFOLD in *. unguard. des; ss.
      }
      subst. move STEP at bottom.
      specialize (unfold_interp_cases txs sytm sh itr_app).
      i. des; revert STEP; rewrite UNFOLD.
      - do 3 simpl_itree_goal. ss. i. inv STEP.
        esplits.
        { econs 2; ss. econs 1. }
        { rewrite UNFOLD. econs 1. }
        { econs 1. }
        left. eauto.
      - do 2 simpl_itree_goal. ss. i. inv STEP.
        exploit IHTAU; eauto.
        { rewrite bind_bind_eq. refl. }
        i. des; esplits; eauto; econs 2; eauto; ss.
      - do 2 simpl_itree_goal. ss.
      - ss. unfold MWITree.bsendE_itree.
        destruct (check_send_hist sh tid_d) eqn:CHECK.
        { do 3 simpl_itree_goal. ss. }
        do 5 simpl_itree_goal. i. inv STEP.
        exploit IHTAU; eauto.
        { rewrite bind_bind_eq. refl. }
        i. des; esplits; eauto; try by (econs 2; eauto; ss).
        + econs 3; eauto; econs; eauto.
        + econs 3; eauto; econs; eauto.
    Qed.

    Lemma sh_tau_steps_cases
          sh ast1 ast2
          (TAU: AbstAsyncSysModel.AANode.sh_tau_steps sh snode ast1 ast2):
      (<<REFL: ast1 = ast2>>) \/
      exists ast',
        (<<TAU: AbstAsyncSysModel.AANode.sh_tau_steps sh snode ast1 ast'>>) /\
        ((<<PLUS: SNode.app_step snode ast' ast2>>) \/
         (exists snde tid msg,
             (<<SEND_EVENT: snde = AbstSendEvent tid msg>>) /\
             (<<AT_EVENT: SNode.at_event snode ast' (EventCall (inr1 snde))>>) /\
             (<<AFT_EVENT: SNode.after_event snode ast' (Event (inr1 snde) tt) ast2>>) /\
             (<<CHECK: check_send_hist sh tid = None>>))).
    Proof.
      induction TAU; eauto; right.
      - des; subst.
        + esplits; [econs 1|]; eauto.
        + esplits; [econs 2|]; eauto.
        + esplits; [econs 2|]; eauto. right. esplits; eauto.
      - des; subst.
        + esplits; [econs 1|]; eauto. right. esplits; eauto.
        + esplits; [econs 3|]; eauto.
        + esplits; [econs 3|]; eauto. right. esplits; eauto.
    Qed.

    Lemma sim_app
          (r: DTime.t -> Node.istate node_src ->
              Node.istate node_tgt -> Prop)
          txs rxs
          gtm ltm lat idx tlim
          sytm inbc (inbn: MWITree.inbox_t) inbp sh ast itr
          (CSKEW: valid_clock_skew gtm ltm)
          (SYTM_DIV: Nat.divide period sytm)
          (EXPIRED: sytm < ltm)
          (TLIM: tlim <= sytm + period - DELTA)
          (CIH_OFF:
             forall gtm,
               r gtm
                 (AbstMW.State tid ip snode AbstMW.Off)
                 (OSNode.Off prog))
          (ID_NEQ: txs =? rxs = false)
          (TAU: itree_tau_star
                  itr
                  ('(mst', ast') <-
                   ('(_, ast') <- interp (MWITree.send_handler tid txs sytm) ast sh ;;
                    Ret ((inbn, MWITree.reset_inbox inbc), ast')) ;;
                   Tau (MWITree.main_loop tid app_mod MWITree.ltb_max_time txs rxs mst' ast' (sytm + period))))
          (DONE:
             forall gtm ltm lat idx inbp itr_app itr_app' ast sh itr
               (CSKEW: valid_clock_skew gtm ltm)
               (TAU: itree_tau_star
                       itr
                       (MWITree.main_loop tid app_mod MWITree.ltb_max_time txs rxs
                                          (inbn, MWITree.reset_inbox inbc) ast (sytm + period)))
               (TAU_SNODE : AbstAsyncSysModel.AANode.sh_tau_steps sh snode itr_app itr_app')
               (PERIOD_END: observe itr_app' = RetF ast),
               paco3 (_sim_nstates node_src node_tgt) r gtm
                     (AbstMW.State tid ip snode
                                   (AbstMW.On (node:=snode) sytm inbp inbn
                                              (AbstMW.Running sh) itr_app))
                     (OSNode.On prog ltm lat
                                (OSNode.Proc
                                   prog
                                   (OS.State (sockets_of txs rxs inbp) Timer.Init
                                             (Some tlim) OS.Idle)
                                   (idx, itr)))):
      paco3 (_sim_nstates node_src node_tgt) r gtm
            (AbstMW.State tid ip snode
                          (AbstMW.On (node:=snode) sytm inbp inbn
                                     (AbstMW.Running sh) ast))
            (OSNode.On prog ltm lat
                       (OSNode.Proc
                          prog
                          (OS.State (sockets_of txs rxs inbp) Timer.Init
                                    (Some tlim) OS.Idle)
                          (idx, itr))).
    Proof.
      revert gtm ltm lat idx itr inbp sh ast CSKEW EXPIRED TAU.
      pcofix CIH_TMP. i.
      exploit (@app_cases txs rxs sytm inbn inbc ast sh); try refl. i. des.
      { (* inftau *)
        rewrite -> INF in *.
        exploit itree_tau_star_spin; eauto. i. subst.
        clear DONE CIH_TMP TAU INF.
        revert gtm ltm lat idx inbp CSKEW EXPIRED.
        pcofix CIH_TMP. i.

        pfold. econs. i.
        inv STEP_TGT; ss. inv ESTEP; ss; cycle 2.
        { (* off *)
          esplits.
          { econs; eauto. econs 1. }
          { ss. }
          { inv NOT_NB_TGT. ss. }
          { ss. }
          inv IST_ADV_LCLOCK.
          right. eapply CIH_TMP0. eapply CIH_OFF.
        }
        { (* latency *)
          esplits.
          { econs; eauto. econs 6.
            eapply cskew_time_not_over; eauto; try nia. ss.
            rewrite Nat.leb_gt in *. nia.
          }
          { ss. }
          { inv NOT_NB_TGT. ss. }
          { ss. }
          inv IST_ADV_LCLOCK.
          inv ADV_LCLOCK.
          right. eapply CIH_TMP; eauto. nia.
        }

        (* proc step *)
        inv PROC_STEP; cycle 1.
        { inv OS_STEP. }
        { inv OS_RET. ss. }

        inv PEFF_STEP; ss.
        { destruct pst_m.
          exploit tau_steps_itree_tau_star; eauto. s. i.
          exploit spin_itree_tau_star; eauto. i. subst.
          inv AT_EVT.
          replace (observe ITree.spin) with (@TauF progE unit (itree progE unit) ITree.spin) in *; ss.
        }
        { destruct pst_m.
          exploit tau_steps_itree_tau_star; eauto. s. i.
          exploit spin_itree_tau_star; eauto. i. subst.
          inv AT_EVT.
          replace (observe ITree.spin) with (@TauF progE unit (itree progE unit) ITree.spin) in *; ss.
        }
        { exploit Prog.tau_steps_app; eauto; i.
          { econs 2; [|econs 1]. ss. eauto. }
          destruct pst'.
          exploit tau_steps_itree_tau_star; eauto. s. i.
          exploit spin_itree_tau_star; eauto. i. subst.
          esplits.
          { econs; eauto. econs 6.
            eapply cskew_time_not_over; eauto; try nia. ss.
            rewrite Nat.leb_gt in *. nia.
          }
          { ss. }
          { inv NOT_NB_TGT. ss. }
          { ss. }
          inv IST_ADV_LCLOCK.
          inv ADV_LCLOCK.
          exploit (sockets_of_accept_msgs txs rxs inbp); eauto.
          unfold Socket.set_accept_msgs. ss. i.
          rewrite x2. clear x2.
          remember (inbp ++ AbstMW.filter_port dms) as inbp0.
          right. eapply CIH_TMP; eauto. nia.
        }
        { destruct pst_m.
          exploit tau_steps_itree_tau_star; eauto. s. i.
          exploit spin_itree_tau_star; eauto. i. subst.
          inv APP_STEP.
          replace (observe ITree.spin) with (@TauF progE unit (itree progE unit) ITree.spin) in *; ss.
        }
        { destruct pst_m.
          exploit tau_steps_itree_tau_star; eauto. s. i.
          exploit spin_itree_tau_star; eauto. i. subst.
          exfalso.
          inv PROG_STUCK. apply STUCK_STEP. destruct n.
          - esplits. econs.
            replace (observe ITree.spin) with (@TauF progE unit (itree progE unit) ITree.spin) in *; ss.
          - esplits. econs.
        }
      }
      { subst.
        eapply paco3_mon; eauto.
        eapply DONE; eauto.
        eapply itree_tau_star_trans; eauto.
      }

      pfold. econs. i.
      inv STEP_TGT; ss. inv ESTEP; ss; cycle 2.
      { (* off *)
        esplits.
        { econs; eauto. econs 1. }
        { ss. }
        { inv NOT_NB_TGT. ss. }
        { ss. }
        inv IST_ADV_LCLOCK.
        right. eapply CIH_TMP0. eapply CIH_OFF.
      }
      { (* latency *)
        esplits.
        { econs; eauto. econs 6.
          eapply cskew_time_not_over; eauto; try nia. ss.
          rewrite Nat.leb_gt in *. nia.
        }
        { ss. }
        { inv NOT_NB_TGT. ss. }
        { ss. }
        inv IST_ADV_LCLOCK.
        inv ADV_LCLOCK.
        right. eapply CIH_TMP; eauto. nia.
      }

      (* proc step *)
      inv PROC_STEP; cycle 1.
      { inv OS_STEP. }
      { inv OS_RET. ss. }

      inv PEFF_STEP; ss.
      { (* os call *)
        inv AT_EVT.
        exploit tau_steps_itree_tau_star; try exact PROG_SILENT_STEPS. s. i.
        exploit itree_tau_star_trans; [exact TAU|exact TAU0|]. i.
        unguardH x0. des.
        { exploit itree_event_eq; [exact x2|exact x1| | |]; try congr.
          { rewrite APP. do 2 simpl_itree_goal. ss. }
          i. subst.
          rewrite APP in OBS. revert OBS.
          do 2 simpl_itree_goal. ss. i. inv OBS. existT_elim. subst.
          revert H3. unfold embed, embed_event_call. destruct os_ec. i.
          destruct sys_ec; inv H3.
        }

        exploit itree_event_eq; [exact x2|exact x1| | |]; try congr.
        { rewrite APP. do 4 simpl_itree_goal. ss. }
        i. subst.
        rewrite APP in *. revert OBS.
        do 4 simpl_itree_goal. ss. i. inv OBS. existT_elim. subst.
        revert H3. unfold embed, embed_event_call. destruct os_ec. i. inv H3. existT_elim.
        unfold resum, ReSum_id, id_, Id_IFun in H4. subst.

        esplits.
        { econs; eauto. econs 6.
          eapply cskew_time_not_over; eauto; try nia. ss.
          rewrite Nat.leb_gt in *. nia.
        }
        { ss. }
        { inv NOT_NB_TGT. ss. }
        { ss. }
        inv IST_ADV_LCLOCK. inv OS_CALL. inv ADV_LCLOCK. existT_elim. subst.
        left.
        exploit (sockets_of_accept_msgs txs rxs inbp); eauto.
        unfold Socket.set_accept_msgs. ss. i.
        rewrite x0. clear x0.
        remember (inbp ++ AbstMW.filter_port dms) as inbp0.
        clear dms inbp DONE NOT_NB_TGT WF_DMS OS_IDLE Heqinbp0.
        exploit Nat.lt_le_trans; try exact EXPIRED; eauto.
        remember (DTime.succ gtm) as gtm0.
        clear gtm ltm idx CSKEW EXPIRED TLIM_OK PROG_SILENT_STEPS H1 Heqgtm0.
        rename gtm0 into gtm, ltm' into ltm, inbp0 into inbp, H2 into CSKEW.
        intro EXPIRED.

        eapply sim_latency; eauto.
        { s. i. subst. econs 6.
          eapply cskew_time_not_over; eauto; try nia. ss.
          rewrite Nat.leb_gt in *. nia.
        }
        i. subst.
        erewrite sockets_of_accept_msgs; eauto. ss.
        remember (inbp ++ AbstMW.filter_port dms) as inbp0.
        exploit Nat.lt_le_trans; try exact EXPIRED; eauto.
        clear gtm ltm CSKEW EXPIRED GTM LTM dms inbp Heqinbp0.
        rename gtm0 into gtm, ltm0 into ltm, CSKEW0 into CSKEW, inbp0 into inbp.
        intro EXPIRED.

        pfold. econs; i.
        inv STEP_TGT; ss. inv ESTEP; ss; cycle 1.
        { (* off *)
          esplits.
          { econs; eauto. econs 1. }
          { ss. }
          { inv NOT_NB_TGT. ss. }
          { ss. }
          inv IST_ADV_LCLOCK.
          right. eapply CIH_TMP0. eapply CIH_OFF.
        }

        inv PROC_STEP; ss; cycle 1.
        { inv OS_RET. ss. }
        existT_elim. subst.
        inv OS_STEP; ss. existT_elim. inv H5.
        esplits.
        { econs; eauto. econs 8.
          - eapply cskew_time_not_over; eauto; try nia. ss.
            rewrite Nat.leb_gt in *. nia.
          - eauto.
          - econs 3; eauto.
            + econs; eauto.
            + econs; eauto.
          - s. rewrite CHECK. f_equal. inv SENDTO.
            unfold Socket._sendto. ss.
            rewrite Nat.eqb_refl.
            unfold AbstMW.srl_pm. condtac; ss.
            + replace ip with (tid2ip tid); ss.
              move TASK_ID_IP at bottom.
              unfold tid2ip, task_id_ip, dest_ips in *.
              exploit nth_error_Some1; try rewrite TASK_ID_IP; ss. i.
              rewrite app_nth1; ss.
              eapply nth_error_nth; eauto.
            + apply Nat.ltb_ge in COND.
              exploit serialize_msg_size_lt_maxlen; eauto; cycle 1.
              { i. exploit Nat.le_lt_trans; try exact COND; try eapply x0. nia. }
              erewrite resize_bytes_length; eauto.
          - ss.
          - ss.
        }
        { ss. }
        { inv NOT_NB_TGT. ss. }
        { inv SENDTO. unfold Socket._sendto. ss.
          rewrite Nat.eqb_refl. condtac; ss.
          econs. econs. ss.
          eapply serialize_msg_size_lt_maxlen; eauto.
          erewrite resize_bytes_length; eauto.
        }

        inv IST_ADV_LCLOCK. inv ADV_LCLOCK.
        exploit (sockets_of_accept_msgs txs rxs inbp); eauto.
        unfold Socket.set_accept_msgs. ss. i.
        rewrite x0 in *. clear x0.
        exploit Nat.lt_le_trans; try exact EXPIRED; eauto.
        remember (DTime.succ gtm) as gtm0.
        remember (inbp ++ AbstMW.filter_port dms) as inbp0 in *.
        clear gtm ltm inbp CSKEW Heqgtm0 EXPIRED NOT_NB_TGT TLIM_OK H1 Heqinbp0.
        rename gtm0 into gtm, ltm' into ltm, inbp0 into inbp, H2 into CSKEW.
        intro EXPIRED.

        left. eapply sim_ose_ret; eauto.
        { ss. }
        { s. i. subst. econs 6.
          eapply cskew_time_not_over; eauto; try nia. ss.
          rewrite Nat.leb_gt in *. nia.
        }
        i. subst.
        esplits.
        { econs 6.
          eapply cskew_time_not_over; eauto; try nia. ss.
          rewrite Nat.leb_gt in *. nia.
        }
        erewrite sockets_of_accept_msgs; eauto. ss.

        inv ADV_LCLOCK.
        right. eapply CIH_TMP; eauto; try nia.
        do 4 simpl_itree_goal. econs 2; ss.
        rewrite bind_bind_eq. econs 1.
      }

      { (* sys event *)
        inv AT_EVT. existT_elim. subst.
        exploit tau_steps_itree_tau_star; try exact PROG_SILENT_STEPS. s. i.
        exploit itree_tau_star_trans; [exact TAU|exact TAU0|]. i.
        unguardH x0. des; cycle 1.
        { exploit itree_event_eq; [exact x2|exact x1| | |]; try congr.
          { rewrite APP. do 4 simpl_itree_goal. ss. }
          i. subst.
          rewrite APP in OBS. revert OBS.
          do 4 simpl_itree_goal. ss.
        }

        exploit itree_event_eq; [exact x2|exact x1| | |]; try congr.
        { rewrite APP. do 2 simpl_itree_goal. ss. }
        i. subst.
        rewrite APP in *. revert OBS.
        do 2 simpl_itree_goal. ss. i. inv OBS. existT_elim. subst.
        destruct sys_ec as [sys_ec|err_e], sys_ec0 as [sys_ec0|err_e0]; inv H3.
        - esplits.
          { econs; eauto. econs 8.
            - eapply cskew_time_not_over; eauto; try nia. ss.
              rewrite Nat.leb_gt in *. nia.
            - eauto.
            - econs 2.
              + econs; eauto.
              + econs; eauto.
              + eauto.
            - ss.
            - ss.
            - ss.
          }
          { ss. }
          { inv NOT_NB_TGT. ss.
            replace (base_time period ltm) with sytm; ss.
            move EXPIRED at bottom.
            move TLIM_OK at bottom. apply Nat.leb_gt in TLIM_OK.
            unfold base_time.
            eapply divide_range_eq; try eapply SYTM_DIV; try nia.
            - eapply sub_mod_divide. nia.
            - split; try nia.
              apply sub_mod_range; try nia; ss.
          }
          { ss. }
          inv IST_ADV_LCLOCK. inv AFT_EVT. existT_elim. subst.
          inv OBS. existT_elim. subst.
          exploit (sockets_of_accept_msgs txs rxs inbp); eauto.
          unfold Socket.set_accept_msgs. ss. i.
          rewrite x0. clear x0.
          rewrite <- bind_bind_eq.
          right. eapply CIH_TMP; eauto.
          + inv ADV_LCLOCK. ss.
          + inv ADV_LCLOCK. nia.
          + do 2 simpl_itree_goal. econs 2; ss.
            rewrite bind_bind_eq. econs 1.
        - esplits.
          { econs; eauto. econs 8.
            - eapply cskew_time_not_over; eauto; try nia. ss.
              rewrite Nat.leb_gt in *. nia.
            - eauto.
            - econs 2.
              + econs; eauto.
              + econs; eauto.
              + eauto.
            - ss.
            - ss.
            - ss.
          }
          { ss. }
          { inv NOT_NB_TGT. ss.
            replace (base_time period ltm) with sytm; ss.
            move EXPIRED at bottom.
            move TLIM_OK at bottom. apply Nat.leb_gt in TLIM_OK.
            unfold base_time.
            eapply divide_range_eq; try eapply SYTM_DIV; try nia.
            - eapply sub_mod_divide. nia.
            - split; try nia.
              apply sub_mod_range; try nia; ss.
          }
          { ss. }
          inv IST_ADV_LCLOCK. inv AFT_EVT. existT_elim. subst.
          inv OBS. existT_elim. subst.
          exploit (sockets_of_accept_msgs txs rxs inbp); eauto.
          unfold Socket.set_accept_msgs. ss. i.
          rewrite x0. clear x0.
          rewrite <- bind_bind_eq.
          right. eapply CIH_TMP; eauto.
          + inv ADV_LCLOCK. ss.
          + inv ADV_LCLOCK. nia.
          + do 2 simpl_itree_goal. econs 2; ss.
            rewrite bind_bind_eq. econs 1.
      }

      { (* itree step *)
        destruct pst'.
        exploit Prog.tau_steps_app; eauto; i.
        { econs 2; [|econs 1]. ss. eauto. }
        exploit tau_steps_itree_tau_star; try exact x1. s. i.
        exploit itree_tau_star_trans; [exact TAU|exact TAU0|]. i.
        exploit itree_tau_star_until_observe; [exact x2|exact x3|..]; ii.
        { move x1 at bottom. unguardH x0. des; subst; ss.
          - revert H1. rewrite APP. do 2 simpl_itree_goal. ss.
          - revert H1. rewrite APP. do 4 simpl_itree_goal. ss.
        }

        exploit sh_tau_steps_cases; try exact TAU_SNODE. i. des; subst.
        { esplits.
          { econs; eauto. econs 6.
            eapply cskew_time_not_over; eauto; try nia. ss.
            rewrite Nat.leb_gt in *. nia.
          }
          { ss. }
          { inv NOT_NB_TGT. ss. }
          { ss. }
          inv IST_ADV_LCLOCK. inv ADV_LCLOCK. ss.
          exploit (sockets_of_accept_msgs txs rxs inbp); eauto.
          unfold Socket.set_accept_msgs. ss. i.
          rewrite x5. clear x5.
          right. eapply CIH_TMP; eauto; try nia.
        }
        { esplits.
          { econs; eauto. econs 8; eauto.
            - eapply cskew_time_not_over; eauto; try nia. ss.
              rewrite Nat.leb_gt in *. nia.
            - econs 1; eauto.
            - ss.
          }
          { ss. }
          { inv NOT_NB_TGT. ss. }
          { ss. }
          inv IST_ADV_LCLOCK. inv ADV_LCLOCK. ss.
          exploit (sockets_of_accept_msgs txs rxs inbp); eauto.
          unfold Socket.set_accept_msgs. ss. i.
          rewrite x5. clear x5.
          right. eapply CIH_TMP; eauto; try nia.
        }
        { esplits.
          { econs; eauto. econs 8; eauto.
            - eapply cskew_time_not_over; eauto; try nia. ss.
              rewrite Nat.leb_gt in *. nia.
            - econs 3; eauto.
            - ss. rewrite CHECK. ss.
          }
          { ss. }
          { inv NOT_NB_TGT. ss. }
          { ss. }
          inv IST_ADV_LCLOCK. inv ADV_LCLOCK. ss.
          exploit (sockets_of_accept_msgs txs rxs inbp); eauto.
          unfold Socket.set_accept_msgs. ss. i.
          rewrite x5. clear x5.
          right. eapply CIH_TMP; eauto; try nia.
        }
      }

      { (* final *)
        inv APP_STEP.
        exploit tau_steps_itree_tau_star; try exact PROG_SILENT_STEPS. s. i.
        exploit itree_tau_star_trans; [exact TAU|exact TAU0|]. i.
        unguardH x0. des; subst.
        - exploit itree_event_eq; [exact x1|exact x2|..]; try congr.
          { rewrite APP. do 2 simpl_itree_goal. ss. }
          i. subst. revert OBS_RET. rewrite APP. do 2 simpl_itree_goal. ss.
        - exploit itree_event_eq; [exact x1|exact x2|..]; try congr.
          { rewrite APP. do 2 simpl_itree_goal. ss. }
          i. subst. revert OBS_RET. rewrite APP. do 4 simpl_itree_goal. ss.
      }

      { (* UB *)
        exfalso.
        inv PROG_STUCK. destruct pst_m. ss.
        destruct n; cycle 1.
        { apply STUCK_STEP. esplits. econs; eauto. }
        exploit tau_steps_itree_tau_star; try exact PROG_SILENT_STEPS. s. i.
        exploit itree_tau_star_trans; [exact TAU|exact TAU0|]. i.
        unguardH x0. des; rewrite APP in *; subst.
        - exploit itree_tau_star_until_observe; [exact x1|exact x2|..].
          { do 2 simpl_itree_goal. ss. }
          i. inv x0.
          + apply NOT_AT_EVENT. do 2 simpl_itree_goal. esplits. econs; ss.
          + apply STUCK_STEP. esplits. econs; eauto.
        - exploit itree_tau_star_until_observe; [exact x1|exact x2|..].
          { do 4 simpl_itree_goal. ss. }
          i. inv x0.
          + apply NOT_AT_EVENT. do 4 simpl_itree_goal. esplits. econs; ss.
          + apply STUCK_STEP. esplits. econs; eauto.
      }
      Unshelve.
      { auto. }
      { auto. }
      { auto. }
    Qed.

    Lemma sim_main_loop
          (r: DTime.t -> Node.istate node_src ->
              Node.istate node_tgt -> Prop)
          gtm ltm lat
          sytm inbp
          txs rxs tlim idx ast nsytm
          (CSKEW: valid_clock_skew gtm ltm)
          (SYTM_DIV: Nat.divide period sytm)
          (SYTM_MIN: sytm > period)
          (TLIM: tlim <= sytm - DELTA)
          (CIH_OFF:
             forall gtm,
               r gtm
                 (AbstMW.State tid ip snode AbstMW.Off)
                 (OSNode.Off prog))
          (ID_NEQ: txs =? rxs = false)
          (NSYTM: nsytm = sytm + period):
      paco3 (_sim_nstates node_src node_tgt) r gtm
            (AbstMW.State tid ip snode
                          (AbstMW.Prep (node:=snode) [] (sytm - max_clock_skew - max_nw_delay)
                                       inbp (Ret ast)))
            (OSNode.On prog ltm lat
                       (OSNode.Proc
                          prog
                          (OS.State (sockets_of txs rxs inbp) Timer.Init (Some tlim) OS.Idle)
                          (idx,
                           MWITree.main_loop tid app_mod MWITree.ltb_max_time txs rxs MWITree.init_mstore
                                             ast nsytm))).
    Proof.
      rewrite MWITree.unfold_main_loop.
      condtac; ss; i; cycle 1.
      { (* exceeded max time *)
        eapply sim_final; eauto.
        { econs 1. }
        { ss. }
        s. i. subst. econs 3.
        eapply cskew_time_not_over; eauto; try nia. ss.
        rewrite Nat.leb_gt in *. nia.
      }

      (** - Call OSWaitTimer *)
      eapply sim_ose_call; eauto.
      { econs 1. }
      { do 2 simpl_itree_goal. ss. }
      { i. ss. subst. econs 3.
        eapply cskew_time_not_over; eauto; try nia. ss.
        rewrite Nat.leb_gt in *. nia.
      }
      i. subst.
      esplits.
      { econs 5; eauto.
        eapply cskew_time_not_over; eauto; try nia. ss.
        rewrite Nat.leb_gt in *. nia.
      }
      erewrite sockets_of_accept_msgs; eauto. ss.
      remember (inbp ++ AbstMW.filter_port dms) as inbp0.
      clear gtm ltm lat idx dms inbp CSKEW GTM LTM Heqinbp0.
      inv ADV_LCLOCK.
      remember (DTime.succ gtm0) as gtm1.
      clear gtm0 ltm0 CSKEW0 TLIM_NOT_OVER Heqgtm1 H1.
      rename gtm1 into gtm, ltm1 into ltm, lat0 into lat, inbp0 into inbp, H2 into CSKEW.

      (** - Proc OSWaitTimer *)
      eapply sim_wait_timer; eauto.
      { nia. }
      { s. i. subst. econs 6; eauto.
        eapply cskew_time_not_over; eauto; try nia. ss.
        rewrite Nat.leb_gt in *. nia.
      }
      i. subst. left.
      erewrite sockets_of_accept_msgs; eauto. s.
      remember (inbp ++ AbstMW.filter_port dms) as inbp0.
      clear gtm ltm lat dms inbp CSKEW Heqinbp0.
      rename gtm0 into gtm, ltm0 into ltm, lat0 into lat, inbp0 into inbp, CSKEW0 into CSKEW.

      replace (sytm - max_clock_skew - max_nw_delay + max_clock_skew + max_nw_delay + period) with
          (sytm + period); cycle 1.
      { specialize period_cond. nia. }
      remember (sytm + period) as sytm'.
      assert (SYTM_DIV': Nat.divide period sytm').
      { subst. apply Nat.divide_add_r; ss. refl. }
      assert (SYTM_MIN': sytm' > period) by nia.
      clear tlim sytm Heqsytm' TLIM SYTM_DIV SYTM_MIN.
      rename tlim' into tlim, sytm' into sytm, TLIM0 into TLIM,
      SYTM_DIV' into SYTM_DIV, SYTM_MIN' into SYTM_MIN.
      unfold AbstMW.init_inbox.
      fold num_tasks.
      remember (repeat None num_tasks) as inbm.
      assert (INBM: length inbm = num_tasks).
      { subst. apply repeat_length. }
      replace (MWITree.init_inbox, MWITree.init_inbox) with (inbm, MWITree.init_inbox) by (subst; ss).
      clear Heqinbm.
      remember (Ret ast) as itr_pe.
      assert (APP_ITR_OBS_RET: observe itr_pe = RetF ast) by (subst; ss).
      clear Heqitr_pe.

      revert gtm ltm lat tlim sytm inbp inbm ast itr_pe
             TLIM COND CSKEW EXPIRED SYTM_DIV SYTM_MIN INBM APP_ITR_OBS_RET.
      pcofix CIH_MAIN_LOOP. i.

      (** - ret *)
      eapply sim_ose_ret; eauto.
      { do 2 simpl_itree_goal. ss. }
      { i. subst. ss. econs 6.
        eapply cskew_time_not_over; eauto; try nia. ss.
        rewrite Nat.leb_gt in *. nia.
      }
      i. subst.
      esplits.
      { econs 6.
        eapply cskew_time_not_over; eauto; try nia. ss.
        rewrite Nat.leb_gt in *. nia.
      }
      left.
      erewrite sockets_of_accept_msgs; ss.
      remember (inbp ++ AbstMW.filter_port dms) as inbp0.
      exploit Nat.lt_le_trans; try exact EXPIRED; eauto.
      clear gtm ltm lat inbp dms CSKEW GTM LTM EXPIRED Heqinbp0.
      inv ADV_LCLOCK.
      remember (DTime.succ gtm0) as gtm1.
      clear gtm0 ltm0 Heqgtm1 CSKEW0 TLIM_NOT_OVER H1.
      rename gtm1 into gtm, ltm1 into ltm, lat0 into lat, idx0 into idx, inbp0 into inbp, H2 into CSKEW.
      intro EXPIRED.

      (** - fetch_msgs *)
      specialize min_num_tasks. fold num_tasks. i.
      unfold MWITree.fetch_msgs, MWITree.init_inbox.
      pose (fetchn := process_firstn (AbstMW.fetch_one_msg sytm)
                                     inbp (inbm, repeat None num_tasks) 0).
      assert (FETCHN: fetchn = (inbm, repeat None num_tasks, inbp)).
      { unfold fetchn. destruct inbp; ss. }
      replace inbp with (snd fetchn) at 2 by (rewrite FETCHN; ss).
      pattern inbm at 2.
      replace inbm with (fst (fst fetchn)) at 1 by (rewrite FETCHN; ss).
      replace (repeat None num_tasks) with (snd (fst fetchn)) by (rewrite FETCHN; ss).
      clear FETCHN.
      assert (FETCHN: fetchn = process_firstn (AbstMW.fetch_one_msg sytm)
                                              inbp (inbm, repeat None num_tasks) 0) by auto.
      remember fetchn as fetchn'. clear fetchn Heqfetchn'.
      remember 0 as n in FETCHN.
      replace (num_tasks * 4) with (num_tasks * 4 - n) by (subst; nia).
      assert (N: n < num_tasks * 4) by nia.
      assert (LEN: n <= length inbp) by nia.
      clear Heqn.
      rename fetchn' into fetchn.
      guardH FETCHN.

      eapply sim_fetch_msgs; eauto.
      { rewrite <- Nat.ltb_lt. ss. }
      clear gtm ltm lat idx inbp fetchn n CSKEW EXPIRED H1 FETCHN N LEN COND.
      intros gtm ltm lat idx inbp_init n inbc inbn inbp_left inbp itr_init. i.

      exploit process_firstn_length; eauto. i. des.
      rewrite INBM in INBC.
      rewrite repeat_length in INBN.
      clear inbm n inbp_init inbp_left INBM N FETCHN.

      unfold MWITree.interp_send.
      inv PERIOD_BEGIN. rewrite RET in *. inv APP_ITR_OBS_RET.

      eapply sim_app; eauto.
      { econs 1. }
      clear itr_pe ast RET.
      clear gtm ltm lat idx inbp CSKEW EXPIRED. i.

      (** - next main loop *)
      revert TAU.
      replace (MWITree.reset_inbox inbc) with (repeat (@None (list byte)) num_tasks); cycle 1.
      { clear - INBC.
        remember num_tasks as n. clear Heqn.
        revert n INBC.
        induction inbc; ss; i.
        - rewrite <- INBC. ss.
        - rewrite <- INBC. ss.
          erewrite <- IHinbc; eauto.
      }

      rewrite MWITree.unfold_main_loop.
      condtac; ss; i; cycle 1.
      { (* exceeded max time *)
        eapply sim_final; eauto.
        s. i. subst. econs 6.
        eapply cskew_time_not_over; eauto; try nia. ss.
        rewrite Nat.leb_gt in *. nia.
      }

      (** - Call OSWaitTimer *)
      eapply sim_ose_call; eauto.
      { do 2 simpl_itree_goal. ss. }
      { i. ss. subst. econs 6.
        eapply cskew_time_not_over; eauto; try nia. ss.
        rewrite Nat.leb_gt in *. nia.
      }
      i. subst.
      esplits.
      { econs 9; eauto.
        - eapply cskew_time_not_over; eauto; try nia. ss.
          rewrite Nat.leb_gt in *. nia.
        - ss. unfold ITrSNode.period_end. setoid_rewrite PERIOD_END. ss.
      }
      erewrite sockets_of_accept_msgs; eauto. ss.
      remember (inbp ++ AbstMW.filter_port dms) as inbp0.
      clear gtm ltm lat idx dms inbp CSKEW GTM LTM Heqinbp0.
      inv ADV_LCLOCK.
      remember (DTime.succ gtm0) as gtm1.
      clear gtm0 ltm0 CSKEW0 TLIM_NOT_OVER Heqgtm1 H1.
      rename gtm1 into gtm, ltm1 into ltm, lat0 into lat, inbp0 into inbp, H2 into CSKEW.

      (** - Proc OSWaitTimer *)
      eapply sim_wait_timer; eauto.
      { s. i. subst. econs 6; eauto.
        eapply cskew_time_not_over; eauto; try nia. ss.
        rewrite Nat.leb_gt in *. nia.
      }
      i. subst.
      erewrite sockets_of_accept_msgs; eauto. s.
      remember (inbp ++ AbstMW.filter_port dms) as inbp0.
      clear gtm ltm lat dms inbp CSKEW Heqinbp0.
      rename gtm0 into gtm, ltm0 into ltm, lat0 into lat, inbp0 into inbp, CSKEW0 into CSKEW.

      right. eapply CIH_MAIN_LOOP; eauto; try nia.
      apply Nat.divide_add_r; try refl. ss.
    Qed.
  End LEMMAS.

  Lemma sim_abst_mw: fmsim_nodes node_src node_tgt.
  Proof.
    assert (TID: tid2ip tid = ip).
    { move TASK_ID_IP at bottom.
      unfold tid2ip, task_id_ip, dest_ips in *.
      exploit nth_error_Some1; try rewrite TASK_ID_IP; ss. i.
      rewrite app_nth1; ss.
      eapply nth_error_nth; eauto.
    }

    r. split; ss.
    i. rewrite TID in *. clear TID.
    esplits; eauto.
    apply sim_nstates_impl_fmsim.
    rename gtm_init into gtm.
    revert gtm.

    pcofix CIH_OFF. i.

    (** - Boot *)
    pfold. econs; eauto. i. ss.
    inv STEP_TGT. inv ESTEP; inv IST_ADV_LCLOCK; ss; cycle 1.
    { (* Off *)
      esplits; ss.
      { econs; eauto. econs 1. }
      { ss. }
      right. eapply CIH_OFF; eauto.
    }

    inv INIT_PROC; cycle 1.
    { (* UB *)
      exfalso. apply PROG_INIT_STATE.
      eexists (0, _). ss.
    }

    esplits.
    { econs; eauto. econs 1. }
    { ss. }
    { inv NOT_NB_TGT. ss. }
    { ss. }
    left.
    inv PROG_INIT_STATE.
    unfold spec_itree.
    update_times. rename ltm' into ltm.
    assert (CSKEW: valid_clock_skew gtm ltm).
    { inv ADV_LCLOCK. ss. }
    clear gtm_p dms WF_DMS NOT_NB_TGT ltm_p ADV_LCLOCK GTM_UPD te_tgt.

    (** - Call OSInitTimer *)
    eapply sim_ose_call; eauto.
    { econs 1. }
    { unfold MWITree.main_itree.
      simpl_itree_goal. ss. }
    { i. subst. econs. }
    i. ss. subst.
    esplits; [econs 1|].
    inv ADV_LCLOCK.
    remember (DTime.succ gtm0) as gtm1.
    clear dms gtm ltm lat_i idx CSKEW LTM GTM dms.
    clear gtm0 ltm0 CSKEW0 Heqgtm1 TLIM_NOT_OVER H1.
    rename gtm1 into gtm, ltm1 into ltm, H2 into CSKEW.

    (** - latency *)
    eapply sim_latency; eauto; i; ss; subst.
    { econs 1. }
    clear dms lat ltm gtm CSKEW GTM LTM.
    rename gtm0 into gtm, ltm0 into ltm, CSKEW0 into CSKEW.

    (** - Proc OS_STEP *)
    pfold. econs. i.
    inv STEP_TGT. inv ESTEP; cycle 1.
    { ss. }
    { inv IST_ADV_LCLOCK.
      esplits; ss; eauto.
      econs; eauto. econs.
    }
    rename lat' into lat.
    inv PROC_STEP; ss.
    2: { inv OS_RET. ss. }
    inv OS_STEP; ss.
    existT_elim. clear_tt.
    rename r0 into retz.
    inv IST_ADV_LCLOCK.

    esplits.
    { econs; eauto. econs 1. }
    { ss. }
    { inv NOT_NB_TGT. ss. }
    { ss. }

    left.
    update_times. rename ltm' into ltm.
    assert (CSKEW: valid_clock_skew gtm ltm).
    { inv ADV_LCLOCK. ss. }
    clear gtm_p ltm_p NOT_NB_TGT ADV_LCLOCK GTM_UPD dms WF_DMS te_tgt.

    (** - ret *)
    eapply sim_ose_ret; eauto.
    { unfold MWITree.main_itree.
      simpl_itree_goal. ss. }
    { i. subst. ss. econs 1. }
    i. subst. ss.
    esplits; [econs 1|]. left.
    inv ADV_LCLOCK.
    remember (DTime.succ gtm0) as gtm1.
    clear dms gtm ltm lat CSKEW GTM LTM.
    clear gtm0 ltm0 CSKEW0 Heqgtm1 TLIM_NOT_OVER H1.
    rename gtm1 into gtm, ltm1 into ltm, lat0 into lat, idx0 into idx, H2 into CSKEW.

    (* divide cases *)
    inv CREATE.
    { (* timer init failed *)
      destruct (Z.ltb_spec Z_mone 0); ss.
      eapply sim_final; eauto.
      { econs 1. }
      { ss. }
      { s. i. subst. econs 1. }
    }
    rewrite Z.ltb_irrefl.

    (** - Call OSGetTime *)
    eapply sim_ose_call; eauto.
    { econs 1. }
    { simpl_itree_goal. ss. }
    { i. ss. clarify. econs 1. }
    i. ss. subst.
    esplits; [econs 1|].
    inv ADV_LCLOCK.
    remember (DTime.succ gtm0) as gtm1.
    clear dms gtm ltm lat CSKEW GTM LTM.
    clear gtm0 ltm0 CSKEW0 Heqgtm1 TLIM_NOT_OVER H1.
    rename gtm1 into gtm, ltm1 into ltm, lat0 into lat, H2 into CSKEW.

    (** - latency *)
    eapply sim_latency; eauto; i; ss; subst.
    { econs 1. }
    clear dms lat ltm gtm CSKEW GTM LTM.
    rename gtm0 into gtm, ltm0 into ltm, CSKEW0 into CSKEW.

    (** - Proc OS_STEP *)
    pfold. econs. i.
    inv STEP_TGT. inv ESTEP; cycle 1.
    { ss. }
    { inv IST_ADV_LCLOCK.
      esplits; ss; eauto.
      econs; eauto. econs.
    }
    rename lat' into lat.
    inv PROC_STEP; ss.
    2: { inv OS_RET. ss. }
    inv OS_STEP; ss.
    existT_elim. clear_tt.
    inv IST_ADV_LCLOCK.

    esplits.
    { econs; eauto. econs 1. }
    { ss. }
    { inv NOT_NB_TGT. ss. }
    { ss. }

    left.
    update_times. rename ltm' into ltm.
    assert (CSKEW: valid_clock_skew gtm ltm).
    { inv ADV_LCLOCK. ss. }
    clear gtm_p NOT_NB_TGT ADV_LCLOCK GTM_UPD dms WF_DMS te_tgt.
    rename ltm_p into ltm_first.

    (** - ret *)
    eapply sim_ose_ret; eauto.
    { unfold MWITree.main_itree.
      simpl_itree_goal. ss. }
    { i. subst. ss. econs 1. }
    i. subst. ss.
    esplits; [econs 1|]. left.
    inv ADV_LCLOCK.
    remember (DTime.succ gtm0) as gtm1.
    clear dms gtm ltm lat idx CSKEW GTM LTM.
    clear gtm0 ltm0 CSKEW0 Heqgtm1 TLIM_NOT_OVER H1.
    rename gtm1 into gtm, ltm1 into ltm, lat0 into lat, idx0 into idx, H2 into CSKEW.

    (* divide cases *)

    destruct (Nat.leb_spec ltm_first (Z.to_nat Int64.max_unsigned)) as [RANGE_LTM_F|]; ss.
    2: { (* get_time failed *)
      eapply sim_final; eauto.
      { econs 1. }
      { ss. }
      { s. i. subst. econs 1. }
    }
    rewrite Nat2Z.id.
    destruct (Nat.eqb_spec ltm_first 0) as [|LTM_F_POS]; ss.
    { (* considered as failed *)
      eapply sim_final; eauto.
      { econs 1. }
      { ss. }
      { s. i. subst. econs 1. }
    }

    destruct (Nat.ltb_spec ltm_first MAX_TIME)
      as [LTM_F_MAXT|]; ss.
    2: { (* too late to start *)
      eapply sim_final; eauto.
      { econs 1. }
      { ss. }
      { s. i. subst. econs 1. }
    }

    (** - Call OSOpenSocket *)
    eapply sim_ose_call; eauto.
    { econs 1. }
    { simpl_itree_goal. ss. }
    { i. ss. clarify. econs 1. }
    i. ss. subst.
    esplits; [econs 1|].
    inv ADV_LCLOCK.
    remember (DTime.succ gtm0) as gtm1.
    clear dms gtm ltm lat idx CSKEW GTM LTM.
    clear gtm0 ltm0 CSKEW0 Heqgtm1 TLIM_NOT_OVER H1.
    rename gtm1 into gtm, ltm1 into ltm, lat0 into lat, H2 into CSKEW.

    (** - latency *)
    eapply sim_latency; eauto; i; ss; subst.
    { econs 1. }
    clear dms lat ltm gtm CSKEW GTM LTM.
    rename gtm0 into gtm, ltm0 into ltm, CSKEW0 into CSKEW.

    (** - Proc OS_STEP *)
    pfold. econs. i.
    inv STEP_TGT. inv ESTEP; cycle 1.
    { ss. }
    { inv IST_ADV_LCLOCK.
      esplits; ss; eauto.
      econs; eauto. econs.
    }
    rename lat' into lat.
    inv PROC_STEP; ss.
    2: { inv OS_RET. ss. }
    inv OS_STEP; ss.
    existT_elim. clear_tt.
    rename r0 into retz_txs.
    inv IST_ADV_LCLOCK.

    esplits.
    { econs; eauto. econs 1. }
    { ss. }
    { inv NOT_NB_TGT. ss. }
    { ss. }

    left.
    update_times. rename ltm' into ltm.
    assert (CSKEW: valid_clock_skew gtm ltm).
    { inv ADV_LCLOCK. ss. }
    clear gtm_p ltm_p NOT_NB_TGT ADV_LCLOCK GTM_UPD dms WF_DMS te_tgt TLIM_OK.

    (** - ret *)
    eapply sim_ose_ret; eauto.
    { simpl_itree_goal. ss. }
    { i. subst. ss. econs 1. }
    i. subst. ss.
    esplits; [econs 1|]. left.
    inv ADV_LCLOCK.
    remember (DTime.succ gtm0) as gtm1.
    replace (Socket.set_accept_msgs dms skts1) with skts1 by (inv CREATE; ss).
    clear dms gtm ltm lat CSKEW GTM LTM.
    clear gtm0 ltm0 CSKEW0 Heqgtm1 TLIM_NOT_OVER H1.
    rename gtm1 into gtm, ltm1 into ltm, lat0 into lat, idx0 into idx, H2 into CSKEW.

    (** - Call OSOpenSocket *)
    eapply sim_ose_call; eauto.
    { econs 1. }
    { simpl_itree_goal. ss. }
    { i. ss. clarify. econs 1. }
    i. ss. subst.
    esplits; [econs 1|].
    replace (Socket.set_accept_msgs dms skts1) with skts1 by (inv CREATE; ss).
    inv ADV_LCLOCK.
    remember (DTime.succ gtm0) as gtm1.
    clear dms gtm ltm idx lat CSKEW GTM LTM.
    clear gtm0 ltm0 CSKEW0 Heqgtm1 TLIM_NOT_OVER H1.
    rename gtm1 into gtm, ltm1 into ltm, lat0 into lat, H2 into CSKEW.

    (** - latency *)
    eapply sim_latency; i; ss; subst.
    { econs 1. }
    replace (Socket.set_accept_msgs dms skts1) with skts1 by (inv CREATE; ss).
    clear dms lat ltm gtm CSKEW GTM LTM.
    rename gtm0 into gtm, ltm0 into ltm, CSKEW0 into CSKEW.

    (** - Proc OS_STEP *)
    pfold. econs. i.
    inv STEP_TGT. inv ESTEP; cycle 1.
    { ss. }
    { inv IST_ADV_LCLOCK.
      esplits; ss; eauto.
      econs; eauto. econs.
    }
    rename lat' into lat.
    inv PROC_STEP; ss.
    2: { inv OS_RET. ss. }
    inv OS_STEP; ss.
    existT_elim. clear_tt.
    rename r0 into retz_rxs.
    inv IST_ADV_LCLOCK.

    esplits.
    { econs; eauto. econs 1. }
    { ss. }
    { inv NOT_NB_TGT. ss. }
    { ss. }

    left.
    update_times. rename ltm' into ltm.
    assert (CSKEW: valid_clock_skew gtm ltm).
    { inv ADV_LCLOCK. ss. }
    replace (Socket.set_accept_msgs dms skts1) with skts1 in * by (inv CREATE; ss).
    clear gtm_p ltm_p NOT_NB_TGT ADV_LCLOCK GTM_UPD dms WF_DMS te_tgt TLIM_OK.

    (** - ret *)
    eapply sim_ose_ret; eauto.
    { simpl_itree_goal. ss. }
    { i. subst. ss. econs 1. }
    i. subst. ss.
    esplits; [econs 1|]. left.
    replace (Socket.set_accept_msgs dms skts2) with skts2 by (inv CREATE; inv CREATE0; ss).
    inv ADV_LCLOCK.
    remember (DTime.succ gtm0) as gtm1.
    clear dms gtm ltm lat CSKEW GTM LTM.
    clear gtm0 ltm0 CSKEW0 Heqgtm1 TLIM_NOT_OVER H1.
    rename gtm1 into gtm, ltm1 into ltm, lat0 into lat, idx0 into idx, H2 into CSKEW.

    inv CREATE; cycle 1.
    { (* create socket failed *)
      destruct (Z.ltb_spec Z_mone 0); ss.
      eapply sim_final; eauto.
      { econs 1. }
      { ss. }
      { s. i. subst. econs 1. }
    }
    inv CREATE0; cycle 1.
    { (* create socket failed *)
      destruct (Z.ltb_spec Z_mone 0); ss.
      rewrite Bool.orb_true_r.
      eapply sim_final; eauto.
      { econs 1. }
      { ss. }
      { s. i. subst. econs 1. }
    }
    destruct (Z.ltb_spec (Z.of_nat id_new) 0); try nia.
    destruct (Z.ltb_spec (Z.of_nat id_new0) 0); try nia.
    ss. clear H1 H2.
    hexploit ID_FRESH0.
    { left. eauto. }
    intro ID_NEQ. ss.
    clear ID_FRESH ID_FRESH0.

    (** - Call OSWaitTimer *)
    eapply sim_ose_call; eauto.
    { econs 1. }
    { simpl_itree_goal. ss. }
    { i. ss. clarify. econs 1. }
    i. ss. subst.
    esplits; [econs 1|].
    unfold Socket.accept_msgs; ss.
    inv ADV_LCLOCK.
    remember (DTime.succ gtm0) as gtm1.
    clear dms gtm ltm lat idx CSKEW GTM LTM dms.
    clear gtm0 ltm0 CSKEW0 Heqgtm1 TLIM_NOT_OVER H1.
    rename gtm1 into gtm, ltm1 into ltm, lat0 into lat, H2 into CSKEW.

    (** - Proc OSWaitTimer *)
    eapply sim_wait_timer; eauto.
    { unfold base_time.
      specialize period_cond. i.
      exploit (Nat.mod_upper_bound ltm_first period); try nia.
    }
    { s. i. subst. econs 1. }
    s. i. subst. left.
    unfold Socket.accept_msgs; ss.
    clear gtm ltm lat dms CSKEW.
    rename gtm0 into gtm, ltm0 into ltm, lat0 into lat, tlim' into tlim, CSKEW0 into CSKEW.

    (** - ret *)
    eapply sim_ose_ret; eauto.
    { simpl_itree_goal. ss. }
    { i. subst. ss. econs 1. }
    i. subst. ss.
    esplits; [econs 1|]. left.
    unfold Socket.accept_msgs; ss.
    inv ADV_LCLOCK.
    remember (DTime.succ gtm0) as gtm1.
    rename ltm into ltm_wait, LTM into LTM_INCR.
    clear dms gtm lat CSKEW GTM.
    clear gtm0 ltm0 CSKEW0 Heqgtm1 TLIM_NOT_OVER H1.
    rename gtm1 into gtm, ltm1 into ltm, lat0 into lat, idx0 into idx, H2 into CSKEW.

    (** - Call OSBindSocket *)
    eapply sim_ose_call; eauto.
    { econs 1. }
    { simpl_itree_goal. ss. }
    { i. ss. clarify. econs 1. }
    i. ss. subst.
    esplits; [econs 1|].
    unfold Socket.accept_msgs; ss.
    rewrite LTM in LTM_INCR.
    inv ADV_LCLOCK.
    remember (DTime.succ gtm0) as gtm1.
    clear gtm ltm lat idx CSKEW GTM LTM dms.
    clear gtm0 ltm0 CSKEW0 Heqgtm1 TLIM_NOT_OVER H1.
    rename gtm1 into gtm, ltm1 into ltm, lat0 into lat, H2 into CSKEW.

    (** - latency *)
    eapply sim_latency; i; ss; subst; eauto.
    { econs 1. }
    unfold Socket.accept_msgs; ss.
    rewrite LTM in LTM_INCR.
    clear dms lat ltm gtm CSKEW GTM LTM.
    rename gtm0 into gtm, ltm0 into ltm, CSKEW0 into CSKEW.

    (** - Proc OS_STEP *)
    pfold. econs. i.
    inv STEP_TGT. inv ESTEP; ss; cycle 1.
    { inv IST_ADV_LCLOCK.
      esplits; ss; eauto.
      econs; eauto. econs.
    }
    rename lat' into lat.
    inv PROC_STEP; ss.
    2: { inv OS_RET. ss. }

    inv OS_STEP; ss.
    existT_elim. inv H5.
    inv IST_ADV_LCLOCK.
    unfold Socket.accept_msgs in *; ss.

    do 2 rewrite Nat2Z.id in *. inv BIND.
    destruct is_ok; cycle 1.
    { (* bind fails *)
      replace skts1 with
          [Socket.new_socket id_new; Socket.new_socket id_new0] in *; cycle 1.
      { revert BIND0. unfold Socket._bind. condtac; ss; cycle 1.
        { i. inv BIND0. ss. }
        unfold repl_byid. unfold repl_byid'. ss.
        condtac; ss.
        condtac; ss.
        i. inv BIND0. ss.
      }

      clear skts1 BIND0.
      esplits.
      { econs; eauto. econs 1. }
      { ss. }
      { inv NOT_NB_TGT. ss. }
      { ss. }

      left.
      update_times. rename ltm' into ltm.
      assert (CSKEW: valid_clock_skew gtm ltm).
      { inv ADV_LCLOCK. ss. }
      clear ltm_p gtm_p TLIM_OK ADV_LCLOCK LTM_INCR GTM_UPD NOT_NB_TGT dms WF_DMS te_tgt.
      clear ltm_wait EXPIRED.

      eapply sim_ose_ret; eauto.
      { simpl_itree_goal. ss. }
      { i. subst. ss. econs 1. }
      i. ss. subst.
      esplits; [econs 1|]. left.
      inv ADV_LCLOCK.
      clear gtm ltm lat CSKEW GTM LTM.
      rename gtm0 into gtm, ltm0 into ltm, lat0 into lat, idx0 into idx, CSKEW0 into CSKEW.

      eapply sim_final; eauto.
      - econs 1.
      - ss.
      - s. i. subst. econs 1.
    }

    (* AbstMW TurnOn *)
    assert (BASE: get_skwd_base_time period gtm = base_time period ltm_first + 2 * period).
    { rewrite Nat.leb_gt in TLIM_OK.
      move CSKEW at bottom. unfold valid_clock_skew, nat_diff in CSKEW.
      unfold get_skwd_base_time, base_time in *.
      remember (DTime.to_ns_rd gtm + max_clock_skew) as g.
      cut (ltm_first - ltm_first mod period + 2 * period < g <
           ltm_first - ltm_first mod period + 2 * period + period).
      { i. clear - H1.
        symmetry.
        eapply divide_range_eq; try eapply sub_mod_divide; try nia.
        - repeat apply Nat.divide_add_r; try refl; try apply Nat.divide_0_r.
          eapply sub_mod_divide. nia.
        - split; try nia.
          eapply sub_mod_range; try nia.
          apply Nat.divide_add_r; try eapply sub_mod_divide; try nia.
          repeat apply Nat.divide_add_r; try refl; try apply Nat.divide_0_r.
      }
      assert (GRANGE: ltm < g < ltm + max_clock_skew + max_clock_skew).
      { revert CSKEW. condtac; ss; i.
        - rewrite Nat.leb_le in COND. subst. split; nia.
        - rewrite Nat.leb_gt in COND. subst. split; nia.
      }
      unfold DELTA in *. nia.
    }

    esplits.
    { econs; eauto. econs 2; cycle 1; eauto.
      - assert (get_skwd_base_time period gtm >= period) by nia. ss.
        apply Nat.leb_gt in TLIM_OK. rewrite <- BASE in *.
        revert TLIM_OK EXPIRED H1. unfold DELTA.
        revert CSKEW. unfold valid_clock_skew, nat_diff.
        unfold DTime.of_ns, get_skwd_base_time, base_time, DTime.to_ns_rd. s. i.
        clear - TLIM CSKEW TLIM_OK EXPIRED LTM_INCR H1.
        specialize DTime.units_per_ns_pos. i.
        specialize period_cond. i.
        specialize max_clock_skew_pos. i.
        split.
        + eapply Nat.lt_le_trans.
          { eapply mult_lt_compat_r; [|auto].
            instantiate (1 := ltm - max_clock_skew).
            nia.
          }
          revert CSKEW. condtac; i.
          * apply Nat.lt_sub_lt_add_r in CSKEW.
            assert (ltm - max_clock_skew <= gtm / DTime.units_per_ns) by nia.
            etrans; [|eapply Nat.mul_div_le].
            { rewrite mult_comm. eapply mult_le_compat_l. ss. }
            nia.
          * apply Nat.leb_gt in COND.
            etrans; [|eapply Nat.mul_div_le].
            { rewrite mult_comm. eapply mult_le_compat_l. nia. }
            nia.
        + eapply Nat.le_lt_trans; cycle 1.
          { instantiate (1 := (ltm + max_clock_skew) * DTime.units_per_ns).
            eapply Nat.lt_le_trans; [eapply mult_lt_compat_r|].
            - apply plus_lt_compat_r. eapply TLIM_OK.
            - ss.
            - unfold get_skwd_base_time, base_time, DTime.to_ns_rd, DELTA in TLIM. nia.
          }
          revert CSKEW. condtac; i.
          * apply Nat.leb_le in COND.
            apply Nat.lt_le_incl. apply div_ub_inv; ss. nia.
          * apply Nat.leb_gt in COND.
            apply Nat.lt_le_incl. apply div_ub_inv; ss. nia.
      - econs; eauto.
      - rewrite BASE. nia.
    }
    { ss. }
    { inv NOT_NB_TGT. ss. }
    { ss. }

    left.
    update_times. rename ltm' into ltm.
    assert (CSKEW: valid_clock_skew gtm ltm).
    { inv ADV_LCLOCK. ss. }
    rewrite BASE in *.
    clear ltm_wait TLIM_OK EXPIRED LTM_INCR.
    clear gtm_p ltm_p ADV_LCLOCK BASE GTM_UPD NOT_NB_TGT dms WF_DMS te_tgt.

    assert (skts1 = [Socket.new_socket id_new; (Socket.mk id_new0 (Some port) [])]).
    { revert BIND0. unfold Socket._bind. condtac; ss.
      unfold repl_byid. unfold repl_byid'. ss.
      condtac; ss.
      { rewrite Nat.eqb_eq in COND0. subst. ss. }
      condtac; ss.
      i. inv BIND0. ss.
    }
    subst. clear BIND0.

    (** - ret *)
    eapply sim_ose_ret; eauto.
    { simpl_itree_goal. ss. }
    { i. subst. ss. econs 3.
      eapply cskew_time_not_over; eauto; try nia. ss.
      rewrite Nat.leb_gt in *. nia.
    }
    i. subst.
    esplits.
    { econs 3.
      eapply cskew_time_not_over; eauto; try nia. ss.
      rewrite Nat.leb_gt in *. nia.
    }
    left.
    erewrite sockets_of_accept_msgs; ss.
    inv ADV_LCLOCK.
    remember (DTime.succ gtm0) as gtm1.
    clear gtm ltm lat CSKEW GTM LTM.
    clear gtm0 ltm0 CSKEW0 Heqgtm1 TLIM_NOT_OVER H1.
    rename gtm1 into gtm, ltm1 into ltm, lat0 into lat, idx0 into idx, H2 into CSKEW.

    (** - mcast join *)
    rewrite mcast_join_equiv.
    remember (get_mcast_of tid) as tids.
    unfold get_mcast_of in Heqtids.
    rewrite <- Heqtids.

    eapply sim_mcast_join; eauto.
    { i. eapply cskew_time_not_over; eauto; try nia. ss.
      rewrite Nat.leb_gt in *. nia. }
    { subst.
      remember (get_mcast_of tid) as tids.
      generalize Heqtids. unfold get_mcast_of. i.
      rewrite <- Heqtids0. rewrite Heqtids.
      apply Forall_forall. i.
      exploit get_mcast_of_spec; eauto. i. des. subst.
      unfold tid2ip, num_tasks, dest_ips.
      rewrite app_nth2; try nia.
      replace (length task_ips + midx - length task_ips) with midx by nia.
      erewrite nth_error_nth; eauto.
      specialize mcast_ips_mcast_ip. i.
      eapply Forall_forall in H2; eauto.
      eapply nth_error_In; eauto.
    }
    i. subst.
    clear gtm ltm lat idx CSKEW GTM LTM dms.
    rename gtm0 into gtm, ltm0 into ltm, lat0 into lat, idx0 into idx,
    CSKEW0 into CSKEW, inbp0 into inbp.

    (** - main loop *)
    unfold MWITree.run_task.
    eapply sim_main_loop; eauto.
    - unfold base_time.
      repeat apply Nat.divide_add_r; try refl; try apply Nat.divide_0_r.
      apply sub_mod_divide.
      specialize period_cond. nia.
    - specialize period_cond. nia.
    - rewrite Nat.eqb_neq. ss.
    - nia.
  Qed.
End PROOF.
