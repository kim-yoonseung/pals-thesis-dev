From ITree Require Import ITree.
From compcert Require Coqlib.
From Paco Require Import paco.

Require Import List.
Require Import Arith ZArith Lia.

Require Import sflib.
Require Import Axioms StdlibExt IntegersExt.

Require Import SysSem.
Require Import IPModel DiscreteTimeModel.
Require Import NWSysModel.
Require Import RTSysEnv SyncSysModel.
Require Import AbstAsyncSysModel AbstMW.

Require Import FMSim.

Generalizable Variable sysE.
Set Nested Proofs Allowed.



Ltac inv_valid_delay :=
  match goal with
  | H: valid_delay_added _ _ |- _ => inv H
  end.




Module MCastIDProps.
  Section MCAST_ID.
    Context `{sysE: Type -> Type}.
    Context `{SystemEnv}.

    Definition mcm_pending (nw: NW.t)
               (nip mip: ip_t) : Prop :=
      In (mip, nip) (map fst (NW.mcast_msg_pool nw)).

    Definition mcm_active (nw: NW.t)
               (nip mip: ip_t): Prop :=
      In (mip, nip) (NW.mcast_groupinfo nw).

    Inductive mcast_id_domain (nw: NW.t)
              (nip: ip_t) (mids: list Tid): Prop :=
      MCastIDDomain
        mips
        (MCAST_IPS: Forall2 mcast_id_ip mids mips)
        (PENDING_INCL:
           forall mip'
             (MCM_PENDING: mcm_pending nw nip mip'),
             In mip' mips)
        (ACTIVE_INCL:
           forall mip'
             (MCM_ACTIVE: mcm_active nw nip mip'),
             In mip' mips)
    .

    Inductive mcast_id_in_nw (nw:NW.t)
              (nip: ip_t) (mids: list Tid): Prop :=
      MCastIDInNW
        mips
        (MCAST_IPS: Forall2 mcast_id_ip mids mips)
        (MCMS_IN_NW:
           Forall (mcm_pending nw nip \1/ mcm_active nw nip) mips)
    .

    Inductive mcast_id_active (nw:NW.t)
              (nip: ip_t) (mids: list Tid): Prop :=
      MCastIDActive
        mips
        (MCAST_IPS: Forall2 mcast_id_ip mids mips)
        (MCMS_ACTIVE:
           Forall (mcm_active nw nip) mips)
        (MCMS_INCLUSIVE:
           forall mip'
             (MCM_ACTIVE: mcm_active nw nip mip'),
             In mip' mips)
        (NO_PENDING:
           forall mip'
             (MCM_PENDING: mcm_pending nw nip mip'),
             False)
    .

    Lemma mcast_id_active_impl_domain
          nw nip mids
          (ACTIVE: mcast_id_active nw nip mids)
      : mcast_id_domain nw nip mids.
    Proof.
      inv ACTIVE.
      econs; eauto.
      i. hexploit NO_PENDING; eauto. ss.
    Qed.

    Lemma distr_pending
          nw nw1 dms
          (DISTR: NW.distr nw = (nw1, dms))
      : forall ip mip
          (PENDING: mcm_pending nw ip mip),
        mcm_pending nw1 ip mip \/
        mcm_active nw1 ip mip.
    Proof.
      destruct nw as [mcg msg_pl mc_pl]. ss.
      destruct (partition_map age_delay msg_pl) as [pmp' dpms] eqn: PART_MSG.
      destruct (partition_map age_delay mc_pl) as [mcmp' mcm_add] eqn: PART_MC.
      clarify.

      i. r in PENDING. ss.
      assert (IN_MCAST_POOL: exists dly,
                 In (mip, ip, dly) mc_pl).
      { apply in_map_iff in PENDING. des.
        destruct x as [[? ?] ?]. ss. clarify.
        esplits; eauto. }
      des.

      destruct dly as [| dly'].
      - (* delay = 0 *)
        right. r. ss.
        assert (IN_NEW_ENTRIES: In (mip, ip) mcm_add).
        { eapply in_partition_map_r1; try apply PART_MC; eauto. }
        apply NW.join_spec. eauto.
      - (* delay > 0 *)
        left. r. ss.
        apply in_map_iff.

        hexploit in_partition_map_l1; try apply PART_MC; eauto.
        { ss. }
        i. esplits; eauto. ss.
    Qed.

    Lemma distr_active
          nw nw1 dms
          (DISTR: NW.distr nw = (nw1, dms))
      : forall ip mip
          (ACTIVE: mcm_active nw ip mip),
        mcm_active nw1 ip mip.
    Proof.
      destruct nw as [mcg msg_pl mc_pl]. ss.
      destruct (partition_map age_delay msg_pl) as [pmp' dpms] eqn: PART_MSG.
      destruct (partition_map age_delay mc_pl) as [mcmp' mcm_add] eqn: PART_MC.
      clarify.

      i. r in ACTIVE. ss.
      r. ss.
      apply NW.join_spec. eauto.
    Qed.

    Lemma distr_pending_inv
          nw nw1 dms
          (DISTR: NW.distr nw = (nw1, dms))
      : forall ip mip
          (PENDING: mcm_pending nw1 ip mip),
        mcm_pending nw ip mip.
    Proof.
      destruct nw as [mcg msg_pl mc_pl]. ss.
      destruct (partition_map age_delay msg_pl) as [pmp' dpms] eqn: PART_MSG.
      destruct (partition_map age_delay mc_pl) as [mcmp' mcm_add] eqn: PART_MC.
      clarify.

      i. r in PENDING. ss.
      r. ss.

      eapply in_map_iff in PENDING. des.
      destruct x. ss. clarify.

      hexploit in_partition_map_l2; try apply PART_MC; eauto.
      i. des.
      destruct a as [[? ?] ?]. ss. desf.
      apply in_map_iff. esplits; eauto. ss.
    Qed.


    Lemma distr_active_inv
          nw nw1 dms
          (DISTR: NW.distr nw = (nw1, dms))
      : forall ip mip
          (ACTIVE: mcm_active nw1 ip mip),
        mcm_active nw ip mip \/ mcm_pending nw ip mip.
    Proof.
      destruct nw as [mcg msg_pl mc_pl]. ss.
      destruct (partition_map age_delay msg_pl) as [pmp' dpms] eqn: PART_MSG.
      destruct (partition_map age_delay mc_pl) as [mcmp' mcm_add] eqn: PART_MC.
      clarify.

      i. r in ACTIVE. ss.
      assert (EITHER: In (mip, ip) mcg \/
                      In (mip, ip) mcm_add).
      { apply NW.join_spec. ss. }
      destruct EITHER as [IN|IN].
      - left. r. ss.
      - right. r. ss.

        hexploit in_partition_map_r2; try apply PART_MC; eauto.
        i. des.
        destruct a as [[? ?] ?]. ss. desf.
        apply in_map_iff. esplits; eauto. ss.
    Qed.

    Lemma mcast_id_domain_distr
          nw mids nw1 dms ip
          (INCL: mcast_id_domain nw ip mids)
          (DISTR: NW.distr nw = (nw1, dms))
      : mcast_id_domain nw1 ip mids.
    Proof.
      inv INCL.
      econs; eauto.
      - i. hexploit distr_pending_inv; eauto.
      - i. hexploit distr_active_inv; eauto.
        destruct 1; eauto.
    Qed.

    Lemma mcast_id_in_nw_distr
          nw mids nw1 dms ip
          (INCL: mcast_id_in_nw nw ip mids)
          (DISTR: NW.distr nw = (nw1, dms))
      : mcast_id_in_nw nw1 ip mids.
    Proof.
      inv INCL.
      econs; eauto.
      apply Forall_forall.
      intros x IN.
      rewrite Forall_forall in MCMS_IN_NW.
      hexploit MCMS_IN_NW; eauto.
      destruct 1.
      + hexploit distr_pending; eauto.
      + hexploit distr_active; eauto.
    Qed.

    Lemma mcast_id_active_distr
          nw mids nw1 dms ip
          (INCL: mcast_id_active nw ip mids)
          (DISTR: NW.distr nw = (nw1, dms))
      : mcast_id_active nw1 ip mids.
    Proof.
      inv INCL.
      econs; eauto.
      - eapply Forall_impl.
        2: { eauto. }
        i. eapply distr_active; eauto.
      - i. hexploit distr_active_inv; eauto.
        destruct 1; eauto.
        hexploit NO_PENDING; eauto. ss.
      - i. hexploit distr_pending_inv; eauto.
    Qed.

    Lemma gather_active
          nw1 ip mip
          ps nw'
          (GATHER: NW.gather nw1 ps nw')
          (ACTIVE: mcm_active nw1 ip mip)
      : mcm_active nw' ip mip.
    Proof.
      inv GATHER.
      r. ss.
    Qed.

    Lemma gather_pending
          nw1 ip mip
          ps nw'
          (GATHER: NW.gather nw1 ps nw')
          (PENDING: mcm_pending nw1 ip mip)
      : mcm_pending nw' ip mip.
    Proof.
      inv GATHER.
      r in PENDING. r. ss.
      rewrite map_app.
      apply in_or_app. left. ss.
    Qed.

    Lemma gather_active_inv
          nw1 ip mip
          ps nw'
          (GATHER: NW.gather nw1 ps nw')
          (ACTIVE: mcm_active nw' ip mip)
      : mcm_active nw1 ip mip.
    Proof.
      inv GATHER.
      r in ACTIVE. ss.
    Qed.

    Lemma gather_pending_inv
          nw1 ip mip
          ps nw'
          (GATHER: NW.gather nw1 ps nw')
          (PENDING: mcm_pending nw' ip mip)
      : mcm_pending nw1 ip mip \/
        In (Packet.MCast (mip, ip)) ps.
    Proof.
      inv GATHER.
      unfold mcm_pending in *. ss.
      rewrite map_app in PENDING.
      apply in_app_or in PENDING.
      destruct PENDING as [IN | IN].
      { eauto. }

      right.
      cut (In (mip, ip) mcms_new).
      { i. eapply in_partition_map_r2 in CLASSIFY; eauto.
        unfold id in CLASSIFY.
        des. clarify. }
      clear - IN VALID_DELAYS_MCMS.

      apply in_map_iff in IN.
      destruct IN as (x & EQ & IN).
      apply In_nth_error in IN. des.

      rewrite Forall2_nth in VALID_DELAYS_MCMS.
      specialize (VALID_DELAYS_MCMS n).
      rewrite IN in VALID_DELAYS_MCMS.
      inv VALID_DELAYS_MCMS.

      inv_valid_delay. ss. clarify.
      eapply nth_error_In; eauto.
    Qed.

  End MCAST_ID.
End MCastIDProps.



Section PROOF.
  Import AbstMW.
  Import MCastIDProps.

  Context {sysE: Type -> Type}. (* {msgT: Set}. *)
  (* Context `{rnws_params}. *)
  Context `{SystemEnv}.

  Let msgT: Set := bytes.
  Variable nodes: list (@SNode.t sysE msgT).
  Let num_nodes: nat := length nodes.

  Variable tm_init: nat.
  Hypothesis TASK_IPS_LENGTH: num_tasks = num_nodes.
  Hypothesis TM_INIT_SYTM: Nat.divide period (tm_init + max_clock_skew).

  Let PERIOD_COND: 2 * max_clock_skew + max_nw_delay + max_wait_delay < period.
  Proof.
    apply period_cond.
  Qed.

  (* Hypothesis WF_NODES: *)
  (*   List.Forall (SNode.wf imcasts) nodes. *)

  Let sys_src := AASys.as_dsys nodes tm_init.
  Let sys_tgt := NWSys.as_dsys
                   (imap AbstMW.as_node 0 nodes) tm_init.
                   (* (map (uncurry (AbstMW.as_node)) *)
                   (*      (attach_index nodes)) tm_init. *)
  (* move *)


  Lemma pm_pool_ip_neq
        pm (ips: list ip_t)
        (pmp: list (ip_t * Packet.msg_t * nat)) ip
        (VD: Forall2 valid_delay_added (map (fun x => (x, pm)) ips) pmp)
        (NOT_IP: Forall (fun x => x <> ip) ips)
    : forall ip' pm' (IN: In (ip', pm') (map fst pmp)),
      ip' <> ip.
  Proof.
    i. apply in_map_iff in IN.
    destruct IN as [[[ip2 pm2] dly] [? IN1]].
    ss. clarify.
    apply In_nth_error in IN1. des.

    rewrite Forall2_nth in VD.
    specialize (VD n).
    rewrite IN1 in VD.

    cut (nth_error ips n = Some ip').
    { intro IPS_NTH.
      assert (IP_NEQ': ip' <> ip).
      { rewrite Forall_forall in NOT_IP.
        apply NOT_IP.
        eapply nth_error_In; eauto. }

      unfold Node.chget_pm_by_dest. ss.
    }

    inv VD.
    match goal with
    | H: _ = nth_error (map ?f _) _,
         H': valid_delay_added _ _
      |- _ =>
      inv H'; symmetry in H;
        eapply map_nth_error_iff in H; eauto
    end.
    des. clarify.
  Qed.


  Inductive match_pkt
            (sytm: nat) (tid_s: Tid)
    : (Tid * msgT)? -> Packet.t? -> Prop :=
  | MatchPkt_None
    : match_pkt sytm tid_s None None
  | MatchPkt_MCast
      mid mip tip
      (MCAST_MEMBER: mcast_member tid_s mid)
      (MCAST_ID_IP: mcast_id_ip mid mip)
      (TASK_ID_IP: task_id_ip tid_s tip)
    : match_pkt sytm tid_s None (Some (inr (mip, tip)))
  | MatchPkt_Some
      tid_d rmsg
      ip_s ip_d
      pld pm
      (RANGE_SYTM: IntRange.uint64 sytm)
      (LENGTH_RMSG: length rmsg = msg_size)
      (IP_SENDER: task_id_ip tid_s ip_s)
      (IP_DEST: dest_id_ip tid_d ip_d)
      (SRL_MSG: serialize_msg sytm tid_s rmsg = pld)
      (PACKET_MSG: pm = Packet.mkMsg ip_s ip_d port pld)
    : match_pkt sytm tid_s (Some (tid_d, rmsg)) (Some (inl pm))
  .

  Section AUX_MSGS_TO.

    Definition aux_msgs_to (mcg: list Packet.mcm_t)
               (ip: ip_t)
               (op: Packet.t?)
    : Packet.msg_t? :=
      match op with
      | Some (inl pm) =>
        let ip_d := Packet.dest_ip pm in
        if (ip_d =? ip)%nat then Some pm else
          if existsb (fun x => andb (fst x =? ip_d)
                                 (snd x =? ip)) mcg then
            Some pm else None
      | _ => None
      end.


    Lemma match_pkt_tgt_Some_impl
          nw mcg ip mids
          sytm tid_s tid_r
          out_src out_tgt pm
          (TASK_ID_IP: task_id_ip tid_r ip)
          (AUX_TGT: aux_msgs_to mcg ip out_tgt = Some pm)
          (MATCH: match_pkt sytm tid_s out_src out_tgt)
          (MCAST_GROUP: NW.mcast_groupinfo nw = mcg)
          (WF_MCG: Forall Packet.mcm_wf mcg)
          (* (ACTIVE: mcast_id_active nw ip mids) *)
          (MCAST_OF_TID: mids = get_mcast_of tid_r)
          (MC_DOM: mcast_id_domain nw ip mids)
      : <<OUT_TGT_EQ: out_tgt = Some (inl pm)>> /\
        exists tid_d msg,
        <<OUT_SRC_EQ: out_src = Some (tid_d, msg)>> /\
        <<OUT_SRC_F: AANode.get_msg_by_dest tid_r out_src = [msg]>>
    .
    Proof.
      guardH MCAST_OF_TID.
      destruct out_tgt as [p|]; ss.
      destruct p as [pm'|?]; ss.
      desf.
      - split; ss.
        inv MATCH; ss.

        assert (ip_d = ip).
        { apply beq_nat_true. ss. }
        subst ip_d.

        assert (tid_d = tid_r).
        { eapply dest_id_ip_inv_det; eauto.
          inv TASK_ID_IP. r.
          unfold dest_ips.
          rewrite nth_error_app1; eauto.
          eapply nth_error_Some. congruence. }
        subst tid_d.

        esplits; ss.
        rewrite Nat.eqb_refl. ss.

      - split; ss.
        inv MATCH; ss.
        esplits; ss.

        assert (IN_MCG: In (ip_d, ip) (NW.mcast_groupinfo nw)).
        { match goal with
          | H: existsb _ _ = true |- _ =>
            rename H into EXISTSB
          end.

          apply existsb_exists in EXISTSB.
          destruct EXISTSB as [[mip_e nip_e] [A B]].
          ss.
          apply Bool.andb_true_iff in B. des.
          rewrite Nat.eqb_eq in *. clarify.
        }

        (* unfold filter_by_dest, chget_by_dest. ss. *)
        rewrite <- MCAST_OF_TID.
        cut (In tid_d mids).
        { intro IN_MIDS.
          cut (existsb (Nat.eqb tid_d) mids = true).
          { intro T. rewrite T.
            rewrite Bool.orb_true_r. ss. }

          apply existsb_exists.
          esplits.
          { eauto. }
          apply Nat.eqb_refl.
        }

        assert (IP_D_MCAST: IP.mcast_ip ip_d).
        { rewrite Forall_forall in WF_MCG.
          hexploit WF_MCG; eauto.
          inversion 1. clarify. }

        (* inv ACTIVE. *)
        inv MC_DOM.
        r in IP_DEST.

        assert (MCAST_ID_IP_D: mcast_id_ip tid_d ip_d).
        { unfold dest_ips in IP_DEST.
          destruct (lt_ge_dec tid_d num_tasks).
          - exfalso.
            rewrite nth_error_app1 in IP_DEST by ss.
            apply nth_error_In in IP_DEST.
            hexploit task_ips_not_mcast; eauto.
            i. congruence.
          - rewrite nth_error_app2 in IP_DEST by ss.
            r. exists (tid_d - num_tasks).
            splits; ss. nia.
        }

        hexploit ACTIVE_INCL; eauto.
        intro IN_IP_D.
        apply In_nth_error in IN_IP_D. des.
        rewrite Forall2_nth in MCAST_IPS.
        specialize (MCAST_IPS n).
        rewrite IN_IP_D in MCAST_IPS.

        assert (exists tid_d',
                   <<TID_D': nth_error mids n = Some tid_d'>> /\
                   <<MCAST_ID_IP': mcast_id_ip tid_d' ip_d>>).
        { inv MCAST_IPS. esplits; eauto. }
        des.
        cut (tid_d' = tid_d).
        { i. subst.
          eapply nth_error_In; eauto. }
        eapply dest_id_ip_inv_det; eauto.
        inv MCAST_ID_IP'. des.
        r. clarify.
        unfold dest_ips.
        rewrite nth_error_app2.
        2: { fold num_tasks. nia. }
        fold num_tasks.
        rewrite minus_plus. ss.
    Qed.


    Lemma outs_size_incl_aux
          nw mcg ip mids
          sytm tid_r
          outs_src outs_tgt n
          (TASK_ID_IP: task_id_ip tid_r ip)
          (MCAST_GROUP: NW.mcast_groupinfo nw = mcg)
          (WF_MCG: Forall Packet.mcm_wf mcg)
          (NODUP_MCG: NoDup mcg)
          (* (ACTIVE: mcast_id_active nw ip mids) *)
          (MCAST_OF_TID: mids = get_mcast_of tid_r)
          (MCAST_DOM: mcast_id_domain nw ip mids)
          (MATCH_OUTMSGS : iForall2 (match_pkt sytm) n outs_src outs_tgt)
      : length (filtermap (aux_msgs_to mcg ip) outs_tgt) <=
        AANode.inbox_sz (map (AANode.get_msg_by_dest tid_r)
                             outs_src).
    Proof.
      depgen outs_src. revert n.
      guardH MCAST_GROUP.
      induction outs_tgt as [| h_tgt t_tgt IH]; i; ss.
      { nia. }
      destruct outs_src as [| h_src t_src]; ss.
      { inv MATCH_OUTMSGS. }
      inv MATCH_OUTMSGS.

      hexploit IH; eauto. intro LEN_IH.

      destruct (aux_msgs_to mcg ip h_tgt) eqn: AUX1; ss.
      - hexploit match_pkt_tgt_Some_impl; eauto.
        i. des. clarify.
        rewrite OUT_SRC_F.
        unfold AANode.inbox_sz in *. ss. nia.
      - unfold AANode.inbox_sz in *. ss.
        rewrite app_length. nia.
    Qed.

    Lemma aux_msgs_to_equiv
          mcg outs_tgt ip
          pms_new mcms_new pmp_new
          (WF_MCG: Forall Packet.mcm_wf mcg)
          (NODUP_MCG: NoDup mcg)
          (IP_LOCAL: IP.local_ip ip)
          (CLASSIFY: partition_map id (filtermap id outs_tgt) = (pms_new, mcms_new))
          (VALID_DELAYS: Forall2 valid_delay_added (concat (map (NW.attach_adest mcg) pms_new)) pmp_new)
      : Node.distr_msgs_to ip (map fst pmp_new) =
        filtermap (aux_msgs_to mcg ip) outs_tgt.
    Proof.
      revert pms_new mcms_new pmp_new CLASSIFY VALID_DELAYS.
      induction outs_tgt as [| h t IH]; i; ss.
      { clarify. ss.
        inv VALID_DELAYS. ss. }

      destruct h as [pkt|]; ss.
      2: { eauto. }
      destruct pkt as [pm|mcm]; ss.
      2: { desf. eauto. }

      destruct (partition_map id (filtermap id t))
        as [pms_new' mcms_new'] eqn:PART_TL.
      clarify. ss.
      eapply Forall2_app_inv_l in VALID_DELAYS.
      destruct VALID_DELAYS as
          (pmp_pm & pmp_new' &
           VALID_DELAY_PM & VALID_DELAYS & PMP_NEW_EQ).
      hexploit IH; eauto. intro IH_EQ.

      rewrite PMP_NEW_EQ.
      rewrite map_app.
      unfold Node.distr_msgs_to.
      rewrite filtermap_app.

      unfold Node.distr_msgs_to in IH_EQ.
      rewrite IH_EQ.

      cut (filtermap (Node.chget_pm_by_dest ip) (map fst pmp_pm) =
           opt2list (aux_msgs_to mcg ip (Some (inl pm)))).
      { ss. intro R. rewrite R. desf. }

      ss.
      assert (IP_NOT_MCAST: IP.mcast_ip ip = false).
      { generalize (IP.normal_mcast_disjoint ip).
        rewrite IP_LOCAL. ss. }

      destruct (Nat.eqb_spec (Packet.dest_ip pm) ip) as [IP_EQ | IP_NEQ]; ss.
      { (* unicast *)
        unfold NW.attach_adest in VALID_DELAY_PM.
        rewrite IP_EQ in VALID_DELAY_PM.
        rewrite IP_NOT_MCAST in VALID_DELAY_PM.

        assert (exists dly, pmp_pm = [(ip, pm, dly)]).
        { inv VALID_DELAY_PM.
          match goal with
          | H: valid_delay_added _ _,
               H': Forall2 _ [] _ |- _ => inv H; inv H'
          end.
          esplits; ss.
        }
        des. clarify.

        ss. unfold Node.chget_pm_by_dest. ss.
        rewrite Nat.eqb_refl. ss.
      }

      desf.
      { rename Heq into EXISTSB. ss.
        rewrite existsb_exists in EXISTSB.
        destruct EXISTSB as [[mip1 ip1] [IN_MCG MEM_IP_EQ]]; ss.
        apply Bool.andb_true_iff in MEM_IP_EQ. des.
        apply beq_nat_true in MEM_IP_EQ.
        apply beq_nat_true in MEM_IP_EQ0.
        clarify.

        unfold NW.attach_adest in VALID_DELAY_PM.
        rewrite Forall_forall in WF_MCG.
        hexploit WF_MCG; eauto. intro WF_MCM.
        inv WF_MCM.
        rewrite MCAST_IP in VALID_DELAY_PM.

        assert (IP_IN_ARECV: In ip (NW.get_actual_receivers mcg (Packet.dest_ip pm))).
        { unfold NW.get_actual_receivers.
          eapply in_filtermap; eauto. ss.
          rewrite Nat.eqb_refl. ss.
        }

        assert (exists ips1 ips2,
                   <<ARECV_EQ: NW.get_actual_receivers mcg (Packet.dest_ip pm) = ips1 ++ ip :: ips2>> /\
                   <<IPS1_NOT_IP: Forall (fun x => x <> ip) ips1>> /\
                   <<IPS2_NOT_IP: Forall (fun x => x <> ip) ips2>>).
        { eapply in_split in IP_IN_ARECV. des.
          rewrite IP_IN_ARECV.
          eapply nodup_div in IP_IN_ARECV; eauto.
          apply NW.get_actual_receivers_nodup; eauto.
        }
        des.
        rewrite ARECV_EQ in VALID_DELAY_PM.

        rewrite map_app in VALID_DELAY_PM.
        eapply Forall2_app_inv_l in VALID_DELAY_PM.

        destruct VALID_DELAY_PM
          as (pmp1 & pmp' & FA1 & FA2 & PMP'_EQ).
        destruct pmp' as [| pmp pmp2]; inv FA2.
        rewrite map_app. rewrite filtermap_app.
        replace (pmp::pmp2) with ([pmp] ++ pmp2) by ss.
        rewrite map_app. rewrite filtermap_app.

        rewrite (filtermap_nil _ _ _ (map fst pmp1)).
        2: {
          intros [ip' pm'] IN_FST_PMP1.

          cut (ip' <> ip).
          { intro NEQ.
            unfold Node.chget_pm_by_dest. ss.
            destruct (Nat.eqb_spec ip' ip); ss. }
          eapply (pm_pool_ip_neq pm ips1); eauto.
        }
        rewrite (filtermap_nil _ _ _ (map fst pmp2)).
        2: {
          intros [ip' pm'] IN_FST_PMP2.
          cut (ip' <> ip).
          { intro NEQ.
            unfold Node.chget_pm_by_dest. ss.
            destruct (Nat.eqb_spec ip' ip); ss. }
          eapply (pm_pool_ip_neq pm ips2); eauto.
        }
        ss.

        match goal with
        | H: valid_delay_added _ _ |- _ => inv H
        end.
        unfold Node.chget_pm_by_dest. ss.
        rewrite Nat.eqb_refl. ss.
      }
      rename Heq into EXISTSB.

      ss. unfold NW.attach_adest in VALID_DELAY_PM.
      destruct (IP.mcast_ip (Packet.dest_ip pm)) eqn: IS_DEST_MCAST.
      2: {
        inv VALID_DELAY_PM.
        match goal with
        | H: Forall2 _ [] _,
             H': valid_delay_added _ _ |- _ => inv H; inv H'
        end.
        ss. unfold Node.chget_pm_by_dest. ss.
        destruct (Nat.eqb_spec (Packet.dest_ip pm) ip); ss.
      }

      cut (Forall (fun x => x <> ip)
                  (NW.get_actual_receivers mcg (Packet.dest_ip pm))).
      { intro FA.
        apply filtermap_nil. i.
        destruct a as [ip' pm'].
        hexploit pm_pool_ip_neq; eauto.
        unfold Node.chget_pm_by_dest. ss.
        destruct (Nat.eqb_spec ip' ip); ss.
      }

      apply existsb_false_iff in EXISTSB.
      apply Forall_forall. intros ip1 IN.
      unfold NW.get_actual_receivers in IN.
      ii. subst ip1.

      eapply filtermap_in in IN. des.
      rewrite Forall_forall in EXISTSB.
      hexploit EXISTSB; eauto.
      desf. ss.
      rewrite Nat.eqb_refl. ss.
    Qed.

  End AUX_MSGS_TO.


  Inductive old_msg (sytm_ub_exc: nat) (pm_old: Packet.msg_t): Prop :=
    OldMsg
      sytm_old tid_s bs
      (* (WF_PMS: Packet.msg_wf pm_old) *)
      (PORT_EQ: Packet.dest_port pm_old = port)
      (PARSE_OK:
         parse_msg (firstn pld_size (Packet.payload pm_old)) =
         Some (sytm_old, tid_s, bs))
      (SYTM_OLD: sytm_old < sytm_ub_exc)
  .

  Lemma old_msg_adv
        stm1 stm2 pm
        (OLD: old_msg stm1 pm)
        (TM_LE: stm1 <= stm2)
    : old_msg stm2 pm.
  Proof.
    inv OLD.
    econs; eauto. nia.
  Qed.

  Lemma fetch_msgs_old
        cbt ms inbs
        (OLD_MSGS: Forall (old_msg cbt) ms)
    : List.fold_left
        (flip (fetch_one_msg cbt)) ms inbs =
      inbs.
  Proof.
    induction ms as [| m ms' IH]; ss.
    assert (<<OLD_M: old_msg cbt m>> /\
                     <<OLD_MSGS': Forall (old_msg cbt) ms'>>).
    { inv OLD_MSGS. ss. }

    des.
    assert (FETCH_OLD1: fetch_one_msg cbt m inbs = inbs).
    { unfold fetch_one_msg.
      inv OLD_M.
      unfold parse_pld.

      destruct (Nat.ltb_spec (length (Packet.payload m)) pld_size); ss.
      rewrite PARSE_OK.

      destruct (Nat.eqb_spec sytm_old cbt); ss.
      { nia. }
      destruct (Nat.eqb_spec sytm_old (cbt + period)); ss.
      { nia. }
      desf.
    }
    unfold flip at 2.
    rewrite FETCH_OLD1.
    eapply IH; eauto.
  Qed.


  Definition nw_msgs_to (ip: ip_t) (nw: NW.t)
    : list Packet.msg_t :=
    Node.distr_msgs_to
      ip (map fst (NW.packet_msg_pool nw)).

  Inductive match_inb_pre (sytm: nat)
            (ip: ip_t) (nw: NW.t)
            (inbp: list Packet.msg_t)
            (inbn: list (list msgT)): Prop :=
    MatchInbPre
      pms_tot
      (INBN_LENGTH: length inbn = num_tasks)
      (PMS_TOT: pms_tot = inbp ++ nw_msgs_to ip nw)
      (* (SYTM: sytm = get_skwd_base_time period tm) *)
      (PMS_TOT_OLD: Forall (old_msg (sytm + 2 * period)) pms_tot)
      (PMS_TOT_LEN: length pms_tot <= AANode.inbox_sz inbn)
  .


  Inductive match_inb
            (sytm: nat) (* (tid: Tid) *)
            (inb: list (list msgT))
            (inbm: list msgT?)
            (pms: list Packet.msg_t)
    : Prop :=
    MatchInbox
      (INB_LENGTH: length inb = num_tasks)
      (SIZE_INCL: length (filtermap id inbm) + length pms
                  <= AANode.inbox_sz inb)
      (PMS_IN_INB:
         Forall (fun pm: Packet.msg_t =>
                   exists tid_s msg inb_r,
                     <<PORT_EQ: Packet.dest_port pm = port>> /\
                     <<PLD_SIZE_EQ: length (Packet.payload pm) = pld_size>> /\
                     <<PARSE_OK: parse_msg (Packet.payload pm) =
                                 Some (sytm, tid_s, msg)>> /\
                     <<INB_ROW_EX: nth_error inb tid_s = Some inb_r>> /\
                     <<IN_INB_ROW: In msg inb_r>>)
                pms)
      (INBM_IN_INB:
         Forall2 (fun om ms =>
                    forall m (MSG_EX: om = Some m), In m ms)
                 inbm inb)
      (WHEN_INBM_EMPTY:
         forall tid_s inb_r m
           (* (TID: IntRange.sint8 tid_s) *)
           (INB_ROW: nth_error inb tid_s = Some inb_r)
           (INBM_ROW: nth_error inbm tid_s = Some None)
           (IN_ROW: In m inb_r)
         ,
         exists pm,
           <<IN_PMS: In pm pms>> /\
           <<PORT_EQ: Packet.dest_port pm = port>> /\
           <<PLD_SIZE_EQ: length (Packet.payload pm) = pld_size>> /\
           <<PARSE_OK: parse_msg (Packet.payload pm) =
                       Some (sytm, tid_s, m)>>)
  .


  Definition nw_inv (tm: DTime.t)
             (nw: NW.t) : Prop :=
    forall sytm_sk
      (SKWD_SYNC_TIME: Nat.divide period
                                  (sytm_sk + max_clock_skew))
      (RANGE_TM: tm <= DTime.of_ns sytm_sk),
      Forall (fun p => DTime.uadd tm (snd p) <
                    DTime.of_ns sytm_sk)
             (NW.packet_msg_pool nw) /\
      Forall (fun p => DTime.uadd tm (snd p) <
                    DTime.of_ns sytm_sk)
             (NW.mcast_msg_pool nw)
  .

  Lemma nw_msgs_to_distr
        ip nw nw1 dms
        pms_nw pms_nw1 pms_d
        (DISTR: NW.distr nw = (nw1, dms))
        (PMS_NW: pms_nw = nw_msgs_to ip nw)
        (PMS_NW1: pms_nw1 = nw_msgs_to ip nw1)
        (PMS_D: pms_d = Node.distr_msgs_to ip dms)
    : length pms_nw = length pms_nw1 + length pms_d /\
      (forall pm, In pm pms_nw1 -> In pm pms_nw) /\
      (forall pm, In pm pms_d -> In pm pms_nw) /\
      (forall pm, In pm pms_nw -> In pm pms_nw1 \/ In pm pms_d).
  Proof.
    destruct nw as [mgs pm_pl mcm_pl]. ss.
    assert (exists pm_pl1,
               <<PART_PM_PL: partition_map age_delay pm_pl = (pm_pl1, dms)>> /\
               <<PM_PL1_EQ: pm_pl1 = NW.packet_msg_pool nw1>>).
    { desf. eauto. }

    clear DISTR. des.
    unfold nw_msgs_to in PMS_NW1.
    rewrite <- PM_PL1_EQ in PMS_NW1.
    unfold nw_msgs_to in PMS_NW. ss.
    clear PM_PL1_EQ. subst.

    revert pm_pl1 dms PART_PM_PL.
    induction pm_pl as [| h t IH]; i; ss.
    { clarify. }

    destruct h as [[ip_dest pm] dly]. ss.
    destruct (partition_map age_delay t) as [pt1 pt2].

    hexploit IH; eauto.
    clear IH. intros (IH_LEN & IH_IN1 & IH_IN2 & IH_INR).

    destruct dly as [|dly'].
    - (* delay zero *)
      clarify.
      splits.
      + unfold Node.distr_msgs_to in *. ss.
        desf. ss.
        rewrite IH_LEN. ss.
      + intros pm1 IN1.
        apply IH_IN1 in IN1.
        clear - IN1.
        unfold Node.distr_msgs_to in *. ss.
        desf. ss. eauto.
      + intros pm2 IN2.
        clear - IN2 IH_IN2.
        unfold Node.distr_msgs_to in *. ss.
        desf; ss.
        2: { eapply IH_IN2 in IN2. ss. }
        des; eauto.
      + intros pm' INR.
        clear - INR IH_INR.
        unfold Node.distr_msgs_to in *. ss.
        desf; ss.
        * des; eauto.
          hexploit IH_INR; eauto.
          destruct 1; eauto.
        * des; eauto.

    - (* delay pos *)
      clarify.
      splits.
      + unfold Node.distr_msgs_to in *. ss.
        desf. ss.
        rewrite IH_LEN. ss.
      + intros pm1 IN1.
        clear - IN1 IH_IN1.
        unfold Node.distr_msgs_to in *. ss.
        desf; ss.
        2: { eapply IH_IN1 in IN1. ss. }
        des; eauto.
      + intros pm2 IN2.
        apply IH_IN2 in IN2.
        clear - IN2.
        unfold Node.distr_msgs_to in *. ss.
        desf. ss. eauto.
      + intros pm' INR.
        clear - INR IH_INR.
        unfold Node.distr_msgs_to in *. ss.
        desf; ss.
        * des; eauto.
          hexploit IH_INR; eauto.
          destruct 1; eauto.
        * des; eauto.
  Qed.

  Lemma pre_filter_port_noeff
        sytm ip nw inbp inbn
        nw1 dms
        (PRE: match_inb_pre sytm ip nw inbp inbn)
        (DISTR: NW.distr nw = (nw1, dms))
    : AbstMW.filter_port (Node.distr_msgs_to ip dms) =
      Node.distr_msgs_to ip dms.
  Proof.
    hexploit (nw_msgs_to_distr ip); eauto.
    intros (LEN_EQ & INCL1 & INCL2 & _).
    inv PRE.

    unfold AbstMW.filter_port.
    apply filter_all_ok.

    apply Forall_app_inv in PMS_TOT_OLD.
    destruct PMS_TOT_OLD as [_ PMS_OLD2].
    apply Forall_forall.
    intros pm IN.
    apply INCL2 in IN.
    rewrite Forall_forall in PMS_OLD2.
    apply PMS_OLD2 in IN. inv IN.
    rewrite Nat.eqb_eq; ss.
  Qed.


  Lemma match_inb_pre_distr
        sytm nw nw1 dms
        ip inbp inbn
        (PRE: match_inb_pre sytm ip nw inbp inbn)
        (DISTR: NW.distr nw = (nw1, dms))
    : match_inb_pre
        sytm ip nw1
        (inbp ++ AbstMW.filter_port (Node.distr_msgs_to ip dms))
        inbn.
  Proof.
    hexploit pre_filter_port_noeff; eauto.
    intro FILTER_PORT_NOEFF.

    hexploit (nw_msgs_to_distr ip); eauto.
    intros (LEN_EQ & INCL1 & INCL2 & _).
    inv PRE.

    econs; eauto.
    - eapply Forall_app_inv in PMS_TOT_OLD.
      destruct PMS_TOT_OLD as [FA_INBP FA_DEST].

      eapply Forall_app.
      2: {
        eapply Forall_forall.
        intros pm IN.
        eapply Forall_forall; eauto.
      }
      eapply Forall_app; eauto.
      { eapply Forall_forall.
        intros pm IN.
        eapply Forall_forall; eauto.
      }
    - do 2 rewrite app_length.
      rewrite app_length in PMS_TOT_LEN. nia.
  Qed.


  Lemma nw_gather_matchinfo
        tid mids (ip: ip_t)
        sytm oms ops
        nw1 nw' inb_m
        (* (RANGE_SYTM: IntRange.uint64 sytm) *)
        (WF_NW1: NW.wf nw1)
        (TASK_ID_IP: task_id_ip tid ip)
        (MCAST_DOM: mcast_id_domain nw1 ip mids)
        (MCAST_OF_TID: mids = get_mcast_of tid)
        (* (LEN_OUTS: length oms = num_tasks) *)
        (MATCH: iForall2 (match_pkt sytm) 0 oms ops)
        (GATHER: NW.gather nw1 (filtermap id ops) nw')
        (INB_TO_MERGE: inb_m = map (AANode.get_msg_by_dest tid) oms)
    : exists npms_ip,
      (* Forall (fun pm => In (Packet.Msg pm) (filtermap id ops)) npms_ip /\ *)
      (* npms_ip = Node.distr_msgs_to ip (map fst pmp_new) /\ *)
      npms_ip = filtermap (aux_msgs_to (NW.mcast_groupinfo nw1) ip) ops /\

      nw_msgs_to ip nw' =
      nw_msgs_to ip nw1 ++ npms_ip /\
      length npms_ip <= AANode.inbox_sz inb_m /\
      (* (AANode.inbox_sz inb_m = 0 -> npms_ip = []) /\ *)
      (forall pm (IN: In pm npms_ip),
          exists tid_s msg inb_r_m,
            <<PM_PORT: Packet.dest_port pm = port>> /\
            (* <<AbstMW.parse_pld (Packet.payload pm) = *)
            (* Some (sytm, tid_s, msg) /\  *)
            <<PLD_SIZE_EQ: length (Packet.payload pm) = pld_size>> /\
            <<PARSE_OK: parse_msg (Packet.payload pm) =
                        Some (sytm, tid_s, msg)>> /\
            <<ROW_NTH: nth_error inb_m tid_s = Some inb_r_m>> /\
            <<IN_ROW: In msg inb_r_m>>)
  .
  Proof.
    inv GATHER.
    unfold nw_msgs_to. ss.
    exists (Node.distr_msgs_to ip (map fst pmp_new)).

    renames oms ops into outs_src outs_tgt.

    assert (AUX_EQ: Node.distr_msgs_to ip (map fst pmp_new) =
                    filtermap (aux_msgs_to mcg ip) outs_tgt).
    { inv WF_NW1; ss.
      eapply aux_msgs_to_equiv; eauto.
      hexploit task_id_ip_comput; eauto. i. des. ss. }

    splits.
    - ss.
    - unfold Node.distr_msgs_to.
      rewrite map_app.
      rewrite filtermap_app. ss.
    - rewrite AUX_EQ.
      inv WF_NW1. ss.
      eapply outs_size_incl_aux; eauto; ss.
    - rewrite AUX_EQ.
      intros pm IN_AUX.
      hexploit filtermap_in; eauto.
      intros (op & IN_OUTS_TGT & AUX_SOME).

      eapply In_nth_error in IN_OUTS_TGT. des.
      rewrite iForall2_nth in MATCH.
      specialize (MATCH n).
      rewrite IN_OUTS_TGT in MATCH. ss.

      assert (exists out_src,
                 <<OUT_SRC: nth_error outs_src n = Some out_src>> /\
                 <<MATCH_PKT: match_pkt sytm n out_src op>>).
      { inv MATCH.
        esplits; eauto. }
      des.
      hexploit match_pkt_tgt_Some_impl; eauto; ss.
      { inv WF_NW1. ss. }
      i. des. clarify.
      inv MATCH_PKT. ss.

      assert (RANGE_N: IntRange.sint8 n).
      { cut (n < num_tasks).
        { i. pose proof range_num_tasks as RANGE_NT.
          range_stac. }
        inv IP_SENDER.
        unfold num_tasks.
        apply nth_error_Some. congruence.
      }

      esplits; ss.
      + erewrite serialize_msg_size_eq; eauto.
        rewrite LENGTH_RMSG. ss.
      + apply serialize_parse_msg_inv; eauto.
      + erewrite map_nth_error; eauto.
      + ss. rewrite OUT_SRC_F. left. eauto.
  Qed.

  Lemma match_inb_pre_empty
        tm ip mw inbp inbn
        (MATCH_INB_PRE: match_inb_pre tm ip mw inbp inbn)
    : match_inb_pre tm ip mw [] inbn.
  Proof.
    inv MATCH_INB_PRE.
    econs; eauto.
    - rewrite Forall_forall in PMS_TOT_OLD.
      apply Forall_forall. i.
      eapply PMS_TOT_OLD.
      apply in_or_app. eauto.
    - rewrite app_length in PMS_TOT_LEN. ss. nia.
  Qed.

  Lemma nw_exact_empty
        (tm: DTime.t)
        nw cbt
        (NW_INV: nw_inv tm nw)
        (EXACT: exact_skwd_base_time period tm = Some cbt)
    : NW.packet_msg_pool nw = [] /\ NW.mcast_msg_pool nw = [] /\
      NW.distr nw = (nw, []).
  Proof.
    eapply exact_skwd_base_time_iff in EXACT.
    destruct EXACT as (CBT_POS & TM_EQ & CBT_DIV).

    assert (period <= cbt).
    { r in CBT_DIV. des.
      destruct z; nia. }
    hexploit (NW_INV (cbt - max_clock_skew)).
    { rewrite Nat.sub_add by nia. ss. }
    { ss. nia. }
    intros (MSG_PL & MC_PL).

    assert (MSG_POOL_EMPTY: NW.packet_msg_pool nw = []).
    { destruct (NW.packet_msg_pool nw) as [| h t]; ss.
      exfalso.
      inv MSG_PL. nia. }

    assert (MCAST_EMPTY: NW.mcast_msg_pool nw = []).
    { destruct (NW.mcast_msg_pool nw) as [| h t]; ss.
      exfalso.
      inv MC_PL. nia. }

    splits; ss.
    unfold NW.distr.
    destruct nw as [mg pmp mcmp]. ss.
    clarify.
  Qed.

  Lemma match_inb_pre_nwstep_exact
        tm sytm nw nw1 dms
        cbt ops nw' oms
        ip inbp inbn
        (* inbn1 *) tid mids inbn'
        (WF_NW: NW.wf nw)
        (* (RANGE_SYTM: IntRange.uint64 sytm) *)
        (TASK_ID_IP: task_id_ip tid ip)
        (MCAST_ID_DOMAIN: mcast_id_domain nw ip mids)
        (MCAST_OF_TID: mids = get_mcast_of tid)
        (PRE: match_inb_pre cbt ip nw inbp inbn)
        (DISTR: NW.distr nw = (nw1, dms))
        (NW_INV: nw_inv tm nw)
        (SYTM_EQ: sytm = cbt + period)
        (GATHER: NW.gather nw1 (filtermap id ops) nw')
        (* (WF_OPS: Forall (option_rel1 Packet.wf) ops) *)
        (LEN_OMS: length oms = num_tasks)
        (MATCH_MSGS: iForall2 (match_pkt (cbt + period))
                              0 oms ops)
        (EXACT: exact_skwd_base_time period tm = Some cbt)
        (INBN': inbn' = AANode.merge_inbox
                          AANode.init_inbox
                          (map (AANode.get_msg_by_dest tid) oms))
    : match_inb_pre
        cbt ip nw'
        (filter_port (Node.distr_msgs_to ip dms)) inbn'.
  Proof.
    assert (MCAST_ID_DOMAIN1: mcast_id_domain nw1 ip mids).
    { eapply mcast_id_domain_distr; eauto. }
    hexploit match_inb_pre_distr; eauto.
    intro MATCH_DISTR.

    assert (exists tm_ns, <<TM_EQ: tm = DTime.of_ns tm_ns>> /\
                     <<TM_SYNC: tm_ns + max_clock_skew = cbt>> /\
                     <<SYNC_DIV: Nat.divide period cbt>>).
    { apply exact_skwd_base_time_iff in EXACT; eauto.
      destruct EXACT as (TM_LB & TM_EQ & CBT_DIV).
      exists (cbt - max_clock_skew).
      esplits; ss.
      { apply DTime_units_eq.
        rewrite TM_EQ. ss. }

      cut (period <= cbt).
      { nia. }
      r in CBT_DIV. des. destruct z; nia.
    }
    des.

    hexploit nw_exact_empty; eauto.
    intros (MSG_PL_EMPTY & MCAST_PL_EMPTY & DISTR_EQ).
    rewrite DISTR_EQ in DISTR. clarify.

    assert (FPM_NIL: Node.distr_msgs_to ip [] = []) by ss.
    rewrite FPM_NIL in *.
    rewrite app_nil_r in *.

    inv MATCH_DISTR.
    hexploit nw_gather_matchinfo; eauto.
    intros (npms_ip & _ & NPMS_AUG & NPMS_LEN &
            (* NPMS_NIL_IFF & *) NPMS_PARSE).

    econs; eauto.
    - rewrite AANode.merge_inbox_length.
      unfold AANode.init_inbox.
      apply repeat_length.
    - apply Forall_app_inv in PMS_TOT_OLD.
      destruct PMS_TOT_OLD as [OLD1 OLD2].
      apply Forall_app; ss.
      rewrite NPMS_AUG.
      apply Forall_app; ss.
      apply Forall_forall.
      intros pm IN.
      hexploit NPMS_PARSE; eauto. i. des.
      unfold AbstMW.parse_pld in *. desf.
      econs; eauto.
      { rewrite firstn_all2; eauto.
        nia. }
      nia.

    - rewrite NPMS_AUG.
      unfold nw_msgs_to.
      rewrite MSG_PL_EMPTY. ss.

      rewrite AANode.merge_inbox_size.
      2: { unfold AANode.init_inbox.
           rewrite repeat_length.
           rewrite map_length.
           rewrite <- LEN_OMS. ss.
      }
      rewrite AANode.inbox_size_empty. ss.
  Qed.

  Lemma match_inb_pre_nwstep_nexact
        tm sytm nw nw1 dms
        cbt ops nw' oms
        ip inbp inbn
        (* inbn1 *) tid mids inbn'
        (TASK_ID_IP: task_id_ip tid ip)
        (MCAST_ID_DOMAIN: mcast_id_domain nw ip mids)
        (MCAST_OF_TID: mids = get_mcast_of tid)
        (PRE: match_inb_pre cbt ip nw inbp inbn)
        (DISTR: NW.distr nw = (nw1, dms))
        (NW_INV: nw_inv tm nw)
        (WF_NW: NW.wf nw)
        (TIME_POS: 0 < tm)
        (SYTM_EQ: sytm = cbt + period)
        (* (RANGE_SYTM: IntRange.uint64 sytm) *)
        (GATHER: NW.gather nw1 (filtermap id ops) nw')
        (* (WF_OPS: Forall (option_rel1 Packet.wf) ops) *)
        (LEN_OMS: length oms = num_tasks)
        (MATCH_MSGS: iForall2 (match_pkt sytm)
                              0 oms ops)
        (SKWD_BASE_TIME: get_skwd_base_time period tm = cbt)
        (EXACT: exact_skwd_base_time period tm = None)
        (INBN': inbn' = AANode.merge_inbox
                          inbn (map (AANode.get_msg_by_dest tid) oms))
    : match_inb_pre
        cbt ip nw'
        (inbp ++ filter_port (Node.distr_msgs_to ip dms)) inbn'.
  Proof.
    assert (MCAST_ID_DOMAIN1: mcast_id_domain nw1 ip mids).
    { eapply mcast_id_domain_distr; eauto. }
    hexploit match_inb_pre_distr; eauto.
    intro MATCH_DISTR.

    apply exact_skwd_base_time_None_iff in EXACT.
    2: { ss. }
    destruct EXACT as (cbt' & RANGE_CBT & CBT_DIV).

    assert (cbt' = cbt).
    { eapply get_skwd_base_time_iff in SKWD_BASE_TIME.
      des.
      hexploit (skwd_time_range_almost_overwrap
                  tm cbt cbt'); eauto.
      { nia. }
      i. des; ss.
      subst cbt. nia.
    }
    subst cbt'.

    hexploit nw_gather_matchinfo; try apply GATHER; eauto.
    { eapply NW.wf_distr_preserve; eauto. }
    intros (npms & NPMS_EQ & NPMS_AUG & NPMS_SZ & NPMS_PROP).
    guardH NPMS_EQ.

    inv MATCH_DISTR.
    econs; eauto.
    - rewrite AANode.merge_inbox_length. ss.
    - rewrite NPMS_AUG.
      rewrite app_assoc.
      apply Forall_app; eauto.
      apply Forall_forall.
      intros pm IN_NPMS.
      hexploit NPMS_PROP; eauto. i. des.
      econs; eauto.
      { rewrite firstn_all2; eauto. nia. }
      nia.
    - rewrite NPMS_AUG.
      rewrite app_assoc.
      rewrite app_length.
      rewrite AANode.merge_inbox_size.
      2: { rewrite map_length.
           fold msgT. nia. }
      nia.
  Qed.


  Lemma match_inb_pre_nwstep
        tm sytm nw nw1 dms
        cbt ops nw' oms
        ip inbp inbn
        (* inbn1 *) tid mids inbn'
        (WF_NW: NW.wf nw)
        (* (RANGE_SYTM: IntRange.uint64 sytm) *)
        (TASK_ID_IP: task_id_ip tid ip)
        (MCAST_OF_TID: mids = get_mcast_of tid)
        (MCAST_ID_DOMAIN: mcast_id_domain nw ip mids)
        (PRE: match_inb_pre cbt ip nw inbp inbn)
        (DISTR: NW.distr nw = (nw1, dms))
        (NW_INV: nw_inv tm nw)
        (TM_POS: 0 < tm)
        (SYTM_EQ: sytm = cbt + period)
        (GATHER: NW.gather nw1 (filtermap id ops) nw')
        (* (WF_OPS: Forall (option_rel1 Packet.wf) ops) *)
        (LEN_OMS: length oms = num_tasks)
        (MATCH_MSGS: iForall2 (match_pkt sytm)
                              0 oms ops)
        (SKWD_BASE_TIME: get_skwd_base_time period tm = cbt)
        (INBN': inbn' = AANode.merge_inbox
                          (match exact_skwd_base_time period tm with
                           | Some _ => AANode.init_inbox
                           | None => inbn
                           end)
                          (map (AANode.get_msg_by_dest tid) oms))
    : match_inb_pre cbt ip nw' [] inbn'.
  Proof.
    destruct (exact_skwd_base_time period tm)
      as [cbt'|] eqn: EXACT_TM.
    { assert (cbt' = cbt).
      { apply exact_skwd_impl_get in EXACT_TM.
        clarify. }
      subst cbt'.
      eapply match_inb_pre_empty.
      eapply match_inb_pre_nwstep_exact; eauto.
      subst. ss.
    }
    { eapply match_inb_pre_empty.
      (* hexploit match_inb_pre_empty; eauto. i. *)
      eapply match_inb_pre_nwstep_nexact; eauto.
    }
  Qed.

  Lemma match_inb_impl_pre
        cbt
        inbn inbm ms ip nw'
        (* (SYTM: get_skwd_base_time period tm + period = sytm) *)
        (MATCH_INB : match_inb
                       (cbt + period) inbn inbm
                       (ms ++ nw_msgs_to ip nw'))
    : match_inb_pre cbt ip nw' [] inbn.
  Proof.
    inv MATCH_INB.
    econs; eauto; ss.
    - apply Forall_app_inv in PMS_IN_INB.
      destruct PMS_IN_INB as [_ PMS_IN_INB2].
      apply Forall_forall.
      intros pm IN.
      rewrite Forall_forall in PMS_IN_INB2.
      hexploit PMS_IN_INB2; eauto.
      i. des.
      econs; eauto.
      { rewrite firstn_all2; eauto. nia. }
      nia.
    - rewrite app_length in SIZE_INCL. nia.
  Qed.


  Lemma match_inb_pre_adv
        cbt1 cbt2 ip nw inbp inbn
        (MATCH: match_inb_pre cbt1 ip nw inbp inbn)
        (TM_ADV: cbt1 <= cbt2)
    : match_inb_pre cbt2 ip nw inbp inbn.
  Proof.
    inv MATCH.
    econs; eauto.
    eapply Forall_impl; try apply PMS_TOT_OLD.
    i. eapply old_msg_adv; eauto. nia.
  Qed.


  Inductive match_join_pkt (tip: ip_t)
    : Tid? -> Packet.t? -> Prop :=
  | MatchJoinPkt_None
    : match_join_pkt tip None None
  | MatchJoinPkt_None_MsgPkt
      pm
    : match_join_pkt tip None (Some (inl pm))
  | MatchJoinPkt_None_Join
      mid mip
      (MCAST_ID_IP: mcast_id_ip mid mip)
    : match_join_pkt tip (Some mid) (Some (inr (mip, tip)))
  .

  Lemma task_id_ip_impl_dest
        tid tip
        (TASK_ID_IP: task_id_ip tid tip)
    : dest_id_ip tid tip.
  Proof.
    r in TASK_ID_IP.
    r. unfold dest_ips.
    rewrite nth_error_app1; eauto.
    apply nth_error_Some. congruence.
  Qed.

  Lemma mcast_id_ip_impl_dest
        mid mip
        (MCAST_ID_IP: mcast_id_ip mid mip)
    : dest_id_ip mid mip.
  Proof.
    r in MCAST_ID_IP. des.
    r. subst. unfold num_tasks, dest_ips.
    rewrite nth_error_app2.
    - rewrite minus_plus. ss.
    - nia.
  Qed.


  Lemma mcast_id_domain_nwstep
        tid tip mids sytm
        nw nw1 dms
        outs_src outs_tgt nw'
        (TASK_ID_IP: task_id_ip tid tip)
        (MIDS: mids = get_mcast_of tid)
        (MCAST_ID_DOMAIN: mcast_id_domain nw tip mids)
        (DISTR: NW.distr nw = (nw1, dms))
        (MATCH_MSGS: iForall2 (match_pkt sytm)
                              0 outs_src outs_tgt)
        (GATHER: NW.gather nw1 (filtermap id outs_tgt) nw')
    : mcast_id_domain nw' tip mids.
  Proof.
    hexploit mcast_id_domain_distr; eauto.
    intro MC_DISTR.
    inv MC_DISTR.
    econs; eauto.
    - i. hexploit gather_pending_inv; eauto.
      destruct 1 as [? | IN_PKT].
      + eapply PENDING_INCL; eauto.
      + cut (In (Some (Packet.MCast (mip', tip)))
                outs_tgt).
        { intro IN_OUTS_TGT.
          apply In_nth_error in IN_OUTS_TGT. des.
          rewrite iForall2_nth in MATCH_MSGS.
          specialize (MATCH_MSGS n).
          rewrite IN_OUTS_TGT in MATCH_MSGS.
          inv MATCH_MSGS. ss.
          match goal with
          | H: match_pkt _ _ _ _ |- _ => inv H
          end.

          assert (n = tid).
          { eapply dest_id_ip_inv_det.
            - apply task_id_ip_impl_dest; eauto.
            - apply task_id_ip_impl_dest; eauto.
          }
          subst n.

          apply In_nth_error in MCAST_MEMBER. des.
          rewrite Forall2_nth in MCAST_IPS.
          specialize (MCAST_IPS n).
          rewrite MCAST_MEMBER in MCAST_IPS.
          inv MCAST_IPS.
          assert (y = mip').
          { eapply mcast_id_ip_det; eauto. }
          clarify.
          eapply nth_error_In; eauto.
        }

        eapply filtermap_in in IN_PKT.
        unfold id in IN_PKT.
        des. clarify.
    - i.
      hexploit gather_active_inv; eauto.
  Qed.

  Lemma mcast_id_in_nw_nwstep
        tid nw ip mids
        nw1 dms nw'
        nsytm opkt
        outs_src outs_tgt omid
        (* (TIDS: get_mcast_of tid = mids) *)
        (TASK_ID_IP: task_id_ip tid ip)
        (NW_MCM: mcast_id_in_nw nw ip mids)
        (DISTR: NW.distr nw = (nw1, dms))
        (GATHER: NW.gather nw1 (filtermap id outs_tgt) nw')
        (MATCH_PKTS: iForall2 (match_pkt nsytm)
                              0 outs_src outs_tgt)
        (OUTS_TGT_NTH: nth_error outs_tgt tid =
                       Some opkt)
        (OMID: match_join_pkt ip omid opkt)
    : mcast_id_in_nw nw' ip (mids ++ opt2list omid).
  Proof.
    hexploit mcast_id_in_nw_distr; eauto.
    intro MC_DISTR.
    inv MC_DISTR.

    assert (MCMS_IN_NW' : Forall (mcm_pending nw' ip \1/ mcm_active nw' ip) mips).
    { apply Forall_forall.
      intros mip IN.
      rewrite Forall_forall in MCMS_IN_NW.
      hexploit MCMS_IN_NW; eauto.
      i. des.
      - hexploit gather_pending; eauto.
        (* i. des; eauto. *)
      - hexploit gather_active; eauto.
    }

    destruct omid as [mid|].
    2: { ss. rewrite app_nil_r.
         econs; eauto. }

    destruct opkt as [pkt|]; inv OMID. ss.
    econs.
    - apply Forall2_app; eauto.
    - apply Forall_app; eauto.
      econs.
      2: { econs. }
      left.
      r. inv GATHER. ss.
      rewrite map_app. apply in_or_app.
      right.

      eapply in_map_iff.
      cut (In (mip, ip) mcms_new).
      { intro IN.
        apply In_nth_error in IN. des.
        rewrite Forall2_nth in VALID_DELAYS_MCMS.
        specialize (VALID_DELAYS_MCMS n).
        rewrite IN in VALID_DELAYS_MCMS.
        inv VALID_DELAYS_MCMS.
        match goal with
        | H: valid_delay_added _ _ |- _ => inv H
        end.
        exists (mip, ip, dly).
        esplits; eauto.
        eapply nth_error_In; eauto.
      }

      eapply in_partition_map_r1; try apply CLASSIFY; eauto.
      2: { unfold id. ss. }
      eapply in_filtermap; eauto.
      { unfold id. ss. }
      eapply nth_error_In; eauto.
  Qed.


  Lemma mcast_join_from_others_impossible
        sytm outs_src outs_tgt
        tid ip opkt
        (MATCH: iForall2 (match_pkt sytm) 0 outs_src outs_tgt)
        (OUT_N: nth_error outs_tgt tid = Some opkt)
        (TASK_ID_IP: task_id_ip tid ip)
        (ME_NOT_JOINING: match_join_pkt ip None opkt)
    : forall mip1 ip1
        (IN_OUTS_TGT: In (Some (Packet.MCast (mip1, ip1))) outs_tgt),
      ip1 <> ip.
  Proof.
    ii. subst ip1.
    apply In_nth_error in IN_OUTS_TGT. des.
    rewrite iForall2_nth in MATCH. ss.
    specialize (MATCH n).
    rewrite IN_OUTS_TGT in MATCH.

    assert (exists out_src,
               <<OUT_SRC: nth_error outs_src n = Some out_src>> /\
               <<MATCH1: match_pkt sytm n out_src
                                   (Some (Packet.MCast (mip1, ip)))>>).
    { inv MATCH.
      esplits; eauto. }
    des.

    inv MATCH1.
    assert (n = tid).
    { eapply dest_id_ip_inv_det.
      - apply task_id_ip_impl_dest. eauto.
      - apply task_id_ip_impl_dest. eauto.
    }
    subst n.
    clarify.
    inv ME_NOT_JOINING.
  Qed.

  Lemma mcast_id_active_nwstep
        tid nw ip mids
        nw1 dms nw'
        nsytm opkt
        outs_src outs_tgt
        (TASK_ID_IP: task_id_ip tid ip)
        (MCAST_ID_ACTIVE: mcast_id_active nw ip mids)
        (DISTR: NW.distr nw = (nw1, dms))
        (GATHER: NW.gather nw1 (filtermap id outs_tgt) nw')
        (MATCH_PKTS: iForall2 (match_pkt nsytm)
                              0 outs_src outs_tgt)
        (OUTS_TGT_NTH: nth_error outs_tgt tid =
                       Some opkt)
        (OMID: match_join_pkt ip None opkt)
    : mcast_id_active nw' ip mids.
  Proof.
    hexploit mcast_id_active_distr; eauto.
    intro MC_DISTR.
    inv MC_DISTR.

    econs; eauto.
    - apply Forall_forall.
      intros mip IN.
      eapply gather_active; eauto.
      eapply Forall_forall in MCMS_ACTIVE; eauto.
    - intros mip ACT.
      hexploit gather_active_inv; eauto.
    - intros mip' PENDING'.
      r in PENDING'.
      inv GATHER. ss.
      unfold mcm_pending in NO_PENDING. ss.

      rewrite map_app in PENDING'.
      apply in_app_or in PENDING'.
      destruct PENDING' as [?| IN_NEW].
      { eauto. }

      (* destruct opkt as [[pm | mcm]|]; cycle 2. *)
      (* + *)

      apply in_map_iff in IN_NEW.
      destruct IN_NEW as [[[? ?] dly] [? IN_MCMP_NEW]].
      ss. clarify.

      cut (In (mip', ip) mcms_new).
      { intro IN_MCMS_NEW.
        hexploit in_partition_map_r2; eauto.
        unfold id.
        intros [? [IN_F ?]]. clarify.
        eapply filtermap_in in IN_F. des. clarify.
        hexploit mcast_join_from_others_impossible; eauto.
      }
      apply In_nth_error in IN_MCMP_NEW. des.
      rewrite Forall2_nth in VALID_DELAYS_MCMS.
      specialize (VALID_DELAYS_MCMS n).
      rewrite IN_MCMP_NEW in VALID_DELAYS_MCMS.
      inv VALID_DELAYS_MCMS.
      match goal with
      | H: valid_delay_added _ _ |- _ => inv H
      end.
      eapply nth_error_In; eauto.
  Qed.


  Lemma match_inb_empty sytm
    : match_inb sytm AANode.init_inbox
                AbstMW.init_inbox [].
  Proof.
    econs; eauto.
    - unfold AANode.init_inbox.
      rewrite repeat_length. ss.
    - rewrite filtermap_nil.
      2: { unfold init_inbox.
           i. eapply repeat_spec; eauto. }
      ss. nia.
    - apply Forall2_nth. i.
      destruct (lt_ge_dec n num_tasks).
      + match goal with
        | |- option_rel2 _ ?nth1 ?nth2 =>
          assert ((exists n1, <<NTH1: nth1 = Some n1>>) /\
                  (exists n2, <<NTH2: nth2 = Some n2>>))
        end.
        { split.
          - apply Some_not_None.
            apply nth_error_Some.
            unfold init_inbox.
            rewrite repeat_length. ss.
          - apply Some_not_None.
            apply nth_error_Some.
            unfold AANode.init_inbox.
            rewrite repeat_length. ss.
        }
        des.
        rewrite NTH1. rewrite NTH2. econs.
        eapply nth_error_In in NTH1.
        eapply nth_error_In in NTH2.
        apply repeat_spec in NTH1.
        apply repeat_spec in NTH2.
        clarify.
      + match goal with
        | |- option_rel2 _ ?nth1 ?nth2 =>
          assert ((<<NTH1: nth1 = None>>) /\
                  (<<NTH2: nth2 = None>>))
        end.
        { split.
          - apply nth_error_None.
            unfold init_inbox.
            rewrite repeat_length. ss.
          - apply nth_error_None.
            unfold AANode.init_inbox.
            rewrite repeat_length. ss.
        }
        des.
        rewrite NTH1. rewrite NTH2. econs.
    - i. exfalso.
      apply nth_error_In in INB_ROW.
      apply repeat_spec in INB_ROW.
      clarify.
  Qed.

  Lemma match_inb_distr
        stm inb inbm inbp
        tid ip mids
        nw nw1 dms
        (TASK_ID_IP: task_id_ip tid ip)
        (MCAST_ID_ACTIVE: mcast_id_active nw ip mids)
        (MATCH: match_inb stm inb inbm
                          (inbp ++ nw_msgs_to ip nw))
        (DISTR: NW.distr nw = (nw1, dms))
    : match_inb stm inb inbm
                ((inbp ++ filter_port (Node.distr_msgs_to ip dms)) ++ nw_msgs_to ip nw1) /\
      mcast_id_domain nw1 ip mids.
  Proof.
    hexploit (nw_msgs_to_distr ip); eauto.
    intros (LEN_EQ & INCL1 & INCL2 & INCLR).
    inv MATCH.

    split.
    2: { eapply mcast_id_active_impl_domain.
         eapply mcast_id_active_distr; eauto. }

    econs; eauto.
    - assert (length (filter_port (Node.distr_msgs_to ip dms)) <= length (Node.distr_msgs_to ip dms)).
      { eapply filter_length. }

      do 2 rewrite app_length.
      rewrite app_length in SIZE_INCL. nia.

    - rewrite <- app_assoc.
      apply Forall_app_inv in PMS_IN_INB.
      destruct PMS_IN_INB as [PR1 PR2].
      apply Forall_app; ss.

      rewrite Forall_forall in PR2.
      apply Forall_app.
      + apply Forall_forall.
        intros pm IN1.
        apply filter_In in IN1.
        destruct IN1 as [IN_PM PORT_EQ].
        hexploit PR2; eauto.
      + apply Forall_forall.
        intros pm IN2.
        hexploit PR2; eauto.

    - i. hexploit WHEN_INBM_EMPTY; eauto.
      i. des.
      esplits; eauto.
      apply in_app_or in IN_PMS.
      destruct IN_PMS as [IN1 | IN2].
      + apply in_or_app. left.
        apply in_or_app. left. eauto.
      + hexploit INCLR; eauto.
        destruct 1.
        * apply in_or_app. right. eauto.
        * apply in_or_app. left.
          apply in_or_app. right.

          unfold filter_port.
          apply filter_In.
          split; ss.
          rewrite PORT_EQ.
          rewrite Nat.eqb_refl. ss.
  Qed.


  Inductive match_lstate
            (tm: DTime.t) (nw: NW.t)
    : @AANode.state sysE -> @AbstMW.state sysE -> Prop :=
    (* : @AANode.state sysE msgT -> @Node.state sysE -> Prop := *)
  | Match_Off
      tid node mids ip amw inbn cbt
      (TASK_IP: nth_error task_ips tid = Some ip)
      (MCAST_OF_TID: mids = get_mcast_of tid)
      (MCAST_ID_DOMAIN: mcast_id_domain nw ip mids)
      (ABST_MW_STATE: amw = AbstMW.Off)
      (SKWD_BASE_TIME: get_skwd_base_time period tm = cbt)
      (MATCH_NW: match_inb_pre cbt ip nw [] inbn)
    : match_lstate
        tm nw
        (AANode.State tid node inbn None)
        (* (Node.State (AbstMW.as_node _ _ tid node) *)
        (AbstMW.State tid ip node amw)

  | Match_Off_Prep
      tid node mids ip
      amw mids1 mids2
      jtl inbp ast
      cbt inbn
      (TASK_IP: nth_error task_ips tid = Some ip)
      (MCAST_ID_DOMAIN: mcast_id_domain nw ip mids)
      (MCAST_OF_TID: mids = get_mcast_of tid)
      (CUR_BASE_TIME: cbt = get_skwd_base_time period tm)
      (CBT_LB: period <= cbt)
      (JOIN_BEFORE_START: jtl = cbt + period - max_clock_skew - max_nw_delay)
      (RANGE_TM: DTime.of_ns (cbt - max_clock_skew) < tm
                 <= DTime.of_ns jtl)

      (ABST_INIT_STATE: SNode.init_app_state _ ast)
      (ABST_MW_STATE: amw = AbstMW.Prep
                              mids2 jtl inbp ast)
      (MCAST_IPS_TO_JOIN: mids1 ++ mids2 = mids)
      (JOINED: mcast_id_in_nw nw ip mids1)
      (MATCH_NW: match_inb_pre cbt ip nw inbp inbn)
    : match_lstate
        tm nw
        (AANode.State tid node inbn None)
        (AbstMW.State tid ip node amw)

  | Match_Off_Ready
      tm_p tid node mids inbn ip amw
      cbt fsytm jtl ast inbp inbm
      (TASK_IP: nth_error task_ips tid = Some ip)
      (MCAST_ID_DOMAIN: mcast_id_domain nw ip mids)
      (MCAST_OF_TID: mids = get_mcast_of tid)
      (TM_PREV: DTime.succ tm_p = tm)
      (CUR_BASE_TIME: cbt = get_skwd_base_time period tm_p)
      (JOIN_BEFORE_START: jtl = cbt + period - max_clock_skew - max_nw_delay)
      (RANGE_TM: DTime.of_ns (cbt - max_clock_skew) < tm <=
                 DTime.of_ns (cbt + period - max_clock_skew ))
      (FIRST_SYNC_TIME: fsytm = cbt + period + period)
      (ABST_INIT_STATE: SNode.init_app_state _ ast)
      (INBM_INIT: inbm = AbstMW.init_inbox)
      (ABST_MW_STATE: amw = AbstMW.On
                              fsytm inbp inbm
                              AbstMW.Ready ast)
      (JOINED: mcast_id_in_nw nw ip mids)
      (MATCH_NW: match_inb_pre cbt ip nw inbp inbn)
    : match_lstate
        tm nw
        (AANode.State tid node inbn None)
        (AbstMW.State tid ip node amw)

  | Match_Done_Ready
      tid node inbn mids ip amw
      sytm inbp inbm ast cbt
      ms_old ms_n
      ocnt
      (TASK_IP: nth_error task_ips tid = Some ip)
      (MCAST_ID_ACTIVE : mcast_id_active nw ip mids)
      (MCAST_OF_TID: mids = get_mcast_of tid)
      (CUR_BASE_TIME: Nat.divide period cbt)
      (FIRST_SYNC_TIME: cbt + period = sytm)
      (RANGE_TM: DTime.of_ns (cbt - max_clock_skew) < tm
                 <= DTime.of_ns (sytm - max_clock_skew))
      (ABST_MW_STATE: amw = AbstMW.On
                              sytm inbp inbm
                              AbstMW.Ready ast)
      (INBP_DIV: inbp = ms_old ++ ms_n)
      (* (JOINED: mcast_id_in_nw nw ip mids) *)
      (OLD_CNT: length ms_old = ocnt)
      (OLD_MSGS: Forall (old_msg (cbt + period)) ms_old)
      (MATCH_INB: match_inb sytm inbn inbm
                            (ms_n ++ nw_msgs_to ip nw))
    : match_lstate
        tm nw
        (AANode.State tid node inbn
                      (Some (ocnt, AANode.Done, ast)))
        (AbstMW.State tid ip node amw)

  | Match_Ready
      tid node mids inbn inbc ip amw
      sytm inbp inbm ast
      ms_old ms_c ms_n ocnt
      (TASK_IP: nth_error task_ips tid = Some ip)
      (MCAST_ID_ACTIVE : mcast_id_active nw ip mids)
      (MCAST_OF_TID: mids = get_mcast_of tid)
      (CUR_BASE_TIME: Nat.divide period sytm)
      (RANGE_TM: DTime.of_ns (sytm - max_clock_skew) < tm
                 <= DTime.of_ns (sytm + period - max_clock_skew - max_nw_delay))
      (* (INBM_INIT: inbm = AbstMW.init_inbox msgT) *)
      (ABST_MW_STATE: amw = AbstMW.On
                              sytm inbp inbm
                              AbstMW.Ready ast)
      (* (JOINED: mcast_id_in_nw nw ip mids) *)
      (OLD_CNT: length ms_old = ocnt)
      (OLD_MSGS: Forall (old_msg sytm) ms_old)
      (INBP_DIV: inbp = ms_old ++ ms_c ++ ms_n)
      (MATCH_INBC: match_inb sytm inbc inbm ms_c)
      (MATCH_INBN: match_inb (sytm + period)
                     inbn AbstMW.init_inbox
                     (ms_n ++ nw_msgs_to ip nw))
    : match_lstate
        tm nw
        (AANode.State tid node inbn
                      (Some (ocnt, AANode.Ready sytm inbc, ast)))
        (AbstMW.State tid ip node amw)

  | Match_Running
      tid node mids inbn ip amw
      sytm inbp inbm sh ast
      ms_old ms_n
      ocnt
      (TASK_IP: nth_error task_ips tid = Some ip)
      (MCAST_ID_ACTIVE: mcast_id_active nw ip mids)
      (MCAST_OF_TID: mids = get_mcast_of tid)
      (CUR_BASE_TIME: Nat.divide period sytm)
      (TIME_BELOW_MAX: sytm < MAX_TIME)
      (RANGE_TM: DTime.of_ns (sytm - max_clock_skew) < tm
                 <= DTime.of_ns (sytm + period - max_clock_skew - max_nw_delay))
      (ABST_MW_STATE: amw = AbstMW.On
                              sytm inbp inbm
                              (AbstMW.Running sh) ast)
      (* (JOINED: mcast_id_in_nw nw ip mids) *)
      (INBP_DIV: inbp = ms_old ++ ms_n)
      (OLD_CNT: length ms_old = ocnt)
      (OLD_MSGS: Forall (old_msg (sytm + period)) ms_old)
      (MATCH_INBN: match_inb (sytm + period) inbn inbm
                             (ms_n ++ nw_msgs_to ip nw))
    : match_lstate
        tm nw
        (AANode.State tid node inbn
                      (Some (ocnt, AANode.Running sytm sh, ast)))
        (* (Node.State (AbstMW.as_node _ _ tid node) *)
        (AbstMW.State tid ip node amw)
  .


  Lemma nw_msgs_to_gather
        ip nw1 nw'
        mids sytm tid
        outs_src outs_tgt
        (WF_NW1: NW.wf nw1)
        (IP_LOCAL: IP.local_ip ip)
        (* (RANGE_SYTM: IntRange.uint64 sytm) *)
        (* (RANGE_NUM_TASKS: IntRange.sint8 num_tasks) *)
        (GATHER: NW.gather nw1 (filtermap id outs_tgt) nw')
        (TASK_ID_IP: task_id_ip tid ip)
        (MCAST_ID_ACTIVE: mcast_id_active nw1 ip mids)
        (MCAST_OF_TID: mids = get_mcast_of tid)
        (LEN_OUTS: length outs_src = num_tasks)
        (MATCH_OUTMSGS: iForall2 (match_pkt sytm)
                                 0 outs_src outs_tgt)
    : exists ms_new,
      nw_msgs_to ip nw' = nw_msgs_to ip nw1 ++ ms_new /\
      match_inb sytm
                (map (AANode.get_msg_by_dest tid) outs_src)
                AbstMW.init_inbox ms_new.
  Proof.
    guardH MCAST_OF_TID.
    hexploit nw_gather_matchinfo; eauto.
    { apply mcast_id_active_impl_domain. eauto. }
    intros (npms_ip & NPMS_IN_TGT & NW_MSGS_TO' &
            NPMS_IP_SZ & IN_NPMS_PROP).

    esplits; eauto.

    (* inv GATHER. *)
    (* unfold nw_msgs_to. ss. *)
    (* exists (Node.distr_msgs_to ip (map fst pmp_new)). *)
    (* split. *)
    (* { unfold Node.distr_msgs_to. *)
    (*   rewrite map_app. *)
    (*   rewrite filtermap_app. ss. } *)

    (* assert (AUX_EQ: Node.distr_msgs_to ip (map fst pmp_new) = *)
    (*                 filtermap (aux_msgs_to mcg ip) outs_tgt). *)
    (* { eapply aux_msgs_to_equiv; eauto. *)
    (*   inv WF_NW1; ss. } *)

    econs; ss.
    - rewrite map_length. fold msgT. rewrite LEN_OUTS. ss.
    - rewrite filtermap_init_inbox. ss.
    - apply Forall_forall. ss.
    - apply Forall2_nth. i.
      destruct (nth_error init_inbox n) as [nn|] eqn: INIT_INB_N.
      2: {
        fold bytes msgT in INIT_INB_N.
        rewrite INIT_INB_N.

        assert (SRC_NONE: nth_error outs_src n = None).
        { eapply nth_error_eqlen_None.
          2: { apply INIT_INB_N. }
          unfold msgT.
          rewrite init_inbox_length.
          fold msgT.
          congruence.
        }
        rewrite <- map_nth_error_None_iff in SRC_NONE.
        rewrite SRC_NONE. econs.
      }
      fold bytes msgT in INIT_INB_N.
      rewrite INIT_INB_N.

      assert (NTH_SRC: exists x, nth_error (map (AANode.get_msg_by_dest tid) outs_src) n = Some x).
      { eapply nth_error_eqlen_Some with (l1:=init_inbox); eauto.
        rewrite map_length.
        rewrite init_inbox_length.
        rewrite <- LEN_OUTS. ss.
      }
      des.
      fold msgT in NTH_SRC. fold msgT.
      rewrite NTH_SRC. econs.

      hexploit (init_inbox_nth n).
      { rewrite <- init_inbox_length.
        apply nth_error_Some.
        fold bytes msgT.
        congruence.
      }
      i. subst.
      exfalso.
      unfold msgT in *.
      congruence.

    - fold msgT.
      i. rewrite map_nth_error_iff in INB_ROW.
      destruct INB_ROW as (out_src & OUT_SRC & OUT_SRC_F).
      rewrite iForall2_nth in MATCH_OUTMSGS.
      specialize (MATCH_OUTMSGS tid_s).
      rewrite OUT_SRC in MATCH_OUTMSGS.

      assert (exists out_tgt,
                 <<OUT_TGT: nth_error outs_tgt tid_s = Some out_tgt>> /\
                 <<MATCH_PKT: match_pkt sytm tid_s out_src out_tgt>>).
      { inv MATCH_OUTMSGS. esplits; eauto. }
      des.

      inv MATCH_PKT; ss.
      (* unfold filter_by_dest in IN_ROW. ss. *)
      (* unfold chget_by_dest in IN_ROW. ss. *)

      assert (<<TID_D: (tid_d = tid \/ In tid_d mids)>> /\
              m = rmsg).
      { rewrite <- MCAST_OF_TID in IN_ROW.
        desf. ss.
        des; ss. clarify.
        split; ss.
        destruct (Nat.eqb_spec tid_d tid); eauto.
        ss. rewrite existsb_exists in *. des.
        rewrite Nat.eqb_eq in *.
        clarify. eauto.
      }
      nbdes. clarify.
      clear IN_ROW.
      pose (pm:= Packet.mkMsg
                   ip_s ip_d port
                   (serialize_msg sytm tid_s rmsg)).
      fold pm in OUT_TGT.
      exists pm.

      assert (RANGE_TID_S: IntRange.sint8 tid_s).
      { inv IP_SENDER.
        cut (tid_s < length task_ips).
        { pose proof range_num_tasks as RANGE_NT.
          fold num_tasks.
          range_stac. }
        eapply nth_error_Some. congruence.
      }

      splits; ss; cycle 1.
      { erewrite serialize_msg_size_eq; eauto.
        rewrite LENGTH_RMSG. ss. }
      { erewrite serialize_parse_msg_inv; eauto. }

      inv GATHER.
      erewrite <- aux_msgs_to_equiv; eauto.
      2: { ss. inv WF_NW1. ss. }

      unfold Node.distr_msgs_to.
      eapply in_filtermap.
      { instantiate (1:= (ip, pm)).
        unfold Node.chget_pm_by_dest. ss.
        rewrite Nat.eqb_refl. ss. }

      cut (exists d, In (ip, pm, d) pmp_new).
      { intros [d IN].
        eapply in_map with (f:= fst) in IN. ss. }
      guardH TID_D.

      assert (LOCAL_IP: IP.local_ip ip).
      { pose proof task_ips_local_ip as TL.
        rewrite Forall_forall in TL.
        eapply TL.
        eapply nth_error_In.
        eapply TASK_ID_IP. }
      destruct (IP.mcast_ip ip) eqn:MCAST_IP_F.
      { exfalso.
        generalize (IP.normal_mcast_disjoint ip).
        rewrite MCAST_IP_F. rewrite LOCAL_IP. ss. }

      rewrite <- flat_map_concat_map in VALID_DELAYS_PMS.

      cut (exists x, In x pms_new /\ In (ip, pm) (NW.attach_adest mcg x)).
      { intro FMAP_AUX.
        eapply in_flat_map in FMAP_AUX.
        apply In_nth_error in FMAP_AUX.
        destruct FMAP_AUX as [n NTH_FMAP].

        rewrite Forall2_nth in VALID_DELAYS_PMS.
        specialize (VALID_DELAYS_PMS n).

        clear - VALID_DELAYS_PMS NTH_FMAP.
        rewrite NTH_FMAP in VALID_DELAYS_PMS.
        inv VALID_DELAYS_PMS.
        match goal with
        | H: valid_delay_added _ _ |- _ => inv H
        end.
        exists dly. eapply nth_error_In; eauto.
      }

      cut (<<PM_IN_NEW: In pm pms_new>> /\
                        (ip_d = ip \/
                         (<<IP_D_MCAST: IP.mcast_ip ip_d>> /\
                                        <<IP_IN_GROUP: In ip (NW.get_actual_receivers mcg ip_d)>>))).
      { i. des.
        - subst ip_d.
          exists pm. esplits; eauto.
          unfold NW.attach_adest. ss.
          rewrite MCAST_IP_F. ss. eauto.
        - exists pm. esplits; eauto.
          unfold NW.attach_adest. ss.
          rewrite IP_D_MCAST.
          change (ip, pm) with ((fun x => (x, pm)) ip).
          apply in_map. ss.
      }

      splits.
      * match goal with
        | H: ?lp = (pms_new, _) |- _ =>
          replace pms_new with (fst lp)
        end.
        2: { rewrite CLASSIFY. ss. }

        apply in_partition_map_l_iff.
        esplits; ss.
        eapply in_filtermap; ss.
        eapply nth_error_In; eauto.
      * desH TID_D.
        { left. clarify.
          r in IP_DEST. r in TASK_ID_IP.
          unfold dest_ips in *.
          rewrite nth_error_app1 in IP_DEST.
          2: { apply nth_error_Some. congruence. }
          clarify.
        }
        { right.
          inv MCAST_ID_ACTIVE.

          assert (exists mip', <<IN_MIPS': In mip' mips>> /\
                                      <<MCAST_ID_IP': mcast_id_ip tid_d mip'>>).
          { rewrite Forall2_nth in MCAST_IPS.
            eapply In_nth_error in TID_D. des.
            specialize (MCAST_IPS n).
            rewrite TID_D in MCAST_IPS.
            inv MCAST_IPS.
            esplits; eauto.
            eapply nth_error_In; eauto.
          }
          des.

          hexploit mcast_id_ip_comput; eauto.
          intros [TID2IP' MCAST_IP'].

          assert (MIP_EQ: mip' = ip_d).
          { r in IP_DEST. r in MCAST_ID_IP'.
            unfold dest_ips in *.
            des.
            rewrite nth_error_app2 in IP_DEST.
            2: { fold num_tasks. nia. }
            subst tid_d.
            fold num_tasks in IP_DEST.
            rewrite minus_plus in IP_DEST. clarify.
          }
          rewrite MIP_EQ in *. clear MIP_EQ.
          split.
          { congruence. }

          unfold NW.get_actual_receivers.
          eapply in_filtermap with (a:= (ip_d, ip)).
          { ss. rewrite Nat.eqb_refl. ss. }

          rewrite Forall_forall in MCMS_ACTIVE.
          hexploit MCMS_ACTIVE; eauto.
        }
      * ss. inv WF_NW1. ss.
  Qed.


  Lemma match_inb_gather
        stm inb inbm inbp
        tid ip mids
        nw1 nw'
        outs_src outs_tgt
        (WF_NW1: NW.wf nw1)
        (* (RANGE_STM: IntRange.uint64 stm) *)
        (TASK_ID_IP: task_id_ip tid ip)
        (MCAST_ID_DOMAIN: mcast_id_active nw1 ip mids)
        (MCAST_OF_TID: mids = get_mcast_of tid)
        (OUTS_SRC_LENGTH: length outs_src = num_tasks)
        (MATCH: match_inb stm inb
                          inbm (inbp ++ nw_msgs_to ip nw1))
        (MATCH_OUTMSGS: iForall2 (match_pkt stm)
                                 0 outs_src outs_tgt)
        (GATHER: NW.gather nw1 (filtermap id outs_tgt) nw')
    : match_inb stm
                (AANode.merge_inbox
                   inb (map (AANode.get_msg_by_dest tid) outs_src))
                inbm (inbp ++ nw_msgs_to ip nw').
  Proof.
    inv MATCH.

    (* assert (F_OUTS_SRC_LENGTH: *)
    (*           length (map (filter_by_dest (tid :: mids)) outs_src) = num_tasks). *)
    (* { rewrite map_length. ss. } *)

    hexploit nw_msgs_to_gather; eauto.
    { eapply task_id_ip_comput; eauto. }

    intros (ms_new & NW_MSGS_TO_NEW & MATCH_INB_NEW).
    inv MATCH_INB_NEW.

    econs.
    - rewrite AANode.merge_inbox_length. ss.
    - rewrite AANode.merge_inbox_size.
      2: { fold bytes msgT.
           rewrite map_length. congruence. }
      rewrite NW_MSGS_TO_NEW.
      clear - SIZE_INCL SIZE_INCL0.
      rewrite app_assoc.
      rewrite app_length.
      nia.
    - rewrite NW_MSGS_TO_NEW.
      rewrite app_assoc.
      apply Forall_app.
      + clear - PMS_IN_INB.
        eapply Forall_impl; eauto. ss.
        intros pm ?. des.
        esplits.
        * eauto.
        * eauto.
        * eauto.
        * erewrite AANode.merge_inbox_nth by eauto.
          reflexivity.
        * apply in_or_app. left. ss.
      + (* clear - PMS_IN_INB0 INB_LENGTH F_OUTS_SRC_LENGTH. *)
        eapply Forall_impl; eauto. ss.
        intros pm ?. des.
        assert (exists r, nth_error inb tid_s = Some r).
        { apply Some_not_None.
          apply nth_error_Some.
          rewrite INB_LENGTH.
          rewrite <- INB_LENGTH0.
          apply nth_error_Some.
          fold msgT in INB_ROW_EX. fold msgT.
          congruence.
        }
        des.
        esplits.
        * eauto.
        * eauto.
        * eauto.
        * erewrite AANode.merge_inbox_nth by eauto.
          reflexivity.
        * fold msgT. fold msgT in INB_ROW_EX.
          rewrite INB_ROW_EX.
          apply in_or_app. eauto.
    - clear - INBM_IN_INB.
      apply Forall2_nth.
      rewrite Forall2_nth in INBM_IN_INB.
      intro n. specialize (INBM_IN_INB n).

      destruct (nth_error inbm n) as [inbm_r|] eqn:INBM_R.
      2: { inv INBM_IN_INB.
           rewrite AANode.merge_inbox_nth_None by ss.
           econs. }

      inv INBM_IN_INB.
      hexploit AANode.merge_inbox_nth; eauto.
      intro R. rewrite R.
      econs. i. clarify.
      apply in_or_app.
      left. eauto.

    - i.
      destruct (nth_error inb tid_s) as [inb_r1|] eqn:INT_R1.
      2: {
        exfalso.
        hexploit AANode.merge_inbox_nth_None; eauto.
        intro R. rewrite R in INB_ROW. ss.
      }

      hexploit AANode.merge_inbox_nth; eauto.
      intro R. rewrite R in INB_ROW. clear R.
      clarify.

      assert (INB_R2: exists inb_r2,
                 nth_error (map (AANode.get_msg_by_dest tid)
                                outs_src) tid_s = Some inb_r2).
      { apply Some_not_None.
        eapply nth_error_Some.
        (* rewrite F_OUTS_SRC_LENGTH. *)
        fold msgT. fold msgT in INB_LENGTH0.
        rewrite INB_LENGTH0.
        rewrite <- INB_LENGTH.
        eapply nth_error_Some.
        congruence.
      }
      des.

      fold bytes msgT in INB_R2, IN_ROW.
      rewrite INB_R2 in IN_ROW.
      apply in_app_or in IN_ROW.
      rewrite NW_MSGS_TO_NEW.
      rewrite app_assoc.

      destruct IN_ROW as [IN1 | IN2].
      + hexploit WHEN_INBM_EMPTY; eauto.
        i. des.
        esplits; eauto.
        apply in_or_app. eauto.
      + hexploit WHEN_INBM_EMPTY0; eauto.
        { apply repeat_nth_error_Some.
          fold num_tasks.
          rewrite <- INB_LENGTH.
          apply nth_error_Some.
          congruence.
        }
        i. des.
        esplits; eauto.
        apply in_or_app. eauto.
  Qed.

  Lemma match_inb_nwstep
        stm inb inbm inbp
        tid ip mids
        nw nw1 dms nw'
        outs_src outs_tgt
        (* (RANGE_STM: IntRange.uint64 stm) *)
        (WF_NW: NW.wf nw)
        (TASK_ID_IP: task_id_ip tid ip)
        (MCAST_ID_ACTIVE: mcast_id_active nw ip mids)
        (MCAST_OF_TID: mids = get_mcast_of tid)
        (MATCH: match_inb stm inb
                          inbm (inbp ++ nw_msgs_to ip nw))
        (DISTR: NW.distr nw = (nw1, dms))
        (OUTS_SRC_LENGTH: length outs_src = num_tasks)
        (MATCH_OUTMSGS: iForall2 (match_pkt stm)
                                 0 outs_src outs_tgt)
        (GATHER: NW.gather nw1 (filtermap id outs_tgt) nw')
    : match_inb stm
                (AANode.merge_inbox
                   inb (map (AANode.get_msg_by_dest tid) outs_src))
                inbm ((inbp ++ (filter_port (Node.distr_msgs_to ip dms))) ++
                           nw_msgs_to ip nw')
  .
  Proof.
    hexploit match_inb_distr; eauto. i. des.
    eapply match_inb_gather with (nw1:= nw1); eauto.
    - hexploit NW.wf_distr_preserve; eauto.
      i. des. ss.
    - eapply mcast_id_active_distr; eauto.
  Qed.

  Lemma match_inb_to_pre
        cbt inbn inbm
        ms ip nw
        (MATCH: match_inb (cbt + period) inbn
                          inbm
                          (ms ++ nw_msgs_to ip nw))
    : match_inb_pre cbt ip nw [] inbn.
  Proof.
    inv MATCH.
    econs; eauto.
    - clear - PMS_IN_INB PERIOD_COND. ss.
      apply Forall_forall.
      intros pm IN.
      apply Forall_app_inv in PMS_IN_INB.
      destruct PMS_IN_INB as [_ PMS_IN_INB2].
      rewrite Forall_forall in PMS_IN_INB2.
      hexploit PMS_IN_INB2; eauto. i. des.
      econs; eauto.
      { rewrite firstn_all2; eauto. nia. }
      nia.
    - clear - SIZE_INCL.
      rewrite app_length in SIZE_INCL.
      ss. nia.
  Qed.




  (* Lemma update_msg_sz_inc inbm tid m *)
  (*   : length (filtermap id (update_msg inbm tid m)) *)
  (*     <= S (length (filtermap id inbm)). *)
  (* Proof. *)
  (*   unfold update_msg. *)

  (*   hexploit (replace_nth_spec _ inbm tid). *)
  (*   intros [[? REPL_EQ] | AUX]. *)
  (*   { rewrite REPL_EQ. ss. nia. } *)
  (*   destruct AUX as (l1 & p & l2 & DIV & *)
  (*                    LEN1 & REPL_EQ). *)
  (*   rewrite REPL_EQ, DIV. ss. *)
  (*   do 2 rewrite filtermap_app. *)
  (*   do 2 rewrite app_length. ss. *)
  (*   destruct p; ss; nia. *)
  (* Qed. *)

  Lemma match_inb_upd_msg
        cbt inb inbm tid
        m ms inb_r msg
        (PORT_EQ : Packet.dest_port m = port)
        (PLD_SIZE_EQ : length (Packet.payload m) = pld_size)
        (PARSE_OK : parse_msg (Packet.payload m) = Some (cbt, tid, msg))
        (INB_ROW_EX : nth_error inb tid = Some inb_r)
        (IN_INB_ROW : In msg inb_r)
        (MATCH: match_inb cbt inb inbm (m::ms))
    : match_inb cbt inb
                (update_msg inbm tid msg) ms.
  Proof.
    inv MATCH.
    unfold update_msg.
    destruct (replace_nth_spec _ inbm tid (Some msg))
      as [[? REPL_EQ] | AUX].
    - exfalso.
      cut (nth_error inb tid = None).
      { congruence. }

      eapply nth_error_None.
      apply Forall2_length in INBM_IN_INB.
      fold bytes msgT.
      rewrite <- INBM_IN_INB. ss.
    - destruct AUX as (l1 & p & l2 & DIV &
                       LEN1 & REPL_EQ).
      fold bytes msgT.
      fold bytes msgT in REPL_EQ.
      rewrite REPL_EQ.

      econs; eauto.
      + etransitivity.
        2: { apply SIZE_INCL. }
        etransitivity.
        2: { instantiate (1:= S (length (filtermap id inbm)) + length ms).
             ss. nia. }
        apply plus_le_compat_r.
        rewrite DIV.
        do 4 rewrite filtermap_app. ss.

        destruct p; ss.
        * do 2 rewrite app_length. ss. nia.
        * do 2 rewrite app_length. ss. nia.
      + inv PMS_IN_INB. ss.
      + rewrite DIV in INBM_IN_INB.
        apply Forall2_app_inv_l in INBM_IN_INB.
        destruct INBM_IN_INB as
            (inbc1 & inbc' & IN_INBC1 &
             IN_INBC' & INBC_DIV).
        destruct inbc' as [| inb_tid inbc2].
        { inv IN_INBC'. }
        inv IN_INBC'.

        eapply Forall2_app; eauto.
        econs; eauto.
        i. clarify.

        cut (inb_r = inb_tid).
        { intro R. rewrite <- R. ss. }

        apply Forall2_length in IN_INBC1.
        rewrite IN_INBC1 in INB_ROW_EX.
        clear - INB_ROW_EX.
        rewrite nth_error_app2 in INB_ROW_EX by nia.
        rewrite Nat.sub_diag in INB_ROW_EX.
        ss. clarify.
      + i.
        hexploit WHEN_INBM_EMPTY; eauto.
        { rewrite DIV.

          assert ((<<TID_L1: tid_s < length l1>> /\
                             <<IN_L1: nth_error l1 tid_s = Some None>>) \/
                  (<<TID_L2: length l1 < tid_s>> /\
                             <<IN_L2: nth_error l2 (tid_s - S (length l1)) = Some None>>)).
          { destruct (classic (tid_s < length l1)).
            - left. split; ss. erewrite <- nth_error_app1; eauto.
            - destruct (classic (tid_s = length l1)).
              { subst. rewrite nth_error_app2 in INBM_ROW; eauto; try nia.
                rewrite Nat.sub_diag in *. ss. }
              right. split; unnw; try nia.
              revert INBM_ROW.
              rewrite app_assoc, nth_error_app2; rewrite app_length; ss; try nia.
              rewrite Nat.add_1_r. ss.
          }
          des.
          - rewrite nth_error_app1; ss.
          - rewrite nth_error_app2 by nia.
            replace (tid_s - length l1) with
                (S (tid_s - S (length l1))) by nia.
            ss.
        }
        i. ss. des.
        2: { esplits; eauto. }
        exfalso.
        clarify.
        rewrite nth_error_app2 in INBM_ROW.
        rewrite Nat.sub_diag in INBM_ROW. ss. clarify.
  Qed.



  Lemma fetch_msgs_cur_mid
        cbt ms ms' inbc
        inbm inbn_t
        (MATCH_INBC: match_inb cbt inbc inbm (ms ++ ms'))
    : exists inbm',
      List.fold_left
        (flip (fetch_one_msg cbt)) ms
        (inbm, inbn_t) = (inbm', inbn_t) /\
      match_inb cbt inbc inbm' ms'.
  Proof.
    depgen inbm.
    induction ms as [|m ms1 IH]; i; ss.
    { esplits; eauto. }

    assert (exists inbm1,
               <<FETCH1: fetch_one_msg cbt m (inbm, inbn_t) = (inbm1, inbn_t)>> /\
               <<MATCH1: match_inb cbt inbc inbm1 (ms1 ++ ms')>>).
    { inv MATCH_INBC. ss.
      unfold fetch_one_msg.
      inv PMS_IN_INB. des.
      unfold parse_pld.
      rewrite PLD_SIZE_EQ.
      rewrite Nat.ltb_irrefl.
      rewrite firstn_all2; eauto.
      2: { nia. }
      rewrite PARSE_OK.
      rewrite Nat.eqb_refl.
      esplits; eauto.

      eapply match_inb_upd_msg; eauto.
      econs; eauto.
      econs; eauto.
      esplits; eauto.
    }

    des.
    unfold flip at 2.
    rewrite FETCH1.
    hexploit IH; eauto.
  Qed.


  Lemma match_inb_end_choose_rowmsg
        cbt inbc inbm
        (MATCH: match_inb cbt inbc inbm [])
    : Forall2 AANode.choose_inbox_rowmsg inbc inbm.
  Proof.
    inv MATCH.
    apply Forall2_nth. i.
    rewrite Forall2_nth in INBM_IN_INB.
    specialize (INBM_IN_INB n).
    assert ((exists inbm_r inbc_r,
               <<INBM_R: nth_error inbm n = Some inbm_r>> /\
               <<INBC_R: nth_error inbc n = Some inbc_r>> /\
               <<INBM_INCL: forall m : msgT, inbm_r = Some m -> In m inbc_r>>) \/
            (<<INBM_NONE: nth_error inbm n = None>> /\
             <<INBC_NONE: nth_error inbc n = None>>)).
    { destruct (nth_error inbc n) eqn:INBC_R.
      - left.
        inv INBM_IN_INB.
        esplits; eauto.
      - right.
        inv INBM_IN_INB.
        esplits; eauto.
    }
    des.
    - rewrite INBM_R, INBC_R in INBM_IN_INB.
      fold msgT.
      rewrite INBM_R, INBC_R.
      econs.

      destruct inbc_r.
      + (* nil *)
        destruct inbm_r; ss.
        { exfalso.
          hexploit INBM_INCL; eauto. }
        econs 1.
      + (* cons *)
        destruct inbm_r as [m_ch|].
        * econs 2.
          hexploit INBM_INCL; eauto.
        * exfalso.
          hexploit WHEN_INBM_EMPTY; eauto.
          { left. eauto. }
          i. des.
          inv IN_PMS.
    - fold msgT.
      rewrite INBM_NONE, INBC_NONE. econs.
  Qed.

  Lemma fetch_msgs_cur
        cbt ms inbc
        inbm inbn_t
        (MATCH_INBC: match_inb cbt inbc inbm ms)
    : exists inbc_t',
      List.fold_left
        (flip (fetch_one_msg cbt)) ms
        (inbm, inbn_t) = (inbc_t', inbn_t) /\
      Forall2 AANode.choose_inbox_rowmsg inbc inbc_t'
  .
  Proof.
    replace ms with (ms ++ []) in MATCH_INBC.
    2: { apply app_nil_r. }
    hexploit fetch_msgs_cur_mid; eauto. i. des.
    hexploit match_inb_end_choose_rowmsg; eauto.
  Qed.


  Lemma fetch_msgs_nxt
        cbt inbn
        inbc_t inbm ms1 ms2
        (MATCH_INBN: match_inb
                       (cbt + period) inbn
                       inbm (ms1 ++ ms2))
    : exists inbm',
      List.fold_left
        (flip (fetch_one_msg cbt)) ms1
        (inbc_t, inbm) = (inbc_t, inbm') /\
      match_inb (cbt + period) inbn inbm' ms2.
  Proof.
    depgen inbm.
    induction ms1 as [|m ms1 IH]; i; ss.
    { esplits; eauto. }

    assert (exists inbm1,
               <<FETCH1: fetch_one_msg cbt m (inbc_t, inbm) = (inbc_t, inbm1)>> /\
               <<MATCH1: match_inb (cbt + period) inbn inbm1 (ms1 ++ ms2)>>).
    { inv MATCH_INBN. ss.
      unfold fetch_one_msg.
      inv PMS_IN_INB. des.
      unfold parse_pld.
      rewrite PLD_SIZE_EQ.
      rewrite Nat.ltb_irrefl.
      rewrite firstn_all2; eauto.
      2: { nia. }
      rewrite PARSE_OK.
      rewrite Nat.eqb_refl.

      esplits; eauto.
      { destruct (Nat.eqb_spec (cbt + period) cbt).
        { exfalso. nia. }
        eauto. }

      eapply match_inb_upd_msg; eauto.
      econs; eauto.
      econs; eauto.
      esplits; eauto.
    }

    des.
    unfold flip at 2.
    rewrite FETCH1.
    hexploit IH; eauto.
  Qed.

  Lemma match_fetch_msgs
        cbt ms_old ms_c ms_n ms_nw
        inbc inbn
        inbm inbc_t inbn_t inbp' ocnt
        (OLD_MSGS : Forall (old_msg cbt) ms_old)
        (MATCH_INBC: match_inb cbt inbc inbm ms_c)
        (MATCH_INBN: match_inb (cbt + period)
                               inbn AbstMW.init_inbox
                               (ms_n ++ ms_nw))
        (FETCH: AbstMW.fetch_msgs
                  cbt (ms_old ++ ms_c ++ ms_n) inbm =
                (inbc_t, inbn_t, inbp'))
        (OCNT: ocnt = length ms_old)
    : exists ms_old' ms_n',
      inbp' = ms_old' ++ ms_n' /\
      Forall (old_msg (cbt + period)) ms_old' /\
      match_inb (cbt + period)
                inbn inbn_t (ms_n' ++ ms_nw) /\
      AANode.abst_inbox ocnt inbc
                        inbc_t (length ms_old')
  .
  Proof.
    pose (ms_tot := ms_old ++ ms_c ++ ms_n).
    pose (N := length task_ips * 4).

    unfold fetch_msgs in FETCH.
    fold ms_tot N in FETCH.
    rewrite process_firstn_spec in FETCH.

    destruct (lt_ge_dec N (length ms_old)).
    { assert (exists ms_old1 ms_old2,
                 <<MS_OLD_DIV: ms_old = ms_old1 ++ ms_old2>> /\
                 <<MS_OLD1: firstn N ms_tot = ms_old1>> /\
                 <<MS_REST: skipn N ms_tot = ms_old2 ++ ms_c ++ ms_n>>).
      { exists (firstn N ms_old). exists (skipn N ms_old). split.
        - rewrite firstn_skipn. ss.
        - unfold ms_tot.
          (* dup l. rewrite <- Nat.sub_0_le in l. *)
          (* rewrite firstn_app, skipn_app, l. ss. *)
          (* rewrite app_nil_r. split; ss. *)
          rewrite firstn_app, skipn_app.
          replace (N - length ms_old) with 0 by nia.
          rewrite app_nil_r. split; ss.
      }
      des.
      rewrite MS_OLD1, MS_REST in FETCH.

      rewrite MS_OLD_DIV in OLD_MSGS.
      eapply Forall_app_inv in OLD_MSGS. des.
      rewrite fetch_msgs_old in FETCH by eauto.

      exists (ms_old2 ++ ms_c), ms_n.
      splits.
      - rewrite <- app_assoc. congruence.
      - apply Forall_app.
        + eapply Forall_impl.
          2: { eauto. }
          i. eapply old_msg_adv; eauto. nia.
        + clear MS_OLD1.
          inv MATCH_INBC.
          apply Forall_forall.
          intros pm IN.
          rewrite Forall_forall in PMS_IN_INB.
          hexploit PMS_IN_INB; eauto.
          i. des.
          econs; eauto.
          { rewrite firstn_all2; eauto. nia. }
          nia.
      - congruence.
      - econs 2.
        rewrite OCNT.
        subst ms_tot.
        inv MATCH_INBC. ss.
        unfold msgT in INB_LENGTH.
        rewrite INB_LENGTH.
        unfold num_tasks. fold N. nia.
    }

    destruct (lt_ge_dec N (length (ms_old ++ ms_c)))
     as [LT2 | GE2].
    { assert (exists ms_c1 ms_c2,
                 <<MS_C_DIV: ms_c = ms_c1 ++ ms_c2>> /\
                 <<MS_FSTN: firstn N ms_tot = ms_old ++ ms_c1>> /\
                 <<MS_REST: skipn N ms_tot = ms_c2 ++ ms_n>>).
      { exists (firstn (N - length ms_old) ms_c).
        exists (skipn (N - length ms_old) ms_c). split.
        - rewrite firstn_skipn. ss.
        - unfold ms_tot.
          do 2 rewrite firstn_app, skipn_app.
          rewrite firstn_all2, skipn_all2; try nia. ss.
          rewrite app_length in *.
          replace (N - length ms_old - length ms_c) with 0 by nia.
          splits; ss.
          rewrite app_nil_r. ss.
      }
      des.
      rewrite MS_FSTN, MS_REST in FETCH.
      hexploit fetch_msgs_cur_mid.
      { rewrite MS_C_DIV in MATCH_INBC.
        apply MATCH_INBC. }
      intros (inbm' & PROC_C1 & MATCH_INB_C2).
      rewrite fold_left_app in FETCH.
      rewrite (fetch_msgs_old cbt ms_old) in FETCH by ss.
      rewrite PROC_C1 in FETCH. clarify.

      exists ms_c2, ms_n.
      splits.
      - clarify.
      - inv MATCH_INBC.
        apply Forall_forall.
        intros pm IN.
        rewrite Forall_forall in PMS_IN_INB.
        hexploit PMS_IN_INB; eauto.
        { apply in_or_app. right. eauto. }
        i. des.
        econs; eauto.
        { rewrite firstn_all2; eauto. nia. }
        nia.
      - congruence.
      - econs 2.
        inv MATCH_INBC.
        unfold msgT in INB_LENGTH.
        rewrite INB_LENGTH.
        unfold num_tasks. fold N.
        fold (AANode.inbox_sz inbc).

        assert (length (ms_c1 ++ ms_c2) <= AANode.inbox_sz inbc) by nia.
        eapply lt_le_trans.
        + eauto.
        + rewrite app_length. nia.
    }
    { (* OK *)
      assert (exists ms_n1 ms_n2,
                 <<MS_N_DIV: ms_n = ms_n1 ++ ms_n2>> /\
                 <<MS_FSTN: firstn N ms_tot = ms_old ++ ms_c ++ ms_n1>> /\
                 <<MS_REST: skipn N ms_tot = ms_n2>>).
      { unfold ms_tot. pose (tmp := ms_old ++ ms_c).
        exists (firstn (N - length tmp) ms_n).
        exists (skipn (N - length tmp) ms_n).
        split; try by (rewrite firstn_skipn; ss).
        unfold ms_tot.
        repeat rewrite app_assoc. fold tmp. fold tmp in GE2.
        rewrite firstn_app, skipn_app.
        rewrite firstn_all2, skipn_all2; try nia. ss.
      }
      des. subst ms_n.
      rewrite MS_FSTN, MS_REST in FETCH.

      do 2 rewrite fold_left_app in FETCH.
      rewrite (fetch_msgs_old cbt ms_old) in FETCH by ss.
      eapply fetch_msgs_cur in MATCH_INBC. des.
      rewrite MATCH_INBC in FETCH.
      rewrite <- app_assoc in MATCH_INBN.
      eapply fetch_msgs_nxt in MATCH_INBN. des.
      rewrite MATCH_INBN in FETCH. clarify.

      exists [], ms_n2.
      splits.
      - clarify.
      - econs.
      - congruence.
      - ss. econs 1.
        congruence.
    }
  Qed.


  Lemma infer_mcast_id_active
        nw ip mids
        (MCAST_ID_DOMAIN: mcast_id_domain nw ip mids)
        (MCAST_ID_IN_NW: mcast_id_in_nw nw ip mids)
        (MC_PL_EMPTY : NW.mcast_msg_pool nw = [])
    : mcast_id_active nw ip mids.
  Proof.
    destruct nw as [mcgs msg_pl mc_pl]. ss.
    inv MCAST_ID_DOMAIN.
    renames mips MCAST_IPS into mips1 MCAST_IPS1.
    inv MCAST_ID_IN_NW.
    renames mips MCAST_IPS into mips2 MCAST_IPS2.

    assert (mips2 = mips1).
    { eapply Forall2_det; eauto.
      apply mcast_id_ip_det. }
    subst mips2.

    econs; eauto.
    rewrite Forall_forall in MCMS_IN_NW.
    apply Forall_forall.
    intros x IN.
    hexploit MCMS_IN_NW; eauto. i. des; ss.
  Qed.

  Section MATCH_NODE_PROOF.

    Variable tm: DTime.t.
    Variable nw nw1: NW.t.
    Variable st_src: @AANode.state sysE.
    (* Variable st_tgt st_tgt': @Node.state sysE. *)
    Variable st_tgt st_tgt': @AbstMW.state sysE.
    Variable dpms: list (ip_t * Packet.msg_t).

    Variable tes: tsp * events (nbE +'sysE).
    Variable opkt: Packet.t?.

    Let tid': Tid := AANode.task_id st_src.
    (* Hypothesis RANGE_TID: IntRange.sint8 tid'. *)
    Hypothesis TM_LB: (DTime.of_ns (period - max_clock_skew) <= tm).
    Hypothesis WF_SRC: AANode.state_wf tid' st_src.
    Hypothesis WF_TGT: AbstMW.state_wf tid' st_tgt.

    Hypothesis WF_NW: NW.wf nw.
    Hypothesis NW_INV: nw_inv tm nw.
    Hypothesis MATCH: match_lstate tm nw st_src st_tgt.

    Hypothesis NW_DISTR: NW.distr nw = (nw1, dpms).

    Let ip' : ip_t := AbstMW.ip_addr st_tgt.
    Let dpms_f := Node.distr_msgs_to ip' dpms.

    Let TASK_ID_IP: task_id_ip tid' ip'.
    Proof.
      inv WF_TGT. ss.
    Qed.

    Hypothesis STEP_TGT:
      AbstMW.step tm dpms_f st_tgt tes opkt st_tgt'.

    Let cbt: nat := get_skwd_base_time period tm.

    Let CBT_SYNC: Nat.divide period cbt.
    Proof.
      assert (CBT: get_skwd_base_time period tm = cbt) by ss.
      apply get_skwd_base_time_iff in CBT.
      des. ss.
    Qed.

    Let RANGE_TM_BASETIME:
      DTime.of_ns (cbt - max_clock_skew) <= tm
      < DTime.of_ns (cbt + period - max_clock_skew).
    Proof.
      assert (CBT: get_skwd_base_time period tm = cbt) by ss.
      apply get_skwd_base_time_iff in CBT.
      des. ss.
    Qed.

    Let nsytm: nat := cbt + period.

    Lemma step_src_working
          (TM_POS: 0 < tm)
          (WORKING_TIME: tm < DTime.of_ns (nsytm - max_clock_skew - max_nw_delay))
      : exists st_src1 ms,
        AANode.step tm st_src tes ms st_src1 /\
        option_rel1 Packet.wf opkt /\
        match_pkt nsytm tid' ms opkt /\
        (* match_lstate (DTime.succ tm) nw1 *)
        (*              st_src1 st_tgt' /\ *)
        (forall (outs_src: list (Tid * msgT)?)
           (outs_tgt: list (Packet.t)?)
           nw'
           (LEN_OUTS: length outs_src = num_tasks)
           (MATCH_OUTMSGS: iForall2 (match_pkt nsytm)
                                    0 outs_src outs_tgt)
           (OUTS_SRC_NTH: nth_error outs_src tid' = Some ms)
           (OUTS_TGT_NTH: nth_error outs_tgt tid' = Some opkt)
           (NW: NW.gather nw1 (filtermap id outs_tgt) nw')
          ,
            let st_src' :=
                AANode.accept_msgs tm outs_src st_src1 in
            match_lstate (DTime.succ tm) nw'
                         st_src' st_tgt'
        ).
    Proof.
      subst tid' ip'.

      assert (CBT_SUCC: get_skwd_base_time period (DTime.succ tm) = cbt).
      { apply get_skwd_base_time_iff; eauto. ss.
        splits; ss.
        - clear - RANGE_TM_BASETIME. nia.
        - clear - WORKING_TIME PERIOD_COND.
          pose proof max_nw_delay_pos. nia.
      }

      inv MATCH; ss.
      - (* Off *)
        eexists (AANode.State tid node inbn None), None.

        inv STEP_TGT. ss. existT_elim. subst.
        fold cbt in MATCH_NW.
        inv ISTEP; ss.
        + esplits.
          * econs 1.
          * nia.
          * econs 1.
          * i. econs 1; eauto.
            { eapply mcast_id_domain_nwstep; eauto. }
            (* inv WF_SRC. ss. } *)
            (* eapply match_inb_pre_empty. *)
            eapply match_inb_pre_nwstep; eauto.

        + esplits.
          * econs 1.
          * nia.
          * econs 1.
          * i. econs 2; eauto.
            -- eapply mcast_id_domain_nwstep; eauto.
               (* inv WF_SRC. ss. *)
            -- rewrite CBT_SUCC. ss.
            -- rewrite CBT_SUCC. ss.
               fold cbt in RANGE_TM.
               splits.
               { clear - RANGE_TM. nia. }
               { clear - WORKING_TIME. nia. }
            -- rewrite CBT_SUCC. fold cbt. reflexivity.
            -- inv WF_SRC. eapply app_nil_l.
            -- econs; econs.
            -- rewrite CBT_SUCC.
               (* eapply match_inb_pre_empty. *)
               eapply match_inb_pre_nwstep; eauto.

      - (* Off - Prep *)
        inv STEP_TGT. existT_elim. subst. ss.
        fold cbt in MATCH_NW.

        assert (NOT_EXACT: exact_skwd_base_time period tm = None).
        { eapply exact_skwd_base_time_None_iff.
          - clear - RANGE_TM. nia.
          - exists cbt.
            splits.
            + unfold cbt. apply RANGE_TM.
            + unfold cbt.
              clear - RANGE_TM_BASETIME. nia.
            + ss.
        }

        inv ISTEP; ss.
        + (* Off *)
          esplits.
          * econs 1.
          (* * ss. nia. *)
          * ss.
          * econs 1.
          * i. rewrite <- MCAST_IPS_TO_JOIN in MCAST_ID_DOMAIN.
            econs 1; eauto.
            { eapply mcast_id_domain_nwstep; eauto. }
            eapply match_inb_pre_nwstep; eauto.

        + (* Prep (stay) *)
          esplits.
          * econs 1.
          (* * ss. nia. *)
          * ss.
          * econs 1.
          * i. econs 2.
            -- eauto.
            -- eapply mcast_id_domain_nwstep; eauto.
               congruence.
            -- ss.
            -- rewrite CBT_SUCC. reflexivity.
            -- apply CBT_LB.
            -- reflexivity.
            -- ss. splits.
               { fold cbt in RANGE_TM.
                 clear - RANGE_TM. nia. }
               { fold cbt in BEFORE_LIMIT.
                 clear - BEFORE_LIMIT. nia. }
            -- eauto.
            -- fold cbt. reflexivity.
            -- eauto.
            -- hexploit mcast_id_in_nw_nwstep; eauto.
               { econs 1. }
               ss. rewrite app_nil_r. ss.
            -- rewrite NOT_EXACT.
               eapply match_inb_pre_nwstep_nexact; eauto.

        + (* Prep (join) *)
          assert (MIP1: exists mip1,
                     mcast_member tid mid_j /\
                     mcast_id_ip mid_j mip1).
          { (* inv WF_SRC. *)
            hexploit (get_mcast_of_spec tid mid_j); eauto.
            { rewrite <- MCAST_IPS_TO_JOIN.
              apply in_or_app. right. ss. eauto. }
            i. des.
            exists mip.
            split.
            - r. rewrite <- MCAST_IPS_TO_JOIN.
              apply in_or_app. right. ss. eauto.
            - r. esplits; eauto.
              (* apply map_nth_error_iff. *)
              (* esplits; eauto. *)
          }
          destruct MIP1 as (mip_j & MCM_J & MCAST_ID_IP).

          hexploit mcast_id_ip_comput; eauto.
          destruct 1 as [TID2IP_J MIP_J_MCAST].

          esplits.
          * econs 1.
          (* * ss. nia. *)
          * rewrite TID2IP_J.
            econs. econs.
            { ss. }
            eapply task_id_ip_comput in TASK_ID_IP.
            destruct TASK_ID_IP. ss.
          * rewrite TID2IP_J.
            econs 2; eauto.
          * i. replace (mids1 ++ mid_j :: mids_j') with
                   (snoc mids1 mid_j ++ mids_j').
            2: { unfold snoc. rewrite <- app_assoc. ss. }

            fold cbt.
            replace (mids1 ++ mid_j :: mids_j') with
                (snoc mids1  mid_j ++ mids_j') in MCAST_IPS_TO_JOIN.
            2: { unfold snoc. rewrite <- app_assoc. ss. }

            econs 2; eauto.
            -- rewrite MCAST_IPS_TO_JOIN.
               eapply mcast_id_domain_nwstep; eauto.
            -- rewrite CBT_SUCC. ss.
            -- rewrite CBT_SUCC. ss.
               split.
               { clear - RANGE_TM. nia. }
               { clear - BEFORE_LIMIT. nia. }
            -- rewrite CBT_SUCC. eauto.
            -- hexploit mcast_id_in_nw_nwstep; eauto.
               { econs.
                 rewrite TID2IP_J. eauto. }
               { s. unfold snoc. ss. }
            -- rewrite NOT_EXACT.
               rewrite CBT_SUCC.
               eapply match_inb_pre_nwstep_nexact; eauto.

        + (* ready *)
          esplits.
          { econs 1. }
          (* { ss. nia. } *)
          { ss. }
          { econs 1. }
          i. econs 3; eauto.
          * eapply mcast_id_domain_nwstep; eauto.
            rewrite MCAST_IPS_TO_JOIN. ss.
          * rewrite CBT_SUCC. ss.
            split.
            { clear - RANGE_TM. nia. }
            { clear - BEFORE_LIMIT. nia. }
          * rewrite CBT_SUCC. fold cbt.
            f_equal.
            clear - PERIOD_COND. nia.
          * hexploit mcast_id_in_nw_nwstep; eauto.
            { econs. }
            ss.
          * rewrite NOT_EXACT.
            rewrite CBT_SUCC.
            eapply match_inb_pre_nwstep_nexact; eauto.

      - (* Off-Ready *)
        hexploit (skwd_time_range_almost_overwrap
                    (DTime.succ tm_p) cbt
                    (get_skwd_base_time period tm_p)); eauto.
        { eapply get_skwd_base_time_iff; eauto. }
        intro CBT_PRED. guardH CBT_PRED.

        inv STEP_TGT. existT_elim. subst. ss.
        inv ISTEP; ss.
        + (* Off *)
          esplits.
          { econs 1. }
          (* { ss. nia. } *)
          { ss. }
          { econs 1. }
          i. econs 1; eauto.
          { eapply mcast_id_domain_nwstep; eauto. }
          (* inv WF_SRC. ss. } *)

          desH CBT_PRED.
          * assert (EXACT_NONE: exact_skwd_base_time period (DTime.succ tm_p) = None).
            { eapply exact_skwd_base_time_None_iff.
              { ss. }
              exists cbt.
              splits; ss.
              - rewrite <- CBT_PRED in RANGE_TM.
                apply RANGE_TM.
              - apply RANGE_TM_BASETIME.
            }
            rewrite EXACT_NONE.
            rewrite <- CBT_PRED in MATCH_NW.
            eapply match_inb_pre_empty.
            eapply match_inb_pre_nwstep_nexact; eauto.
          * assert (EXACT_CBT: exact_skwd_base_time period (DTime.succ tm_p) = Some cbt).
            { eapply exact_skwd_base_time_iff.
              splits; ss.
              rewrite CBT_PRED.
              clear - PERIOD_COND. nia. }
            rewrite EXACT_CBT.
            (* rewrite <- CBT_PRED in MATCH_NW. *)
            eapply match_inb_pre_empty.
            eapply match_inb_pre_nwstep_exact; eauto.
            eapply match_inb_pre_adv; eauto.
            clear - CBT_PRED PERIOD_COND. nia.

        + (* Ready *)
          destruct CBT_PRED as [CBT_EQ | [CBT_EQ TM_P_EXACT]].
          * (* stay *)
            assert (EXACT_NONE: exact_skwd_base_time period (DTime.succ tm_p) = None).
            { eapply exact_skwd_base_time_None_iff.
              { ss. }
              exists cbt.
              splits; ss.
              - rewrite <- CBT_EQ in RANGE_TM.
                apply RANGE_TM.
              - apply RANGE_TM_BASETIME.
            }

            esplits.
            { econs 1. }
            (* { ss. nia. } *)
            { ss. }
            { econs 1. }
            i. econs 3; eauto.
            { eapply mcast_id_domain_nwstep; eauto. }
              (* inv WF_SRC; ss. } *)
            { rewrite CBT_SUCC.
              clear - RANGE_TM_BASETIME.
              ss. nia. }
            { rewrite <- CBT_EQ.
              rewrite CBT_SUCC.
              reflexivity. }
            { (*joined_prsv*)
              hexploit mcast_id_in_nw_nwstep; eauto.
              { econs. }
              ss. rewrite app_nil_r. ss. }

            rewrite EXACT_NONE.
            rewrite CBT_SUCC.
            rewrite <- CBT_EQ in MATCH_NW.
            eapply match_inb_pre_nwstep_nexact; eauto.
          * (* Go to Done-Ready *)
            assert (EXACT_CBT: exact_skwd_base_time period (DTime.succ tm_p) = Some cbt).
            { eapply exact_skwd_base_time_iff.
              splits; ss.
              rewrite CBT_EQ.
              clear - PERIOD_COND. nia. }

            hexploit nw_exact_empty; eauto.
            intros (MSG_PL_EMPTY & MC_PL_EMPTY & DISTR_EQ).
            rewrite DISTR_EQ in NW_DISTR.
            symmetry in NW_DISTR. clarify.

            assert (NW_F_EMPTY: nw_msgs_to ip nw = []).
            { unfold nw_msgs_to.
              rewrite MSG_PL_EMPTY. ss. }

            assert (DPMS_F_EMPTY: dpms_f = []).
            { subst dpms_f. ss. }

            esplits; eauto.
            { eapply AANode.Step_TurnOn with
                  (ocnt := length inbp); eauto.
              inv MATCH_NW.
              rewrite NW_F_EMPTY in PMS_TOT_LEN.
              rewrite app_nil_r in PMS_TOT_LEN. ss. }
            (* { ss. nia. } *)
            (* { ss. } *)
            { econs 1. }

            i. rewrite DPMS_F_EMPTY. ss.
            hexploit infer_mcast_id_active; eauto.
            intro MCAST_ID_ACTIVE.

            econs 4; eauto.
            (* { eauto. } *)
            { eapply mcast_id_active_nwstep; eauto.
              econs. }
            { clear - RANGE_TM TM_P_EXACT.
              ss. nia. }
            { rewrite <- CBT_EQ. ss. }
            { inv MATCH_NW.
              rewrite NW_F_EMPTY in PMS_TOT_OLD.
              rewrite app_nil_r in PMS_TOT_OLD.
              eapply Forall_impl.
              2: { eauto. }
              i. eapply old_msg_adv; eauto.
              rewrite CBT_EQ.
              clear.
              hexploit (get_skwd_base_time_mono tm_p (DTime.succ tm_p)).
              { ss. nia. }
              i. nia.
            }

            rewrite EXACT_CBT.
            rewrite app_nil_l.
            hexploit match_inb_nwstep; eauto.
            { rewrite NW_F_EMPTY. rewrite app_nil_r.
              eapply match_inb_empty. }
            ss.

        + (* period_begin *)
          exfalso.
          (* SYNC_TIME *)
          fold cbt in SYNC_TIME.
          desH CBT_PRED.
          * rewrite <- CBT_PRED in SYNC_TIME.
            clear - SYNC_TIME PERIOD_COND. nia.
          * rewrite <- CBT_PRED in SYNC_TIME.
            clear - SYNC_TIME PERIOD_COND. nia.

      - (* Done-Ready *)
        rename cbt0 into cbt_p.
        hexploit (skwd_time_range_almost_overwrap tm cbt cbt_p); eauto.
        intro CBT_PRED. guardH CBT_PRED.

        inv STEP_TGT. existT_elim. subst. ss.
        inv ISTEP; ss.
        + (* Off *)
          esplits.
          { eapply AANode.Step_Fail. }
          (* { ss. nia. } *)
          { ss. }
          { econs 1. }
          i. econs 1; eauto.
          { hexploit mcast_id_active_nwstep; eauto.
            { econs. }
            apply mcast_id_active_impl_domain. }
          eapply match_inb_pre_nwstep; eauto.
          { apply mcast_id_active_impl_domain. ss. }
          eapply match_inb_pre_adv.
          { eapply match_inb_to_pre; eauto. }
          desH CBT_PRED; subst; ss.
          rewrite CBT_PRED. nia.

        + (* Ready *)
          destruct CBT_PRED as [CBT_EQ | [CBT_EQ TM_EQ]].
          * subst cbt_p.
            assert (EXACT_NONE: exact_skwd_base_time period tm = None).
            { apply exact_skwd_base_time_None_iff.
              { clear - RANGE_TM. nia. }
              exists cbt.
              splits; ss; nia.
            }
            esplits.
            { eapply AANode.Step_On_Stay; eauto. }
            (* { ss. nia. } *)
            { ss. }
            { econs 1. }
            i. rewrite <- app_assoc. ss.
            econs 4; eauto.
            { eapply mcast_id_active_nwstep; eauto.
              econs. }
            { clear - RANGE_TM_BASETIME. ss. nia. }

            rewrite EXACT_NONE.
            eapply match_inb_nwstep; eauto.

          * (* Go to Ready-Ready *)
            assert (EXACT_TM: exact_skwd_base_time period tm = Some cbt).
            { apply exact_skwd_base_time_iff.
              splits; ss.
              clear - CBT_EQ PERIOD_COND. nia. }

            hexploit nw_exact_empty; eauto.
            intros (MSG_PL_EMPTY & MC_PL_EMPTY & DISTR_EQ).
            rewrite DISTR_EQ in NW_DISTR.
            symmetry in NW_DISTR. clarify.

            assert (NW_F_EMPTY: nw_msgs_to ip nw = []).
            { unfold nw_msgs_to.
              rewrite MSG_PL_EMPTY. ss. }
            assert (DPMS_F_EMPTY: dpms_f = []).
            { subst dpms_f. ss. }

            rewrite DPMS_F_EMPTY. ss.
            esplits.
            { eapply AANode.Step_Sync; eauto. }
            (* { ss. nia. } *)
            { ss. }
            { econs 1. }
            i. econs 5; eauto.
            { eapply mcast_id_active_nwstep; eauto.
              econs. }
            { clear - RANGE_TM_BASETIME TIME_UB CBT_EQ.
              ss. split; nia. }
            { rewrite <- CBT_EQ.
              rewrite app_assoc. ss. }
            (* { hexploit mcast_id_in_nw_nwstep; eauto. *)
            (*   { econs. } *)
            (*   ss. rewrite app_nil_r. ss. } *)
            { rewrite CBT_EQ. ss. }
            { rewrite CBT_EQ.
              rewrite NW_F_EMPTY in MATCH_INB.
              rewrite app_nil_r in MATCH_INB. ss.
            }
            (* new match_inb *)
            rewrite EXACT_TM.
            replace (nw_msgs_to ip nw') with
                (filter_port dpms_f ++ nw_msgs_to ip nw').
            2: { rewrite DPMS_F_EMPTY. ss. }
            rewrite app_assoc.
            eapply match_inb_nwstep; eauto.
            rewrite NW_F_EMPTY. ss.
            apply match_inb_empty.

        + (* run *)
          exfalso.
          (* fold cbt in SYNC_TIME. *)
          clear - CBT_PRED RANGE_TM RANGE_TIME.
          desH CBT_PRED.
          * subst cbt. nia.
          * subst cbt. nia.

      - (* Ready-Ready *)
        assert (sytm = cbt).
        { hexploit (skwd_time_range_almost_overwrap tm cbt sytm); eauto.
          { clear - RANGE_TM. nia. }
          intros [? | [CBT_EQ TM_EQ]].
          { ss. }
          exfalso.
          rewrite CBT_EQ in TM_EQ.
          clear - RANGE_TM TM_EQ.
          pose proof max_nw_delay_pos. nia.
        }
        subst sytm.
        fold nsytm in RANGE_TM.

        assert (EXACT_NONE: exact_skwd_base_time period tm = None).
        { eapply exact_skwd_base_time_None_iff.
          { clear - RANGE_TM. nia. }
          exists cbt.
          splits; ss; nia. }

        inv STEP_TGT. existT_elim. subst. ss.
        inv ISTEP; ss.
        + (* Off *)
          esplits.
          { eapply AANode.Step_Fail. }
          (* { ss. nia. } *)
          { ss. }
          { econs 1. }
          i. econs 1; eauto.
          { hexploit mcast_id_active_nwstep; eauto.
            { econs. }
            apply mcast_id_active_impl_domain. }
          eapply match_inb_pre_nwstep; eauto.
          { apply mcast_id_active_impl_domain. ss. }
          eapply match_inb_to_pre; eauto.

        + (* Stay *)
          esplits.
          { eapply AANode.Step_On_Stay; eauto. }
          (* { ss. nia. } *)
          { ss. }
          { econs 1. }
          i. econs 5; eauto.
          { eapply mcast_id_active_nwstep; eauto.
            econs. }
          { clear - RANGE_TM TIME_UB. ss. nia. }
          (* { hexploit mcast_id_in_nw_nwstep; eauto. *)
          (*   { econs. } *)
          (*   ss. rewrite app_nil_r. ss. } *)
          { repeat rewrite <- app_assoc. reflexivity. }

          (* rewrite <- app_assoc. *)
          eapply match_inb_nwstep; eauto.
          rewrite EXACT_NONE. ss.

        + (* Go to Running *)
          renames inbc0 inbn0 into inbc_t inbn_t.
          assert (NOT_EXACT: exact_skwd_base_time period tm = None).
          { eapply exact_skwd_base_time_None_iff; eauto.
            exists cbt. splits; ss; nia. }

          repeat rewrite <- app_assoc in FETCH_MSGS.
          hexploit match_inb_distr; eauto.
          intros [MATCH_INB_D MCAST_ID_DOMAIN_D].

          hexploit match_fetch_msgs; eauto.
          intros (ms_old' & ms_n' & INBP' & MS_OLD' &
                  MATCH_INB' & ABST_INBOX).

          esplits; eauto.
          { eapply AANode.Step_StartRun; eauto. }
          (* { ss. nia. } *)
          { econs. }

          i. econs 6; eauto.
          { eapply mcast_id_active_nwstep; eauto.
            econs. }
          { clear - RANGE_TIME. ss. nia. }
          (* { hexploit mcast_id_in_nw_nwstep; eauto. *)
          (*   { econs. } *)
          (*   ss. rewrite app_nil_r. ss. } *)

          rewrite NOT_EXACT.
          eapply match_inb_gather;
            try apply NW; eauto.
          { hexploit NW.wf_distr_preserve; eauto.
            i. des. ss. }
          { eapply mcast_id_active_distr; eauto. }

      - (* Runnings *)
        assert (sytm = cbt).
        { hexploit (skwd_time_range_almost_overwrap tm cbt sytm); eauto.
          { clear - RANGE_TM. nia. }
          intros [? | [CBT_EQ TM_EQ]].
          { ss. }
          exfalso.
          rewrite CBT_EQ in TM_EQ.
          clear - RANGE_TM TM_EQ.
          pose proof max_nw_delay_pos. nia.
        }
        subst sytm.
        fold nsytm in RANGE_TM.

        assert (NOT_EXACT: exact_skwd_base_time period tm = None).
        { eapply exact_skwd_base_time_None_iff; eauto.
          exists cbt. splits; ss; nia. }

        inv STEP_TGT. existT_elim. subst. ss.
        inv ISTEP; ss.
        + (* Off *)
          esplits.
          { eapply AANode.Step_Fail. }
          (* { ss. nia. } *)
          { ss. }
          { econs 1. }
          i. econs 1; eauto.
          { hexploit mcast_id_active_nwstep; eauto.
            { econs. }
            apply mcast_id_active_impl_domain. }
          rewrite NOT_EXACT.
          eapply match_inb_impl_pre.
          eapply match_inb_nwstep; eauto.

        + (* stay *)
          esplits.
          { eapply AANode.Step_On_Stay; eauto. }
          (* { ss. nia. } *)
          { ss. }
          { econs 1. }
          i. ss.
          rewrite <- app_assoc.
          econs 6; eauto.
          { eapply mcast_id_active_nwstep; eauto.
            econs. }
          { clear - RANGE_TM TIME_UB. ss. nia. }

          rewrite NOT_EXACT.
          eapply match_inb_nwstep; eauto.

        + (* Go *)
          assert (RANGE_NSYTM: IntRange.uint64 nsytm).
          { apply lt_maxtime_nxt_in_range. ss. }

          destruct opkt as [pkt|].
          * destruct om as [[tid_d msg]|]; ss.

            destruct (check_send_hist sh tid_d) as [sh''|] eqn:SH'; ss.
            clarify.

            esplits; ss.
            { eapply AANode.Step_Running_Go; eauto.
              ss. rewrite SH'. eauto. }
            (* { ss. } *)
            { eapply wf_srl_pm. }
            { econs; eauto.
              - eapply resize_bytes_length; eauto.
              - r. instantiate (1:= tid2ip tid_d).
                unfold dest_ips.

                eapply check_send_hist_Some in SH'.
                des.
                + rewrite nth_error_app1.
                  2: { apply DEST_TASK_ID. }
                  apply valid_task_id_ip. eauto.
                + hexploit valid_mcast_id_ip; eauto.
                  intro MCAST_ID_IP. r in MCAST_ID_IP. des.
                  rewrite nth_error_app2.
                  2: { fold num_tasks.
                       clear - MCAST_ID_IP. nia. }
                  replace (tid_d - length task_ips) with midx.
                  2: { fold num_tasks.
                       clear - MCAST_ID_IP. nia. }
                  eauto.
                + inv WF_SRC.
                  existT_elim. clarify. ss.
                  inv ISTATE_WF.
                  eauto.
              - f_equal.
                hexploit task_id_ip_comput; eauto.
                i. des. ss.
            }
            i. rewrite <- app_assoc.
            econs 6; eauto.
            { eapply mcast_id_active_nwstep; eauto.
              desf. econs. }
            { clear - RANGE_TM TIME_UB. ss. nia. }
            rewrite NOT_EXACT.
            eapply match_inb_nwstep; eauto.

          * assert (OUT_SRC_NONE: AANode.process_outmsg sh om = (sh, None)).
            { destruct om as [[tid_d m]|]; ss.
              desf. }

            rewrite <- app_assoc.
            esplits; eauto.
            { eapply AANode.Step_Running_Go; eauto. }
            (* { ss. nia. } *)
            { econs. }
            { subst nsytm. econs. }
            i. econs 6; eauto.
            { eapply mcast_id_active_nwstep; eauto. econs. }
            { clear - RANGE_TM TIME_UB. ss. nia. }
            { unfold check_and_send in *. desf. }
            rewrite NOT_EXACT.
            eapply match_inb_nwstep; eauto.

        + (* Done *)
          rewrite <- app_assoc.
          esplits.
          { eapply AANode.Step_Running_Done; eauto. }
          (* { ss. nia. } *)
          { ss. }
          { econs 1. }
          i. econs 4; eauto.
          { eapply mcast_id_active_nwstep; eauto.
            econs. }
          { clear - RANGE_TM TIME_UB. ss. nia. }
          (* { hexploit mcast_id_in_nw_nwstep; eauto. *)
          (*   { econs. } *)
          (*   ss. rewrite app_nil_r. ss. } *)
          rewrite NOT_EXACT.
          eapply match_inb_nwstep; eauto.
    Qed.

    Lemma step_src_in_btw
          (TIME_IN_BTW: DTime.of_ns (nsytm - max_clock_skew - max_nw_delay) <= tm)
      : opkt = None /\
        exists st_src',
        AANode.step tm st_src tes None st_src' /\
        match_lstate (DTime.succ tm) nw1
                     st_src' st_tgt'.
    Proof.
      subst tid'. subst ip'.

      inv MATCH; ss.
      - (* Off-Off *)
        inv STEP_TGT. existT_elim.
        subst. ss.

        assert (MATCH_INB': match_inb_pre cbt ip nw1 [] inbn).
        { eapply match_inb_pre_distr in MATCH_NW; eauto.
          eapply match_inb_pre_empty; eauto. }

        inv ISTEP; ss.
        + esplits; eauto.
          * econs 1; eauto.
          * econs 1; ss.
            { eapply mcast_id_domain_distr; eauto. }
            eapply match_inb_pre_adv; eauto.
            subst nsytm.
            cut (cbt <= get_skwd_base_time period (DTime.succ tm)).
            { nia. }
            subst cbt.
            apply get_skwd_base_time_mono. ss. nia.

        + fold cbt in RANGE_TM.
          assert (SKWD_BASE_TIME_EQ:
                    get_skwd_base_time
                      period (DTime.succ tm) = cbt).
          { apply get_skwd_base_time_iff; eauto. ss.
            splits; ss.
            - clear - RANGE_TM. nia.
            - clear - RANGE_TM PERIOD_COND.
              pose proof max_nw_delay_pos.
              nia.
          }

          esplits; eauto.
          * econs 1; eauto.
          * econs 2; eauto.
            -- eapply mcast_id_domain_distr; eauto.
            -- rewrite SKWD_BASE_TIME_EQ. ss.
            -- rewrite SKWD_BASE_TIME_EQ. ss. nia.
            -- rewrite SKWD_BASE_TIME_EQ.
               fold cbt. reflexivity.
            -- inv WF_SRC. apply app_nil_l.
            -- econs 1; econs.
            -- eapply match_inb_pre_adv; eauto.
               subst nsytm.
               cut (cbt <= get_skwd_base_time
                            period (DTime.succ tm)).
               { nia. }
               subst cbt.
               apply get_skwd_base_time_mono. ss. nia.

      - (* Off-Prep *)
        fold cbt nsytm in RANGE_TM, STEP_TGT, CBT_LB.

        assert (MATCH_INB': match_inb_pre cbt ip nw1 [] inbn).
        { eapply match_inb_pre_distr in MATCH_NW; eauto.
          eapply match_inb_pre_empty; eauto. }

        assert (TM_EQ: DTime.units tm =
                       (nsytm - max_clock_skew - max_nw_delay) *
                       DTime.units_per_ns) by nia.

        inv STEP_TGT. existT_elim. subst.
        inv ISTEP; ss; [|nia..].

        esplits; eauto.
        + econs 1.
        + econs 1; eauto.
          { eapply mcast_id_domain_distr; eauto.
            rewrite MCAST_IPS_TO_JOIN. ss. }
          eapply match_inb_pre_adv; eauto.
          subst nsytm.
          cut (cbt <= get_skwd_base_time period (DTime.succ tm)).
          { nia. }
          subst cbt.
          apply get_skwd_base_time_mono. ss. nia.

      - (* Off - Run *)
        fold cbt nsytm in RANGE_TM, STEP_TGT.

        assert (MATCH_INB': match_inb_pre cbt ip nw1 [] inbn).
        { eapply match_inb_pre_distr in MATCH_NW; eauto.
          eapply match_inb_pre_empty; eauto.
          eapply match_inb_pre_adv; eauto.
          subst nsytm.
          cut (get_skwd_base_time period tm_p <= cbt).
          { nia. }
          apply get_skwd_base_time_mono. ss. nia.
        }

        inv STEP_TGT. existT_elim. subst.
        (* fold cbt in ISTEP. *)

        assert (SKWD_BASE_TIME_P:
                  get_skwd_base_time period tm_p = cbt).
        { apply get_skwd_base_time_iff; eauto.
          splits; ss.
          - clear - PERIOD_COND TIME_IN_BTW.
            unfold DTime.of_ns. ss. nia.
          - unfold DTime.of_ns. ss. nia.
        }
        rewrite SKWD_BASE_TIME_P in *.

        inv ISTEP; ss.
        + (* off *)
          esplits; eauto.
          * econs 1.
          * econs 1; eauto.
            { eapply mcast_id_domain_distr; eauto. }
            eapply match_inb_pre_adv; eauto.
            subst nsytm. subst cbt.
            apply get_skwd_base_time_mono. ss. nia.

        + (* ready *)
          (* rewrite SKWD_BASE_TIME_P. *)
          esplits; eauto.
          * econs 1.
          * econs 3; try reflexivity; eauto.
            -- eapply mcast_id_domain_distr; eauto.
            -- fold cbt. ss. nia.
            -- eapply mcast_id_in_nw_distr; eauto.
            -- eapply match_inb_pre_distr; eauto.
        + (* running *)
          exfalso.
          fold cbt in SYNC_TIME.
          (* rewrite SKWD_BASE_TIME_P in SYNC_TIME. *)
          clear - SYNC_TIME PERIOD_COND. nia.

      - (* Done-Ready *)
        hexploit (skwd_time_range_almost_overwrap
                    tm cbt cbt0); eauto.
        destruct 1 as [CBT_EQ | [CBT_EQ TM_EQ]].
        2: {
          exfalso.
          clear - TIME_IN_BTW TM_EQ PERIOD_COND.
          pose proof DTime.units_per_ns_pos.
          subst nsytm. nia.
        }
        subst cbt0.

        inv STEP_TGT. existT_elim. subst. ss.
        inv ISTEP; ss.
        + (* fail *)
          esplits; ss.
          * eapply AANode.Step_Fail.
          * econs 1; eauto.
            { eapply mcast_id_domain_distr; eauto.
              apply mcast_id_active_impl_domain. ss. }
            eapply match_inb_pre_empty; eauto.
            eapply match_inb_pre_distr; eauto.
            eapply match_inb_impl_pre in MATCH_INB; eauto.
            eapply match_inb_pre_adv in MATCH_INB; eauto.
            apply get_skwd_base_time_mono. ss. nia.

        + (* stay *)
          esplits; ss.
          * eapply AANode.Step_On_Stay; eauto.
            destruct (exact_skwd_base_time period tm) eqn: EXACT_TM; ss.
            apply exact_skwd_base_time_iff in EXACT_TM; eauto.
            destruct EXACT_TM as (N_POS & TM_EQ & N_DIV).
            assert (get_skwd_base_time period tm = n).
            { apply get_skwd_base_time_iff. ss.
              split; ss.
              split.
              - rewrite TM_EQ. ss.
              - rewrite TM_EQ.
                clear - PERIOD_COND.
                pose proof DTime.units_per_ns_pos. nia.
            }
            exfalso.
            clarify.
            fold cbt in TM_EQ. des.
            nia.
          * rewrite <- app_assoc.
            eapply Match_Done_Ready with (inbm := inbm); eauto.
            -- eapply mcast_id_active_distr; eauto.
            -- ss.
               split.
               { clear - RANGE_TM. nia. }
               { clear - RANGE_TM_BASETIME. nia. }
            -- rewrite <- app_assoc.
               (* eapply nw_msgs_to_adv; eauto. *)
               hexploit match_inb_distr; eauto.
               i. des.
               unfold dpms_f.
               rewrite app_assoc. ss.

        + (* running *)
          exfalso.
          fold cbt in SYNC_TIME.
          clear - SYNC_TIME PERIOD_COND. nia.

      - (* Ready-Ready *)
        assert (sytm = cbt).
        { hexploit (skwd_time_range_almost_overwrap
                      tm cbt sytm); eauto.
          { clear - RANGE_TM. nia. }
          intros [? | [CBT_EQ TM_EQ]].
          { ss. }
          exfalso.
          rewrite CBT_EQ in TM_EQ.
          clear - RANGE_TM TM_EQ.
          pose proof max_nw_delay_pos. nia.
        }
        subst sytm.
        fold nsytm in RANGE_TM.

        assert (TM_EQ: (tm: nat) = (nsytm - max_clock_skew - max_nw_delay) * DTime.units_per_ns) by nia.
        ss.

        inv STEP_TGT. existT_elim. subst. ss.
        inv ISTEP; ss.
        + (* fail *)
          esplits; ss.
          * eapply AANode.Step_Fail.
          * econs 1; eauto.
            { eapply mcast_id_domain_distr; eauto.
              apply mcast_id_active_impl_domain. ss. }
            eapply match_inb_impl_pre in MATCH_INBN; eauto.
            eapply match_inb_pre_distr in MATCH_INBN; eauto.
            eapply match_inb_pre_empty in MATCH_INBN; eauto.
            eapply match_inb_pre_adv; eauto.
            apply get_skwd_base_time_mono. ss. nia.

        + (* tgt ready *)
          exfalso.
          clear - TM_EQ TIME_UB. nia.
        + (* tgt running *)
          exfalso.
          clear - TM_EQ RANGE_TIME. nia.

      - (* Runnings *)
        assert (sytm = cbt).
        { hexploit (skwd_time_range_almost_overwrap
                      tm cbt sytm); eauto.
          { clear - RANGE_TM. nia. }
          intros [? | [CBT_EQ TM_EQ]].
          { ss. }
          exfalso.
          rewrite CBT_EQ in TM_EQ.
          clear - RANGE_TM TM_EQ.
          pose proof max_nw_delay_pos. nia.
        }
        subst sytm.
        fold nsytm in RANGE_TM.

        assert (TM_EQ: (tm: nat) = (nsytm - max_clock_skew - max_nw_delay) * DTime.units_per_ns) by nia.
        ss.

        inv STEP_TGT. existT_elim. subst. ss.
        inv ISTEP; ss.
        + (* fail *)
          esplits; ss.
          * eapply AANode.Step_Fail.
          * econs 1; eauto.
            { eapply mcast_id_domain_distr; eauto.
              apply mcast_id_active_impl_domain. ss. }
            eapply match_inb_impl_pre in MATCH_INBN; eauto.
            eapply match_inb_pre_distr in MATCH_INBN; eauto.
            eapply match_inb_pre_empty in MATCH_INBN; eauto.
            eapply match_inb_pre_adv; eauto.
            apply get_skwd_base_time_mono. ss. nia.
        + (* tgt running1 *)
          exfalso.
          clear - TM_EQ TIME_UB. nia.
        + (* tgt running2 *)
          exfalso.
          clear - TM_EQ TIME_UB. nia.
        + (* period end *)
          exfalso.
          clear - TM_EQ TIME_UB. nia.
    Qed.

  End MATCH_NODE_PROOF.


  Inductive amw_lst (tid: Tid)
    : @SNode.t sysE msgT -> @Node.state sysE ->
      @AbstMW.state sysE -> Prop :=
  | AMwLocalState
      node ast
    : amw_lst tid node
              (Node.State (AbstMW.as_node tid node) ast) ast.


  Lemma partition_map_after
        A (l: list (A * nat)) l1 l2
        tm sytm
        (MAP: partition_map age_delay l = (l1, l2))
        (TM: Forall (fun p => tm + snd p < sytm) l):
    Forall (fun p => S (tm + snd p) < sytm) l1.
  Proof.
    revert l1 l2 MAP.
    induction l; i; ss.
    { inv MAP. ss. }
    inv TM.
    destruct (partition_map age_delay l) as [] eqn:MAP'.
    destruct (age_delay a) eqn:DELAY.
    - inv MAP. econs; eauto.
      destruct a, p. ss. destruct n; ss. inv DELAY.
      rewrite Nat.add_succ_r in *. ss.
    - inv MAP. eauto.
  Qed.

  Lemma nw_inv_distr
        tm nw nw' dpms
        (NW_INV: nw_inv tm nw)
        (NW_DISTR: NW.distr nw = (nw', dpms))
    : nw_inv (DTime.succ tm) nw'.
  Proof.
    ii. exploit NW_INV; eauto; ss; try nia. i. des.
    destruct nw. ss.
    destruct (partition_map age_delay packet_msg_pool) as [] eqn:MAP1.
    destruct (partition_map age_delay mcast_msg_pool) as [] eqn:MAP2.
    inv NW_DISTR. ss.
    split; eauto using partition_map_after.
  Qed.

  Lemma nw_inv_gather
        tm nw1 ps nw'
        (NW_INV: nw_inv (DTime.succ tm) nw1)
        (TM_IN_BTW: tm < DTime.of_ns (get_skwd_base_time period tm + period - max_clock_skew - max_nw_delay))
        (NW_GATHER: NW.gather nw1 ps nw')
    : nw_inv (DTime.succ tm) nw'.
  Proof.
    r in NW_INV. r. i.
    hexploit NW_INV; eauto.
    intros [MSG_POOL MCAST_POOL].

    inv NW_GATHER. ss.

    pose (cbt := get_skwd_base_time period tm).
    fold cbt in TM_IN_BTW.

    assert (SYTM_SK: exists k, cbt + period * S k =
                          sytm_sk + max_clock_skew).
    { clear - TM_IN_BTW SKWD_SYNC_TIME RANGE_TM.
      r in SKWD_SYNC_TIME.
      des. rewrite SKWD_SYNC_TIME.

      generalize (get_skwd_base_time_iff tm cbt).
      intros [AUX _].
      hexploit AUX; ss.
      intros [TM_RANGE CBT_DIV]. clear AUX.

      r in CBT_DIV.
      destruct CBT_DIV as (w & CBT_EQ).
      assert (cbt < z * period) by nia.
      assert (w < z) by nia.

      exists (pred (z - w)).
      rewrite <- S_pred_pos by nia.
      rewrite CBT_EQ.
      replace (period * (z - w)) with ((z - w) * period).
      2: { apply mult_comm. }
      rewrite <- Nat.mul_add_distr_r.
      rewrite le_plus_minus_r by nia. ss.
    }
    des.

    assert (VALID_DELAY_AUX:
              forall dly, valid_delay dly ->
                     S (tm + dly) < sytm_sk * DTime.units_per_ns).
    { clear - TM_IN_BTW SYTM_SK RANGE_TM.
      intros dly VALID_DELAY.

      r in VALID_DELAY.
      apply le_trans with
          (m:= (cbt + period - max_clock_skew - max_nw_delay + max_nw_delay) * DTime.units_per_ns).
      { nia. }

      assert (SYTM_SK_EQ: sytm_sk = cbt + period * S k - max_clock_skew).
      { nia. }
      subst sytm_sk.
      rewrite Nat.sub_add by nia.
      apply Nat.mul_le_mono_r. nia.
    }

    split.
    - eapply Forall_app; eauto.
      eapply Forall_forall.
      intros [[ip_d pm] dly] IN_PMP_NEW. ss.
      eapply In_nth_error in IN_PMP_NEW. des.
      hexploit Forall2_nth2; try apply VALID_DELAYS_PMS; eauto.
      i. des.
      inv P_FA.
      eapply VALID_DELAY_AUX; eauto.
    - eapply Forall_app; eauto.
      eapply Forall_forall.
      intros [[mip nip] dly] IN_MCMP_NEW. ss.
      eapply In_nth_error in IN_MCMP_NEW. des.
      hexploit Forall2_nth2; try apply VALID_DELAYS_MCMS; eauto.
      i. des.
      inv P_FA.
      eapply VALID_DELAY_AUX; eauto.
  Qed.


  Lemma match_step_sim
        tm nw lsts_tgt lsts_src
        amw_lsts_tgt
        tm' nw' lsts_tgt' es
        (WF_NW: NW.wf nw)
        (NW_INV: nw_inv tm nw)
        (TM_LB: DTime.of_ns (period - max_clock_skew) <= tm)
        (* (RANGE_NUM_LSTS: IntRange.sint8 (length lsts_tgt)) *)
        (MATCH_LSTS: Forall2 (match_lstate tm nw)
                             lsts_src amw_lsts_tgt)
        (AMW_LSTS_TGT: iForall3 amw_lst 0
                                nodes lsts_tgt amw_lsts_tgt)
        (STEP_TGT: NWSys.step
                     (NWSys.State tm nw lsts_tgt) es
                     (NWSys.State tm' nw' lsts_tgt'))
        (WF_SRC: iForall AANode.state_wf 0 lsts_src)
        (WF_TGT: iForall AbstMW.state_wf 0 amw_lsts_tgt)
    : exists lsts_src' amw_lsts_tgt',
      AASys.step (AASys.State tm lsts_src) es
                 (AASys.State tm' lsts_src') /\
      NW.wf nw' /\
      nw_inv tm' nw' /\
      Forall2 (match_lstate tm' nw') lsts_src' amw_lsts_tgt' /\
      iForall3 amw_lst 0 nodes lsts_tgt' amw_lsts_tgt' /\
      iForall AANode.state_wf 0 lsts_src' /\
      iForall AbstMW.state_wf 0 amw_lsts_tgt'.
  Proof.
    inv STEP_TGT.

    pose (cbt := get_skwd_base_time period tm).
    pose (nsytm := cbt + period).

    destruct (le_lt_dec (DTime.of_ns (nsytm - max_clock_skew - max_nw_delay)) tm) as [IN_BTW | WORKING].
    - (* in_btw *)

      assert (ST_SRC_EX:
                forall n (N_UB: n < length lsts_tgt),
                exists x,
                  (fun n (x: AANode.state * state) =>
                     let (st_src', alst_tgt') := x in
                     nth_error opkts n = Some None /\
                     option_rel4
                       (AANode.step tm)
                       (nth_error lsts_src n)
                       (nth_error es n)
                       (Some None)
                       (Some st_src') /\
                     option_rel2
                       (match_lstate (DTime.succ tm) nw1)
                       (Some st_src')
                       (Some alst_tgt') /\
                     option_rel3
                       (amw_lst n)
                       (nth_error nodes n)
                       (nth_error lsts_tgt' n)
                       (Some alst_tgt') /\
                     AANode.state_wf n st_src' /\
                     state_wf n alst_tgt')
                    n x).
      { i.
        assert (LST_TGT_N: exists lst_tgt_n,
                   nth_error lsts_tgt n = Some lst_tgt_n).
        { apply Some_not_None. apply nth_error_Some. ss. }
        des.

        assert (exists es_n opkt_n lst_tgt_n',
                   <<ES_N: nth_error es n = Some es_n>> /\
                   <<OPKT_N: nth_error opkts n = Some opkt_n>> /\
                   <<LST_TGT_N': nth_error lsts_tgt' n = Some lst_tgt_n'>> /\
                   <<NODE_STEP:
                   Node.step tm dpms
                             lst_tgt_n es_n opkt_n lst_tgt_n'>>).
        { rewrite Forall4_nth in LOCAL_STEPS.
          specialize (LOCAL_STEPS n).
          rewrite LST_TGT_N in LOCAL_STEPS.
          inv LOCAL_STEPS.
          esplits; eauto. }

        rewrite iForall3_nth in AMW_LSTS_TGT.
        specialize (AMW_LSTS_TGT n).
        rewrite LST_TGT_N in AMW_LSTS_TGT.
        assert (exists nd_n alst_tgt_n,
                   <<NODE_N: nth_error nodes n = Some nd_n>> /\
                   <<ALST_TGT_N: nth_error amw_lsts_tgt n = Some alst_tgt_n>> /\
                   <<AMW_LST: amw_lst n nd_n lst_tgt_n alst_tgt_n>>).
        { inv AMW_LSTS_TGT. ss.
          esplits; eauto. }
        des.
        inv AMW_LST.

        rewrite Forall2_nth in MATCH_LSTS.
        specialize (MATCH_LSTS n).
        rewrite ALST_TGT_N in MATCH_LSTS.
        assert (LST_SRC_N: exists lst_src_n,
                   nth_error lsts_src n = Some lst_src_n /\
                   match_lstate tm nw lst_src_n alst_tgt_n).
        { inv MATCH_LSTS. esplits; eauto. }
        des. rename LST_SRC_N0 into MATCH_LST.

        rewrite Forall4_nth in LOCAL_STEPS.
        specialize (LOCAL_STEPS n).
        rewrite LST_TGT_N in LOCAL_STEPS.

        rewrite iForall_nth in WF_SRC.
        generalize (WF_SRC n). ss.
        rewrite LST_SRC_N.
        intro WF_SRC_N. r in WF_SRC_N.

        rewrite iForall_nth in WF_TGT.
        generalize (WF_TGT n). ss.
        rewrite ALST_TGT_N.
        intro WF_TGT_N. r in WF_TGT_N.

        pose (dpms_f := Node.distr_msgs_to (tid2ip n) dpms).
        inv NODE_STEP. existT_elim. clarify. ss.

        assert (N_TID: n = AANode.task_id lst_src_n).
        { inv WF_SRC_N. ss. }
        guardH N_TID.

        hexploit step_src_in_btw; try apply MATCH_LST; eauto.
        { inv WF_SRC_N. ss. }
        { rewrite <- N_TID. ss. }
        { inv WF_TGT_N. ss.
          hexploit task_id_ip_comput; eauto.
          intros [IP_EQ _].
          rewrite IP_EQ in ISTEP.
          eauto.
        }

        intros (OPKT_NONE & st_src' & STEP_SRC & MATCH').
        exists (st_src', ist').
        rewrite OPKT_N, ES_N, NODE_N, LST_TGT_N'.

        splits.
        - clarify.
        - econs. ss.
        - econs. ss.
        - econs. ss.
        - eapply AANode.wf_prsv; eauto.
        - eapply AbstMW.wf_prsv; eauto.
      }

      apply exists_list in ST_SRC_EX.
      destruct ST_SRC_EX as
          (xs & LEN_LSTS_SRC' & LSTS_SRC_PROPS).
      des.

      pose (lsts_src' := map fst xs).
      pose (alsts_tgt' := map snd xs).

      assert (OPKTS_ALL_NONE:
                forall op (IN: In op opkts), op = None).
      { i. apply In_nth_error in IN. des.

        hexploit Forall2_length; eauto. i.
        hexploit Forall4_length; eauto. i. des.

        assert (exists x, nth_error xs n = Some x).
        { apply Some_not_None.
          apply nth_error_Some.
          replace (length xs) with (length opkts) by nia.
          apply nth_error_Some. congruence.
        }

        des.
        exploit LSTS_SRC_PROPS; eauto.
        destruct x. ss.
        i. des. clarify.
      }

      assert (nw' = nw1).
      { assert (OPKTS_F_NIL: filtermap id opkts = []).
        { clear - OPKTS_ALL_NONE.
          induction opkts as [| h t IH]; ss.
          destruct h; ss.
          - exfalso.
            hexploit OPKTS_ALL_NONE; eauto. ss.
          - eapply IH. eauto.
        }
        rewrite OPKTS_F_NIL in NW_STEP.
        inv NW_STEP. ss. clarify. ss.
        inv VALID_DELAYS_PMS.
        inv VALID_DELAYS_MCMS.
        do 2 rewrite app_nil_r. ss.
      }
      subst nw'.

      assert (<<STEPS_SRC:
                Forall4 (AANode.step tm)
                        lsts_src es (List.repeat None (length lsts_src)) lsts_src'>> /\
                <<MATCH': Forall2 (match_lstate (DTime.succ tm) nw1)
                                  lsts_src' alsts_tgt'>> /\
                <<AMW_LST': iForall3 amw_lst 0 nodes
                                     lsts_tgt' alsts_tgt'>> /\
                <<WF_SRC': iForall AANode.state_wf 0 lsts_src'>> /\
                <<WF_TGT': iForall AbstMW.state_wf 0 alsts_tgt'>>
             ).
      { cut (forall n,
                (<<LSTS_SRC: nth_error lsts_src n = None>> /\
                 <<ES: nth_error es n = None>> /\
                 <<LSTS_SRC': nth_error lsts_src' n = None>> /\
                 <<ALSTS_TGT': nth_error alsts_tgt' n = None>> /\
                 <<ANODES: nth_error nodes n = None>> /\
                 <<LSTS_TGT': nth_error lsts_tgt' n = None>>) \/
                (exists lst_src_n es_n lst_src_n'
                   alst_tgt_n' nd_n lst_tgt_n',
                    <<LSTS_SRC: nth_error lsts_src n = Some lst_src_n>> /\
                    <<ES: nth_error es n = Some es_n>> /\
                    <<LSTS_SRC': nth_error lsts_src' n = Some lst_src_n'>> /\
                    <<ALSTS_TGT': nth_error alsts_tgt' n = Some alst_tgt_n'>> /\
                    <<ANODES: nth_error nodes n = Some nd_n>> /\
                    <<LSTS_TGT': nth_error lsts_tgt' n = Some lst_tgt_n'>> /\
                    <<STEP_SRC: AANode.step tm lst_src_n es_n None lst_src_n'>> /\
                    <<MATCH: match_lstate (DTime.succ tm) nw1
                                 lst_src_n' alst_tgt_n'>> /\
                    <<AMW_LST': amw_lst n nd_n lst_tgt_n' alst_tgt_n'>> /\
                    <<WF_SRC': AANode.state_wf n lst_src_n'>> /\
                    <<WF_TGT': AbstMW.state_wf n alst_tgt_n'>>
                )
            ).
        { intro AUX.
          splits.
          - apply Forall4_nth. i.
            specialize (AUX n).
            des.
            + rewrite LSTS_SRC, ES, LSTS_SRC'.
              rewrite repeat_nth_error_None.
              2: { apply nth_error_None. ss. }
              econs.
            + rewrite LSTS_SRC, ES, LSTS_SRC'.
              rewrite repeat_nth_error_Some.
              2: { apply nth_error_Some. congruence. }
              econs; ss.
          - apply Forall2_nth. i.
            specialize (AUX n).
            des.
            + rewrite LSTS_SRC', ALSTS_TGT'.
              econs.
            + rewrite LSTS_SRC', ALSTS_TGT'.
              econs; ss.
          - apply iForall3_nth. i.
            specialize (AUX n). ss.
            des.
            + rewrite ANODES, LSTS_TGT', ALSTS_TGT'.
              econs.
            + rewrite ANODES, LSTS_TGT', ALSTS_TGT'.
              econs. ss.
          - apply iForall_nth. i.
            specialize (AUX n). ss.
            des.
            + r. rewrite LSTS_SRC'. ss.
            + r. rewrite LSTS_SRC'. ss.
          - apply iForall_nth. i.
            specialize (AUX n). ss.
            des.
            + rewrite ALSTS_TGT'. ss.
            + rewrite ALSTS_TGT'. ss.
        }

        intro n.
        destruct (le_lt_dec (length xs) n) as [LE|LT].
        - left.

          assert (LST_SRC_N': nth_error lsts_src' n = None).
          { subst lsts_src'.
            apply map_nth_error_None_iff.
            apply nth_error_None. ss. }
          assert (ALST_TGT_N': nth_error alsts_tgt' n = None).
          { subst lsts_src'.
            apply map_nth_error_None_iff.
            apply nth_error_None. ss. }

          assert (LST_TGT_N: nth_error lsts_tgt n = None).
          { apply nth_error_None.
            rewrite <- LEN_LSTS_SRC'. ss. }

          assert (<<ALST_TGT_N: nth_error amw_lsts_tgt n = None>> /\
                  <<ANODES_N: nth_error nodes n = None>>).
          { rewrite iForall3_nth in AMW_LSTS_TGT.
            specialize (AMW_LSTS_TGT n).
            rewrite LST_TGT_N in AMW_LSTS_TGT.
            inv AMW_LSTS_TGT. ss. }

          assert (<<ES_N: nth_error es n = None>> /\
                  <<LST_TGT_N': nth_error lsts_tgt' n = None>>).
          { rewrite Forall4_nth in LOCAL_STEPS.
            specialize (LOCAL_STEPS n).
            rewrite LST_TGT_N in LOCAL_STEPS.
            inv LOCAL_STEPS. ss. }
          des.

          assert (LST_SRC_N: nth_error lsts_src n = None).
          { rewrite Forall2_nth in MATCH_LSTS.
            specialize (MATCH_LSTS n).
            rewrite ALST_TGT_N in MATCH_LSTS.
            inv MATCH_LSTS. ss. }

          splits; ss.

        - right.
          assert (X_N: exists x, nth_error xs n = Some x).
          { apply Some_not_None.
            apply nth_error_Some. ss. }
          des.

          exploit LSTS_SRC_PROPS; eauto.
          destruct x as [st_src' alst_tgt'].
          intros (OPKT_N & STEP_SRC & MATCH' & AMW_LST' &
                  WF_SRC' & WF_TGT').
          inv MATCH'.

          destruct (nth_error lsts_src n) as [lst_src_n|].
          2: { inv STEP_SRC. }
          destruct (nth_error es n) as [es_n|].
          2: { inv STEP_SRC. }
          inv STEP_SRC.

          destruct (nth_error nodes n) as [nd_n|] eqn:ND_N.
          2: { inv AMW_LST'. }
          destruct (nth_error lsts_tgt' n) as [lst_tgt_n'|].
          2:{ inv AMW_LST'. }
          inv AMW_LST'.

          rewrite iForall3_nth in AMW_LSTS_TGT.
          specialize (AMW_LSTS_TGT n). ss.

          assert (LST_TGT_N: exists lst_tgt_n,
                     nth_error lsts_tgt n = Some lst_tgt_n).
          { apply Some_not_None.
            apply nth_error_Some. nia. }
          des.

          assert (exists nd_n' alst_tgt_n,
                     <<ND_N': nth_error nodes n = Some nd_n'>> /\
                     <<ALST_TGT_N: nth_error amw_lsts_tgt n = Some alst_tgt_n>> /\
                     <<AMW_LST': amw_lst n nd_n' lst_tgt_n alst_tgt_n>>).
          { rewrite LST_TGT_N in AMW_LSTS_TGT.
            inv AMW_LSTS_TGT.
            esplits; eauto. }
          des.

          esplits; eauto.
          + subst lsts_src'.
            apply map_nth_error_iff.
            esplits; eauto.
          + subst lsts_src'.
            apply map_nth_error_iff.
            esplits; eauto.
      }

      des.
      exists lsts_src', alsts_tgt'.
      splits; ss.
      + econs; eauto.
        apply map_id_ext.
        i. destruct a; ss.

        assert (RANGE_TM: DTime.of_ns (nsytm - max_clock_skew - max_nw_delay)
                <= tm < DTime.of_ns (nsytm - max_clock_skew)).
        { subst nsytm. ss.
          split.
          - nia.
          - hexploit (get_skwd_base_time_range tm); eauto.
            fold cbt. ss. nia.
        }
        assert (EXACT_NONE: exact_skwd_base_time period tm = None).
        { apply exact_skwd_base_time_None_iff.
          { clear - IN_BTW PERIOD_COND.
            subst nsytm.
            pose proof DTime.units_per_ns_pos.
            nia. }
          exists cbt.
          split.
          - clear - RANGE_TM PERIOD_COND.
            subst nsytm. ss. nia.
          - assert (CBT_EQ: get_skwd_base_time period tm = cbt)
              by ss.

            apply get_skwd_base_time_iff in CBT_EQ.
            des. ss.
        }
        rewrite EXACT_NONE.

        rewrite map_repeat. ss.
        rewrite AANode.merge_inbox_nils. ss.
      + eapply NW.wf_distr_preserve; eauto.
      + eapply nw_inv_distr; eauto.

    - (* working time *)

      assert (TM_POS: 0 < tm).
      { ss. nia. }


      assert (ST_SRC_EX:
                forall n (N_UB: n < length amw_lsts_tgt),
                exists x,
                  (fun n (x: @AANode.state sysE * (Tid * msgT)? * state) =>
                     let '(st_src1, ms, st_tgt') := x in
                     let tid := n in
                     option_rel4
                       (AANode.step tm)
                       (nth_error lsts_src n)
                       (nth_error es n)
                       (Some ms) (Some st_src1) /\
                     (* length ms <= 1 /\ *)
                     option_rel1
                       (fun opkt =>
                          option_rel1 Packet.wf opkt /\
                          match_pkt nsytm tid ms opkt)
                       (nth_error opkts tid) /\

                     option_rel1
                       (fun opkt =>
                          forall (outs_src: list (Tid * msgT)?)
                            (outs_tgt: list (Packet.t)?)
                            nw'
                            (LEN_OUTS: length outs_src = num_tasks)
                            (MATCH_OUTMSGS: iForall2 (match_pkt nsytm)
                                                     0 outs_src outs_tgt)
                            (OUT_SRC_N: nth_error outs_src tid = Some ms)
                            (OUT_TGT_N: nth_error outs_tgt tid = Some opkt)
                            (NW: NW.gather nw1 (filtermap id outs_tgt) nw')
                          ,
                            let st_src' :=
                                AANode.accept_msgs
                                  tm outs_src st_src1 in
                            match_lstate (DTime.succ tm) nw'
                                         st_src' st_tgt' /\
                            AANode.state_wf tid st_src')
                       (nth_error opkts n) /\
                     option_rel3
                       (amw_lst n)
                       (nth_error nodes n)
                       (nth_error lsts_tgt' n)
                       (Some st_tgt') /\
                     (* (uncurry_p (AANode.state_wf imcasts)) (n, st_src') /\ *)
                     (state_wf n st_tgt')
                  ) n x).
      { i.
        hexploit nth_error_Some2; eauto. i. des.
        renames e1 NTH_EX into alst_tgt ALST_TGT.

        hexploit Forall2_nth2; try apply MATCH_LSTS; eauto. i. des.
        renames e1 NTH1 P_FA into lst_src LST_SRC MATCH_LST.

        rewrite iForall3_nth in AMW_LSTS_TGT.
        specialize (AMW_LSTS_TGT n). ss.
        rewrite ALST_TGT in AMW_LSTS_TGT.

        assert (exists nd_n lst_tgt,
                   <<ND_N: nth_error nodes n = Some nd_n>> /\
                   <<LST_TGT: nth_error lsts_tgt n = Some lst_tgt>> /\
                   <<AMW_LST: amw_lst n nd_n lst_tgt alst_tgt>>).
        { inv AMW_LSTS_TGT. esplits; eauto. }
        des.

        assert (WF_SRC_N: AANode.state_wf n lst_src).
        { eapply iForall_nth1 in WF_SRC; try apply LST_SRC; eauto. }
        assert (WF_TGT_N: AbstMW.state_wf n alst_tgt).
        { eapply iForall_nth1 in WF_TGT; try apply ALST_TGT; eauto. }

        hexploit Forall4_nth1; eauto. i. des.
        renames e2 NTH2 into es_n ES_N.
        renames e3 NTH3 into opkt OPKT.
        renames e4 NTH4 into lst_tgt' LST_TGT'.
        rename P_FA into STEP_TGT.

        inv AMW_LST. ss.
        inv STEP_TGT. existT_elim. clarify. ss.

        assert (TASK_ID_SRC: AANode.task_id lst_src = n).
        { inv WF_SRC_N. ss. }
        guardH TASK_ID_SRC.
        assert (exists ip,
                   <<TASK_ID_IP: task_id_ip n ip>> /\
                   <<IP_EQ: ip = tid2ip n>> /\
                   <<IP_LOCAL: IP.local_ip ip = true>> /\
                   <<IP_ADDR_TGT: ip_addr alst_tgt = ip>>).
        { inv WF_TGT_N.
          hexploit task_id_ip_comput; eauto. i. des.
          esplits; eauto. }
        des. guardH IP_EQ.
        rewrite <- IP_EQ in ISTEP.

        hexploit step_src_working; eauto.
        { rewrite TASK_ID_SRC. ss. }
        { rewrite TASK_ID_SRC. ss. }
        { rewrite IP_ADDR_TGT. eauto. }

        intros (lst_src' & ms & STEP_SRC &
                WF_OPKT & MATCH_PKT & MATCH_LST').

        exists (lst_src', ms, ist').
        rewrite LST_SRC, ES_N, OPKT.
        splits; eauto.
        { econs. eauto. }
        { econs; eauto.
          rewrite TASK_ID_SRC in MATCH_PKT.
          fold cbt nsytm in MATCH_PKT. ss. }
        { r. fold cbt nsytm in MATCH_LST'.
          rewrite TASK_ID_SRC in MATCH_LST'.
          i.
          split; eauto.
          apply AANode.wf_accept_msgs_prsv.
          eapply AANode.wf_prsv; eauto.
        }
        { rewrite ND_N, LST_TGT'. econs.
          econs. }
        { unfold uncurry_p. ss.
          eapply wf_prsv; eauto.
        }
      }

      apply exists_list in ST_SRC_EX.
      destruct ST_SRC_EX as (xs & XS_LEN & XS_PROPS).
      des.

      pose (lsts_src1 := map fst (map fst xs)).
      pose (outs_src := map snd (map fst xs)).
      pose (alsts_tgt' := map snd xs).

      pose (lsts_src' := map (AANode.accept_msgs tm outs_src) lsts_src1).

      assert (<<L_LSTS_SRC: length lsts_src = length xs>> /\
              <<L_ES: length es = length xs>> /\
              <<L_OPKTS: length opkts = length xs>> /\
              <<L_LSTS_TGT: length lsts_tgt = length xs>> /\
              <<L_LSTS_TGT': length lsts_tgt' = length xs>> /\
              <<L_NODES: length nodes = length xs>>).
      { apply Forall2_length in MATCH_LSTS.
        apply iForall3_length in AMW_LSTS_TGT.
        (* rewrite attach_index_length in AMW_LSTS_TGT. *)
        apply Forall4_length in LOCAL_STEPS.
        des.
        splits; nia.
      }
      des.

      cut (forall n,
              (exists lst_src es_n opkt_n lst_tgt lst_tgt'
                 lst_src1 alst_tgt' out_src lst_src' node,
                  <<LST_SRC: nth_error lsts_src n = Some lst_src>> /\
                  <<LST_SRC1: nth_error lsts_src1 n = Some lst_src1>> /\
                  <<LST_SRC': nth_error lsts_src' n = Some lst_src'>> /\
                  <<LST_TGT: nth_error lsts_tgt n = Some lst_tgt>> /\
                  <<LST_TGT': nth_error lsts_tgt' n = Some lst_tgt'>> /\
                  <<ES_N: nth_error es n = Some es_n>> /\
                  <<OPKT_N: nth_error opkts n = Some opkt_n>> /\
                  <<ALST_TGT': nth_error alsts_tgt' n = Some alst_tgt'>> /\
                  <<OUT_SRC: nth_error outs_src n = Some out_src>> /\
                  <<NODE: nth_error nodes n = Some node>> /\

                  <<STEP: AANode.step tm lst_src es_n out_src lst_src1>> /\
                  (* <<LEN_OUT_SRC: length out_src <= 1>> /\ *)
                  <<WF_OPKT: option_rel1 Packet.wf opkt_n>> /\
                  <<MATCH_PKT: match_pkt nsytm n out_src opkt_n>> /\
                  <<LST_SRC'_EQ:
                    lst_src' = AANode.accept_msgs tm outs_src lst_src1>> /\

                  <<MATCH_LST:
                    (* forall (outs_src : list (list (nat * msgT))) (outs_tgt : list Packet.t ?) (nw' : NW.t), *)
                    (*   length outs_src = num_tasks -> *)
                    (*   Forall2 (match_pkt nsytm) (attach_index outs_src) outs_tgt -> *)
                    (*   nth_error outs_src n = Some out_src -> *)
                    (*   nth_error outs_tgt n = Some opkt_n -> *)
                    (*   NW.gather nw1 (filtermap id outs_tgt) nw' -> *)
                      match_lstate (DTime.succ tm) nw' lst_src' alst_tgt'>> /\
                  <<AMW_LST': amw_lst n node lst_tgt' alst_tgt'>> /\
                  <<WF_SRC': AANode.state_wf n lst_src'>> /\
                  <<WF_TGT': state_wf n alst_tgt'>>)
              \/
              (<<LST_SRC: nth_error lsts_src n = None>> /\
               <<LST_SRC1: nth_error lsts_src1 n = None>> /\
               <<LST_SRC': nth_error lsts_src' n = None>> /\
               <<LST_TGT: nth_error lsts_tgt n = None>> /\
               <<LST_TGT': nth_error lsts_tgt' n = None>> /\
               <<ES_N: nth_error es n = None>> /\
               <<OPKT_N: nth_error opkts n = None>> /\
               <<ALST_TGT': nth_error alsts_tgt' n = None>> /\
               <<OUT_SRC: nth_error outs_src n = None>> /\
               <<NODE: nth_error nodes n = None>>)
          ).
      { intro LIST_ELEMS.
        exists lsts_src', alsts_tgt'.

        splits.
        - econs; eauto.
          2: { subst lsts_src'. eauto. }
          apply Forall4_nth.
          intro n. fold msgT.
          specialize (LIST_ELEMS n). des.
          + rewrite LST_SRC, ES_N, OUT_SRC, LST_SRC1.
            econs. eauto.
          + rewrite LST_SRC, ES_N, OUT_SRC, LST_SRC1.
            econs.
        - eapply NW.wf_gather_preserve; eauto.
          { eapply NW.wf_distr_preserve; eauto. }

          apply Forall_forall.
          intros p IN_F.
          apply filtermap_in in IN_F.
          unfold id in IN_F. des. subst.

          apply In_nth_error in IN_F. des.
          specialize (LIST_ELEMS n). des.
          + rewrite OPKT_N in IN_F. clarify.
          + rewrite OPKT_N in IN_F. clarify.
        - eapply nw_inv_gather; eauto.
          eapply nw_inv_distr; eauto.
        - rewrite Forall2_nth. i.
          specialize (LIST_ELEMS n). des.
          + rewrite LST_SRC', ALST_TGT'. econs.
            eapply MATCH_LST; eauto.
          + rewrite LST_SRC', ALST_TGT'. econs.
        - rewrite iForall3_nth. i. ss.
          specialize (LIST_ELEMS n). des.
          + rewrite NODE, LST_TGT', ALST_TGT'.
            econs. ss.
          + rewrite NODE, LST_TGT', ALST_TGT'.
            econs.
        - apply iForall_nth. i. ss.
          specialize (LIST_ELEMS n). des.
          + rewrite LST_SRC'. ss.
          + rewrite LST_SRC'. ss.
        - apply iForall_nth. i. ss.
          specialize (LIST_ELEMS n). des.
          + rewrite ALST_TGT'. ss.
          + rewrite ALST_TGT'. ss.
      }

      assert (MATCH_PKTS:
                iForall2 (match_pkt nsytm)
                         0 outs_src opkts).
      { apply iForall2_nth.
        intros n.
        destruct (nth_error xs n) as
            [[[st_src1 outs_n] st_tgt']|] eqn:XS_N.
        2: {
          assert (N_XS: length xs <= n).
          { apply nth_error_None in XS_N. ss. }
          repeat rewrite nth_error_None2 by nia.

          rewrite nth_error_None2.
          2: { unfold outs_src.
               do 2 rewrite map_length. ss. }
          rewrite nth_error_None2 by nia.
          econs.
        }

        assert (N_XS: n < length xs).
        { apply nth_error_Some. congruence. }
        repeat rewrite nth_error_None2 by nia.

        subst outs_src. ss.
        replace (nth_error (map snd (map fst xs)) n) with (Some outs_n).
        2: {
          symmetry.
          do 2 rewrite Coqlib.list_map_nth.
          rewrite XS_N. ss.
        }

        hexploit (nth_error_Some2 _ opkts n); eauto.
        { nia. }
        i. des. renames e1 NTH_EX into op OP.
        rewrite OP. econs.

        exploit XS_PROPS; eauto. s.
        rewrite OP.
        intros (? & OPP1 & ?).
        inv OPP1. ss.
      }

      intro n.
      destruct (lt_ge_dec n (length xs)).
      + hexploit (nth_error_Some2 _ xs n); [nia|].
        i. des. renames e1 NTH_EX into xs_n XS_N.
        destruct xs_n as [[lst_src1 out_src] alst_tgt'].

        assert (LST_SRC1: nth_error lsts_src1 n = Some lst_src1).
        { subst lsts_src1.
          do 2 rewrite Coqlib.list_map_nth.
          rewrite XS_N. ss. }
        assert (OUT_SRC: nth_error outs_src n = Some out_src).
        { subst outs_src.
          do 2 rewrite Coqlib.list_map_nth.
          rewrite XS_N. ss. }
        assert (ALST_TGT': nth_error alsts_tgt' n = Some alst_tgt').
        { subst alsts_tgt'.
          rewrite Coqlib.list_map_nth.
          rewrite XS_N. ss. }
        assert (LST_SRC': nth_error lsts_src' n =
                          Some (AANode.accept_msgs tm outs_src lst_src1)).
        { subst lsts_src'.
          rewrite Coqlib.list_map_nth.
          rewrite LST_SRC1. ss. }

        hexploit (nth_error_Some2 _ lsts_src n); [nia|].
        i. des. renames e1 NTH_EX into lst_src LST_SRC.
        hexploit (nth_error_Some2 _ lsts_tgt n); [nia|].
        i. des. renames e1 NTH_EX into lst_tgt LST_TGT.
        hexploit (nth_error_Some2 _ lsts_tgt' n); [nia|].
        i. des. renames e1 NTH_EX into lst_tgt' LST_TGT'.
        hexploit (nth_error_Some2 _ es n); [nia|].
        i. des. renames e1 NTH_EX into es_n ES_N.
        hexploit (nth_error_Some2 _ opkts n); [nia|].
        i. des. renames e1 NTH_EX into opkt_n OPKT_N.
        hexploit (nth_error_Some2 _ nodes n); [nia|].
        i. des. renames e1 NTH_EX into node NODE.

        left.
        exploit XS_PROPS; eauto. s.
        rewrite LST_SRC, ES_N, OUT_SRC, LST_SRC1.
        rewrite OPKT_N, NODE, LST_TGT', ALST_TGT'.
        intros (STEP_P & OP & ALST_TGT_P' & AMW_LST' & WF_TGT_N).
        inv STEP_P. inv OP. inv AMW_LST'. r in ALST_TGT_P'.
        hexploit ALST_TGT_P'; eauto.
        { subst outs_src.
          do 2 rewrite map_length. nia. }
        intros (MATCH & WF_SRC_N).

        esplits; eauto.

      + right.
        rewrite (nth_error_None2 _ lsts_src) by nia.
        rewrite (nth_error_None2 _ lsts_tgt) by nia.
        rewrite (nth_error_None2 _ es) by nia.
        rewrite (nth_error_None2 _ opkts) by nia.
        rewrite (nth_error_None2 _ nodes) by nia.
        rewrite (nth_error_None2 _ lsts_tgt') by nia.
        rewrite (nth_error_None2 _ lsts_src1).
        2: { subst lsts_src1.
             do 2 rewrite map_length. ss. }
        rewrite (nth_error_None2 _ lsts_src').
        2: { subst lsts_src' lsts_src1.
             do 3 rewrite map_length. ss. }
        rewrite (nth_error_None2 _ alsts_tgt').
        2: { subst alsts_tgt'.
             rewrite map_length. ss. }
        rewrite (nth_error_None2 _ outs_src).
        2: { subst outs_src.
             do 2 rewrite map_length. ss. }
        splits; ss.
  Qed.


  Lemma fmsim_running
    : forall tm lsts_src
        nw lsts_tgt amw_lsts_tgt
        st_src st_tgt
        (NW_WF: NW.wf nw)
        (NW_INV: nw_inv tm nw)
        (* (LEN: IntRange.sint8 (length lsts_tgt)) *)
        (TM_LB: DTime.of_ns (period - max_clock_skew) <= tm)
        (MATCH_LSTS: Forall2 (match_lstate tm nw)
                             lsts_src amw_lsts_tgt)
        (AMW_LSTS: iForall3 amw_lst 0 nodes
                           lsts_tgt amw_lsts_tgt)

        (ST_SRC: st_src = AASys.State tm lsts_src)
        (ST_TGT: st_tgt = NWSys.State tm nw lsts_tgt)
        (WF_SRC: iForall AANode.state_wf 0 lsts_src)
        (WF_TGT: iForall state_wf 0 amw_lsts_tgt)
    ,
      fmsim_states _ sys_src sys_tgt
                   st_src st_tgt.
  Proof.
    pcofix CIH. i.
    pfold. econs.
    { ss. }
    i. ss. inv STEPS. ss.
    inv MSTEPS_REST. ss.

    exists 1. exists tr_tgt.
    destruct st_tgt' as [tm' nw' lsts_tgt']. ss.

    hexploit match_step_sim; try apply STEP; eauto.
    intros (lsts_src' & amw_lsts_tgt' & STEP_SRC &
            WF_NW' & NW_INV' & MATCH' & AMW_LSTS' &
            WF_SRC' & WF_TGT').

    esplits.
    { ss. }
    { econs; eauto.
      econs. ss.
      unfold AASys.num_sites. ss.
      f_equal.
      replace (length lsts_tgt') with (length amw_lsts_tgt').
      2: { symmetry.
           apply iForall3_length in AMW_LSTS'.
           des. congruence. }
      symmetry.
      eapply Forall2_length in MATCH'; eauto.
    }
    { apply Forall2_tes_equiv_refl. }

    right. eapply CIH; try reflexivity; eauto.
    cut (tm' = DTime.succ tm).
    { intro TM'.
      assert (tm < tm').
      { rewrite TM'. ss. }
      nia. }
    inv STEP. ss.
  Qed.

End PROOF.
