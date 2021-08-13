From ITree Require Import ITree.
From compcert Require Coqlib.
Require Import Paco.paco.

Require Import List.
Require Import Arith ZArith Lia.

Require Import sflib.
Require Import Axioms StdlibExt IntegersExt.

Require Import SysSem.
Require Import IPModel DiscreteTimeModel.




(**)
Module Packet.

  (* payload limit is actually 65507, considering header_size*)
  Definition maxlen: nat := Z.to_nat 65536.

  Lemma maxlen_lt_intmax_signed
    : (Z.of_nat maxlen < Int.max_signed)%Z.
  Proof.
    unfold maxlen.
    rewrite Z2Nat.id by ss.
    ss.
  Qed.

  (* UDP/IP packet *)
  Record msg_t : Type :=
    mkMsg { src_ip: ip_t;
            dest_ip: ip_t;
            dest_port: nat;
            payload: list byte;
          }.

  Inductive msg_wf (m: msg_t): Prop :=
    MsgWf
      (* (SIP_RANGE: src_ip m <= Z.to_nat Int.max_unsigned) *)
      (* (DIP_RANGE: dest_ip m <= Z.to_nat Int.max_unsigned) *)
      (* (DEST_PORT_RANGE: dest_port m <= Z.to_nat Int.max_signed) *)

      (PAYLOAD_LEN: length (payload m) < maxlen)
  .

  (* multicast group member entry denoted as (group, site) *)
  Definition mcm_t: Type := ip_t * ip_t.

  Definition mcm_eqb (mcm1 mcm2: ip_t * ip_t): bool :=
    andb (fst mcm1 =? fst mcm2) (snd mcm1 =? snd mcm2).


  Lemma mcm_eqb_spec
        a b
    : Bool.reflect (a = b) (mcm_eqb a b).
  Proof.
    unfold mcm_eqb.
    destruct a as [a1 a2].
    destruct b as [b1 b2]. ss.
    destruct (Nat.eqb_spec a1 b1);
      destruct (Nat.eqb_spec a2 b2);
      econs; congruence.
  Qed.


  Inductive mcm_wf : mcm_t -> Prop :=
    MCastMemWf
      mip nip
      (MCAST_IP: IP.mcast_ip mip = true)
      (NODE_IP: IP.local_ip nip = true)
    : mcm_wf (mip, nip).

  Definition t : Type := msg_t + mcm_t.
  (* | MCast (mcm: mcm_t) *)
  (* | Msg (msg: msg_t) *)
  (* . *)

  Definition Msg : msg_t -> t := inl.
  Definition MCast : mcm_t -> t := inr.

  Inductive wf : t -> Prop :=
  | Wf_MCast
      mcm (WF_MCE: mcm_wf mcm)
    : wf (inr mcm)
  | Wf_Msg
      msg (WF_MSG: msg_wf msg)
    : wf (inl msg)
  .

  (* Definition sender (p: t) : ip_t := *)
  (*   match p with *)
  (*   | MCastPkt mce => snd mce *)
  (*   | MsgPkt msg => src_ip msg *)
  (*   end. *)

  (* Definition wf_sender (nip: ip_t) (p: t): Prop := *)
  (*   <<WF_PACKET: wf p>> /\ <<SENDER_EQ: sender p = nip>>. *)

End Packet.

(* Definition pm2pkt (m: Packet.msg_t): Packet.t := inl m. *)
Coercion Packet.Msg : Packet.msg_t >-> Packet.t.

(* reliable network system parameters *)
Class rnws_params: Type :=
  RelNWSysParams
    { (* for network model *)
      max_nw_delay: nat; (* in nanosec *)
      (* for OS model *)
      max_clock_skew: nat; (* in nanosec *)
      (* min_process_restart_delay: nat; (* in nanosec *) *)
      max_wait_delay: nat; (* in nanosec *)

      max_nw_delay_pos: 0 < max_nw_delay;
      max_clock_skew_pos: 0 < max_clock_skew;
      max_wait_delay_pos: 0 < max_wait_delay;
      max_nw_delay_range: IntRange.uint64 max_nw_delay ;
      max_clock_skew_range: IntRange.uint64 max_clock_skew ;

      valid_clock_skew : DTime.t -> nat -> Prop :=
        fun gtm ltm => nat_diff (DTime.to_ns_rd gtm) ltm < max_clock_skew ;
    }.

Lemma DTime_to_ns_rd_succ
      gtm gtm_ns gtm'
      (GTM_NS: gtm_ns = DTime.to_ns_rd gtm)
      (GTM': gtm' = DTime.succ gtm)
  : <<GTM_ADV_EXACT: DTime.to_ns_exact gtm' = Some (S gtm_ns)>> \/
    (<<GTM_ADV_NOT_EXACT: DTime.to_ns_exact gtm' = None>> /\
     <<GTM_NS': DTime.to_ns_rd gtm' = gtm_ns>>).
Proof.
  hexploit DTime_to_ns_rd_spec.
  { symmetry. apply GTM_NS. }
  intros (r & GTM_EQ & RANGE_R).

  unfold DTime.succ in GTM'.
  rewrite GTM_EQ in GTM'.
  rewrite plus_n_Sm in GTM'.

  assert (S_R: S r < DTime.units_per_ns \/ S r = DTime.units_per_ns) by nia.
  des.
  - right.
    split.
    2: { apply DTime_to_ns_rd_iff.
         exists (S r). splits; eauto.
         subst gtm'. ss. }

    apply DTime_to_ns_exact_None_iff.
    exists gtm_ns, (S r).
    esplits; eauto.
    + subst gtm'. ss.
    + symmetry. apply DTime_to_ns_rd_iff.
      exists (S r). splits; eauto.
      subst gtm'. ss.
    + nia.
  - left.
    apply DTime_to_ns_exact_spec.
    subst gtm'. ss. nia.
Qed.

Lemma DTime_to_ns_exact_impl_rd
      gtm ns
      (EXACT: DTime.to_ns_exact gtm = Some ns)
  : DTime.to_ns_rd gtm = ns.
Proof.
  unfold DTime.to_ns_exact, DTime.to_ns_rd in *.
  desf.
Qed.

Section RELIABLE_NW_SYS_PARAMS.
  Context `{rnws_params}.

  Definition adv_local_clock (gtm: DTime.t) (ltm ltm': nat) : Prop :=
    ltm <= ltm' /\ valid_clock_skew (DTime.succ gtm) ltm'.

  Lemma valid_clock_skew_can_advance
        gtm ltm
        (VALID: valid_clock_skew gtm ltm)
    : exists ltm', adv_local_clock gtm ltm ltm'.
  Proof.
    r in VALID.
    pose (gtm' := DTime.succ gtm).
    hexploit (DTime_to_ns_rd_succ gtm); eauto. i. des.
    2: {
      exists ltm.
      r. split.
      - ss.
      - r. rewrite GTM_NS'. ss.
    }

    exists (S ltm).
    r. split.
    - nia.
    - r.
      hexploit DTime_to_ns_exact_impl_rd; eauto.
      intro TO_NS_RD.
      rewrite TO_NS_RD. ss.
  Qed.

  Definition valid_delay (dly: nat): Prop :=
    dly < max_nw_delay * DTime.units_per_ns.

  Inductive valid_delay_added {A} (a: A): A * nat -> Prop :=
    ValidDelayAdded
      dly (VALID_DELAY: valid_delay dly)
    : valid_delay_added a (a, dly).

  Definition age_delay {A} (x: A * nat) : A * nat + A :=
    match x with
    | (a, n) =>
      match n with
      | O => inr a
      | S n' => inl (a, n')
      end
    end.

End RELIABLE_NW_SYS_PARAMS.


Module NW.
  Record t: Type :=
    mk { mcast_groupinfo: list (ip_t * ip_t) ;
         packet_msg_pool: list (ip_t (*actual-dest*) * Packet.msg_t * nat) ;
         mcast_msg_pool: list (ip_t * ip_t * nat) ;
       }.

  Definition init : t := mk [] [] [].

  Section NW_SEM.
    Context `{rnws_params}.

    (* packet-in-pool *)
    (* Inductive pip_wf: ip_t * Packet.msg_t * nat -> Prop := *)
    (*   PIPWf *)
    (*     dip pkt dly *)
    (*     (* (WF_PACKET: Packet.wf pkt) *) *)
    (*     (VALID_DELAY: valid_delay dly) *)
    (*   : pip_wf (dip, pkt, dly). *)

    Record wf (nw: t): Prop :=
      Wf { wf_mcast_groupinfo:
             List.Forall Packet.mcm_wf (mcast_groupinfo nw) ;
           wf_mcast_nodup:
             List.NoDup (mcast_groupinfo nw) ;

           wf_packet_pool:
             Forall (fun pmi =>
                      Packet.msg_wf (snd (fst pmi)) /\
                      valid_delay (snd pmi))
                    (packet_msg_pool nw);
           wf_mcast_msg_pool:
             Forall (fun mcmi =>
                       Packet.mcm_wf (fst mcmi) /\
                       valid_delay (snd mcmi))
                    (mcast_msg_pool nw) ;
         }.

    Lemma wf_init : wf init.
    Proof. econs; ss. econs. Qed.

    Definition get_actual_receivers
               (mg: list (ip_t * ip_t)) (gip: ip_t)
      : list ip_t :=
      filtermap (fun mge =>
                   if (fst mge =? gip)%nat
                   then Some (snd mge) else None) mg.

    (* attach actual dest *)
    Definition attach_adest
               (mg: list (ip_t * ip_t))
               (pm: Packet.msg_t)
      : list (ip_t * Packet.msg_t) :=
      let dip := Packet.dest_ip pm in
      if IP.mcast_ip dip
      then List.map (fun adip => (adip, pm))
                    (get_actual_receivers mg dip)
      else [(dip, pm)].

    Inductive gather: t -> list Packet.t -> t -> Prop :=
      Gather
        mcg pmp mcmp
        pkts pms_new mcms_new
        pms_att pmp_new
        mcmp_new
        pmp' mcmp'
        (* dpkts pp_new pp' *)
        (CLASSIFY: partition_map id pkts = (pms_new, mcms_new))
        (ATTACH_ADEST: concat (List.map (attach_adest mcg) pms_new) = pms_att)
        (VALID_DELAYS_PMS: Forall2 valid_delay_added pms_att pmp_new)
        (ADD_PMP: pmp' = pmp ++ pmp_new)

        (VALID_DELAYS_MCMS: Forall2 valid_delay_added mcms_new mcmp_new)
        (ADD_MCMP: mcmp' = mcmp ++ mcmp_new)
      : gather (mk mcg pmp mcmp) pkts (mk mcg pmp' mcmp').

    Definition join1 (mg: list (ip_t * ip_t))
               (mcm: ip_t * ip_t)
      : list (ip_t * ip_t) :=
      if (existsb (Packet.mcm_eqb mcm) mg) then mg else mcm :: mg.

    Definition join (mg mg_new: list (ip_t * ip_t)) :=
      List.fold_left join1 mg_new mg.

    Definition distr (nw: t)
      : t * list (ip_t * Packet.msg_t) :=
      match nw with
      | mk mg pmp mcmp =>
        let (pmp', dpms) := partition_map age_delay pmp in
        let (mcmp', mcm_add) := partition_map age_delay mcmp in

        (mk (join mg mcm_add) pmp' mcmp', dpms)
        (* let (dmps, mges) := partition_map classify_dpacket dpkts in *)
        (* (mk (mg++mges) pp', dmps) *)
      end.


    Lemma get_actual_receivers_nodup
          mcg
          (* (WF_MCG: Forall Packet.mcm_wf mcg) *)
          (NODUP: NoDup mcg)
      : forall mip,
        NoDup (get_actual_receivers mcg mip).
    Proof.
      clear - NODUP.
      i. unfold get_actual_receivers.
      induction mcg as [| h t IH]; ss.
      { econs. }

      inv NODUP.
      desf.
      2: { eauto. }

      econs.
      2: { eauto. }

      intro IN_F.
      apply filtermap_in in IN_F.
      destruct IN_F as [[mip' ip] [IN_T SOME]].
      desf. ss.
      rewrite Nat.eqb_eq in *. clarify.
      rewrite <- surjective_pairing in IN_T. ss.
    Qed.

    Lemma join_nodup
          mcg mcms
          (NODUP: NoDup mcg)
      : NoDup (join mcg mcms).
    Proof.
      depgen mcg.
      induction mcms as [|h t IH]; i; ss.
      eapply IH.
      unfold join1.
      destruct (existsb (Packet.mcm_eqb h) mcg) eqn: EX.
      { ss. }
      apply existsb_false_iff in EX.
      econs; ss.
      intro IN.
      rewrite Forall_forall in EX.
      hexploit EX; eauto.
      destruct (Packet.mcm_eqb_spec h h); ss.
    Qed.

    Lemma join_spec
          mcm mcg mcms
      : In mcm (join mcg mcms) <->
        In mcm mcg \/ In mcm mcms.
    Proof.
      depgen mcg.
      unfold join.
      induction mcms as [| h t IH]; i; ss.
      { split; i; eauto.
        des; ss. }

      rewrite IH.
      unfold join1.

      destruct (existsb (Packet.mcm_eqb h) mcg) eqn:EX.
      - apply existsb_exists in EX. des.
        destruct (Packet.mcm_eqb_spec h x); ss.
        subst.
        split.
        + i. des; eauto.
        + i. des; subst; eauto.
      - apply existsb_false_iff in EX.
        split.
        + i. ss. des; eauto.
        + i. ss. des; eauto.
    Qed.


    (* Inductive accept_pkts (pkts: list Packet.t) *)
    (*   : t -> list (ip_t * Packet.msg_t) -> t -> Prop := *)
    (*   Accept nw nw1 nw' dmsgs *)
    (*        (GATHER: gather nw pkts nw1) *)
    (*        (* (DISTR: distr nw1 = (nw', dmsgs)) *) *)
    (*   : step pkts nw dmsgs nw'. *)

    (* Definition dmsg_wf (dm: ip_t * Packet.msg_t): Prop := *)
    (*   <<DEST_UCAST_IP: IP.local_ip (fst dm) = true>> /\ *)
    (*   <<MSG_WF: Packet.msg_wf (snd dm)>> *)
    (* . *)

    Lemma wf_gather_preserve
          nw nw' pkts
          (GATHER: gather nw pkts nw')
          (WF_NW: wf nw)
          (WF_PKTS: Forall Packet.wf pkts)
      : <<WF_NW': wf nw'>>.
    Proof.
      inv WF_NW.
      inv GATHER.
      econs; ss.
      - apply Forall_app; ss.
        assert (WF_PMS_NEW: Forall Packet.msg_wf pms_new).
        { apply Forall_forall.
          intros pm PM_IN.
          hexploit in_partition_map_l2; eauto.
          unfold id. i. des. subst.
          rewrite Forall_forall in WF_PKTS.
          hexploit WF_PKTS; eauto.
          intro WF_PKT. inv WF_PKT. ss.
        }

        rewrite <- flat_map_concat_map in VALID_DELAYS_PMS.

        apply Forall_forall.
        intros [[ip_r pm] dly] IN_PMP_NEW. ss.
        apply In_nth_error in IN_PMP_NEW. des.
        hexploit Forall2_nth2; try apply VALID_DELAYS_PMS; eauto.
        i. des.
        destruct e1 as [ip_r' pm'].
        inv P_FA.
        split; ss.

        hexploit nth_error_In; eauto.
        intro IN_FL. apply in_flat_map in IN_FL.
        destruct IN_FL as (pm' & IN_PMS_NEW & IN_ADEST).

        cut (pm' = pm).
        { i. subst.
          rewrite Forall_forall in WF_PMS_NEW.
          apply WF_PMS_NEW; eauto. }

        unfold attach_adest in *. desf.
        + apply in_map_iff in IN_ADEST. des. clarify.
        + ss. des; ss. clarify.

      - apply Forall_app; ss.
        assert (WF_PMS_NEW: Forall Packet.mcm_wf mcms_new).
        { apply Forall_forall.
          intros pm PM_IN.
          hexploit in_partition_map_r2; eauto.
          unfold id. i. des. subst.
          rewrite Forall_forall in WF_PKTS.
          hexploit WF_PKTS; eauto.
          intro WF_PKT. inv WF_PKT. ss.
        }

        rewrite <- flat_map_concat_map in VALID_DELAYS_PMS.

        apply Forall_forall.
        intros [[ip_r pm] dly] IN_PMP_NEW. ss.
        apply In_nth_error in IN_PMP_NEW. des.
        hexploit Forall2_nth2; try apply VALID_DELAYS_MCMS; eauto.
        i. des.
        destruct e1 as [ip_r' pm'].
        inv P_FA.
        split; ss.

        hexploit nth_error_In; eauto. i.

        rewrite Forall_forall in WF_PMS_NEW.
        apply WF_PMS_NEW; eauto.
    Qed.

    Lemma wf_gather_progress
          nw pkts
          (WF_NW: wf nw)
          (WF_PKTS: List.Forall Packet.wf pkts)
      : exists nw', gather nw pkts nw'.
    Proof.
      destruct nw as [mcg mpl mcpl].
      inv WF_NW.

      assert (exists pms' mcms', <<PMAP: partition_map id pkts =
                                    (pms', mcms')>>).
      { esplits. apply surjective_pairing. }
      des.

      pose (pms_ad := concat (List.map (attach_adest mcg) pms')).

      assert (PMS_DLY: exists pmp', Forall2 valid_delay_added
                                       pms_ad pmp').
      { assert (AUX: forall n (LEN: n < length pms_ad),
                   exists dpm,
                     option_rel1
                       (fun pm => valid_delay_added pm dpm)
                       (nth_error pms_ad n)).
        { i.
          hexploit (nth_error_Some2 _ pms_ad n); eauto. i. des.
          rewrite NTH_EX.
          exists (e1, 0). ss.
          econs. r.
          pose proof max_nw_delay_pos.
          pose proof DTime.units_per_ns_pos.
          nia.
        }
        eapply exists_list in AUX. des.
        esplits; eauto.
        apply Forall2_nth. i.
        destruct (lt_ge_dec n (length l)).
        - hexploit (nth_error_Some2 _ pms_ad n).
          { nia. }
          i. des. renames e1 NTH_EX into pm1 PM1.
          hexploit (nth_error_Some2 _ l n); eauto.
          i. des. renames e1 NTH_EX into pmd1 PMD1.
          hexploit NTH_PROP; eauto.
          rewrite PM1. rewrite PMD1. ss.
          i. econs. eauto.
        - rewrite nth_error_None2 by nia.
          rewrite nth_error_None2 by nia.
          econs.
      }


      assert (MCMS_DLY: exists mcmp', Forall2 valid_delay_added
                                        mcms' mcmp').
      { assert (AUX: forall n (LEN: n < length mcms'),
                   exists dpm,
                     option_rel1
                       (fun pm => valid_delay_added pm dpm)
                       (nth_error mcms' n)).
        { i.
          hexploit (nth_error_Some2 _ mcms' n); eauto. i. des.
          rewrite NTH_EX.
          exists (e1, 0). ss.
          econs. r.
          pose proof max_nw_delay_pos.
          pose proof DTime.units_per_ns_pos.
          nia.
        }
        eapply exists_list in AUX. des.
        esplits; eauto.
        apply Forall2_nth. i.
        destruct (lt_ge_dec n (length l)).
        - hexploit (nth_error_Some2 _ mcms' n).
          { nia. }
          i. des. renames e1 NTH_EX into pm1 PM1.
          hexploit (nth_error_Some2 _ l n); eauto.
          i. des. renames e1 NTH_EX into pmd1 PMD1.
          hexploit NTH_PROP; eauto.
          rewrite PM1. rewrite PMD1. ss.
          i. econs. eauto.
        - rewrite nth_error_None2 by nia.
          rewrite nth_error_None2 by nia.
          econs.
      }
      i. des.
      esplits.
      econs; eauto.
    Qed.

    Lemma wf_distr_preserve
          nw nw' dpms
          (DISTR: distr nw = (nw', dpms))
          (WF_NW: wf nw)
      : <<WF_NW': wf nw'>> /\
        <<DMSGS_WF: List.Forall
                      (fun dm => Packet.msg_wf (snd dm)) dpms>>.
    Proof.
      destruct nw as [mcg mpl mcpl].
      inv WF_NW. ss.

      assert (exists pmp' dpms',
                 <<MPL: partition_map age_delay mpl = (pmp', dpms')>>).
      { esplits. apply surjective_pairing. }
      assert (exists mcmp' mcm_add,
                 <<MCPL: partition_map age_delay mcpl = (mcmp', mcm_add)>>).
      { esplits. apply surjective_pairing. }
      des.
      rewrite MPL, MCPL in DISTR. clarify.
      rewrite Forall_forall in *.

      esplits.
      - econs; ss.
        + apply Forall_forall.
          intros mcm IN_JOIN.
          apply join_spec in IN_JOIN. des.
          * apply wf_mcast_groupinfo0. auto.
          * eapply in_partition_map_r2 in IN_JOIN; eauto.
            destruct IN_JOIN as [[mcm' []] [IN_MCPL DELAY]]; ss.
            hexploit wf_mcast_msg_pool0; eauto.
            i. des. ss. clarify.
        + apply join_nodup. ss.
        + apply Forall_forall.
          intros [[ip_d pm] dly] IN_PMP'. ss.
          eapply in_partition_map_l2 in MPL; eauto.
          destruct MPL as [[[? ?] dly_p] [IN_MPL AGE]].
          ss. destruct dly_p; ss. clarify.
          hexploit wf_packet_pool0; eauto. ss.
          intros [WF_PM VD].
          split; eauto.
          r in VD. r. nia.
        + apply Forall_forall.
          intros [mcm dly] IN_MCMP'.
          eapply in_partition_map_l2 in MCPL; eauto.
          destruct MCPL as [[mcm' dly'] [IN_MCPL AGE]].
          ss. desf.
          hexploit wf_mcast_msg_pool0; eauto. ss.
          intros [WF_MCM VD].
          split; auto.
          r in VD. r. nia.
      - apply Forall_forall.
        intros [ip_d pm] IN_DPMS. ss.
        eapply in_partition_map_r2 in MPL; eauto.
        destruct MPL as [[[ip_d' pm'] dly'] [IN_MPL AGE]].
        ss. desf.
        hexploit wf_packet_pool0; eauto. ss.
        intros [WF_PM VD]. ss.
    Qed.

  End NW_SEM.
End NW.


Module Node.
  Section NODE.
    Context {sysE: Type -> Type}.

    Record t : Type :=
      mk { ip_addr : ip_t ;
           (* init_mcast_groups: list ip_t ; *)

           istate : Type ;
           init_istate : (* DTime.t -> *) istate -> Prop;

           istep : DTime.t -> list Packet.msg_t ->
                   istate -> tsp * events (nbE +' sysE) -> Packet.t? -> istate -> Prop ;
           (* accept_packets: DTime.t -> list Packet.msg_t -> istate -> istate -> Prop ; *)
         }.

    Inductive wf (node: t): Prop :=
      Wf
        (NODE_IP: IP.local_ip (ip_addr node) = true)
        (* (MCIPS: Forall (fun mip => IP.mcast_ip mip = true) (init_mcast_groups node)) *)
    .

    Inductive state : Type :=
      State (node: t) (ist: istate node).

    Inductive init (node: t): state -> Prop :=
      InitAt
        ist_init
        (INIT_ISTATE: node.(init_istate) ist_init)
      : init node (State node ist_init).

    Definition chget_pm_by_dest (ip: ip_t)
               (dpm: ip_t * Packet.msg_t)
      : Packet.msg_t? :=
      if (fst dpm =? ip)%nat
      then Some (snd dpm) else None.

    Definition distr_msgs_to
               (ip: ip_t) (dpms: list (ip_t * Packet.msg_t))
      : list Packet.msg_t :=
      filtermap (chget_pm_by_dest ip) dpms.

    Inductive step (gtm: DTime.t) (dpms: list (ip_t * Packet.msg_t))
      : state -> tsp * (events (nbE +' sysE)) -> Packet.t? -> state -> Prop :=
      Step
        node dpms_f ist tes opkt ist'
        (FILTER_BY_DEST: dpms_f = distr_msgs_to node.(ip_addr) dpms)
        (ISTEP: node.(istep) gtm dpms_f ist tes opkt ist')
      : step gtm dpms (State node ist) tes opkt (State node ist').

    (* Inductive distrib_packets *)
    (*            (gtm: DTime.t) (dpms: list (ip_t * Packet.msg_t)) *)
    (*   : state -> state -> Prop := *)
    (*   DistribPackets *)
    (*     nd ist dpms_f ist' *)
    (*     (FILTER: dpms_f = filter_by_dest nd.(ip_addr) dpms) *)
    (*     (ACC: accept_packets nd gtm dpms_f ist ist') *)
    (*   : distrib_packets gtm dpms (State nd ist) (State nd ist'). *)

    Section SAFE_STATE.
      Variable node: t.

      Inductive _safe_istate
                (safe: DTime.t -> istate node -> Prop)
                (tm: DTime.t)
                (ist: istate node): Prop :=
        SafeIState
          (PROGRESS:
             forall msgs
               (WF_PMS: Forall Packet.msg_wf msgs),
             exists tes op ist',
               node.(istep) tm msgs ist tes op ist')
          (SAFE_NEXT:
             forall msgs tes op ist'
               (STEP: node.(istep) tm msgs ist tes op ist')
               (WF_PMS: Forall Packet.msg_wf msgs),
               option_rel1 Packet.wf op /\
               safe (DTime.succ tm) ist')
      .

      Hint Constructors _safe_istate: paco.

      Lemma safe_istate_monotone: monotone2 _safe_istate.
      Proof.
        ii. inv IN. econs; eauto.
        i. hexploit SAFE_NEXT; eauto.
        i. des.
        esplits; eauto.
      Qed.

      Definition safe_istate
        : DTime.t -> istate node -> Prop :=
        paco2 _safe_istate bot2.

    End SAFE_STATE.

    Inductive safe_state (tm: DTime.t): state -> Prop :=
      SafeState
        nd ist
        (SAFE_ISTATE: safe_istate nd tm ist)
      : safe_state tm (State nd ist).

    Inductive safe (node: t): Prop :=
      Safe
        (INIT_EX: exists ist_init,
            node.(init_istate) ist_init)
        (SAFE_ISTATE:
           forall ist tm
             (INIT_ST: node.(init_istate) ist),
             safe_istate node tm ist)
    .

  End NODE.
End Node.


Module NWSys.
  Section SYSTEM.
    Context {sysE: Type -> Type}.
    Context `{rnws_params}.

    Definition t : Type := list (@Node.t sysE).

    Definition wf (sys: t) : Prop :=
      <<WF_NODES: Forall Node.wf sys>> /\
      <<NODE_IPS_UNIQUE: List.NoDup
                           (List.map Node.ip_addr sys)>>.

    Record state: Type :=
      State {
          global_time: DTime.t ;
          network: NW.t ;
          nodes: list (@Node.state sysE) ;
        }.

    (* Definition state_wf *)
    (*            (node_wf: DTime.t -> @Node.state sysE -> Prop) *)
    (*            (st: state) : Prop := *)
    (*   <<WF_NW: NW.wf st.(network)>> /\ *)
    (*   <<WF_NODES: Forall (node_wf st.(global_time)) st.(nodes)>>. *)

    Inductive init (gtm_init: DTime.t) (sys: t)
      : state -> Prop :=
      Init
        nsts_init
        (INIT_NODE_STATES: Forall2 Node.init sys nsts_init)
      : init gtm_init sys (State gtm_init NW.init nsts_init).

    Inductive step: state -> list (tsp * events (nbE +' sysE)) -> state -> Prop :=
      Step
        gtm nw nsts
        nw1 dpms
        tess opkts nsts' nw'
        (NW_DISTR: NW.distr nw = (nw1, dpms))
        (LOCAL_STEPS: Forall4 (Node.step gtm dpms)
                              nsts tess opkts nsts')
        (NW_STEP: NW.gather nw1 (filtermap id opkts) nw')
      : step (State gtm nw nsts) tess (State (DTime.succ gtm) nw' nsts').

    Program Definition as_dsys (sys:t) (tm_init: nat) : DSys.t :=
      {| DSys.state := state ;
         DSys.num_sites := fun st => length st.(nodes);
         DSys.step := step ;
         DSys.initial_state :=
           fun st => init (DTime.of_ns tm_init) sys st ;
      |}.
    Next Obligation.
      inv STEP.
      hexploit Forall4_length; eauto. i. des. ss.
    Qed.

    Lemma wf_distr_msgs_to
          dpms ip
          (WF_DPMS: Forall (fun dpm => Packet.msg_wf (snd dpm)) dpms)
      : Forall Packet.msg_wf
               (Node.distr_msgs_to ip dpms).
    Proof.
      rewrite Forall_forall in *.
      intros pm IN_DISTR.
      unfold Node.distr_msgs_to in IN_DISTR.
      apply filtermap_in in IN_DISTR. des.
      destruct a as [ip_d pm'].
      hexploit WF_DPMS; eauto. ss.
      unfold Node.chget_pm_by_dest in *. ss. desf.
    Qed.

    Lemma safe_nodes_safe (sys: t) tm
          (SAFE_NODES: Forall Node.safe sys)
      : DSys.safe (as_dsys sys tm).
    Proof.
      econs; ss.
      - assert (ISTS_EX: forall n (N_UB: n < length sys),
                   exists nst,
                     option_rel1
                       (fun nd => Node.init nd nst)
                       (nth_error sys n)).
        { i. rewrite Forall_forall in SAFE_NODES.
          hexploit (nth_error_Some2 _ sys n); eauto.
          i. des. renames e1 NTH_EX into nd ND_N.

          hexploit SAFE_NODES.
          { eapply nth_error_In; eauto. }
          intro ND_SAFE.
          inv ND_SAFE. des.
          esplits. rewrite ND_N.
          econs. eauto.
        }
        apply exists_list in ISTS_EX. des.
        esplits. econs.

        instantiate (1:= l).
        eapply Forall2_nth.
        i. specialize (NTH_PROP n).
        destruct (nth_error sys n) as [nd|] eqn:ND_N.
        2: {
          rewrite nth_error_None2.
          { econs. }
          rewrite LIST_LEN.
          apply nth_error_None. ss.
        }
        hexploit (nth_error_Some2 _ l n).
        { rewrite LIST_LEN.
          apply nth_error_Some. congruence. }
        i. des. renames e1 NTH_EX into nst NST_N.
        rewrite NST_N. econs.
        eapply NTH_PROP. eauto.

      - destruct st_i as [? ? nsts].
        i. inv INIT.

        assert (SAFE_NSTS: Forall
                             (Node.safe_state (DTime.of_ns tm))
                             nsts).
        { apply Forall_nth. i.
          destruct (nth_error nsts n) as [nst|] eqn:NST_N.
          2: { ss. }
          hexploit Forall2_nth2; eauto.
          i. des.
          hexploit Forall_nth1; eauto. intro SAFE.
          ss.
          inv P_FA. econs.
          inv SAFE. eauto.
        }

        clear INIT_NODE_STATES.
        generalize NW.wf_init as WF_NW.
        depgen nsts.
        generalize NW.init as nw.
        generalize (DTime.of_ns tm) as gtm.

        pcofix CIH. i.
        pfold.

        assert(exists nw1 dpms,
                  <<DISTR: NW.distr nw = (nw1, dpms)>>).
        { esplits. apply surjective_pairing. }
        des.
        hexploit NW.wf_distr_preserve; eauto.
        intros (WF_NW1 & WF_DPMS). des.

        econs; ss.
        + (* progress *)

          assert (NODES_PROGRESS:
                    exists tes ops nsts',
                      <<NODE_STEPS:
                        Forall4 (Node.step gtm dpms)
                                nsts tes ops nsts'>> /\
                        <<WF_OUTPKTS: Forall (option_rel1 Packet.wf) ops>> /\
                        <<SAFE_NODES: Forall (Node.safe_state (DTime.succ gtm)) nsts'>>).
          {
            assert (AUX: forall n (LEN: n < length nsts),
                       exists (x: (tsp * events (nbE +' sysE)) *
                             (Packet.t?) * Node.state)
                         (nst: Node.state)
                       ,
                         let '(tes, op, nst') := x in
                    <<NST: nth_error nsts n = Some nst>> /\
                    <<SAFE_NST: Node.safe_state gtm nst>> /\
                    <<STEP: Node.step gtm dpms
                                      nst tes op nst'>> /\
                    <<WF_OP: option_rel1 Packet.wf op>> /\
                    <<SAFE_NST': Node.safe_state (DTime.succ gtm) nst'>>).
            { i.
              rewrite Forall_nth in SAFE_NSTS.
              hexploit (nth_error_Some2 _ nsts n); ss.
              i. des.
              renames e1 NTH_EX into nst NST.
              specialize (SAFE_NSTS n).
              rewrite NST in SAFE_NSTS. ss.

              cut (exists tes op nst',
                      Node.step gtm dpms nst tes op nst' /\
                      option_rel1 Packet.wf op /\
                      Node.safe_state (DTime.succ gtm) nst').
              { i. des.
                eexists (_, _, _).
                esplits; eauto. }

              inv SAFE_NSTS.
              punfold SAFE_ISTATE.
              2: { apply Node.safe_istate_monotone. }
              inv SAFE_ISTATE.
              hexploit (PROGRESS (Node.distr_msgs_to (Node.ip_addr nd) dpms)).
              { apply wf_distr_msgs_to. eauto. }
              i. des.
              hexploit SAFE_NEXT; eauto.
              { apply wf_distr_msgs_to; eauto. }
              i. des. pclearbot.

              esplits; eauto.
              - econs; eauto.
              - econs. eauto.
            }

            apply exists_list in AUX. des.
            pose (tes := map fst (map fst l)).
            pose (ops := map snd (map fst l)).
            pose (nsts' := map snd l).
            exists tes, ops, nsts'.
            esplits.
            - apply Forall4_nth. i.
              destruct (lt_ge_dec n (length l)).
              2: {
                subst tes ops nsts'.
                rewrite nth_error_None2 by nia.
                rewrite nth_error_None2.
                2: { do 2 rewrite map_length. nia. }
                rewrite nth_error_None2.
                2: { do 2 rewrite map_length. nia. }
                rewrite nth_error_None2.
                2: { rewrite map_length. nia. }
                econs.
              }

              hexploit (nth_error_Some2 _ l n); ss.
              i. des. rename NTH_EX into L_N.
              destruct e1 as [[tes1 op] nst'].
              hexploit NTH_PROP; eauto. i. des.

              subst tes ops nsts'.
              repeat rewrite Coqlib.list_map_nth.
              rewrite L_N, NST. ss.
              econs. eauto.

            - apply Forall_nth. i.
              subst ops.
              destruct (lt_ge_dec n (length l)).
              2: { rewrite nth_error_None2.
                   2: { do 2 rewrite map_length. ss. }
                   r. ss. }
              do 2 rewrite Coqlib.list_map_nth.
              hexploit (nth_error_Some2 _ l n); ss.
              i. des.
              rewrite NTH_EX. ss.
              exploit NTH_PROP; eauto. i. des.
              destruct e1 as [[]]. ss. des. eauto.

            - apply Forall_nth. i.
              subst nsts'.
              destruct (lt_ge_dec n (length l)).
              2: { rewrite nth_error_None2.
                   2: { rewrite map_length. ss. }
                   r. ss. }
              rewrite Coqlib.list_map_nth.
              hexploit (nth_error_Some2 _ l n); ss.
              i. des.
              rewrite NTH_EX. ss.
              exploit NTH_PROP; eauto. i. des.
              destruct e1 as [[]]. ss. des. eauto.
          }
          des.

          hexploit (NW.wf_gather_progress
                      nw1 (filtermap id ops)); eauto.
          { apply Forall_forall.
            intros pkt PKT_IN.
            rewrite Forall_forall in WF_OUTPKTS.
            apply filtermap_in in PKT_IN.
            unfold id in PKT_IN. des. subst.
            hexploit WF_OUTPKTS; eauto.
          }
          intro GATHER. des.
          esplits. econs; eauto.

        + i. right.
          inv STEP.
          rewrite NW_DISTR in DISTR. clarify.

          assert (<<WF_OUTPKTS: Forall (option_rel1 Packet.wf) opkts>> /\
                  <<SAFE': Forall (Node.safe_state (DTime.succ gtm)) nsts'>>).
          { cut (forall n,
                    (<<OP_N: nth_error opkts n = None>> /\
                     <<NST_N: nth_error nsts' n = None>>) \/
                    (exists nst tes op nst',
              <<NST: nth_error nsts n = Some nst>> /\
              <<TES: nth_error syse n = Some tes>> /\
              <<OP: nth_error opkts n = Some op>> /\
              <<NST': nth_error nsts' n = Some nst'>> /\
              <<WF_OP: option_rel1 Packet.wf op>> /\
              <<SAFE: Node.safe_state (DTime.succ gtm) nst'>>)).
            { intro AUX.
              splits.
              - apply Forall_nth. i.
                specialize (AUX n). des.
                + rewrite OP_N. ss.
                + rewrite OP. ss.
              - apply Forall_nth. i.
                specialize (AUX n). des.
                + rewrite NST_N. ss.
                + rewrite NST'. ss.
            }

            i.
            destruct (lt_ge_dec n (length nsts)).
            2: {
              left.
              hexploit Forall4_length; eauto. i. des.
              rewrite nth_error_None2 by nia.
              rewrite nth_error_None2 by nia.
              eauto.
            }

            right.
            hexploit (nth_error_Some2 _ nsts n); eauto.
            i. des. renames e1 NTH_EX into nst NST.
            hexploit Forall4_nth1; eauto. i. des.
            renames e2 e3 e4 into tes op nst'.
            renames NTH2 NTH3 NTH4 into TES OP NST'.
            rename P_FA into STEP.

            rewrite Forall_nth in SAFE_NSTS.
            specialize (SAFE_NSTS n).
            rewrite NST in SAFE_NSTS. ss.

            cut (option_rel1 Packet.wf op /\
                 Node.safe_state (DTime.succ gtm) nst').
            { i. des.
              esplits; eauto. }

            inv STEP.
            inv SAFE_NSTS. existT_elim. subst.
            punfold SAFE_ISTATE.
            2: { apply Node.safe_istate_monotone. }
            inv SAFE_ISTATE.
            hexploit SAFE_NEXT; eauto.
            { apply wf_distr_msgs_to. ss. }
            i. des. pclearbot.
            esplits; ss.
          }
          des.

          eapply CIH; eauto.
          eapply NW.wf_gather_preserve; eauto.
          apply Forall_forall.
          intros pkt PKT_IN.
          rewrite Forall_forall in WF_OUTPKTS.
          apply filtermap_in in PKT_IN.
          unfold id in PKT_IN. des. subst.
          hexploit WF_OUTPKTS; eauto.
    Qed.

  End SYSTEM.
End NWSys.
