Require Import sflib.

Require Import String List.
Require Import Arith ZArith Lia.

Require Import StdlibExt IntegersExt.
Require Import IPModel DiscreteTimeModel IntByteModel.
Require Import NWSysModel.


Generalizable Variable sysE.


Notation Tid := nat (only parsing).

Definition resize_bytes (size: nat) (bs: bytes): bytes :=
  firstn size bs ++ List.repeat Byte.zero (size - length bs).

Lemma resize_bytes_length sz bs bs_r
      (RESIZED: resize_bytes sz bs = bs_r)
  : length bs_r = sz.
Proof.
  subst. unfold resize_bytes.
  rewrite app_length.
  rewrite repeat_length.
  destruct (le_lt_dec sz (length bs)).
  - rewrite firstn_length_le; ss.
    nia.
  - rewrite firstn_all2 by nia.
    nia.
Qed.


Definition base_time (prd: nat) (tm: nat): nat :=
  tm - Nat.modulo tm prd.

Definition base_time' (prd: nat) (tm: nat): nat :=
  tm / prd * prd.

Lemma base_times_equiv prd tm
      (PRD_POS: 0 < prd)
      (TIME_POS: 0 < tm)
  : base_time prd tm = base_time' prd tm.
Proof.
  unfold base_time, base_time'.
  rewrite (Nat.div_mod tm prd) at 1 by nia.
  rewrite Nat.add_sub. nia.
Qed.


Lemma div_and_mult_range a b
      (POS_B: 0 < b)
  : a - b <= a / b * b <= a.
Proof.
  split.
  - cut (exists r, r < b /\ a = (a / b) * b + r).
    { i. des. nia. }
    exists (Nat.modulo a b).
    split.
    { apply Nat.mod_upper_bound. nia. }
    rewrite mult_comm.
    apply Nat.div_mod. nia.
  - rewrite mult_comm.
    etransitivity.
    { apply Nat.div_mul_le. nia. }
    rewrite mult_comm.
    rewrite Nat.div_mul; nia.
Qed.

Lemma div_ub_inv a b c
      (* (POS_A: 0 <= a) *)
      (POS_B: 0 < b)
      (* (POS_C: 0 <= c) *)
      (COND: a / b < c)
  : a < c * b.
Proof.
  hexploit (div_and_mult_range a b); eauto. i.
  assert (a <= c * b) by nia.
  assert (~ a = c * b).
  { ii. subst a.
    clear - COND POS_B.
    rewrite Nat.div_mul in COND; nia. }
  nia.
Qed.


Lemma base_time_spec prd tm btm
      (PRD_POS: 0 < prd)
      (TIME_POS: 0 < tm)
  : btm = base_time prd tm <->
    Nat.divide prd btm /\ btm <= tm < btm + prd.
Proof.
  split; intro HYP.
  - subst.
    split.
    + unfold base_time.
      rewrite (Nat.div_mod tm prd) by nia.
      rewrite Nat.add_mod_idemp_r by nia.
      rewrite <- (plus_comm tm).
      rewrite (mult_comm prd).
      rewrite Nat.mod_add by nia.
      rewrite Nat.add_sub.
      apply Nat.divide_factor_r.
    + unfold base_time.
      split.
      * nia.
      * cut (tm mod prd < prd).
        { nia. }
        apply Nat.mod_upper_bound. nia.
  - destruct HYP as (DIV & RANGE1 & RANGE2).
    rewrite base_times_equiv; ss.
    unfold base_time'.
    r in DIV. des.
    generalize (lt_eq_lt_dec z (tm/prd)).
    destruct 1 as [[A | ?] | B]; subst; ss; exfalso.
    + hexploit (Nat.div_le_mono tm).
      2: { apply Nat.lt_le_incl. apply RANGE2. }
      { instantiate (1:= prd). nia. }
      replace (z * prd + prd) with ((z + 1) * prd) by nia.
      rewrite Nat.div_mul by nia.
      i.
      assert (DIV_VAL_EQ: tm / prd = z + 1) by nia.
      cut ( prd * (z + 1) <= tm ).
      { nia. }
      rewrite <- DIV_VAL_EQ.
      rewrite mult_comm.
      eapply div_and_mult_range; nia.
    + hexploit div_ub_inv; try apply B.
      { nia. }
      i. nia.
Qed.



Inductive abst_sendE {msgT: Set}: Type -> Type :=
| AbstSendEvent (tid: Tid) (msg: msgT): abst_sendE unit.


Definition bsendE: Type -> Type := @abst_sendE bytes.
Definition BSendEvent (tid_dest: nat) (msg: bytes)
  : bsendE unit :=
  AbstSendEvent tid_dest msg.


Class SystemEnv `{rnws_params} : Type :=
  {
  (* fixed hyper-parameters for middleware *)
  max_num_tasks: nat;
  max_num_mcasts: nat;
  msg_size_k: nat;
  (* msg_size := 8 * msg_size_k + 7; *)
  msg_size: nat;

  (* parameters specific to this system *)
  period: nat ;
  port: nat;

  task_ips_brep: list bytes ;
  task_ips: list ip_t ;
  mcasts: list (bytes * list Tid) ;
  mcast_ips: list ip_t ;

  (* conditions *)
  min_num_tasks: 0 < length task_ips ;
  num_tasks_bound: length task_ips <= max_num_tasks ;
  num_mcasts_bound: length mcast_ips <= max_num_mcasts ;

  range_max_num_tasks: IntRange.sint8 max_num_tasks ;
  range_max_num_mcasts: IntRange.sint8 max_num_mcasts ;

  range_valid_dest_ids:
    IntRange.sint8 (length task_ips + length mcast_ips) ;
  range_period: IntRange.uint64 period ;
  period_cond: 2 * max_clock_skew + max_nw_delay + max_wait_delay < period ;
  period_mul_10_lt_max:
    (Z.of_nat period * 10 < Int64.max_unsigned)%Z ;

  range_port: IntRange.sint port ;

  task_ips_convert_brep:
    Forall2 (fun bs ip => IP.convert_brep bs = Some ip)
            task_ips_brep task_ips ;

  task_ips_local_ip: Forall (IP.local_ip) task_ips ;
  task_ips_unique: List.NoDup task_ips ;

  mcast_ips_convert_brep:
    Forall2 (fun mc ip => IP.convert_brep (fst mc) = Some ip)
            mcasts mcast_ips ;
  mcast_ips_mcast_ip:
    Forall (IP.mcast_ip) mcast_ips ;
  mcast_ips_unique: List.NoDup mcast_ips ;

  mcast_members_valid:
    Forall (fun mc => Forall (fun tid_m => tid_m < length task_ips) (snd mc)) mcasts;


  msg_size_bound: msg_size <= (msg_size_k * 8 + 7);

  packet_length_bound: (msg_size_k * 8 + 16) < Packet.maxlen ;
  }.

Section SYS_ENV.
  (* Context `{msgT: Set}. *)
  Context `{SystemEnv}.
  Let msgT: Set := bytes.

  Definition num_tasks : nat := length task_ips.
  Definition num_mcasts : nat := length mcast_ips.

  Lemma num_mcasts_eq
    : num_mcasts = length mcasts.
  Proof.
    pose proof mcast_ips_convert_brep.
    hexploit Forall2_length; eauto.
  Qed.

  Definition max_msg_size := msg_size_k * 8 + 7.
  Definition max_pld_size: nat := max_msg_size + 9.
  Definition pld_size: nat := msg_size + 9.

  Definition MAX_TIME: nat :=
    Z.to_nat Int64.max_unsigned - period * 10.
  Definition MAX_TIME_Z: Z :=
    Int64.max_unsigned - Z.of_nat period * 10.

  Lemma max_time_to_z
    : Z.of_nat MAX_TIME = MAX_TIME_Z.
  Proof.
    pose proof period_mul_10_lt_max.
    unfold MAX_TIME, MAX_TIME_Z.

    rewrite Nat2Z.inj_sub by nia.
    rewrite Z2Nat.id by ss.
    rewrite Nat2Z.inj_mul.
    replace (Z.of_nat 5) with 5%Z by ss.
    reflexivity.
  Qed.


  Definition DELTA: nat := 2 * max_clock_skew + max_nw_delay.

  Definition dest_ips_brep: list bytes :=
    task_ips_brep ++ map fst mcasts.

  Definition dest_ips: list ip_t := task_ips ++ mcast_ips.

  Definition tid2ip (tid: Tid): ip_t :=
    nth tid dest_ips 0.

  Definition valid_task_id (tid: Tid): Prop :=
    tid < num_tasks.

  Definition valid_mcast_id (mid: Tid): Prop :=
    exists midx, mid = num_tasks + midx /\
            midx < num_mcasts.

  Definition valid_dest_id (dest_id: Tid): Prop :=
    dest_id < num_tasks + num_mcasts.

  Definition group_memflags (ginfo: bytes * (list Tid))
    : list bool :=
    imap (fun n _ => existsb (Nat.eqb n) (snd ginfo))
         0 (List.repeat tt num_tasks).

  Definition mcast_memflags: list (list bool) :=
    map group_memflags mcasts.

  Lemma mcast_memflags_spec
        mid midx mip_bs mems
        (MID: mid = num_tasks + midx)
        (MCAST: nth_error mcasts midx = Some (mip_bs, mems))
    : exists r_mf,
      <<MFLAG_ROW: nth_error mcast_memflags midx = Some r_mf>> /\
      <<MFLAG_ROW_LEN: length r_mf = num_tasks>> /\
      <<MFLAG_ROW_IFF:
          forall tid (VALID_TID: tid < num_tasks),
            nth_error r_mf tid = Some true <->
            In tid mems>>.
  Proof.
    assert (exists r_mf, <<ROW: nth_error mcast_memflags midx = Some r_mf>>).
    { apply Some_not_None.
      apply nth_error_Some.
      unfold mcast_memflags.
      rewrite map_length.
      apply nth_error_Some.
      congruence. }
    des.
    exists r_mf.
    split; auto.
    unfold mcast_memflags in ROW.
    rewrite map_nth_error_iff in ROW. des.
    subst. clarify.

    unfold group_memflags.
    splits.
    - rewrite imap_length.
      rewrite repeat_length. ss.
    - i. ss.
      rewrite imap_nth_error_iff.
      rewrite repeat_nth_error_Some by ss.
      ss.
      split.
      + i. clarify.
        rewrite existsb_exists in *. des.
        hexploit beq_nat_true; eauto. i. subst. ss.
      + intro IN.
        f_equal. apply existsb_exists.
        esplits.
        { eauto. }
        rewrite <- beq_nat_refl. ss.
  Qed.

  (* Arguments Nat.ltb: simpl nomatch. *)

  Lemma range_num_tasks
    : IntRange.sint8 num_tasks.
  Proof.
    pose proof range_valid_dest_ids as RANGE_VT.
    fold num_tasks in RANGE_VT.
    rr in RANGE_VT. rr.
    split.
    - transitivity 0%Z; ss. nia.
    - nia.
  Qed.

  Lemma range_num_mcasts
    : IntRange.sint8 num_mcasts.
  Proof.
    pose proof range_valid_dest_ids as RANGE_VT.
    fold num_mcasts in RANGE_VT.
    range_stac.
  Qed.

  Definition task_id_ip (tid: Tid) (ip: ip_t): Prop :=
    nth_error task_ips tid = Some ip.

  Definition mcast_id_ip (mid: Tid) (ip: ip_t): Prop :=
    exists midx, mid = num_tasks + midx /\
            nth_error mcast_ips midx = Some ip.

  Lemma valid_task_id_ip
        tid
        (VALID_TID: valid_task_id tid)
    : task_id_ip tid (tid2ip tid).
  Proof.
    r. unfold tid2ip.
    r in VALID_TID.
    hexploit nth_error_Some2; eauto. i. des.
    erewrite nth_error_nth; eauto.
    unfold dest_ips.
    rewrite nth_error_app1; eauto.
  Qed.

  Lemma valid_mcast_id_ip
        mid
        (VALID_MID: valid_mcast_id mid)
    : mcast_id_ip mid (tid2ip mid).
  Proof.
    r. unfold tid2ip.
    r in VALID_MID. des.
    exists midx. split; ss.
    hexploit nth_error_Some2; eauto. i. des.

    pose proof mcast_ips_convert_brep as CONV.
    eapply Forall2_nth2 in CONV; eauto.
    des.

    erewrite nth_error_nth; eauto.
    unfold dest_ips.
    (*   apply map_nth_error. eauto. } *)
    rewrite nth_error_app2; eauto.
    2: { fold num_tasks. nia. }
    fold num_tasks.
    replace (mid - num_tasks) with midx by nia.
    eauto.
  Qed.

  Lemma task_id_ip_comput
        tid ip
        (TASK_ID_IP: task_id_ip tid ip)
    : tid2ip tid = ip /\ IP.local_ip ip = true.
  Proof.
    r in TASK_ID_IP.
    unfold tid2ip.
    split.
    - erewrite nth_error_nth; eauto.
      unfold dest_ips.
      rewrite nth_error_app1; eauto.
      apply nth_error_Some. congruence.
    - pose proof task_ips_local_ip as FA.
      eapply Forall_nth in FA.
      rewrite TASK_ID_IP in FA. ss.
  Qed.

  Lemma mcast_id_ip_comput
        mid ip
        (MCAST_ID_IP: mcast_id_ip mid ip)
    : tid2ip mid = ip /\ IP.mcast_ip ip = true.
  Proof.
    r in MCAST_ID_IP. des.
    unfold tid2ip.
    split.
    - erewrite nth_error_nth; eauto.
      subst mid.
      unfold dest_ips.
      rewrite nth_error_app2.
      + rewrite minus_plus. eauto.
      + fold num_tasks. nia.
    - pose proof mcast_ips_mcast_ip as FA.
      eapply Forall_nth in FA.
      rewrite MCAST_ID_IP0 in FA. ss.
  Qed.

  Lemma mcast_id_ip_det
        mid mip1 mip2
        (MIP1: mcast_id_ip mid mip1)
        (MIP2: mcast_id_ip mid mip2)
    : mip1 = mip2.
  Proof.
    inv MIP1. inv MIP2. des.
    assert (x = x0) by nia.
    clarify.
  Qed.

  (* tid & mcast *)
  Definition dest_id_ip (tid: Tid) (ip: ip_t): Prop :=
    nth_error dest_ips tid = Some ip.

  Definition get_mcast_of (tid: Tid)
    : list Tid :=
    map fst (ifilter (fun _ mc_mems =>
                        existsb (Nat.eqb tid)
                                (snd mc_mems))
                     num_tasks mcasts).

  Lemma get_mcast_of_spec
        tid mid
        (MID_IN: In mid (get_mcast_of tid))
    : exists midx mip_bs mip mems,
      <<MCAST_GROUP_ID_EQ: mid = num_tasks + midx>> /\
      <<MCAST_MEMBER: nth_error mcasts midx = Some (mip_bs, mems)>> /\
      <<MCAST_IP: nth_error mcast_ips midx = Some mip>> /\
      <<CONV_IP_BREP: IP.convert_brep mip_bs = Some mip>> /\
      <<TID_IN_MEMBERS: In tid mems>>.
  Proof.
    unfold get_mcast_of in MID_IN.
    apply in_map_iff in MID_IN.
    destruct MID_IN as [[mid' [mip mems]] [MID_EQ IN_IFLT]].
    ss. subst mid'.
    apply ifilter_spec in IN_IFLT. des. ss.

    pose proof mcast_ips_convert_brep as CONV.
    eapply Forall2_nth1 in CONV; eauto. des. ss.

    esplits; eauto.
    apply existsb_exists in F_TRUE. des.
    hexploit beq_nat_true; eauto. i. subst. ss.
  Qed.

  Lemma member_impl_get_mcast_of
        mid midx mip_bs mems tid
        (MID_EQ: mid = num_tasks + midx)
        (MEMBERS: nth_error mcasts midx = Some (mip_bs, mems))
        (TID_MEMBER: In tid mems)
    : In mid (get_mcast_of tid).
  Proof.
    unfold get_mcast_of.
    apply in_map_iff.
    exists (mid, (mip_bs, mems)). ss.

    split; ss.
    apply ifilter_spec.
    esplits; eauto. ss.
    apply existsb_exists.
    esplits.
    { eauto. }
    apply Nat.eqb_refl.
  Qed.

  Definition mcast_member (tid mid: Tid): Prop :=
    In mid (get_mcast_of tid).

  Lemma task_ips_not_mcast
        tip
        (TASK_IP: In tip task_ips)
    : IP.mcast_ip tip = false.
  Proof.
    hexploit task_ips_local_ip; eauto.
    rewrite Forall_forall.
    intro FA. hexploit FA; eauto.
    intro LOCAL.
    generalize (IP.normal_mcast_disjoint tip).
    rewrite LOCAL. ss.
  Qed.

  Lemma dest_id_ip_inv_det
        id1 id2 ip
        (DEST1: dest_id_ip id1 ip)
        (DEST2: dest_id_ip id2 ip)
    : id1 = id2.
  Proof.
    r in DEST1. r in DEST2.
    unfold dest_ips in *.
    destruct (lt_ge_dec id1 (length task_ips)).
    - rewrite nth_error_app1 in DEST1 by ss.
      destruct (lt_ge_dec id2 (length task_ips)).
      + rewrite nth_error_app1 in DEST2 by ss.
        eapply NoDup_nth_error; eauto.
        * apply task_ips_unique.
        * congruence.
      + rewrite nth_error_app2 in DEST2 by ss.
        hexploit task_ips_not_mcast.
        { eapply nth_error_In; eauto. }
        intro MC.

        pose proof mcast_ips_mcast_ip as MC_MC.
        rewrite Forall_forall in MC_MC.
        hexploit MC_MC; eauto.
        { eapply nth_error_In; eauto. }
        i. congruence.
    - rewrite nth_error_app2 in DEST1 by ss.
      destruct (lt_ge_dec id2 (length task_ips)).
      + rewrite nth_error_app1 in DEST2 by ss.
        hexploit task_ips_not_mcast.
        { eapply nth_error_In; eauto. }
        intro MC.

        pose proof mcast_ips_mcast_ip as MC_MC.
        rewrite Forall_forall in MC_MC.
        hexploit MC_MC; eauto.
        { eapply nth_error_In; eauto. }
        i. congruence.
      + rewrite nth_error_app2 in DEST2 by ss.
        cut (id1 - length task_ips =
             id2 - length task_ips).
        { nia. }
        eapply NoDup_nth_error; eauto.
        * apply mcast_ips_unique.
        * eapply nth_error_Some; eauto. congruence.
        * congruence.
  Qed.


  Lemma mcast_member_valid
        tid mid
        (MCM: mcast_member tid mid)
    : exists mip, mcast_id_ip mid mip.
  Proof.
    unfold mcast_member in MCM.
    unfold get_mcast_of in MCM.
    apply get_mcast_of_spec in MCM.
    des.

    pose proof mcast_ips_convert_brep as CONV.
    eapply Forall2_nth1 in CONV; eauto. des.

    exists mip.
    r. esplits; eauto.
    (* apply map_nth_error_iff. *)
    (* esplits; eauto. *)
  Qed.


  Definition parse_msg (pld: list byte)
    : (nat * Tid * list byte)? :=
    match list_divide pld 8 with
    | None => None
    | Some (bs_tm, bs1) =>
      match bs1 with
      | [] => None
      | b_tid :: bs_data =>
        let dtm_i64: int64 := IntByte.of_bytes64 bs_tm in
        let dtm_n : nat := Z.to_nat (Int64.unsigned dtm_i64) in
        match Z_to_nat2 (Byte.signed b_tid) with
        | None => None
        | Some tid_s =>
          (* let msg := abst_msg tid_s tid_r bs_data in *)
          Some (dtm_n, tid_s, bs_data)
        end
      end
    end.

  Definition serialize_msg (sytm: nat) (tid: Tid) (msg: bytes)
    : bytes :=
    let sytm_i: int64 := IntNat.of_nat64 sytm in
    (IntByte.to_bytes64 sytm_i)
      ++ [Byte.repr (Z.of_nat tid)] ++ msg.

  Lemma serialize_parse_msg_inv
        tm tid bs bs_srl
        (RANGE_TM: IntRange.uint64 tm)
        (RANGE_TID: IntRange.sint8 tid)
        (SERIALIZE: serialize_msg tm tid bs = bs_srl)
    : parse_msg bs_srl = Some (tm, tid, bs).
  Proof.
    unfold serialize_msg in SERIALIZE. subst. ss.
    unfold parse_msg.
    rewrite list_divide_succ.
    2: { apply IntByte.to_bytes_length64. }

    rewrite Byte.signed_repr by range_stac.
    unfold Z_to_nat2.
    destruct (Z.ltb_spec (Z.of_nat tid) 0).
    { inv RANGE_TID. nia. }

    rewrite IntByte.to_bytes_inv64.
    unfold IntNat.of_nat64.
    rewrite Int64.unsigned_repr by range_stac.
    do 2 rewrite Nat2Z.id. ss.
  Qed.

  Lemma packet_length_bound_z
    : (Z.of_nat max_pld_size < Z.of_nat Packet.maxlen)%Z.
  Proof.
    pose proof packet_length_bound as PLB.
    apply Nat2Z.inj_lt in PLB.
    (* unfold Packet.maxlen in *. *)
    (* rewrite Z2Nat.id in PLB by nia. *)
    unfold max_pld_size, max_msg_size.
    nia.
  Qed.

  Lemma range_packet_maxlen
    : IntRange.sint Packet.maxlen.
  Proof.
    unf_ranges.
    unfold Packet.maxlen.
    rewrite Z2Nat.id by ss.
    ss.
  Qed.

  Lemma range_max_pld_size
    : IntRange.sint max_pld_size.
  Proof.
    pose proof packet_length_bound_z.
    pose proof range_packet_maxlen.
    range_stac.
  Qed.

  Lemma pld_size_bound
    : pld_size <= max_pld_size.
  Proof.
    unfold max_pld_size, pld_size.
    unfold max_msg_size.
    generalize msg_size_bound. nia.
  Qed.

  Lemma num_tasks_bound'
    : num_tasks <= max_num_tasks.
  Proof.
    pose proof num_tasks_bound.
    unfold num_tasks. ss.
  Qed.

  Lemma msg_size_bound'
    : msg_size <= max_msg_size.
  Proof.
    pose proof msg_size_bound.
    unfold max_msg_size. ss.
  Qed.

  Lemma range_pld_size
    : IntRange.sint pld_size.
  Proof.
    pose proof pld_size_bound.
    pose proof range_max_pld_size.
    range_stac.
  Qed.

  Lemma range_msg_size
    : IntRange.sint msg_size.
  Proof.
    pose proof range_pld_size.
    unfold pld_size in *.
    range_stac.
  Qed.

  Lemma range_max_msg_size
    : IntRange.sint max_msg_size.
  Proof.
    pose proof range_max_pld_size.
    unfold max_pld_size, max_msg_size in *.
    range_stac.
  Qed.

  Lemma serialize_msg_size_eq
        tm tid bs bs_srl
        (SERIALIZE: serialize_msg tm tid bs = bs_srl)
    : length bs_srl = length bs + 9.
  Proof.
    unfold serialize_msg in SERIALIZE.
    subst. do 2 rewrite app_length. ss.
    rewrite IntByte.to_bytes_length64. nia.
  Qed.

  Lemma serialize_msg_size_lt_maxlen
        tm tid bs bs_srl
        (* (RANGE_TM: IntRange.uint64 tm) *)
        (* (RANGE_TID: IntRange.sint8 tid) *)
        (SERIALIZE: serialize_msg tm tid bs = bs_srl)
        (MSG_LENGTH: length bs <= msg_size)
    : length bs_srl < Packet.maxlen.
  Proof.
    assert (length bs_srl <= pld_size).
    { unfold serialize_msg in SERIALIZE.
      subst. do 2 rewrite app_length. ss.
      rewrite IntByte.to_bytes_length64.
      unfold pld_size. nia.
    }
    unfold pld_size in *.
    pose proof (msg_size_bound).
    pose proof (packet_length_bound). nia.
  Qed.

  (* true => available, false => not *)
  Definition check_send_hist_read
             (sh: list bool) (tid: Tid): bool :=
    match nth_error sh tid with
    | Some b => negb b
    | None => false
    end.

  Definition check_send_hist_write
             (sh: list bool) (tids: list Tid)
    : list bool :=
    imap (fun tid_ent hist_ent =>
            if existsb (Nat.eqb tid_ent) tids
            then true else hist_ent)
         0 sh.

  Definition check_send_hist (sh: list bool)
             (id_dest: Tid)
    : (list bool)? :=
    if id_dest <? num_tasks then
      if check_send_hist_read sh id_dest then
        Some (check_send_hist_write sh [id_dest])
      else None
    else
      match nth_error mcasts (id_dest - num_tasks) with
      | Some (_, members) =>
        if andb_all (map (check_send_hist_read sh)
                         members) then
          Some (check_send_hist_write sh members)
        else None
      | None => None
      end
  .

  Lemma check_send_hist_write_spec
        sh tids sh'
        (SH_LEN: length sh = num_tasks)
        (SH_WRITE: check_send_hist_write sh tids = sh')
    : forall tid (VALID: tid < num_tasks),
      (<<IN_TIDS: In tid tids>> /\
       <<SH_TRUE: nth_error sh' tid = Some true>>) \/
      (<<NOT_IN_TIDS: ~ In tid tids>> /\
       <<SH_INVAR: nth_error sh' tid = nth_error sh tid>>).
  Proof.
    i. hexploit (In_dec Nat.eq_dec tid tids).
    intros [IN | NOT_IN].
    - left. esplits; ss.
      unfold check_send_hist_write in SH_WRITE.
      subst sh'.
      rewrite imap_nth_error_iff. ss.
      hexploit (nth_error_Some2 _ sh tid).
      { nia. }
      i. des.
      rewrite NTH_EX. ss.

      replace (existsb (Nat.eqb tid) tids) with true; ss.
      symmetry.
      apply existsb_exists.
      exists tid.
      split; ss.
      apply Nat.eqb_refl.

    - right. esplits; ss.
      unfold check_send_hist_write in SH_WRITE.
      subst sh'.
      rewrite imap_nth_error_iff. ss.

      replace (existsb (Nat.eqb tid) tids) with false.
      { destruct (nth_error sh tid); ss. }
      symmetry.
      apply existsb_false_iff.
      apply Forall_forall. i.
      destruct (Nat.eqb_spec tid x); ss.
      subst. ss.
  Qed.


  Lemma check_send_hist_Some
        sh id_d sh'
        (SEND_HIST_LEN: length sh = num_tasks)
        (SH: check_send_hist sh id_d = Some sh')
    : <<SEND_HIST_LEN': length sh' = num_tasks>> /\
      ((<<DEST_TASK_ID: valid_task_id id_d>> /\
        <<SEND_AVAILABLE: nth_error sh id_d = Some false>> /\
        <<UPD_HIST: nth_error sh' id_d = Some true>> /\
        <<UPD_HIST_OTHERS:
          forall tid
            (TID_NEQ: tid <> id_d),
            nth_error sh' tid = nth_error sh tid>>)
       \/
       (<<DEST_MCAST_ID: valid_mcast_id id_d>> /\
        <<UPD_HIST:
          forall tid
            (* (VALID_TID: valid_task_id tid) *)
            (MEMBER: mcast_member tid id_d),
            valid_task_id tid /\
            nth_error sh tid = Some false /\
            nth_error sh' tid = Some true >> /\
        <<UPD_HIST_OTHERS:
              forall tid
                (NOT_MEMBER: ~ mcast_member tid id_d),
                nth_error sh' tid = nth_error sh tid>>)).
  Proof.
    unfold check_send_hist in SH.
    destruct (Nat.ltb_spec id_d num_tasks).
    { (* unicast *)
      unfold check_send_hist_read in SH.
      hexploit (nth_error_Some2 _ sh id_d).
      { nia. }
      i. des. renames e1 NTH_EX into sh_d SH_D.
      rewrite SH_D in SH.
      destruct sh_d; ss.
      clarify.

      pose (sh' := check_send_hist_write sh [id_d]).
      fold sh'.
      assert (SH'_LEN: length sh' = num_tasks).
      { subst sh'.
        unfold check_send_hist_write.
        rewrite imap_length. ss. }
      splits; ss.
      left.

      hexploit (check_send_hist_write_spec sh [id_d]); eauto.
      ss. i. des; ss.
      2: { exfalso.
           apply NOT_IN_TIDS. eauto. }

      splits; ss.
      i.
      destruct (lt_ge_dec tid num_tasks).
      2: { rewrite nth_error_None2 by nia.
           rewrite nth_error_None2 by nia.
           ss. }

      hexploit (check_send_hist_write_spec sh [id_d]); eauto.
      i. des; ss.
      des; ss. clarify.
    }
    { (* multicast *)
      pose (idx := id_d - num_tasks).
      fold idx in SH.
      destruct (nth_error mcasts idx)
        as [[mip_bs mems]|] eqn: MCAST_IDX; ss.

      assert (CHK_TRUE: andb_all (map (check_send_hist_read sh) mems) = true).
      { desf. }

      rewrite CHK_TRUE in SH. clarify.

      pose (sh' := check_send_hist_write sh mems).
      fold sh'.
      assert (SH'_LEN: length sh' = num_tasks).
      { subst sh'.
        unfold check_send_hist_write.
        rewrite imap_length. ss. }
      splits; ss.

      right.
      rewrite andb_all_true_iff in CHK_TRUE.

      splits.
      - r. exists idx.
        pose proof mcast_ips_convert_brep as CONV_M.
        apply Forall2_length in CONV_M.
        split.
        + nia.
        + unfold num_mcasts. rewrite <- CONV_M.
          apply nth_error_Some. unfold bytes in *. congruence.
      - intros tid MCAST_MEM.
        r in MCAST_MEM.
        eapply get_mcast_of_spec in MCAST_MEM. des.
        assert (midx = idx) by nia.
        subst midx.
        assert (mip_bs0 = mip_bs /\ mems0 = mems).
        { clarify. }
        des. subst mip_bs0 mems0.

        assert (CH_TID_TRUE: check_send_hist_read sh tid = true).
        { apply CHK_TRUE.
          apply in_map. eauto. }

        unfold check_send_hist_read in CH_TID_TRUE.
        desf.
        destruct b; ss.

        assert (VALID_TID: tid < num_tasks).
        { rewrite <- SEND_HIST_LEN.
          apply nth_error_Some. congruence. }

        split; ss.
        subst sh'.
        hexploit (check_send_hist_write_spec sh mems); eauto.
        i. des.
        2: { congruence. }
        ss.
      - i.
        destruct (lt_ge_dec tid num_tasks).
        2: { rewrite nth_error_None2 by nia.
             rewrite nth_error_None2 by nia. ss. }

        r in NOT_MEMBER.
        subst sh'.
        hexploit (check_send_hist_write_spec sh mems); eauto.
        i. des; ss.
        exfalso.
        apply NOT_MEMBER. r.
        eapply member_impl_get_mcast_of; eauto.
        nia.
    }
  Qed.

  Lemma check_send_hist_None
        sh id_d
        (SEND_HIST_LENGTH: length sh = num_tasks)
        (SH_NONE: check_send_hist sh id_d = None)
    : <<INVALID_DEST_ID: ~ valid_dest_id id_d>> \/
      (<<DEST_TASK_ID: valid_task_id id_d>> /\
       <<SEND_DONE: nth_error sh id_d = Some true>>) \/
      (<<DEST_MCAST_ID: valid_mcast_id id_d>> /\
       exists tid_sent,
         <<MEMBER: mcast_member tid_sent id_d>> /\
         (<<TID_INVALID: ~ valid_task_id tid_sent>> \/
          <<SEND_DONE: nth_error sh tid_sent = Some true>>)).
  Proof.
    unfold check_send_hist in SH_NONE.
    destruct (Nat.ltb_spec id_d num_tasks).
    { unfold check_send_hist_read in SH_NONE.
      hexploit (nth_error_Some2 _ sh id_d).
      { nia. }
      i. des. renames e1 NTH_EX into sh_d SH_D.
      rewrite SH_D in SH_NONE.
      destruct sh_d; ss. eauto.
    }
    pose proof mcast_ips_convert_brep as CONV_M.
    apply Forall2_length in CONV_M.

    destruct (nth_error mcasts (id_d - num_tasks))
      as [[mid mems]|] eqn:MCASTS_N.
    { destruct (andb_all (map (check_send_hist_read sh) mems))
               eqn: ANDB_ALL; ss.
      rewrite andb_all_false_iff in ANDB_ALL.
      apply in_map_iff in ANDB_ALL. des.

      right. right.
      esplits.
      - r. exists (id_d - num_tasks).
        split.
        + nia.
        + unfold num_mcasts. rewrite <- CONV_M.
          apply nth_error_Some. unfold bytes in *. congruence.
      - r. eapply member_impl_get_mcast_of; eauto.
        nia.
      - unfold check_send_hist_read in ANDB_ALL.
        destruct (nth_error sh x) eqn:SH_X.
        2: { eapply nth_error_None in SH_X.
             left. unfold valid_task_id. nia. }
        right. destruct b; ss.
    }
    { left. r.
      unfold valid_dest_id.
      eapply nth_error_None in MCASTS_N.
      fold num_mcasts in *.
      unfold bytes in *.
      nia. }
  Qed.

End SYS_ENV.


Section SKWD_BASE_TIME.
  Context `{SystemEnv}.

  Definition get_skwd_base_time
             (period: nat) (gtm: DTime.t): nat :=
    base_time period (DTime.to_ns_rd gtm + max_clock_skew).

  Definition exact_skwd_base_time
             (period: nat)
             (gtm: DTime.t) : nat? :=
    match DTime.to_ns_exact gtm with
    | None => None
    | Some gtm_ns =>
      let sytm_cand := gtm_ns + max_clock_skew in
      if (sytm_cand mod period =? O)%nat
      then Some sytm_cand else None
    end.

  Section LEMMAS.

    Let prd := period.
    Let MAX_CSKEW_POS: 0 < max_clock_skew.
    Proof. apply max_clock_skew_pos. Qed.
    Let PRD_COND: 2 * max_clock_skew + max_nw_delay + max_wait_delay < prd.
    Proof. apply period_cond. Qed.

    Lemma base_time_mono
          (tm1 tm2: nat)
          (LE: tm1 <= tm2)
      : base_time prd tm1 <= base_time prd tm2.
    Proof.
      unfold base_time.
      hexploit (Nat.div_mod tm1 prd).
      { nia. }
      hexploit (Nat.div_mod tm2 prd).
      { nia. }
      intros TM2 TM1.
      replace (tm1 - tm1 mod prd) with
          (prd * (tm1 / prd)) by nia.
      replace (tm2 - tm2 mod prd) with
          (prd * (tm2 / prd)) by nia.
      clear TM1 TM2.
      cut (tm1 / prd <= tm2 / prd).
      { nia. }
      apply Nat.div_le_mono; ss.
      nia.
    Qed.

    Lemma get_skwd_base_time_mono
          (tm1 tm2: DTime.t)
          (TM_LE: tm1 <= tm2)
      : get_skwd_base_time prd tm1 <=
        get_skwd_base_time prd tm2.
    Proof.
      hexploit (DTime_to_ns_rd_le_mono tm1 tm2); eauto.
      i. unfold get_skwd_base_time.
      apply base_time_mono.
      nia.
    Qed.

    Lemma get_skwd_base_time_iff
          tm sbt
      : get_skwd_base_time prd tm = sbt <->
        (DTime.of_ns (sbt - max_clock_skew) <= tm
         < DTime.of_ns (sbt + prd - max_clock_skew) /\
         Nat.divide prd sbt).
    Proof.
      pose proof DTime.units_per_ns_pos as UNITS_POS.
      split.
      - unfold get_skwd_base_time.
        intros BASE_TIME. symmetry in BASE_TIME.
        apply base_time_spec in BASE_TIME; cycle 1.
        { nia. }
        { nia. }

        destruct BASE_TIME as (SBT_DIV & R1 & R2).

        (* assert (TM_DIV_MUL: tm / DTime.units_per_ns * DTime.units_per_ns <= tm). *)
        (* { apply div_and_mult_range. nia. } *)

        splits.
        + hexploit (div_and_mult_range
                      tm DTime.units_per_ns); eauto.
          intros TM_DIV_MUL.

          ss. unfold DTime.to_ns_rd in *.
          assert (AUX1: sbt * DTime.units_per_ns <=
                        (tm / DTime.units_per_ns + max_clock_skew) *
                        DTime.units_per_ns) by nia.
          rewrite Nat.mul_add_distr_r in AUX1. nia.
        + clear R1.
          pose (n := DTime.to_ns_rd tm).
          fold n in R2.

          assert (EQ: DTime.to_ns_rd tm = n) by ss.
          eapply DTime_to_ns_rd_spec in EQ.
          destruct EQ as (r & TM_EQ & RANGE_R).

          assert (AUX1: (n + max_clock_skew) *
                        DTime.units_per_ns + r <
                        (sbt + prd) * DTime.units_per_ns)
            by nia.
          ss. nia.
        + ss.

      - intros (RANGE & DIV).
        unfold get_skwd_base_time.
        symmetry.
        apply base_time_spec.
        { nia. }
        { nia. }

        hexploit (DTime_to_ns_rd_spec tm); eauto.
        intros (R & TM_EQ & RANGE_R).
        destruct tm as [u]; ss.

        splits; ss.
        + nia.
        + nia.
    Qed.


    Lemma get_skwd_base_time_range
          tm sbt
          (SKWD_BASE_TIME: sbt = get_skwd_base_time prd tm)
      : DTime.of_ns (sbt - max_clock_skew) <= tm
        < DTime.of_ns (sbt + prd - max_clock_skew).
    Proof.
      symmetry in SKWD_BASE_TIME.
      apply get_skwd_base_time_iff in SKWD_BASE_TIME.
      des. eauto.
    Qed.


    Lemma exact_skwd_base_time_None_iff (t: DTime.t)
          (TIME_POS: 0 < t)
      : exact_skwd_base_time prd t = None <->
        (exists sbt,
           (sbt - max_clock_skew) * DTime.units_per_ns < t <
           (sbt + prd - max_clock_skew) * DTime.units_per_ns
           /\ Nat.divide prd sbt).
    Proof.
      split.
      - intro EXACT_NONE.
        unfold exact_skwd_base_time in EXACT_NONE.
        destruct (DTime.to_ns_exact t)
          as [tm_ns|] eqn: EXACT.
        + destruct (Nat.eqb_spec ((tm_ns + max_clock_skew) mod prd) 0) as [EQ_Z | NEQ_Z].
          { congruence. }

          eapply DTime_to_ns_exact_spec in EXACT.
          destruct t as [u]. ss. subst.

          hexploit (Nat.div_mod
                      (tm_ns + max_clock_skew) prd).
          { nia. }

          remember ((tm_ns + max_clock_skew) / prd) as q.
          remember ((tm_ns + max_clock_skew) mod prd) as r.
          assert (RANGE_R: 0 < r < prd).
          { split.
            { nia. }
            subst r.
            apply Nat.mod_bound_pos; nia.
          }

          intros TM_NS_EQ.
          exists (prd * q).
          splits; ss.
          * nia.
          * nia.
          * apply Nat.divide_factor_l.
        + apply DTime_to_ns_exact_None_iff in EXACT.
          destruct EXACT as (tm_ns & r & T_EQ & _ & RANGE_R).
          destruct t as [u]; ss. subst u.

          assert (SBT: exists sbt, sbt = base_time prd (tm_ns + max_clock_skew)).
          { esplits; ss. }
          des.
          eapply base_time_spec in SBT; cycle 1.
          { nia. }
          { nia. }
          destruct SBT as (SBT_DIV & RANGE_SBT).

          exists sbt. splits; ss; nia.

      - intros (sbt & RANGE_SBT & SBT_DIV).
        unfold exact_skwd_base_time.
        unfold DTime.to_ns_exact.

        destruct t as [u]; ss.
        destruct (Nat.eqb_spec (u mod DTime.units_per_ns) 0) as [MOD_Z|]; ss.
        rewrite Nat.mod_divide in MOD_Z by nia.
        r in MOD_Z.

        desH MOD_Z. rename z into z1. subst u.
        assert (RANGE2: sbt < z1 + max_clock_skew < sbt + prd).
        { nia. }

        (* assert (RANGE2: (sbt - max_clock_skew) < z1 < sbt + prd - max_clock_skew). *)
        (* { nia. } *)
        clear RANGE_SBT.

        unfold DTime.to_ns_rd. ss.
        rewrite Nat.div_mul by nia.

        destruct (Nat.eqb_spec ((z1 + max_clock_skew) mod prd) 0) as [MOD_Z|]; ss.

        exfalso.
        rewrite Nat.mod_divide in MOD_Z by nia.
        r in MOD_Z.
        desH MOD_Z. rename z into z2.
        rewrite MOD_Z in RANGE2.

        r in SBT_DIV.
        desH SBT_DIV. subst sbt.
        cut (z < z2 < (z + 1)).
        { nia. }
        nia.
    Qed.

    Lemma exact_skwd_base_time_iff
          (t: DTime.t) sbt
          (* (TIME_LB: DTime.of_ns (prd - max_clock_skew) <= t) *)
      : exact_skwd_base_time prd t = Some sbt <->
        (0 < sbt /\
         (* DTime.of_ns (prd - max_clock_skew) <= t /\ *)
         (t:nat) = (sbt - max_clock_skew) * DTime.units_per_ns /\
         Nat.divide prd sbt).
    Proof.
      split; intro X.
      - unfold exact_skwd_base_time in X.
        unfold DTime.to_ns_exact in X.
        desf.
        rewrite Nat.add_sub.
        unfold DTime.to_ns_rd.
        rewrite Nat.mul_comm.
        splits.
        + assert (EXACT: Nat.divide DTime.units_per_ns
                                    (DTime.units t)).
          { apply Nat.mod_divide.
            { pose proof DTime.units_per_ns_pos. nia. }
            apply beq_nat_true. ss. }
          rr in EXACT. des.
          ss. rewrite EXACT.
          cut (prd - max_clock_skew <= z).
          { nia. }

          erewrite DTime_to_ns_rd_eq_exact in *; eauto.

          assert (EXACT2: Nat.divide prd (z + max_clock_skew)).
          { apply Nat.mod_divide.
            { pose proof DTime.units_per_ns_pos. nia. }
            apply beq_nat_true. ss. }

          rr in EXACT2.
          rename z into y. des.
          cut (prd <= y + max_clock_skew).
          { nia. }
          destruct z; nia.
        + apply Nat.div_exact.
          * pose proof DTime.units_per_ns_pos.
            nia.
          * apply beq_nat_true. ss.
        + assert (T: exists n, (t:nat) = DTime.units_per_ns * n).
          { apply Nat.mod_divides.
            - pose proof DTime.units_per_ns_pos. nia.
            - apply beq_nat_true. ss. }
          des. rewrite Nat.mul_comm in T.
          rewrite (DTime_to_ns_rd_eq_exact n t) in * by ss.
          apply Nat.mod_divide.
          { nia. }
          cut (t / DTime.units_per_ns = n).
          { intro R. rewrite R.
            apply beq_nat_true. ss. }
          rewrite T.
          apply Nat.div_mul.
          pose proof DTime.units_per_ns_pos. nia.
      - destruct X as [? [T_EQ SBT_SYNC]].
        unfold exact_skwd_base_time.
        unfold DTime.to_ns_exact.
        rewrite T_EQ.
        rewrite Nat.mod_mul. ss.

        erewrite DTime_to_ns_rd_eq_exact; eauto.
        2: { pose proof DTime.units_per_ns_pos.
             nia. }

        assert (max_clock_skew <= sbt).
        { rr in SBT_SYNC. des. subst.
          destruct z; nia. }
        rewrite Nat.sub_add by nia.
        apply Nat.mod_divide in SBT_SYNC.
        2: { nia. }
        rewrite SBT_SYNC. ss.

        (* assert (prd <= sbt). *)
        (* { pose proof DTime.units_per_ns_pos. *)
        (*   nia. } *)
        (* rewrite Nat.sub_add by nia. *)
        (* apply Nat.mod_divide in SBT_SYNC. *)
        (* 2: { nia. } *)
        (* rewrite SBT_SYNC. ss. *)
    Qed.

    Lemma exact_skwd_impl_get
          tm tm_ex
          (EXACT: exact_skwd_base_time period tm = Some tm_ex)
      : get_skwd_base_time period tm = tm_ex.
    Proof.
      apply exact_skwd_base_time_iff in EXACT.
      des.
      destruct tm as [u]. ss. subst u.
      apply get_skwd_base_time_iff. ss.
      pose proof DTime.units_per_ns_pos.

      splits.
      - nia.
      - nia.
      - ss.
    Qed.

    Lemma skwd_time_range_almost_overwrap
          (tm: DTime.t)
          sbt1 sbt2
          (SYNC1: Nat.divide prd sbt1)
          (SYNC2: Nat.divide prd sbt2)
          (RANGE1: (sbt1 - max_clock_skew) *
                   DTime.units_per_ns <= tm <
                   (sbt1 + prd - max_clock_skew) *
                   DTime.units_per_ns)
          (RANGE2: (sbt2 - max_clock_skew) *
                   DTime.units_per_ns < tm <=
                   (sbt2 + prd - max_clock_skew) *
                   DTime.units_per_ns)
      : sbt1 = sbt2 \/
        (sbt1 = sbt2 + prd /\
         (sbt1 - max_clock_skew) * DTime.units_per_ns = tm).
    Proof.
      destruct RANGE2 as [TM_LB TM_UB].
      apply le_lt_or_eq in TM_UB.

      assert (F1: get_skwd_base_time prd tm = sbt1).
      { apply get_skwd_base_time_iff; ss. }

      desH TM_UB.
      - left.
        cut (get_skwd_base_time prd tm = sbt2).
        { i. clarify. }
        apply get_skwd_base_time_iff; eauto. ss.
        split; ss. nia.
      - right.
        cut (get_skwd_base_time prd tm = (sbt2 + prd)).
        { i.
          cut (sbt1 = sbt2 + prd).
          { split; auto.
            congruence. }
          clarify.
        }

        apply get_skwd_base_time_iff. ss.
        split.
        2: { apply Nat.divide_add_r; auto.
             apply Nat.divide_refl. }
        rewrite TM_UB. ss.
        split.
        { nia. }
        clear - PRD_COND.
        pose proof DTime.units_per_ns_pos.
        nia.
    Qed.



    (* Lemma lt_maxtime_nxt_in_range' *)
    (*       cbt' *)
    (*       (CBT_LT: cbt' < MAX_TIME) *)
    (*   : cbt' + period <= Z.to_nat Int64.max_unsigned. *)
    (* Proof. *)
    (*   revert cbt' CBT_LT. *)
    (*   unfold MAX_TIME. *)
    (*   i. nia. *)
    (* Qed. *)


    Lemma lt_maxtime_nxt_in_range
      : forall cbt'
          (CBT_LT: cbt' < MAX_TIME),
        IntRange.uint64 (cbt' + period).
    Proof.
      i.
      cut (Z.of_nat (cbt' + period) <
           MAX_TIME_Z + Z.of_nat period)%Z.
      { clear.
        unfold MAX_TIME_Z.
        i. range_stac. }
      pose proof max_time_to_z. nia.
    Qed.

    (* Lemma pld_size_lt_intmax *)
    (*   : pld_size < Z.to_nat Int.max_signed. *)
    (* Proof. *)
    (*   pose proof msg_size_bound as MSIZE_BD. *)
    (*   eapply le_lt_trans with (m:= max_pld_size). *)
    (*   { unfold pld_size, max_pld_size. ss. *)
    (*     unfold max_msg_size. nia. } *)
    (*   eapply lt_trans with (m:=Packet.maxlen). *)
    (*   { pose proof packet_length_bound. *)
    (*     unfold max_pld_size, max_msg_size. nia. } *)
    (*   { unfold Packet.maxlen. *)
    (*     apply Z2Nat.inj_lt; ss. } *)
    (* Qed. *)

  End LEMMAS.
End SKWD_BASE_TIME.
