From ITree Require Import ITree.
From compcert Require Import AST Memory Globalenvs Maps Values.

Require Import ZArith String List Lia.

Require Import sflib.
Require Import StdlibExt IntegersExt.
Require Import DiscreteTimeModel IPModel.

Require Import SysSem.
Require Import NWSysModel.
Require Import OSModel OSNodes.
Require Import RTSysEnv.
Require Import CProgEventSem.
Require Import SyncSysModel.
Require Import ProgSem.

Require Import PALSSystem.

From compcert Require Import Ctypes.
From compcert Require Import Clight.
Require Import ITreeTac.
Require Import CompcertLemmas.


Local Opaque Z.to_nat Z.of_nat.

Import ITreeNotations.
Import ListNotations.

(* TODO: move to another place *)
Notation appE := (obsE +' bsendE).


Module ActiveStandbyIPAxiom.
  Parameter ip_con_bs: ip_brep.
  Parameter ip_ctrl1_bs: ip_brep.
  Parameter ip_ctrl2_bs: ip_brep.
  Parameter ip_dev1_bs: ip_brep.
  Parameter ip_dev2_bs: ip_brep.
  Parameter ip_dev3_bs: ip_brep.
  Parameter ip_mcast_bs: ip_brep.

  Parameter ip_con: ip_t.
  Parameter ip_ctrl1: ip_t.
  Parameter ip_ctrl2: ip_t.
  Parameter ip_dev1: ip_t.
  Parameter ip_dev2: ip_t.
  Parameter ip_dev3: ip_t.
  Parameter ip_mcast: ip_t.

  Axiom ip_con_prop:
    IP.convert_brep ip_con_bs = Some ip_con /\
    IP.local_ip ip_con = true.
  Axiom ip_ctrl1_prop:
    IP.convert_brep ip_ctrl1_bs = Some ip_ctrl1 /\
    IP.local_ip ip_ctrl1 = true.
  Axiom ip_ctrl2_prop:
    IP.convert_brep ip_ctrl2_bs = Some ip_ctrl2 /\
    IP.local_ip ip_ctrl2 = true.
  Axiom ip_dev1_prop:
    IP.convert_brep ip_dev1_bs = Some ip_dev1 /\
    IP.local_ip ip_dev1 = true.
  Axiom ip_dev2_prop:
    IP.convert_brep ip_dev2_bs = Some ip_dev2 /\
    IP.local_ip ip_dev2 = true.
  Axiom ip_dev3_prop:
    IP.convert_brep ip_dev3_bs = Some ip_dev3 /\
    IP.local_ip ip_dev3 = true.
  Axiom ip_mcast_prop:
    IP.convert_brep ip_mcast_bs = Some ip_mcast /\
    IP.mcast_ip ip_mcast = true.

  Axiom task_ips_nodup:
    NoDup [ip_con; ip_ctrl1; ip_ctrl2; ip_dev1; ip_dev2; ip_dev3].

End ActiveStandbyIPAxiom.

Import ActiveStandbyIPAxiom.

(* active-standby constants *)
Module ActiveStandby.

  (* 50 ms *)
  Definition max_clock_skew: Z := 50000000.
  (* 70 ms *)
  Definition max_nw_delay: Z := 70000000.
  (* 10 ms *)
  Definition max_wait_delay: Z := 10000000.

  (* 400 ms *)
  (* Definition period: nat := Z.to_nat 400000000. *)
  Definition period: Z := 400000000.

  Definition port: Z := 3333.

End ActiveStandby.



Program Instance rnws_params_obj: rnws_params :=
  {| NWSysModel.max_nw_delay := Z.to_nat ActiveStandby.max_nw_delay;
     NWSysModel.max_clock_skew := Z.to_nat ActiveStandby.max_clock_skew;
     NWSysModel.max_wait_delay := Z.to_nat ActiveStandby.max_wait_delay;
  |}.
Next Obligation.
  unfold ActiveStandby.max_nw_delay. nia.
Qed.
Next Obligation.
  unfold ActiveStandby.max_clock_skew. nia.
Qed.
Next Obligation.
  unfold ActiveStandby.max_wait_delay. nia.
Qed.
Next Obligation.
  unfold ActiveStandby.max_nw_delay.
  r. rewrite Z2Nat.id by nia.
  range_stac.
Qed.
Next Obligation.
  unfold ActiveStandby.max_clock_skew.
  r. rewrite Z2Nat.id by nia.
  range_stac.
Qed.

Obligation Tactic := i.



Program Instance system_env_obj: SystemEnv :=
  {| max_num_tasks := 16 ;
     max_num_mcasts := 8 ;
     msg_size_k := 1 ;
     msg_size := 8 ;
     RTSysEnv.period := Z.to_nat ActiveStandby.period ;
     port := Z.to_nat ActiveStandby.port ;

     task_ips_brep :=
       [ip_con_bs; ip_ctrl1_bs; ip_ctrl2_bs;
       ip_dev1_bs; ip_dev2_bs; ip_dev3_bs] ;
     task_ips :=
       [ip_con; ip_ctrl1; ip_ctrl2;
       ip_dev1; ip_dev2; ip_dev3] ;

     mcasts := [(ip_mcast_bs, [1; 2])] ;
     mcast_ips := [ip_mcast] ;
  |}.
Next Obligation.
  ss. nia.
Qed.
Next Obligation.
  ss. nia.
Qed.
Next Obligation.
  ss. nia.
Qed.
Next Obligation.
  range_stac.
Qed.
Next Obligation.
  range_stac.
Qed.
Next Obligation.
  ss.
Qed.
Next Obligation.
  r. unfold ActiveStandby.period.
  rewrite Z2Nat.id by nia.
  r. ss.
Qed.
Next Obligation.
  simpl NWSysModel.max_nw_delay.
  simpl NWSysModel.max_clock_skew.
  simpl NWSysModel.max_wait_delay.
  unfold ActiveStandby.max_clock_skew, ActiveStandby.max_nw_delay,
  ActiveStandby.max_wait_delay,
  ActiveStandby.period.
  replace 2 with (Z.to_nat 2) by ss.
  rewrite <- Z2Nat.inj_mul by nia.
  rewrite <- Z2Nat.inj_add by nia.
  rewrite <- Z2Nat.inj_add by nia.
  rewrite <- Z2Nat.inj_lt by nia.
  ss.
Qed.
Next Obligation.
  unfold ActiveStandby.period.
  rewrite Z2Nat.id by nia.
  ss.
Qed.
Next Obligation.
  r. unfold ActiveStandby.port.
  rewrite Z2Nat.id by ss.
  ss.
Qed.
Next Obligation.
  econs.
  { apply ip_con_prop. }
  econs.
  { apply ip_ctrl1_prop. }
  econs.
  { apply ip_ctrl2_prop. }
  econs.
  { apply ip_dev1_prop. }
  econs.
  { apply ip_dev2_prop. }
  econs.
  { apply ip_dev3_prop. }
  econs.
Qed.
Next Obligation.
  econs.
  { apply ip_con_prop. }
  econs.
  { apply ip_ctrl1_prop. }
  econs.
  { apply ip_ctrl2_prop. }
  econs.
  { apply ip_dev1_prop. }
  econs.
  { apply ip_dev2_prop. }
  econs.
  { apply ip_dev3_prop. }
  econs.
Qed.
Next Obligation.
  apply task_ips_nodup.
Qed.
Next Obligation.
  econs.
  { ss. apply ip_mcast_prop. }
  econs.
Qed.
Next Obligation.
  econs.
  { apply ip_mcast_prop. }
  econs.
Qed.
Next Obligation.
  econs; ss. econs.
Qed.
Next Obligation.
  econs.
  { ss.
    econs.
    { nia. }
    econs.
    { nia. }
    econs.
  }
  econs.
Qed.
Next Obligation.
  nia.
Qed.
Next Obligation.
  unfold Packet.maxlen.
  nia.
Qed.



Definition get_user_input_ef: AST.external_function :=
  EF_external "get_user_input"
              (mksignature nil AST.Tint cc_default).
Definition check_demand_ef: AST.external_function :=
  EF_external "check_demand"
              (mksignature nil AST.Tint cc_default).
Definition use_resource_ef: AST.external_function :=
  EF_external "use_resource"
              (mksignature nil AST.Tvoid cc_default).
Definition write_log_ef: AST.external_function :=
  EF_external "write_log"
              (mksignature (AST.Tint :: nil)
                           AST.Tvoid cc_default).


Definition GetUserInput: extcallE int :=
  ExtcallEvent_Int "get_user_input" [].

Definition CheckDemand: extcallE int :=
  ExtcallEvent_Int "check_demand" [].

Definition UseResource: extcallE unit :=
  ExtcallEvent_Void "use_resource" [].

Definition WriteLog (log_val: Z): extcallE unit :=
  ExtcallEvent_Void "write_log" [Vint (Int.repr log_val)].


Notation tid_con := 0.
Notation tid_ctrl1 := 1.
Notation tid_ctrl2 := 2.
Notation tid_dev1 := 3.
Notation tid_dev2 := 4.
Notation tid_dev3 := 5.
Notation mid_mcast := 6.

(* Notation progE := (osE +' tlimE +' ActiveStandby.sysE). *)
(* Notation appE := (extcallE +' bsendE). *)

Definition toggle_msg: list byte :=
  Byte.repr 1 :: List.repeat Byte.zero 7.

Definition grant_msg: list byte :=
  Byte.repr 1 :: List.repeat Byte.zero 7.

Definition acq_msg: list byte :=
  Byte.repr 1 :: List.repeat Byte.zero 7.

Definition rel_msg: list byte :=
  Byte.repr 2 :: List.repeat Byte.zero 7.


(* TODO: move*)

Ltac simpl_itree_interp :=
  match goal with
  | |- context [ interp _ ?t ] =>
    let ITREE := fresh in
    let itr := fresh in
    remember t as itr eqn: ITREE; symmetry in ITREE;
    simpl_itree_hyp ITREE; subst itr
  end.



Ltac unfold_align :=
  unfold align_attr, Coqlib.align; s.

Lemma loadbytes_load_byte
      m blk ofs z
      (LBS: Mem.loadbytes m blk ofs 1 = Some ([Byte (Byte.repr z)]))
      (RANGE_Z: IntRange.sintz8 z)
  : Mem.load Mint8signed m blk ofs = Some (Vint (Int.repr z)).
Proof.
  erewrite Mem.loadbytes_load; eauto.
  - rewrite decode_val_signed_byte.
    rewrite Byte.signed_repr by range_stac.
    ss.
  - ss. solve_divide.
Qed.



Lemma unchanged_on_disjoint_ids
      ge1 ids1 ids2 m m'
      (UNCH: mem_unchanged_except (blocks_of ge1 ids1) m m')
      (DISJ: Coqlib.list_disjoint ids1 ids2)
  : Mem.unchanged_on (blocks_of ge1 ids2) m m'.
Proof.
  eapply Mem.unchanged_on_implies; eauto.
  clear - DISJ.
  unfold blocks_of. ii. des.
  cut (b <> b).
  { ss. }
  apply (@Genv.global_addresses_distinct
           _ _ ge1 id id0); eauto.
Qed.
