From ITree Require Import ITree.
From compcert Require Coqlib.
From compcert Require Import
     AST Memory Globalenvs Maps Values Linking
     Ctypes Clight Clightdefs.
From Paco Require Import paco.

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
Require Import LinkLemmas.
Require Import MWITree.

Require Import config_prm main_prm SystemProgs.
Require Import VerifProgBase.
Require Import MWLinkInversion.
Require Import PALSSystem.

Require Import ctrl.
Require Import AcStSystem.

Require Import SpecConsole SpecController SpecDevice.
Require Import SpecSingleController SpecDummy.
Require Import SyncSysNBModel.
Require Import FMSim.

Require Import ZArith String Bool List Lia.
Require Import RelationClasses.
Require Import Classical.

Require Import ITreeTac.

Local Opaque Z.to_nat Z.of_nat PTree.combine.

Import ITreeNotations.
Import ListNotations.

Import ActiveStandby.

Set Nested Proofs Allowed.


Ltac condtac :=
  match goal with
  | [|- context[if ?c then _ else _]] =>
    let COND := fresh "COND" in
    destruct c eqn:COND
  end.

Ltac refl := reflexivity.
Ltac etrans := etransitivity.
Ltac congr := congruence.


Section SingleControllerRef.
  Hint Constructors option_rel2: core.
  Variable tm_init: nat.

  Let mcasts := [[tid_ctrl1; tid_ctrl2]].
  Let sntz := fun bs => Some (resize_bytes 8 bs).

  Definition node_is_on (node: (@SNode.state obsE bytes)?): bool :=
    match node with
    | Some (SNode.State _ _ _ (Some _)) => true
    | _ => false
    end.

  Definition no_hb_recieved (node: (@SNode.state obsE bytes)?): bool :=
    match node with
    | Some (SNode.State tid _ inb (Some _)) =>
      match nth (3 - tid) inb None with
      | None => true
      | _ => false
      end
    | _ => false
    end.

  Definition ctrl_fail_src (ctrl ctrl': (@SNode.state obsE bytes)?): bool :=
    node_is_on ctrl && negb (node_is_on ctrl').

  Definition nb_src (nodes1 nodes2: list (@SNode.state obsE bytes)): bool :=
    ctrl_fail_src (nth_error nodes1 1) (nth_error nodes2 1).

  Definition ctrl_fail_tgt (ctrl1 ctrl2 ctrl1' ctrl2': (@SNode.state obsE bytes)?): bool :=
    (node_is_on ctrl1 || node_is_on ctrl2) && negb (node_is_on ctrl1') && negb (node_is_on ctrl2') ||
    ((no_hb_recieved ctrl1 || (node_is_on ctrl1 && negb (node_is_on ctrl2))) && negb (node_is_on ctrl1')) ||
    ((no_hb_recieved ctrl2 || (node_is_on ctrl2 && negb (node_is_on ctrl1))) && negb (node_is_on ctrl2')).

  Definition nb_tgt (nodes1 nodes2: list (@SNode.state obsE bytes)): bool :=
    ctrl_fail_tgt (nth_error nodes1 1) (nth_error nodes1 2)
                  (nth_error nodes2 1) (nth_error nodes2 2).

  Let sync_sys_src: SyncSysNB.t :=
    SyncSysNB.mk (Z.to_nat period)
                 [(ITrSNode.to_snode con_mod);
                 SingleCtrlSNode.to_snode;
                 DummySNode.to_snode;
                 (ITrSNode.to_snode dev_mod);
                 (ITrSNode.to_snode dev_mod);
                 (ITrSNode.to_snode dev_mod)
                 ]
                 mcasts
                 sntz.

  Let sync_sys_tgt: SyncSysNB.t :=
    SyncSysNB.mk (Z.to_nat period)
                 [(ITrSNode.to_snode con_mod);
                 (ITrSNode.to_snode (ctrl_mod 1));
                 (ITrSNode.to_snode (ctrl_mod 2));
                 (ITrSNode.to_snode dev_mod);
                 (ITrSNode.to_snode dev_mod);
                 (ITrSNode.to_snode dev_mod)
                 ]
                 mcasts
                 sntz.

  Let sys_src: DSys.t := SyncSysNB.as_dsys nb_src sync_sys_src tm_init.
  Let sys_tgt: DSys.t := SyncSysNB.as_dsys nb_tgt sync_sys_tgt tm_init.


  (** simulation relations *)

  Variant sim_console: forall (con_src con_tgt: @SNode.state obsE bytes), Prop :=
  | SimConsole
      inb_src inb_tgt ast:
      sim_console
        (SNode.State 0 (ITrSNode.to_snode con_mod) inb_src ast)
        (SNode.State 0 (ITrSNode.to_snode con_mod) inb_tgt ast)
  .

  Definition is_stuttering (msg: bytes?) (ctrl: CtrlState.t): bool :=
    match msg, ctrl.(CtrlState.mode) with
    | None, CtrlState.Standby =>
      (ctrl.(CtrlState.timeout) =? SpecController.MAX_TIMEOUT)%Z
    | _, _ => false
    end.

  Variant ctrl_state_wf:
    forall (sttr: bool) (sctrl ctrl1 ctrl2: CtrlState.t?) (msg1 msg2: bytes?), Prop :=
  | CtrlStateWf_NN:
      ctrl_state_wf false None None None None None
  | CtrlStateWf_NU
      sctrl
      (SCTRL: sctrl = active CtrlState.init):
      ctrl_state_wf false (Some sctrl)
                    None (Some CtrlState.init) None None
  | CtrlStateWf_UN
      sctrl
      (SCTRL: sctrl = active CtrlState.init):
      ctrl_state_wf false (Some sctrl)
                    (Some CtrlState.init) None None None
  | CtrlStateWf_UU
      sctrl
      (SCTRL: sctrl = active CtrlState.init):
      ctrl_state_wf false (Some sctrl)
                    (Some CtrlState.init) (Some CtrlState.init) None None
  | CtrlStateWf_SN
      sttr sctrl ctrl msg1 msg2
      (STTR: sttr = is_stuttering msg2 ctrl)
      (CTRL1: ctrl.(CtrlState.mode) <> CtrlState.Uninit)
      (SCTRL: sctrl = active ctrl)
      (MSG1: msg1 = Some (CtrlState.to_bytes ctrl))
      (MSG2: match ctrl.(CtrlState.mode) with
             | CtrlState.Active => True
             | _ =>
               match msg2 with
               | Some msg => sctrl = active (CtrlState.of_bytes msg)
               | None => True
               end
             end)
      (WF: CtrlState.wf ctrl):
      ctrl_state_wf sttr (Some sctrl) (Some ctrl) None msg1 msg2
  | CtrlStateWf_NS
      sttr sctrl ctrl msg1 msg2
      (STTR: sttr = is_stuttering msg1 ctrl)
      (CTRL2: ctrl.(CtrlState.mode) <> CtrlState.Uninit)
      (SCTRL: sctrl = active ctrl)
      (MSG1: match ctrl.(CtrlState.mode) with
             | CtrlState.Active => True
             | _ =>
               match msg1 with
               | Some msg => sctrl = active (CtrlState.of_bytes msg)
               | None => True
               end
             end)
      (MSG2: msg2 = Some (CtrlState.to_bytes ctrl))
      (WF: CtrlState.wf ctrl):
      ctrl_state_wf sttr (Some sctrl) None (Some ctrl) msg1 msg2
  | CtrlStateWf_SU
      sttr sctrl ctrl msg1
      (STTR: sttr = is_stuttering None ctrl)
      (CTRL1: ctrl.(CtrlState.mode) <> CtrlState.Uninit)
      (SCTRL: sctrl = active ctrl)
      (MSG1: msg1 = Some (CtrlState.to_bytes ctrl))
      (WF: CtrlState.wf ctrl):
      ctrl_state_wf sttr (Some sctrl) (Some ctrl) (Some CtrlState.init) msg1 None
  | CtrlStateWf_US
      sttr sctrl ctrl msg2
      (STTR: sttr = is_stuttering None ctrl)
      (CTRL2: ctrl.(CtrlState.mode) <> CtrlState.Uninit)
      (SCTRL: sctrl = active ctrl)
      (MSG2: msg2 = Some (CtrlState.to_bytes ctrl))
      (WF: CtrlState.wf ctrl):
      ctrl_state_wf sttr (Some sctrl) (Some CtrlState.init) (Some ctrl) None msg2
  | CtrlStateWf_SS
      sctrl ctrl1 ctrl2 msg1 msg2
      (SCTRL: match ctrl1.(CtrlState.mode), ctrl2.(CtrlState.mode) with
              | CtrlState.Active, CtrlState.Standby =>
                sctrl = ctrl1
              | CtrlState.Standby, CtrlState.Active =>
                sctrl = ctrl2
              | _, _ => False
              end)
      (MSG2: msg1 = Some (CtrlState.to_bytes ctrl1))
      (MSG2: msg2 = Some (CtrlState.to_bytes ctrl2))
      (WF1: CtrlState.wf ctrl1)
      (WF2: CtrlState.wf ctrl2):
      ctrl_state_wf false (Some sctrl) (Some ctrl1) (Some ctrl2) msg1 msg2
  .
  Hint Constructors ctrl_state_wf: core.

  Variant ctrl_wf: forall (sttr: bool) (sctrl: CtrlState.t?)
                     (inb1 inb2: list bytes?) (ctrl1 ctrl2: CtrlState.t?), Prop :=
  | CtrlWf
      sttr sctrl inb1 inb2 ctrl1 ctrl2
      (STATE: ctrl_state_wf sttr sctrl ctrl1 ctrl2
                            (nth 1 inb2 None) (nth 2 inb1 None))
      (INCON: nth 0 inb1 None = nth 0 inb2 None):
      ctrl_wf sttr sctrl inb1 inb2 ctrl1 ctrl2
  .
  Hint Constructors ctrl_wf: core.

  Variant sim_ctrl_state:
    forall (sttr: bool) (sctrl: CtrlState.t?) (st_src: SingleCtrlSNode.astate_t?), Prop :=
  | SimCtrlStateNone
      sttr:
      sim_ctrl_state sttr None None
  | SimCtrlStateSome
      sttr sctrl:
      sim_ctrl_state sttr (Some sctrl) (Some (sttr, sctrl))
  .
  Hint Constructors sim_ctrl_state: core.

  Variant sim_ctrl_inbox (inb_src inb_tgt: list bytes?): Prop :=
  | SimCtrlInbox
      (INDEV1: nth 3 inb_src None = nth 3 inb_tgt None)
      (INDEV2: nth 4 inb_src None = nth 4 inb_tgt None)
      (INDEV3: nth 5 inb_src None = nth 5 inb_tgt None)
  .
  Hint Constructors sim_ctrl_inbox: core.

  Program Instance sim_ctrl_inbox_Equivalence: Equivalence sim_ctrl_inbox.
  Next Obligation.
    ii. econs; eauto.
  Qed.
  Next Obligation.
    ii. inv H. econs; eauto.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; congr.
  Qed.

  Definition ctrl_state (itr: itree (obsE +' bsendE) CtrlState.t) (ctrl: CtrlState.t): Prop :=
    itr = Ret ctrl.
  Hint Unfold ctrl_state: core.

  Definition single_ctrl_state (ast: SingleCtrlSNode.t) (ctrl: SingleCtrlSNode.astate_t): Prop :=
    ast = SingleCtrlSNode.PrdEnd ctrl.
  Hint Unfold single_ctrl_state: core.

  Variant sim_controller:
    forall (ctrl1_src ctrl2_src ctrl1_tgt ctrl2_tgt: @SNode.state obsE bytes), Prop :=
  | SimController
      inb1_src ctrl_src ast1_src
      inb2_src
      inb1_tgt ctrl1_tgt ast1_tgt
      inb2_tgt ctrl2_tgt ast2_tgt
      sctrl sttr
      (CTRL_SRC: option_rel2 single_ctrl_state ast1_src ctrl_src)
      (CTRL1_TGT: option_rel2 ctrl_state ast1_tgt ctrl1_tgt)
      (CTRL2_TGT: option_rel2 ctrl_state ast2_tgt ctrl2_tgt)
      (CTRL_WF: ctrl_wf sttr sctrl inb1_tgt inb2_tgt ctrl1_tgt ctrl2_tgt)
      (CTRL_STATE: sim_ctrl_state sttr sctrl ctrl_src)
      (CTRL_INBOX1: sim_ctrl_inbox inb1_src inb1_tgt)
      (CTRL_INBOX2: sim_ctrl_inbox inb1_src inb2_tgt):
      sim_controller
        (SNode.State 1 SingleCtrlSNode.to_snode inb1_src ast1_src)
        (SNode.State 2 DummySNode.to_snode inb2_src None)
        (SNode.State 1 (ITrSNode.to_snode (ctrl_mod 1)) inb1_tgt ast1_tgt)
        (SNode.State 2 (ITrSNode.to_snode (ctrl_mod 2)) inb2_tgt ast2_tgt)
  .
  Hint Constructors sim_controller: core.

  Definition sim_grant (grant_src grant1_tgt grant2_tgt: bytes?): Prop :=
    match grant_src, grant1_tgt, grant2_tgt with
    | Some _, Some _, _
    | Some _, _, Some _
    | None, None, None => True
    | _, _, _ => False
    end.
  Hint Unfold sim_grant: core.

  Variant sim_controller_out:
    forall (outb1_src outb2_src outb1_tgt outb2_tgt: list bytes?)
      (ctrl1_src ctrl2_src ctrl1_tgt ctrl2_tgt: @SNode.state obsE bytes), Prop :=
  | SimControllerOut
      outb1_src inb1_src ctrl_src ast1_src
      inb2_src
      outb1_tgt inb1_tgt ctrl1_tgt ast1_tgt
      outb2_tgt inb2_tgt ctrl2_tgt ast2_tgt
      sctrl sttr
      (CTRL_SRC: option_rel2 single_ctrl_state ast1_src ctrl_src)
      (CTRL1_TGT: option_rel2 ctrl_state ast1_tgt ctrl1_tgt)
      (CTRL2_TGT: option_rel2 ctrl_state ast2_tgt ctrl2_tgt)
      (CTRL_STATE_WF: ctrl_state_wf sttr sctrl ctrl1_tgt ctrl2_tgt
                                    (nth 2 outb1_tgt None) (nth 1 outb2_tgt None))
      (CTRL_STATE: sim_ctrl_state sttr sctrl ctrl_src)
      (OUTDEV1: sim_grant (nth 3 outb1_src None)
                          (nth 3 outb1_tgt None)
                          (nth 3 outb2_tgt None))
      (OUTDEV2: sim_grant (nth 4 outb1_src None)
                          (nth 4 outb1_tgt None)
                          (nth 4 outb2_tgt None))
      (OUTDEV3: sim_grant (nth 5 outb1_src None)
                          (nth 5 outb1_tgt None)
                          (nth 5 outb2_tgt None)):
      sim_controller_out
        outb1_src [] outb1_tgt outb2_tgt
        (SNode.State 1 SingleCtrlSNode.to_snode inb1_src ast1_src)
        (SNode.State 2 DummySNode.to_snode inb2_src None)
        (SNode.State 1 (ITrSNode.to_snode (ctrl_mod 1)) inb1_tgt ast1_tgt)
        (SNode.State 2 (ITrSNode.to_snode (ctrl_mod 2)) inb2_tgt ast2_tgt)
  .
  Hint Constructors sim_controller_out: core.

  Variant sim_device_inbox (inb_src inb_tgt: list bytes?): Prop :=
  | SimDeviceInbox
      (MSG1: sim_grant (nth 1 inb_src None)
                       (nth 1 inb_tgt None)
                       (nth 2 inb_tgt None))
      (MSG2: nth 2 inb_src None = None)
  .

  Variant sim_device (tid: nat): forall (dev_src dev_tgt: @SNode.state obsE bytes), Prop :=
  | SimDevice
      inb_src inb_tgt ast
      (INBOX: sim_device_inbox inb_src inb_tgt):
      sim_device tid
                 (SNode.State tid (ITrSNode.to_snode dev_mod) inb_src ast)
                 (SNode.State tid (ITrSNode.to_snode dev_mod) inb_tgt ast)
  .

  Variant sim_nodes: forall (nodes_src nodes_tgt: list (@SNode.state obsE bytes)), Prop :=
  | SimNodes
      con_src ctrl1_src ctrl2_src dev1_src dev2_src dev3_src
      con_tgt ctrl1_tgt ctrl2_tgt dev1_tgt dev2_tgt dev3_tgt
      (CON: sim_console con_src con_tgt)
      (CTRL: sim_controller ctrl1_src ctrl2_src ctrl1_tgt ctrl2_tgt)
      (DEV1: sim_device 3 dev1_src dev1_tgt)
      (DEV2: sim_device 4 dev2_src dev2_tgt)
      (DEV3: sim_device 5 dev3_src dev3_tgt):
      sim_nodes [con_src; ctrl1_src; ctrl2_src; dev1_src; dev2_src; dev3_src]
                [con_tgt; ctrl1_tgt; ctrl2_tgt; dev1_tgt; dev2_tgt; dev3_tgt]
  .

  Variant sim_states: forall (st_src: sys_src.(DSys.state)) (st_tgt: sys_tgt.(DSys.state)), Prop :=
  | SimStates
      tm nodes_src nodes_tgt
      (NODES: sim_nodes nodes_src nodes_tgt):
      sim_states (SyncSysNB.State tm nodes_src) (SyncSysNB.State tm nodes_tgt)
  .


  (** proofs *)

  Lemma sim_nodes_length
        nodes_src nodes_tgt
        (SIM: sim_nodes nodes_src nodes_tgt):
    length nodes_src = 6 /\
    length nodes_tgt = 6.
  Proof.
    inv SIM. ss.
  Qed.

  Lemma sim_console_step
        con1_src
        tm con1_tgt es outb con2_tgt
        (SIM1: sim_console con1_src con1_tgt)
        (STEP: SNode.step sntz 6 mcasts tm con1_tgt es outb con2_tgt):
    exists con2_src,
      (<<STEP: SNode.step sntz 6 mcasts tm con1_src es outb con2_src>>) /\
      (<<SIM2: sim_console con2_src con2_tgt>>) /\
      (<<OUTB: nth 1 outb None = nth 2 outb None>>).
  Proof.
    inv SIM1. inv STEP; existT_elim; subst.
    - esplits; [econs 1|..]; eauto. econs.
    - esplits; [econs 2|..]; eauto. econs.
    - inv RUN_PERIOD.
      { esplits.
        - econs 3; eauto. econs 1.
        - ss.
        - ss.
      }
      esplits.
      + econs 3; eauto. econs 2; eauto.
        inv PERIOD_BEGIN. econs; eauto.
      + ss.
      + inv PERIOD_BEGIN; ss.
        unfold con_job in *.

        inv STAR; ss. inv ASTEP; cycle 2.
        { inv AT_EVENT. existT_elim. subst. ss. }
        { inv TAU_STEP. ss. }
        inv AT_EVENT. existT_elim. subst. ss.
        revert OBS. simpl_itree_goal. ss. i. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

        des_ifs; cycle 1.
        { inv ASTAR'; ss. inv ASTEP; cycle 2.
          { inv AT_EVENT. existT_elim. subst. ss. }
          { inv TAU_STEP. ss. }
          inv AT_EVENT. existT_elim. subst. ss.
          revert OBS. simpl_itree_goal. ss. i. inv OBS. existT_elim. subst.
          inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.
          inv ASTAR'0; ss. inv ASTEP.
          - inv TAU_STEP. ss.
          - inv AT_EVENT. ss.
          - inv AT_EVENT. ss.
        }

        inv ASTAR'; ss. inv ASTEP.
        { inv TAU_STEP. ss. }
        { inv AT_EVENT. existT_elim. subst. ss. }
        inv AT_EVENT. existT_elim. subst. ss.
        revert OBS. simpl_itree_goal. ss. i. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

        inv ASTAR'0; ss. inv ASTEP; cycle 2.
        { inv AT_EVENT. existT_elim. subst. ss. }
        { inv TAU_STEP. ss. }
        inv AT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

        inv ASTAR'; ss. inv ASTEP.
        * inv TAU_STEP. ss.
        * inv AT_EVENT. ss.
        * inv AT_EVENT. ss.
  Qed.

  Definition pure_job_controller (tid: Z) (st: CtrlState.t) (inb: list bytes?):
    (Tid * bytes)? * CtrlState.t :=
    let st0 := sync_istate tid st inb in
    let st1 := update_queue st0 inb in
    let (st2, tid_owner) := update_owner st1 in
    let omsg :=
        if check_dev_id tid_owner
        then Some (Z.to_nat tid_owner, grant_msg)
        else None
    in
    (omsg, st2).

  Variant abst_ctrl_step (tid: Z) (tm: Z) (inb: list bytes?):
    forall (ast1: (itree (obsE +' bsendE) CtrlState.t)?)
      (outb: list bytes?)
      (ast2: (itree (obsE +' bsendE) CtrlState.t)?), Prop :=
  | AbstCtrlStepNoneNone:
      abst_ctrl_step tid tm inb
                     None [] None
  | AbstCtrlStepNoneSome:
      abst_ctrl_step tid tm inb
                     None [] (Some (Ret CtrlState.init))
  | AbstCtrlStepSome
      st1 grant outb st2 ast2
      (PURE_STEP: (grant, st2) = pure_job_controller tid st1 inb)
      (OUT: ((<<AST2: ast2 = Some (Ret st2)>>) /\
             (<<OUT: outb =
                     SNode.update_outbox
                       sntz 6 mcasts
                       (SNode.update_outbox sntz 6 mcasts (SNode.init_box 6) grant)
                       (Some (Z.to_nat (3 - tid), CtrlState.to_bytes st2))>>)) \/
            ((<<AST2: ast2 = None>>) /\
             (<<OUT: __guard__ (
                         (outb = [] \/ outb = SNode.init_box 6) \/
                         outb = SNode.update_outbox sntz 6 mcasts (SNode.init_box 6) grant \/
                         outb =
                         SNode.update_outbox
                           sntz 6 mcasts
                           (SNode.update_outbox sntz 6 mcasts (SNode.init_box 6) grant)
                           (Some (Z.to_nat (3 - tid), CtrlState.to_bytes st2)))>>))):
      abst_ctrl_step tid tm inb
                     (Some (Ret st1)) outb ast2
  .

  Lemma controller_step_inv
        tm tid inb1 ast1 es outb snode2
        (AST1: __guard__ (ast1 = None \/ exists st1, ast1 = Some (Ret st1)))
        (STEP: SNode.step sntz 6 mcasts tm
                          (SNode.State tid (ITrSNode.to_snode (ctrl_mod (Z.of_nat tid))) inb1 ast1)
                          es outb snode2):
    exists ast2,
      (<<SNODE2: snode2 = SNode.State tid (ITrSNode.to_snode (ctrl_mod (Z.of_nat tid)))
                                      (SNode.init_box 6) ast2>>) /\
      (<<EVENTS: es = []>>) /\
      (<<ABST_STEP: abst_ctrl_step (Z.of_nat tid) (Z.of_nat tm) inb1 ast1 outb ast2>>).
  Proof.
    Opaque SNode.update_outbox.
    inv STEP; existT_elim; subst; ss.
    { (* None -> None *)
      esplits; eauto. econs 1.
    }
    { (* None -> Some *)
      esplits; auto.
      inv INIT_APP_STATE. ss. econs 2.
    }

    rename oast' into ast2. exists ast2.
    inv RUN_PERIOD; ss.
    { (* init failed *)
      splits; auto.
      unguard. des; ss. inv AST1.
      destruct (pure_job_controller (Z.of_nat tid) st1 inb1) as [grant st2] eqn:PURE_STEP.
      econs 3; eauto. right. unguard. auto.
    }

    inv PERIOD_BEGIN. ss.
    unguard. des; ss. inv AST1. ss. symmetry in RET. inv RET.
    destruct ast2 as [ast2|]; ss.
    { (* Some -> Some *)
      unfold ITrSNode.period_end in *.
      inv STAR; ss.
      { revert FINAL.
        unfold ctrl_job, job_controller_itree. ss.
        destruct (update_owner (update_istate (Z.of_nat tid) st1 inb1)).
        destruct (check_dev_id z); simpl_itree_goal; ss.
      }

      revert ASTEP.
      unfold ctrl_job, job_controller_itree.
      destruct (update_owner (update_istate (Z.of_nat tid) st1 inb1)) as [st2 tid_owner] eqn:UPD.
      destruct (check_dev_id tid_owner) eqn:CHECK.
      - i. inv ASTEP.
        { inv TAU_STEP. ss. }
        { inv AT_EVENT. existT_elim. subst. ss. }
        inv AT_EVENT. existT_elim. subst. ss.
        revert OBS. simpl_itree_goal. ss. i. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss.
        inv OBS. existT_elim. subst.

        inv ASTAR'; ss.
        inv ASTEP.
        { inv TAU_STEP. ss. }
        { inv AT_EVENT. existT_elim. subst. ss. }
        unfold send_hb_itree in *.
        inv AT_EVENT. existT_elim. subst. ss.
        revert OBS. simpl_itree_goal. ss. i. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss.
        inv OBS. existT_elim. subst.

        inv ASTAR'0; ss; cycle 1.
        { inv ASTEP.
          - inv TAU_STEP. ss.
          - inv AT_EVENT. ss.
          - inv AT_EVENT. ss.
        }

        splits; ss. econs 3; eauto.
        unfold pure_job_controller, update_istate in *.
        rewrite UPD, CHECK. ss.

      - unfold send_hb_itree. i. inv ASTEP.
        { inv TAU_STEP. ss. }
        { inv AT_EVENT. existT_elim. subst. ss. }
        inv AT_EVENT. existT_elim. subst. ss.
        revert OBS. do 2 simpl_itree_goal. ss. i. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss.
        inv OBS. existT_elim. subst.

        inv ASTAR'; ss; cycle 1.
        { inv ASTEP.
          - inv TAU_STEP. ss.
          - inv AT_EVENT. ss.
          - inv AT_EVENT. ss.
        }

        splits; ss. econs 3; eauto.
        + unfold pure_job_controller, update_istate in *.
          rewrite UPD, CHECK. ss.
        + Transparent SNode.update_outbox. left. ss.
    }

    { (* Some -> None *)
      Opaque SNode.update_outbox.
      destruct (pure_job_controller (Z.of_nat tid) st1 inb1) as [grant st_end] eqn:PURE_STEP.
      inv STAR; ss.
      { splits; ss. econs 3; eauto. right. unguard. auto. }

      revert ASTEP.
      unfold ctrl_job, job_controller_itree.
      destruct (update_owner (update_istate (Z.of_nat tid) st1 inb1)) as [st2 tid_owner] eqn:UPD.
      destruct (check_dev_id tid_owner) eqn:CHECK.
      - i. inv ASTEP.
        { inv TAU_STEP. ss. }
        { inv AT_EVENT. existT_elim. subst. ss. }
        inv AT_EVENT. existT_elim. subst. ss.
        revert OBS. simpl_itree_goal. ss. i. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss.
        inv OBS. existT_elim. subst.

        inv ASTAR'; ss.
        { splits; ss. econs 3; eauto.
          revert PURE_STEP.
          unfold pure_job_controller, update_istate in *.
          rewrite UPD, CHECK. i. inv PURE_STEP.
          unguard. right. auto.
        }

        inv ASTEP.
        { inv TAU_STEP. ss. }
        { inv AT_EVENT. existT_elim. subst. ss. }
        unfold send_hb_itree in *.
        inv AT_EVENT. existT_elim. subst. ss.
        revert OBS. simpl_itree_goal. ss. i. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss.
        inv OBS. existT_elim. subst.

        inv ASTAR'0; ss; cycle 1.
        { inv ASTEP.
          - inv TAU_STEP. ss.
          - inv AT_EVENT. ss.
          - inv AT_EVENT. ss.
        }

        splits; ss. econs 3; eauto.
        revert PURE_STEP.
        unfold pure_job_controller, update_istate in *.
        rewrite UPD, CHECK. i. inv PURE_STEP.
        unguard. right. auto.

      - unfold send_hb_itree. i. inv ASTEP.
        { inv TAU_STEP. ss. }
        { inv AT_EVENT. existT_elim. subst. ss. }
        inv AT_EVENT. existT_elim. subst. ss.
        revert OBS. do 2 simpl_itree_goal. ss. i. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss.
        inv OBS. existT_elim. subst.

        inv ASTAR'; ss; cycle 1.
        { inv ASTEP.
          - inv TAU_STEP. ss.
          - inv AT_EVENT. ss.
          - inv AT_EVENT. ss.
        }

        splits; ss. econs 3; eauto.
        revert PURE_STEP.
        unfold pure_job_controller, update_istate in *.
        rewrite UPD, CHECK. i. inv PURE_STEP.
        unguard. right. auto.
    }
  Qed.

  Lemma next_state_snode_step_normal
        tm sttr inb1 ctrl1 ctrl2 grant
        (NEXT: (grant, ctrl2) = next_state sttr (active ctrl1) inb1):
    SNode.step
      sntz 6 mcasts tm
      (SNode.State 1 SingleCtrlSNode.to_snode inb1
                   (Some (SingleCtrlSNode.PrdEnd (sttr, ctrl1))))
      [] (SNode.update_outbox sntz 6 mcasts (SNode.init_box 6) grant)
      (SNode.State 1 SingleCtrlSNode.to_snode (SNode.init_box 6)
                   (Some (SingleCtrlSNode.PrdEnd (false, ctrl2)))).
  Proof.
    econs; eauto. econs; try by econs.
    destruct grant as [[tid msg]|].
    - econs; eauto.
      + econs. econs 2. econs 1; eauto.
      + econs.
        * econs 3; eauto; econs.
        * ss.
        * econs 2.
        * ss.
      + ss.
    - econs; eauto.
      + econs. econs. econs 1; eauto.
      + econs.
      + ss.
  Qed.

  Lemma next_state_snode_step_stutter
        tm inb1 ctrl1 ctrl2 omsg
        (NEXT: (omsg, ctrl2) = next_state false (active ctrl1) inb1)
        (TOUT: (ctrl2.(CtrlState.timeout) =? SpecController.MAX_TIMEOUT)%Z = true):
    SNode.step
      sntz 6 mcasts tm
      (SNode.State 1 SingleCtrlSNode.to_snode inb1
                   (Some (SingleCtrlSNode.PrdEnd (false, ctrl1))))
      [] (SNode.update_outbox sntz 6 mcasts (SNode.init_box 6) None)
      (SNode.State 1 SingleCtrlSNode.to_snode (SNode.init_box 6)
                   (Some (SingleCtrlSNode.PrdEnd (true, ctrl2)))).
  Proof.
    rewrite Z.eqb_eq in *.
    econs; eauto. econs; try by econs.
    econs; eauto.
    - econs. econs 1. econs 2; eauto.
    - econs.
    - ss.
  Qed.

  Lemma next_state_snode_step_stutter_send
        tm inb1 ctrl1 ctrl2 omsg
        (NEXT: (omsg, ctrl2) = next_state false (active ctrl1) inb1)
        (TOUT: (ctrl2.(CtrlState.timeout) =? SpecController.MAX_TIMEOUT)%Z = true):
    SNode.step
      sntz 6 mcasts tm
      (SNode.State 1 SingleCtrlSNode.to_snode inb1
                   (Some (SingleCtrlSNode.PrdEnd (false, ctrl1))))
      [] (SNode.update_outbox sntz 6 mcasts (SNode.init_box 6) omsg)
      (SNode.State 1 SingleCtrlSNode.to_snode (SNode.init_box 6)
                   (Some (SingleCtrlSNode.PrdEnd (true, ctrl2)))).
  Proof.
    rewrite Z.eqb_eq in *.
    econs; eauto. econs; try by econs.
    destruct omsg as [[tid msg]|].
    - econs; eauto.
      + econs. econs 2. econs 2; eauto.
      + econs.
        * econs 3; eauto; econs.
        * ss.
        * econs 2.
        * ss.
      + ss.
    - econs; eauto.
      + econs. econs 1. econs 2; eauto.
      + econs.
      + ss.
  Qed.

  Definition after_sync (st: CtrlState.t) (inb: list bytes?): (Tid * bytes)? * CtrlState.t :=
    let st1 := update_queue st inb in
    let (st2, tid_owner) := update_owner st1 in
    let omsg :=
        if check_dev_id tid_owner
        then Some (Z.to_nat tid_owner, grant_msg)
        else None
    in
    (omsg, st2).

  Lemma sim_ctrl_inbox_update_queue
        inb_src inb_tgt st
        (SIM: sim_ctrl_inbox inb_src inb_tgt):
    update_queue st inb_src = update_queue st inb_tgt.
  Proof.
    inv SIM.
    unfold update_queue. ss.
    repeat (f_equal; ss).
  Qed.

  Lemma try_add_queue_mode
        st1 id_dev st2
        (ADD: st2 = try_add_queue st1 id_dev):
    st2.(CtrlState.mode) = st1.(CtrlState.mode).
  Proof.
    unfold try_add_queue in *. ss. des_ifs.
  Qed.

  Lemma apply_devmsg_mode
        st1 id msg st2
        (APPLY: st2 = apply_devmsg st1 id msg):
    st2.(CtrlState.mode) = st1.(CtrlState.mode).
  Proof.
    unfold apply_devmsg in *.
    des_ifs; eauto using try_add_queue_mode.
    unfold try_release. des_ifs.
  Qed.

  Lemma reduce_timeout_mode
        st1 st2
        (REDUCE: st2 = reduce_timeout st1):
    st2.(CtrlState.mode) = st1.(CtrlState.mode).
  Proof.
    unfold reduce_timeout in *. des_ifs.
  Qed.

  Lemma update_queue_mode
        inb st1 st2
        (QUEUE: st2 = update_queue st1 inb):
    st2.(CtrlState.mode) = st1.(CtrlState.mode).
  Proof.
    unfold update_queue in *. ss. subst.
    etrans; [eapply reduce_timeout_mode; eauto|].
    do 3 (etrans; [eapply apply_devmsg_mode; eauto|]). ss.
  Qed.

  Lemma try_add_queue_active
        st id_dev st'
        (ACTIVE: st' = active st):
    try_add_queue st' id_dev =
    active (try_add_queue st id_dev).
  Proof.
    subst. destruct st. ss.
    unfold try_add_queue. ss. des_ifs.
  Qed.

  Lemma apply_devmsg_active
        st id msg st'
        (ACTIVE: st' = active st):
    apply_devmsg st' id msg =
    active (apply_devmsg st id msg).
  Proof.
    subst. unfold apply_devmsg in *.
    des_ifs; eauto using try_add_queue_active.
    unfold try_release. destruct st. ss.
    des_ifs.
  Qed.

  Lemma reduce_timeout_active
        st st'
        (ACTIVE: st' = active st):
    reduce_timeout st' =
    active (reduce_timeout st).
  Proof.
    subst. destruct st.
    unfold reduce_timeout. ss. des_ifs.
  Qed.

  Lemma update_queue_active
        inb st st'
        (ACTIVE: st' = active st):
    update_queue st' inb =
    active (update_queue st inb).
  Proof.
    subst. unfold update_queue. ss.
    apply reduce_timeout_active.
    repeat apply apply_devmsg_active. ss.
  Qed.

  Lemma active_eq
        st
        (MODE: st.(CtrlState.mode) = CtrlState.Active):
    st = active st.
  Proof.
    destruct st. ss. subst. refl.
  Qed.

  Lemma check_dev_id_mone:
    check_dev_id Z_mone = false.
  Proof.
    unfold check_dev_id. ss.
  Qed.

  Lemma update_owner_mode
        st1 st2 grant
        (UPDATE: (grant, st2) =
                 let (st2, tid_owner) := update_owner st1 in
                 (if check_dev_id tid_owner
                  then Some (Z.to_nat tid_owner, grant_msg)
                  else None,
                  st2)):
    st2.(CtrlState.mode) = st1.(CtrlState.mode).
  Proof.
    destruct st1; ss. des_ifs.
  Qed.

  Lemma update_owner_inv
        st1 st2 grant st2_src grant_src
        (UPDATE: (grant, st2) =
                 let (st2, tid_owner) := update_owner st1 in
                 (if check_dev_id tid_owner
                  then Some (Z.to_nat tid_owner, grant_msg)
                  else None,
                  st2))
        (UPDATE_ACTIVE: (grant_src, st2_src) =
                        let (st2_src, tid_owner) := update_owner (active st1) in
                        (if check_dev_id tid_owner
                         then Some (Z.to_nat tid_owner, grant_msg)
                         else None,
                         st2_src)):
    (<<STATE: st2_src = active st2>>) /\
    (<<GRANT_SRC: (st2.(CtrlState.timeout) =? SpecController.MAX_TIMEOUT)%Z = false ->
                   grant_src = None>>) /\
    (<<GRANT_TGT1: st1.(CtrlState.mode) <> CtrlState.Active -> grant = None>>) /\
    (<<GRANT_TGT2: st1.(CtrlState.mode) = CtrlState.Active -> grant = grant_src>>) /\
    (<<MODE: st2.(CtrlState.mode) = st1.(CtrlState.mode)>>).
  Proof.
    destruct st1; ss. revert UPDATE_ACTIVE.
    repeat (condtac; ss); i; inv UPDATE_ACTIVE.
    - destruct mode; ss.
      + rewrite check_dev_id_mone in *. inv UPDATE.
        esplits; eauto; ss.
      + rewrite COND0 in *. inv UPDATE.
        esplits; eauto; ss.
      + rewrite check_dev_id_mone in *. inv UPDATE.
        esplits; eauto; ss.
    - destruct mode; ss.
      + rewrite check_dev_id_mone in *. inv UPDATE.
        esplits; eauto; ss.
      + rewrite COND0 in *. inv UPDATE.
        esplits; eauto; ss.
      + rewrite check_dev_id_mone in *. inv UPDATE.
        esplits; eauto; ss.
    - destruct mode; ss.
      + rewrite check_dev_id_mone in *. inv UPDATE.
        esplits; eauto.
      + inv UPDATE. esplits; eauto.
      + rewrite check_dev_id_mone in *. inv UPDATE.
        esplits; eauto.
  Qed.

  Lemma make_stutter_sync_istate
        tid st inb st_src st_tgt
        (TID: tid = 1 \/ tid = 2)
        (MSG: match st.(CtrlState.mode) with
              | CtrlState.Active => True
              | _ =>
                match nth (3 - tid) inb None with
                | Some msg => active st = active (CtrlState.of_bytes msg)
                | None => True
                end
              end)
        (STUTTER: st_src =
                  make_stutter (is_stuttering (nth (3 - tid) inb None) st) (active st))
        (SYNC: st_tgt = sync_istate (Z.of_nat tid) st inb):
    st_src = active st_tgt.
  Proof.
    unfold sync_istate in *.
    replace (Z.to_nat (3 - Z.of_nat tid)) with (3 - tid) in *; cycle 1.
    { inv TID; ss. }
    clear TID.
    destruct (nth (3 - tid) inb None) as [msg|].
    - destruct st, mode; ss; subst; ss. condtac; ss.
    - destruct st, mode; ss; subst; ss. condtac; ss.
  Qed.

  Lemma make_stutter_sync_istate_None
        tid st inb st_src st_tgt
        (TID: tid = 1 \/ tid = 2)
        (MSG: nth (3 - tid) inb None = None)
        (STUTTER: st_src =
                  make_stutter (is_stuttering (nth (3 - tid) inb None) st) (active st))
        (SYNC: st_tgt = sync_istate (Z.of_nat tid) st inb)
        (MODE: st.(CtrlState.mode) <> CtrlState.Uninit):
    (<<CTRL: st_src = st_tgt>>) /\
    (<<MODE: st_tgt.(CtrlState.mode) = CtrlState.Active>>).
  Proof.
    unfold sync_istate in *.
    replace (Z.to_nat (3 - Z.of_nat tid)) with (3 - tid) in *; cycle 1.
    { inv TID; ss. }
    clear TID. rewrite MSG in *.
    destruct st, mode; ss; subst; split; ss. condtac; ss.
  Qed.

  Lemma make_stutter_sync_istate_uninit
        tid st inb msg st_src st_tgt
        (TID: tid = 1 \/ tid = 2)
        (MSG1: nth (3 - tid) inb None = Some msg)
        (MSG2: active st = active (CtrlState.of_bytes msg))
        (STUTTER: st_src =
                  make_stutter (is_stuttering (nth (3 - tid) inb None) st) (active st))
        (SYNC: st_tgt = sync_istate (Z.of_nat tid) CtrlState.init inb):
    (<<CTRL: st_src = active st_tgt>>) /\
    (<<MODE: st_tgt.(CtrlState.mode) = CtrlState.Standby>>).
  Proof.
    unfold sync_istate in *.
    replace (Z.to_nat (3 - Z.of_nat tid)) with (3 - tid) in *; cycle 1.
    { inv TID; ss. }
    clear TID. rewrite MSG1 in *. ss.
    unfold CtrlState.copy_state_from_hb in *.
    destruct st. ss. subst. ss.
  Qed.

  Lemma is_stuttering_true_next
        tid inb st1 st2 grant hb
        (TID: tid = 1 \/ tid = 2)
        (STTR: is_stuttering (nth (3 - tid) inb None) st1 = true)
        (PURE: (grant, st2) = pure_job_controller (Z.of_nat tid) st1 inb):
    is_stuttering hb st2 = false.
  Proof.
    unfold is_stuttering in STTR. des_ifs.
    revert PURE. unfold pure_job_controller.
    unfold sync_istate.
    rewrite Heq0.
    replace (Z.to_nat (3 - Z.of_nat tid)) with (3 - tid); cycle 1.
    { des; subst; ss. }
    rewrite Heq. i.
    exploit update_owner_mode; eauto. i. symmetry in x0.
    erewrite update_queue_mode in x0; eauto.
    unfold is_stuttering.
    destruct hb; ss.
    destruct (CtrlState.mode st2); ss.
    revert x0.
    unfold activate_nhb. destruct st1; ss.
  Qed.

  Lemma pure_step_mode
        tid st1 inb grant st2
        (PURE_STEP: (grant, st2) = pure_job_controller tid st1 inb):
    st2.(CtrlState.mode) <> CtrlState.Uninit.
  Proof.
    unfold pure_job_controller in *.
    erewrite update_owner_mode; eauto.
    erewrite update_queue_mode; eauto.
    destruct st1.
    unfold sync_istate, CtrlState.default_mode. des_ifs; try congr.
  Qed.

  Lemma standby_grant_None
        inb st1 st2 grant
        (MODE: st1.(CtrlState.mode) = CtrlState.Standby)
        (PURE: (grant, st2) =
               let (st2, tid_owner) := update_owner (update_queue st1 inb) in
               (if check_dev_id tid_owner
                then Some (Z.to_nat tid_owner, grant_msg)
                else None,
                st2)):
    grant = None.
  Proof.
    destruct (update_owner (update_queue st1 inb)) as [st tid_owner] eqn:UPD.
    cut (tid_owner = Z_mone).
    { i. subst. unfold check_dev_id in *.
      replace (Z.of_nat 3) with 3%Z in * by ss.
      replace (Z.of_nat 4) with 4%Z in * by ss.
      replace (Z.of_nat 5) with 5%Z in * by ss.
      ss. inv PURE. ss.
    }
    remember (update_queue st1 inb) as st'.
    exploit update_queue_mode; try exact MODE; eauto. i.
    revert UPD. unfold update_owner. destruct st'. ss.
    condtac; ss; try congr.
    rewrite x0, MODE. i. inv UPD. ss.
  Qed.

  Lemma pure_step_wf
        tid st1 inb grant st2
        (WF1: CtrlState.wf st1)
        (PURE_STEP: (grant, st2) = pure_job_controller tid st1 inb):
    CtrlState.wf st2.
  Proof.
    unfold pure_job_controller in *.
    destruct (update_owner (update_queue (sync_istate tid st1 inb) inb))
      as [st tid_owner] eqn:UPD.
    exploit wf_update_owner; try eapply UPD.
    { apply wf_update_queue. apply wf_sync_istate. ss. }
    i. des. des_ifs.
  Qed.

  Lemma of_bytes_to_bytes
        ctrl
        (WF: CtrlState.wf ctrl):
    CtrlState.of_bytes (CtrlState.to_bytes ctrl) = ctrl.
  Proof.
    inv WF. ss.
    Transparent CtrlState.of_bytes.
    unfold CtrlState.of_bytes. ss.
    f_equal; try by (rewrite Byte.signed_repr; eauto).
    - destruct md; ss.
    - repeat (destruct q; ss).
      repeat (match goal with [H: Forall _ _ |- _] => inv H end).
      repeat (rewrite Byte.signed_repr; eauto).
  Qed.

  Lemma make_stutter_sync_istate_both
        sctrl ctrl1 ctrl2 inb1_tgt inb2_tgt
        st_src st1_tgt st2_tgt
        (STUTTER: st_src = make_stutter false sctrl)
        (SYNC1: st1_tgt = sync_istate (Z.of_nat 1) ctrl1 inb1_tgt)
        (SYNC2: st2_tgt = sync_istate (Z.of_nat 2) ctrl2 inb2_tgt)
        (WF1: CtrlState.wf ctrl1)
        (WF2: CtrlState.wf ctrl2)
        (CON: nth 0 inb1_tgt None = nth 0 inb2_tgt None)
        (MSG1: nth 1 inb2_tgt None = Some (CtrlState.to_bytes ctrl1))
        (MSG2: nth 2 inb1_tgt None = Some (CtrlState.to_bytes ctrl2))
        (SCTRL: match ctrl1.(CtrlState.mode), ctrl2.(CtrlState.mode) with
                | CtrlState.Active, CtrlState.Standby => sctrl = ctrl1
                | CtrlState.Standby, CtrlState.Active => sctrl = ctrl2
                | _, _ => False
                end):
    (<<ST1: st1_tgt = st_src>>) /\
    (<<MODE1: st1_tgt.(CtrlState.mode) = CtrlState.Active>>) /\
    (<<ST2: active st2_tgt = st_src>>) /\
    (<<MODE2: st2_tgt.(CtrlState.mode) = CtrlState.Standby>>) \/
    (<<ST1: active st1_tgt = st_src>>) /\
    (<<MODE1: st1_tgt.(CtrlState.mode) = CtrlState.Standby>>) /\
    (<<ST2: st2_tgt = st_src>>) /\
    (<<MODE2: st2_tgt.(CtrlState.mode) = CtrlState.Active>>).
  Proof.
    revert SYNC1 SYNC2. unfold sync_istate.
    replace (Z.to_nat (3 - Z.of_nat 1)) with 2 by ss.
    replace (Z.to_nat (3 - Z.of_nat 2)) with 1 by ss.
    rewrite MSG1, MSG2.
    unfold CtrlState.copy_state_from_hb.
    repeat (rewrite of_bytes_to_bytes; eauto).
    destruct ctrl1, ctrl2. ss.
    des_ifs; s; i; subst; ss;
      (try by right; ss); (try by left; ss).
  Qed.

  Lemma to_bytes_length
        ctrl
        (WF: CtrlState.wf ctrl):
    length (CtrlState.to_bytes ctrl) = 8.
  Proof.
    inv WF. ss.
    rewrite map_length. rewrite QUEUE_LENGTH. ss.
  Qed.

  Lemma sanitize_ctrl
        ctrl
        (WF: CtrlState.wf ctrl):
    sntz (CtrlState.to_bytes ctrl) = Some (CtrlState.to_bytes ctrl).
  Proof.
    unfold sntz, resize_bytes.
    rewrite to_bytes_length; ss.
    rewrite app_nil_r.
    replace 8 with (length (CtrlState.to_bytes ctrl))
      by (apply to_bytes_length; ss).
    rewrite firstn_all. ss.
  Qed.

  Lemma check_dev_id_inv
        tid
        (CHECK: check_dev_id tid = true):
    tid = 3%Z \/ tid = 4%Z \/ tid = 5%Z.
  Proof.
    unfold check_dev_id in *. ss.
    destruct (tid =? Z.of_nat 3)%Z eqn:TID3; ss.
    { rewrite Z.eqb_eq in *. subst. eauto. }
    destruct (tid =? Z.of_nat 4)%Z eqn:TID4; ss.
    { rewrite Z.eqb_eq in *. subst. eauto. }
    destruct (tid =? Z.of_nat 5)%Z eqn:TID5; ss.
    { rewrite Z.eqb_eq in *. subst. eauto. }
  Qed.

  Lemma grant_tid
        tid msg st2 st1
        (GRANT: (Some (tid, msg), st2) =
                let (st2, tid_owner) := update_owner st1 in
                (if check_dev_id tid_owner
                 then Some (Z.to_nat tid_owner, grant_msg)
                 else None,
                 st2)):
    tid = 3 \/ tid = 4 \/ tid = 5.
  Proof.
    destruct (update_owner st1).
    des_ifs.
    exploit check_dev_id_inv; eauto. i. des; subst; eauto.
  Qed.

  Lemma sim_controller_step
        tm
        ctrl1_src ctrl2_src
        ctrl1_tgt es1 outb1 ctrl1'_tgt
        ctrl2_tgt es2 outb2 ctrl2'_tgt
        (SIM1: sim_controller ctrl1_src ctrl2_src ctrl1_tgt ctrl2_tgt)
        (STEP1: SNode.step sntz 6 mcasts tm ctrl1_tgt es1 outb1 ctrl1'_tgt)
        (STEP2: SNode.step sntz 6 mcasts tm ctrl2_tgt es2 outb2 ctrl2'_tgt)
        (NONB: ctrl_fail_tgt (Some ctrl1_tgt) (Some ctrl2_tgt)
                             (Some ctrl1'_tgt) (Some ctrl2'_tgt) = false):
    es1 = [] /\ es2 = [] /\
    exists outb ctrl1'_src ctrl2'_src,
      (<<STEP1: SNode.step sntz 6 mcasts tm ctrl1_src [] outb ctrl1'_src>>) /\
      (<<STEP2: SNode.step sntz 6 mcasts tm ctrl2_src [] [] ctrl2'_src>>) /\
      (<<SIM2: sim_controller_out outb [] outb1 outb2 ctrl1'_src ctrl2'_src ctrl1'_tgt ctrl2'_tgt>>) /\
      (<<NONB: ctrl_fail_src (Some ctrl1_src) (Some ctrl1'_src) = false>>).
  Proof.
    Opaque nth CtrlState.of_bytes.
    unfold ctrl_fail_tgt in *. inv SIM1.
    replace 1%Z with (Z.of_nat 1) in * by ss.
    replace 2%Z with (Z.of_nat 2) in * by ss.
    exploit controller_step_inv; try eapply STEP1.
    { unguard. inv CTRL1_TGT; eauto. inv H. eauto. }
    i. des. subst. clear STEP1.
    rename ast2 into ast1'_tgt, ABST_STEP into ABST_STEP1.
    exploit controller_step_inv; try eapply STEP2.
    { unguard. inv CTRL2_TGT; eauto. inv H. eauto. }
    i. des. subst. clear STEP2.
    rename ast2 into ast2'_tgt, ABST_STEP into ABST_STEP2.
    splits; ss.

    inv CTRL_WF.
    inv STATE; inv CTRL1_TGT; inv CTRL2_TGT; inv CTRL_STATE; inv CTRL_SRC; ss.

    { (* Off, Off *)
      inv ABST_STEP1; inv ABST_STEP2; ss.

      { esplits.
        - econs 1; eauto.
        - econs 1; eauto.
        - econs; eauto; ss.
        - ss.
      }

      { esplits.
        - econs 2; eauto. econs.
        - econs 1; eauto.
        - econs; eauto; ss. econs; eauto.
        - ss.
      }

      { esplits.
        - econs 2; eauto. econs.
        - econs 1; eauto.
        - econs; eauto; ss. econs; eauto.
        - ss.
      }

      { esplits.
        - econs 2; eauto. econs.
        - econs 1; eauto.
        - econs; eauto; ss. econs; eauto.
        - ss.
      }
    }

    { (* Off, Uninit *)
      inv H1. inv H2.
      destruct (next_state false (active CtrlState.init) inb1_src)
        as [grant_src st2_src] eqn:NEXT.
      dup NEXT. unfold next_state in NEXT. ss.

      inv ABST_STEP2. des; subst; ss; cycle 1.
      { des_ifs. }
      clear NONB.
      exploit pure_step_wf; eauto using CtrlState.wf_init. intro WF2.
      unfold pure_job_controller in *. ss.
      unfold sync_istate in *. ss.
      replace (Z.to_nat (3 - Z.of_nat 2)) with 1 in * by ss.
      rewrite <- H4 in *.
      unfold CtrlState.default_mode in *.
      replace (Z.of_nat 2 =? 1)%Z with false in * by ss.
      erewrite <- sim_ctrl_inbox_update_queue in PURE_STEP; try exact CTRL_INBOX2.

      erewrite update_queue_active with
          (st:=CtrlState.mk CtrlState.Standby 0 0 0 [0; 0; 0; 0]%Z) in NEXT; ss.
      match goal with
      | [H: context[update_owner ?st] |- _] => remember st as ust
      end.
      guardH Hequst.
      exploit update_queue_mode; try exact Hequst. s. i. clear Hequst.
      exploit update_owner_inv; eauto. i. des.
      exploit GRANT_TGT1; try congr. i. subst. clear GRANT_TGT1 GRANT_TGT2.

      destruct ((st2.(CtrlState.timeout) =? SpecController.MAX_TIMEOUT)%Z) eqn:TOUT.
      { (* stutter *)
        clear GRANT_SRC.
        replace (CtrlState.mk CtrlState.Active 0 0 0 [0; 0; 0; 0]%Z)
          with (active (active CtrlState.init)) in * by ss.
        exploit next_state_snode_step_stutter; eauto.
        { destruct st2; ss. }
        intro STEP_SRC.
        esplits; [exact STEP_SRC|econs 1; eauto|..]; eauto.
        clear NEXT0 STEP_SRC.

        Transparent nth.
        inv ABST_STEP1.
        { (* Off, On *)
          econs; eauto; ss.
          econs 6; ss; try congr.
          - rewrite MODE. rewrite x0. ss.
          - rewrite MODE. rewrite x0. ss.
          - rewrite SNode.update_outbox_None.
            erewrite SNode.update_outbox_in; ss; try nia.
            apply sanitize_ctrl. ss.
        }

        { (* Uninit, On *)
          econs; eauto; ss.
          econs 8; ss; try congr.
          - rewrite MODE. rewrite x0. ss.
          - rewrite SNode.update_outbox_None.
            erewrite SNode.update_outbox_in; ss; try nia.
            apply sanitize_ctrl. ss.
        }
      }

      { (* normal *)
        exploit GRANT_SRC; eauto. i. subst.
        replace (CtrlState.mk CtrlState.Active 0 0 0 [0; 0; 0; 0]%Z)
          with (active (active CtrlState.init)) in * by ss.
        exploit next_state_snode_step_normal; eauto. intro STEP_SRC.
        esplits; [exact STEP_SRC|econs 1; eauto|..]; eauto.
        clear NEXT0 STEP_SRC.

        inv ABST_STEP1.
        { (* Off, On *)
          econs; eauto; ss.
          econs 6; ss; try congr.
          - rewrite MODE. rewrite x0. ss.
          - rewrite MODE. rewrite x0. ss.
          - rewrite SNode.update_outbox_None.
            erewrite SNode.update_outbox_in; ss; try nia.
            apply sanitize_ctrl. ss.
        }

        { (* Uninit, On *)
          econs; eauto; ss.
          econs 8; ss; try congr.
          - rewrite MODE. rewrite x0. ss.
          - rewrite SNode.update_outbox_None.
            erewrite SNode.update_outbox_in; ss; try nia.
            apply sanitize_ctrl. ss.
        }
      }
    }

    { (* Uninit, Off *)
      Opaque nth.
      inv H1. inv H2.
      destruct (next_state false (active CtrlState.init) inb1_src)
        as [grant_src st2_src] eqn:NEXT.
      dup NEXT. unfold next_state in NEXT. ss.

      inv ABST_STEP1. des; subst; ss; cycle 1.
      { des_ifs. }
      clear NONB.
      exploit pure_step_wf; eauto using CtrlState.wf_init. intro WF2.
      unfold pure_job_controller in *. ss.
      unfold sync_istate in *. ss.
      replace (Z.to_nat (3 - Z.of_nat 1)) with 2 in * by ss.
      rewrite <- H5 in *.
      unfold CtrlState.default_mode in *.
      replace (Z.of_nat 1 =? 1)%Z with true in * by ss.
      erewrite <- sim_ctrl_inbox_update_queue in PURE_STEP; try exact CTRL_INBOX1.

      rewrite NEXT in *. inv PURE_STEP.
      replace (CtrlState.mk CtrlState.Active 0 0 0 [0; 0; 0; 0]%Z)
        with (active (active CtrlState.init)) in * by ss.
      exploit next_state_snode_step_normal; eauto. intro STEP_SRC.
      esplits; [exact STEP_SRC|econs 1; eauto|..]; eauto.
      clear NEXT0 STEP_SRC.
      exploit update_owner_mode; eauto. i. symmetry in x0.
      erewrite update_queue_mode in x0; eauto. simpl in x0.

      Transparent nth.
      inv ABST_STEP2.
      { (* On, Off *)
        econs; eauto; ss.
        - econs 5; ss; try congr.
          + rewrite <- x0. ss.
          + apply active_eq; eauto.
          + erewrite SNode.update_outbox_in; ss; try nia.
            { rewrite SNode.update_outbox_length. ss. }
            { apply sanitize_ctrl. ss. }
            { rewrite SNode.update_outbox_length. ss. nia. }
            unfold SNode.get_actual_dest. condtac; ss.
            unfold SNode.check_available. ss.
            destruct grant_src as [[tid msg]|]; cycle 1.
            { rewrite SNode.update_outbox_None. ss. }
            rewrite SNode.update_outbox_check_available; ss.
            exploit grant_tid; eauto. i.
            des; subst; ss; try nia.
          + rewrite <- x0. ss.
        - rewrite SNode.update_outbox_not_in; ss; try nia.
          unfold sim_grant. des_ifs.
        - rewrite SNode.update_outbox_not_in; ss; try nia.
          unfold sim_grant. des_ifs.
        - rewrite SNode.update_outbox_not_in; ss; try nia.
          unfold sim_grant. des_ifs.
      }

      { (* Uninit, On *)
        econs; eauto; ss.
        - econs 7; ss; try congr.
          + rewrite <- x0. ss.
          + apply active_eq; eauto.
          + erewrite SNode.update_outbox_in; ss; try nia.
            { rewrite SNode.update_outbox_length. ss. }
            { apply sanitize_ctrl. ss. }
            { rewrite SNode.update_outbox_length. ss. nia. }
            unfold SNode.get_actual_dest. condtac; ss.
            unfold SNode.check_available. ss.
            destruct grant_src as [[tid msg]|]; cycle 1.
            { rewrite SNode.update_outbox_None. ss. }
            rewrite SNode.update_outbox_check_available; ss.
            exploit grant_tid; eauto. i.
            des; subst; ss; try nia.
        - rewrite SNode.update_outbox_not_in; ss; try nia.
          unfold sim_grant. des_ifs.
        - rewrite SNode.update_outbox_not_in; ss; try nia.
          unfold sim_grant. des_ifs.
        - rewrite SNode.update_outbox_not_in; ss; try nia.
          unfold sim_grant. des_ifs.
      }
    }

    { (* Uninit, Uninit *)
      inv H1. inv H2. inv H3.
      destruct (next_state false (active CtrlState.init) inb1_src)
        as [grant_src st2_src] eqn:NEXT.
      dup NEXT. unfold next_state in NEXT. ss.

      inv ABST_STEP1. inv ABST_STEP2.
      exploit pure_step_wf; try exact PURE_STEP; try apply CtrlState.wf_init. intro WF2.
      exploit pure_step_wf; try exact PURE_STEP0; try apply CtrlState.wf_init. intro WF3.
      unfold pure_job_controller in *.
      unfold sync_istate in *. ss.
      replace (Z.to_nat (3 - Z.of_nat 1)) with 2 in * by ss.
      replace (Z.to_nat (3 - Z.of_nat 2)) with 1 in * by ss.
      rewrite <- H4, <- H5 in *.
      unfold CtrlState.default_mode in *.
      replace (Z.of_nat 1 =? 1)%Z with true in * by ss.
      replace (Z.of_nat 2 =? 1)%Z with false in * by ss.
      erewrite <- sim_ctrl_inbox_update_queue in PURE_STEP; try exact CTRL_INBOX1.
      erewrite <- sim_ctrl_inbox_update_queue in PURE_STEP0; try exact CTRL_INBOX2.

      des; subst; ss.
      move NEXT at bottom. rewrite NEXT in *. inv PURE_STEP. ss.
      erewrite update_queue_active with
          (st:=CtrlState.mk CtrlState.Standby 0 0 0 [0; 0; 0; 0]%Z) in NEXT; ss.
      move PURE_STEP0 at bottom.
      match goal with
      | [H: context[update_owner ?st] |- _] => remember st as ust
      end.
      guardH Hequst.
      exploit update_queue_mode; try exact Hequst. s. i. clear Hequst.
      exploit update_owner_inv; eauto. i. des.
      exploit GRANT_TGT1; try congr. i. subst. clear GRANT_TGT1 GRANT_TGT2.

      replace (CtrlState.mk CtrlState.Active 0 0 0 [0; 0; 0; 0]%Z)
        with (active (active CtrlState.init)) in * by ss.
      exploit next_state_snode_step_normal; eauto. intro STEP_SRC.
      esplits; [exact STEP_SRC|econs 1; eauto|..]; eauto.
      clear NEXT0 STEP_SRC.

      econs; eauto; ss.
      - econs 9; ss.
        + destruct st0; ss. rewrite MODE, x0. ss.
        + erewrite SNode.update_outbox_in; ss; try nia.
          { rewrite SNode.update_outbox_length. ss. }
          { apply sanitize_ctrl. ss. }
          { rewrite SNode.update_outbox_length. ss. nia. }
          unfold SNode.get_actual_dest. condtac; ss.
          unfold SNode.check_available. ss.
          destruct grant_src as [[tid msg]|]; cycle 1.
          { rewrite SNode.update_outbox_None. ss. }
          rewrite SNode.update_outbox_check_available; ss.
          exploit grant_tid; eauto. i.
          des; subst; ss; try nia.
        + rewrite SNode.update_outbox_None.
          erewrite SNode.update_outbox_in; ss; try nia.
          apply sanitize_ctrl. ss.
      - rewrite SNode.update_outbox_not_in; ss; try nia.
        unfold sim_grant. des_ifs.
      - rewrite SNode.update_outbox_not_in; ss; try nia.
        unfold sim_grant. des_ifs.
      - rewrite SNode.update_outbox_not_in; ss; try nia.
        unfold sim_grant. des_ifs.
    }

    { (* On, Off *)
      inv H1. inv H2.
      destruct (next_state (is_stuttering (nth 2 inb1_tgt None) ctrl) (active ctrl) inb1_src)
        as [grant_src st2_src] eqn:NEXT.
      dup NEXT. unfold next_state in NEXT.

      inv ABST_STEP1. des; subst; ss; cycle 1.
      { des_ifs. }
      clear NONB.
      exploit pure_step_wf; eauto using CtrlState.wf_init. intro WF2.
      hexploit pure_step_mode; eauto. i.
      dup PURE_STEP. unfold pure_job_controller in PURE_STEP.

      remember (make_stutter (is_stuttering (nth 2 inb1_tgt None) ctrl) (active ctrl)) as st_src.
      remember (sync_istate (Z.of_nat 1) ctrl inb1_tgt) as st.
      exploit make_stutter_sync_istate; try exact Heqst; eauto.
      i. guardH Heqst. guardH Heqst_src. subst.
      erewrite <- sim_ctrl_inbox_update_queue in PURE_STEP; try exact CTRL_INBOX1.

      erewrite update_queue_active in NEXT; ss.
      move PURE_STEP at bottom.
      match goal with
      | [H: context[update_owner ?st] |- _] => remember st as ust
      end.
      guardH Hequst.
      exploit update_queue_mode; try exact Hequst. i. guardH Hequst.
      exploit update_owner_inv; eauto. i. des.

      destruct (is_stuttering None st2) eqn:STTR2.
      { (* stutter *)
        clear GRANT_SRC.
        destruct (is_stuttering (nth 2 inb1_tgt None) ctrl) eqn:STTR1.
        { exploit is_stuttering_true_next; try eapply PURE_STEP0; eauto. i.
          rewrite x1 in *. ss.
        }
        replace (active ctrl) with (active (active ctrl)) in NEXT0; cycle 1.
        { destruct ctrl; ss. }

        destruct grant as [[tid msg]|].
        { exploit next_state_snode_step_stutter_send; eauto.
          { subst. destruct st2; ss. destruct mode; ss. }
          intro STEP_SRC.
          esplits; [exact STEP_SRC|econs 1; eauto|..]; eauto.
          clear NEXT0 STEP_SRC.
          exploit GRANT_TGT2; eauto.
          { destruct ust.(CtrlState.mode); eauto.
            - exploit GRANT_TGT1; ss.
            - exploit GRANT_TGT1; ss.
          }
          i. subst.

          inv ABST_STEP2.
          { (* On, OFF *)
            econs; eauto; ss.
            - econs 5; ss; try congr.
              + erewrite SNode.update_outbox_in; ss; try nia.
                { rewrite SNode.update_outbox_length. ss. }
                { apply sanitize_ctrl. ss. }
                { unfold SNode.get_actual_dest. condtac; ss. eauto. }
                { rewrite SNode.update_outbox_length. ss. nia. }
                { unfold SNode.get_actual_dest. condtac; ss.
                  unfold SNode.check_available. ss.
                  rewrite SNode.update_outbox_check_available; ss.
                  exploit grant_tid; eauto. i. des; subst; ss; nia.
                }
              + des_ifs.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
          }

          { (* On, Uninit *)
            econs; eauto; ss.
            - econs 7; ss; try congr.
              erewrite SNode.update_outbox_in; ss; try nia.
              { rewrite SNode.update_outbox_length. ss. }
              { apply sanitize_ctrl. ss. }
              { unfold SNode.get_actual_dest. condtac; ss. eauto. }
              { rewrite SNode.update_outbox_length. ss. nia. }
              { unfold SNode.get_actual_dest. condtac; ss.
                unfold SNode.check_available. ss.
                rewrite SNode.update_outbox_check_available; ss.
                exploit grant_tid; eauto. i. des; subst; ss; nia.
              }
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
          }
        }

        { exploit next_state_snode_step_stutter; eauto.
          { subst. destruct st2; ss. destruct mode; ss. }
          intro STEP_SRC.
          esplits; [exact STEP_SRC|econs 1; eauto|..]; eauto.
          clear NEXT0 STEP_SRC.

          inv ABST_STEP2.
          { (* On, OFF *)
            econs; eauto; ss.
            econs 5; ss; try congr.
            - erewrite SNode.update_outbox_in; ss; try nia.
              { apply sanitize_ctrl. ss. }
              { unfold SNode.get_actual_dest. condtac; ss. eauto. }
              { rewrite SNode.update_outbox_length. ss. nia. }
            - des_ifs.
          }

          { (* On, Uninit *)
            econs; eauto; ss.
            econs 7; ss; try congr.
            erewrite SNode.update_outbox_in; ss; try nia.
            { apply sanitize_ctrl. ss. }
            { unfold SNode.get_actual_dest. condtac; ss. eauto. }
            { rewrite SNode.update_outbox_length. ss. nia. }
          }
        }
      }

      { (* normal *)
        replace (active ctrl) with (active (active ctrl)) in NEXT0; cycle 1.
        { destruct ctrl; ss. }
        hexploit pure_step_mode; eauto. i.
        assert (grant = grant_src).
        { destruct st2, mode; ss; eauto.
          exploit GRANT_SRC; eauto. i. subst.
          exploit GRANT_TGT1; eauto. congr.
        }
        subst.
        exploit next_state_snode_step_normal; eauto. intro STEP_SRC.
        esplits; [exact STEP_SRC|econs 1; eauto|..]; eauto.
        clear NEXT0 STEP_SRC.

        inv ABST_STEP2.
        { (* On, OFF *)
          econs; eauto; ss.
          - econs 5; ss; try congr.
            + erewrite SNode.update_outbox_in; ss; try nia.
              { rewrite SNode.update_outbox_length. ss. }
              { apply sanitize_ctrl. ss. }
              { unfold SNode.get_actual_dest. condtac; ss. eauto. }
              { rewrite SNode.update_outbox_length. ss. nia. }
              { unfold SNode.get_actual_dest. condtac; ss.
                unfold SNode.check_available. ss.
                destruct grant_src as [[]|]; cycle 1.
                { rewrite SNode.update_outbox_None. ss. }
                rewrite SNode.update_outbox_check_available; ss.
                exploit grant_tid; eauto. i. des; subst; ss; nia.
              }
            + des_ifs.
          - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
            { unfold SNode.get_actual_dest. condtac; ss. nia. }
            unfold sim_grant. des_ifs.
          - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
            { unfold SNode.get_actual_dest. condtac; ss. nia. }
            unfold sim_grant. des_ifs.
          - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
            { unfold SNode.get_actual_dest. condtac; ss. nia. }
            unfold sim_grant. des_ifs.
        }

        { (* On, Uninit *)
          econs; eauto; ss.
          - econs 7; ss; try congr.
            erewrite SNode.update_outbox_in; ss; try nia.
            { rewrite SNode.update_outbox_length. ss. }
            { apply sanitize_ctrl. ss. }
            { unfold SNode.get_actual_dest. condtac; ss. eauto. }
            { rewrite SNode.update_outbox_length. ss. nia. }
            { unfold SNode.get_actual_dest. condtac; ss.
              unfold SNode.check_available. ss.
              destruct grant_src as [[]|]; cycle 1.
              { rewrite SNode.update_outbox_None. ss. }
              rewrite SNode.update_outbox_check_available; ss.
              exploit grant_tid; eauto. i. des; subst; ss; nia.
            }
          - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
            { unfold SNode.get_actual_dest. condtac; ss. nia. }
            unfold sim_grant. des_ifs.
          - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
            { unfold SNode.get_actual_dest. condtac; ss. nia. }
            unfold sim_grant. des_ifs.
          - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
            { unfold SNode.get_actual_dest. condtac; ss. nia. }
            unfold sim_grant. des_ifs.
        }
      }
    }

    { (* Off, On *)
      inv H1. inv H2.
      destruct (next_state (is_stuttering (nth 1 inb2_tgt None) ctrl) (active ctrl) inb1_src)
        as [grant_src st2_src] eqn:NEXT.
      dup NEXT. unfold next_state in NEXT.

      inv ABST_STEP2. des; subst; ss; cycle 1.
      { des_ifs. }
      clear NONB.
      exploit pure_step_wf; eauto using CtrlState.wf_init. intro WF2.
      hexploit pure_step_mode; eauto. i.
      dup PURE_STEP. unfold pure_job_controller in PURE_STEP.

      remember (make_stutter (is_stuttering (nth 1 inb2_tgt None) ctrl) (active ctrl)) as st_src.
      remember (sync_istate (Z.of_nat 2) ctrl inb2_tgt) as st.
      exploit make_stutter_sync_istate; try exact Heqst; eauto.
      i. guardH Heqst. guardH Heqst_src. subst.
      erewrite <- sim_ctrl_inbox_update_queue in PURE_STEP; try exact CTRL_INBOX2.

      erewrite update_queue_active in NEXT; ss.
      move PURE_STEP at bottom.
      match goal with
      | [H: context[update_owner ?st] |- _] => remember st as ust
      end.
      guardH Hequst.
      exploit update_queue_mode; try exact Hequst. i. guardH Hequst.
      exploit update_owner_inv; eauto. i. des.

      destruct (is_stuttering None st2) eqn:STTR2.
      { (* stutter *)
        clear GRANT_SRC.
        destruct (is_stuttering (nth 1 inb2_tgt None) ctrl) eqn:STTR1.
        { exploit is_stuttering_true_next; try eapply PURE_STEP0; eauto. i.
          rewrite x1 in *. ss.
        }
        replace (active ctrl) with (active (active ctrl)) in NEXT0; cycle 1.
        { destruct ctrl; ss. }

        destruct grant as [[tid msg]|].
        { exploit next_state_snode_step_stutter_send; eauto.
          { subst. destruct st2; ss. destruct mode; ss. }
          intro STEP_SRC.
          esplits; [exact STEP_SRC|econs 1; eauto|..]; eauto.
          clear NEXT0 STEP_SRC.
          exploit GRANT_TGT2; eauto.
          { destruct ust.(CtrlState.mode); eauto.
            - exploit GRANT_TGT1; ss.
            - exploit GRANT_TGT1; ss.
          }
          i. subst.

          inv ABST_STEP1.
          { (* On, OFF *)
            econs; eauto; ss.
            - econs 6; ss; try congr.
              + des_ifs.
              + erewrite SNode.update_outbox_in; ss; try nia.
                { rewrite SNode.update_outbox_length. ss. }
                { apply sanitize_ctrl. ss. }
                { unfold SNode.get_actual_dest. condtac; ss. eauto. }
                { rewrite SNode.update_outbox_length. ss. nia. }
                { unfold SNode.get_actual_dest. condtac; ss.
                  unfold SNode.check_available. ss.
                  rewrite SNode.update_outbox_check_available; ss.
                  exploit grant_tid; eauto. i. des; subst; ss; nia.
                }
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
          }

          { (* On, Uninit *)
            econs; eauto; ss.
            - econs 8; ss; try congr.
              erewrite SNode.update_outbox_in; ss; try nia.
              { rewrite SNode.update_outbox_length. ss. }
              { apply sanitize_ctrl. ss. }
              { unfold SNode.get_actual_dest. condtac; ss. eauto. }
              { rewrite SNode.update_outbox_length. ss. nia. }
              { unfold SNode.get_actual_dest. condtac; ss.
                unfold SNode.check_available. ss.
                rewrite SNode.update_outbox_check_available; ss.
                exploit grant_tid; eauto. i. des; subst; ss; nia.
              }
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
          }
        }

        { exploit next_state_snode_step_stutter; eauto.
          { subst. destruct st2; ss. destruct mode; ss. }
          intro STEP_SRC.
          esplits; [exact STEP_SRC|econs 1; eauto|..]; eauto.
          clear NEXT0 STEP_SRC.

          inv ABST_STEP1.
          { (* On, OFF *)
            econs; eauto; ss.
            econs 6; ss; try congr.
            - des_ifs.
            - erewrite SNode.update_outbox_in; ss; try nia.
              { apply sanitize_ctrl. ss. }
              { unfold SNode.get_actual_dest. condtac; ss. eauto. }
              { rewrite SNode.update_outbox_length. ss. nia. }
          }

          { (* On, Uninit *)
            econs; eauto; ss.
            econs 8; ss; try congr.
            erewrite SNode.update_outbox_in; ss; try nia.
            { apply sanitize_ctrl. ss. }
            { unfold SNode.get_actual_dest. condtac; ss. eauto. }
            { rewrite SNode.update_outbox_length. ss. nia. }
          }
        }
      }

      { (* normal *)
        replace (active ctrl) with (active (active ctrl)) in NEXT0; cycle 1.
        { destruct ctrl; ss. }
        hexploit pure_step_mode; eauto. i.
        assert (grant = grant_src).
        { destruct st2, mode; ss; eauto.
          exploit GRANT_SRC; eauto. i. subst.
          exploit GRANT_TGT1; eauto. congr.
        }
        subst.
        exploit next_state_snode_step_normal; eauto. intro STEP_SRC.
        esplits; [exact STEP_SRC|econs 1; eauto|..]; eauto.
        clear NEXT0 STEP_SRC.

        inv ABST_STEP1.
        { (* On, OFF *)
          econs; eauto; ss.
          - econs 6; ss; try congr.
            + des_ifs.
            + erewrite SNode.update_outbox_in; ss; try nia.
              { rewrite SNode.update_outbox_length. ss. }
              { apply sanitize_ctrl. ss. }
              { unfold SNode.get_actual_dest. condtac; ss. eauto. }
              { rewrite SNode.update_outbox_length. ss. nia. }
              { unfold SNode.get_actual_dest. condtac; ss.
                unfold SNode.check_available. ss.
                destruct grant_src as [[]|]; cycle 1.
                { rewrite SNode.update_outbox_None. ss. }
                rewrite SNode.update_outbox_check_available; ss.
                exploit grant_tid; eauto. i. des; subst; ss; nia.
              }
          - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
            { unfold SNode.get_actual_dest. condtac; ss. nia. }
            unfold sim_grant. des_ifs.
          - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
            { unfold SNode.get_actual_dest. condtac; ss. nia. }
            unfold sim_grant. des_ifs.
          - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
            { unfold SNode.get_actual_dest. condtac; ss. nia. }
            unfold sim_grant. des_ifs.
        }

        { (* On, Uninit *)
          econs; eauto; ss.
          - econs 8; ss; try congr.
            erewrite SNode.update_outbox_in; ss; try nia.
            { rewrite SNode.update_outbox_length. ss. }
            { apply sanitize_ctrl. ss. }
            { unfold SNode.get_actual_dest. condtac; ss. eauto. }
            { rewrite SNode.update_outbox_length. ss. nia. }
            { unfold SNode.get_actual_dest. condtac; ss.
              unfold SNode.check_available. ss.
              destruct grant_src as [[]|]; cycle 1.
              { rewrite SNode.update_outbox_None. ss. }
              rewrite SNode.update_outbox_check_available; ss.
              exploit grant_tid; eauto. i. des; subst; ss; nia.
            }
          - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
            { unfold SNode.get_actual_dest. condtac; ss. nia. }
            unfold sim_grant. des_ifs.
          - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
            { unfold SNode.get_actual_dest. condtac; ss. nia. }
            unfold sim_grant. des_ifs.
          - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
            { unfold SNode.get_actual_dest. condtac; ss. nia. }
            unfold sim_grant. des_ifs.
        }
      }
    }

    { (* On, Uninit *)
      inv H1. inv H2.
      match goal with
      | [H:context[single_ctrl_state _ (?sttr, _)] |- _] =>
        replace sttr with (is_stuttering None ctrl) in * by ss
      end.
      Opaque is_stuttering. inv H3.
      destruct (next_state (is_stuttering None ctrl) (active ctrl) inb1_src)
        as [grant_src st2_src] eqn:NEXT.
      dup NEXT. unfold next_state in NEXT.

      inv ABST_STEP1. des; subst; ss; cycle 1.
      { des_ifs. }
      clear NONB.
      exploit pure_step_wf; eauto. intro WF2.
      hexploit pure_step_mode; eauto. i.
      dup PURE_STEP. unfold pure_job_controller in PURE_STEP.

      remember (make_stutter (is_stuttering None ctrl) (active ctrl)) as st_src.
      remember (sync_istate (Z.of_nat 1) ctrl inb1_tgt) as st.
      exploit make_stutter_sync_istate_None; try exact Heqst; eauto.
      s. rewrite <- H5, <- Heqst_src. i. des.
      guardH Heqst. guardH Heqst_src. subst.
      erewrite <- sim_ctrl_inbox_update_queue in PURE_STEP; try exact CTRL_INBOX1.
      rewrite NEXT in *. inv PURE_STEP.
      exploit update_owner_mode; eauto. i. symmetry in x0.
      erewrite update_queue_mode in x0; eauto.
      rewrite <- Heqst, MODE in x0. symmetry in x0.

      inv ABST_STEP2. guardH OUT.
      exploit pure_step_wf; try exact PURE_STEP; try apply CtrlState.wf_init. intro WF3.
      hexploit pure_step_mode; try eapply PURE_STEP. i.
      dup PURE_STEP. unfold pure_job_controller in PURE_STEP.

      remember (sync_istate (Z.of_nat 2) CtrlState.init inb2_tgt) as st'.
      exploit make_stutter_sync_istate_uninit; try exact Heqst'; eauto.
      s. unfold is_stuttering at 1. rewrite MSG1. i. des.
      guardH Heqst'.
      erewrite <- sim_ctrl_inbox_update_queue in PURE_STEP; try exact CTRL_INBOX2.

      exploit standby_grant_None; eauto. i. subst.
      exploit update_owner_mode; try exact PURE_STEP. i. symmetry in x1.
      erewrite update_queue_mode in x1; eauto.
      rewrite MODE0 in x1. symmetry in x1.

      replace (active ctrl) with (active (active ctrl)) in NEXT0; cycle 1.
      { rewrite active_eq; ss. destruct ctrl. ss. }
      exploit next_state_snode_step_normal; eauto.
      instantiate (1:=tm). intro STEP_SRC.

      inv OUT; des; subst.
      { (* On, On *)
        esplits; eauto; [econs 1; eauto|].
        econs; eauto; ss.
        - econs 9; eauto.
          + rewrite x0, x1. ss.
          + erewrite SNode.update_outbox_in; ss; try nia.
            { rewrite SNode.update_outbox_length. ss. }
            { apply sanitize_ctrl. ss. }
            { unfold SNode.get_actual_dest. condtac; ss. eauto. }
            { rewrite SNode.update_outbox_length. ss. nia. }
            { unfold SNode.get_actual_dest. condtac; ss.
              unfold SNode.check_available. ss.
              destruct grant_src as [[]|]; cycle 1.
              { rewrite SNode.update_outbox_None. ss. }
              rewrite SNode.update_outbox_check_available; ss.
              exploit grant_tid; eauto. i. des; subst; ss; nia.
            }
          + erewrite SNode.update_outbox_in; ss; try nia.
            { apply sanitize_ctrl. ss. }
            { unfold SNode.get_actual_dest. condtac; ss. eauto. }
            { rewrite SNode.update_outbox_length. ss. nia. }
        - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
          { unfold SNode.get_actual_dest. condtac; ss. nia. }
          unfold sim_grant. des_ifs.
        - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
          { unfold SNode.get_actual_dest. condtac; ss. nia. }
          unfold sim_grant. des_ifs.
        - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
          { unfold SNode.get_actual_dest. condtac; ss. nia. }
          unfold sim_grant. des_ifs.
      }

      { (* On, Off *)
        esplits; eauto; [econs 1; eauto|].
        econs; eauto; ss.
        - econs 5; eauto.
          + Transparent is_stuttering. unfold is_stuttering.
            rewrite x0. des_ifs.
          + apply active_eq. ss.
          + erewrite SNode.update_outbox_in; ss; try nia.
            { rewrite SNode.update_outbox_length. ss. }
            { apply sanitize_ctrl. ss. }
            { unfold SNode.get_actual_dest. condtac; ss. eauto. }
            { rewrite SNode.update_outbox_length. ss. nia. }
            { unfold SNode.get_actual_dest. condtac; ss.
              unfold SNode.check_available. ss.
              destruct grant_src as [[]|]; cycle 1.
              { rewrite SNode.update_outbox_None. ss. }
              rewrite SNode.update_outbox_check_available; ss.
              exploit grant_tid; eauto. i. des; subst; ss; nia.
            }
          + rewrite x0. ss.
        - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
          { unfold SNode.get_actual_dest. condtac; ss. nia. }
          unfold sim_grant. des_ifs.
          + unguardH OUT. des; subst; ss.
          + unguardH OUT. des; subst; ss.
        - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
          { unfold SNode.get_actual_dest. condtac; ss. nia. }
          unfold sim_grant. des_ifs.
          + unguardH OUT. des; subst; ss.
          + unguardH OUT. des; subst; ss.
        - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
          { unfold SNode.get_actual_dest. condtac; ss. nia. }
          unfold sim_grant. des_ifs.
          + unguardH OUT. des; subst; ss.
          + unguardH OUT. des; subst; ss.
      }
    }

    { (* Uninit, On *)
      inv H1. inv H2.
      match goal with
      | [H:context[single_ctrl_state _ (?sttr, _)] |- _] =>
        replace sttr with (is_stuttering None ctrl) in * by ss
      end.
      Opaque is_stuttering. inv H3.
      destruct (next_state (is_stuttering None ctrl) (active ctrl) inb1_src)
        as [grant_src st2_src] eqn:NEXT.
      dup NEXT. unfold next_state in NEXT.

      inv ABST_STEP2. des; subst; ss; cycle 1.
      { des_ifs. }
      clear NONB.
      exploit pure_step_wf; eauto. intro WF2.
      hexploit pure_step_mode; eauto. i.
      dup PURE_STEP. unfold pure_job_controller in PURE_STEP.

      remember (make_stutter (is_stuttering None ctrl) (active ctrl)) as st_src.
      remember (sync_istate (Z.of_nat 2) ctrl inb2_tgt) as st.
      exploit make_stutter_sync_istate_None; try exact Heqst; eauto.
      s. rewrite <- H4, <- Heqst_src. i. des.
      guardH Heqst. guardH Heqst_src. subst.
      erewrite <- sim_ctrl_inbox_update_queue in PURE_STEP; try exact CTRL_INBOX2.
      rewrite NEXT in *. inv PURE_STEP.
      exploit update_owner_mode; eauto. i. symmetry in x0.
      erewrite update_queue_mode in x0; eauto.
      rewrite <- Heqst, MODE in x0. symmetry in x0.

      inv ABST_STEP1. guardH OUT.
      exploit pure_step_wf; try exact PURE_STEP; try apply CtrlState.wf_init. intro WF3.
      hexploit pure_step_mode; try eapply PURE_STEP. i.
      dup PURE_STEP. unfold pure_job_controller in PURE_STEP.

      remember (sync_istate (Z.of_nat 1) CtrlState.init inb1_tgt) as st'.
      exploit make_stutter_sync_istate_uninit; try exact Heqst'; eauto.
      s. unfold is_stuttering at 1. rewrite MSG2. i. des.
      guardH Heqst'.
      erewrite <- sim_ctrl_inbox_update_queue in PURE_STEP; try exact CTRL_INBOX1.

      exploit standby_grant_None; eauto. i. subst.
      exploit update_owner_mode; try exact PURE_STEP. i. symmetry in x1.
      erewrite update_queue_mode in x1; eauto.
      rewrite MODE0 in x1. symmetry in x1.

      replace (active ctrl) with (active (active ctrl)) in NEXT0; cycle 1.
      { rewrite active_eq; ss. destruct ctrl. ss. }
      exploit next_state_snode_step_normal; eauto.
      instantiate (1:=tm). intro STEP_SRC.

      inv OUT; des; subst.
      { (* On, On *)
        esplits; eauto; [econs 1; eauto|].
        econs; eauto; ss.
        - econs 9; eauto.
          + rewrite x0, x1. ss.
          + erewrite SNode.update_outbox_in; ss; try nia.
            { apply sanitize_ctrl. ss. }
            { unfold SNode.get_actual_dest. condtac; ss. eauto. }
            { rewrite SNode.update_outbox_length. ss. nia. }
          + erewrite SNode.update_outbox_in; ss; try nia.
            { rewrite SNode.update_outbox_length. ss. }
            { apply sanitize_ctrl. ss. }
            { unfold SNode.get_actual_dest. condtac; ss. eauto. }
            { rewrite SNode.update_outbox_length. ss. nia. }
            { unfold SNode.get_actual_dest. condtac; ss.
              unfold SNode.check_available. ss.
              destruct grant_src as [[]|]; cycle 1.
              { rewrite SNode.update_outbox_None. ss. }
              rewrite SNode.update_outbox_check_available; ss.
              exploit grant_tid; eauto. i. des; subst; ss; nia.
            }
        - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
          { unfold SNode.get_actual_dest. condtac; ss. nia. }
          unfold sim_grant. des_ifs.
        - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
          { unfold SNode.get_actual_dest. condtac; ss. nia. }
          unfold sim_grant. des_ifs.
        - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
          { unfold SNode.get_actual_dest. condtac; ss. nia. }
          unfold sim_grant. des_ifs.
      }

      { (* On, Off *)
        esplits; eauto; [econs 1; eauto|].
        econs; eauto; ss.
        - econs 6; eauto.
          + Transparent is_stuttering. unfold is_stuttering.
            rewrite x0. des_ifs.
          + apply active_eq. ss.
          + rewrite x0. ss.
          + erewrite SNode.update_outbox_in; ss; try nia.
            { rewrite SNode.update_outbox_length. ss. }
            { apply sanitize_ctrl. ss. }
            { unfold SNode.get_actual_dest. condtac; ss. eauto. }
            { rewrite SNode.update_outbox_length. ss. nia. }
            { unfold SNode.get_actual_dest. condtac; ss.
              unfold SNode.check_available. ss.
              destruct grant_src as [[]|]; cycle 1.
              { rewrite SNode.update_outbox_None. ss. }
              rewrite SNode.update_outbox_check_available; ss.
              exploit grant_tid; eauto. i. des; subst; ss; nia.
            }
        - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
          { unfold SNode.get_actual_dest. condtac; ss. nia. }
          unfold sim_grant. des_ifs.
          + unguardH OUT. des; subst; ss.
          + unguardH OUT. des; subst; ss.
        - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
          { unfold SNode.get_actual_dest. condtac; ss. nia. }
          unfold sim_grant. des_ifs.
          + unguardH OUT. des; subst; ss.
          + unguardH OUT. des; subst; ss.
        - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
          { unfold SNode.get_actual_dest. condtac; ss. nia. }
          unfold sim_grant. des_ifs.
          + unguardH OUT. des; subst; ss.
          + unguardH OUT. des; subst; ss.
      }
    }

    { (* On, On *)
      inv H1. inv H2. inv H3. rename sctrl0 into sctrl.
      destruct (next_state false sctrl inb1_src) as [grant_src st2_src] eqn:NEXT.
      dup NEXT. unfold next_state in NEXT.

      inv ABST_STEP1. inv ABST_STEP2.
      guardH OUT. guardH OUT0.
      exploit pure_step_wf; try exact PURE_STEP; eauto. intro WF3.
      exploit pure_step_wf; try exact PURE_STEP0; eauto. intro WF4.
      dup PURE_STEP. unfold pure_job_controller in PURE_STEP.
      dup PURE_STEP0. unfold pure_job_controller in PURE_STEP0.

      remember (make_stutter false sctrl) as st_src.
      remember (sync_istate (Z.of_nat 1) ctrl1 inb1_tgt) as st1_tgt.
      remember (sync_istate (Z.of_nat 2) ctrl2 inb2_tgt) as st2_tgt.

      erewrite <- sim_ctrl_inbox_update_queue in PURE_STEP; try exact CTRL_INBOX1.
      erewrite <- sim_ctrl_inbox_update_queue in PURE_STEP0; try exact CTRL_INBOX2.
      exploit make_stutter_sync_istate_both;
        [exact Heqst_src|exact Heqst1_tgt|exact Heqst2_tgt|..]; eauto.
      guardH Heqst_src. guardH Heqst1_tgt. guardH Heqst2_tgt.
      move NEXT at bottom. clear SCTRL.
      i. des; subst.

      { (* Active, Standby *)
        rewrite NEXT in PURE_STEP. inv PURE_STEP.
        erewrite update_queue_active in NEXT; ss.
        remember (update_queue st2_tgt inb1_src) as ust. guardH Hequst.
        exploit update_queue_mode; try exact Hequst. i.
        exploit update_owner_inv; eauto. i. des. unguardH Hequst. subst.
        exploit standby_grant_None; eauto. i. subst.
        clear GRANT_TGT1 GRANT_TGT2.
        symmetry in MODE. erewrite update_queue_mode in MODE; eauto.
        unguardH Heqst_src. subst.
        replace (active st2_tgt) with (active (active (st2_tgt))) in NEXT0; cycle 1.
        { rewrite active_eq; ss. }

        inv OUT; des; subst.
        { exploit next_state_snode_step_normal; eauto. intro STEP_SRC.
          esplits; eauto; [econs 1; eauto|..].
          inv OUT0; des; subst.
          { (* On, On *)
            econs; eauto.
            - econs 9; eauto.
              + rewrite <- MODE. rewrite MODE2. destruct st0; ss.
              + erewrite SNode.update_outbox_in; ss; try nia.
                { rewrite SNode.update_outbox_length. ss. }
                { apply sanitize_ctrl. ss. }
                { unfold SNode.get_actual_dest. condtac; ss. eauto. }
                { rewrite SNode.update_outbox_length. ss. nia. }
                { unfold SNode.get_actual_dest. condtac; ss.
                  unfold SNode.check_available. ss.
                  destruct grant_src as [[]|]; cycle 1.
                  { rewrite SNode.update_outbox_None. ss. }
                  rewrite SNode.update_outbox_check_available; ss.
                  exploit grant_tid; eauto. i. des; subst; ss; nia.
                }
              + erewrite SNode.update_outbox_in; ss; try nia.
                { apply sanitize_ctrl. ss. }
                { unfold SNode.get_actual_dest. condtac; ss. eauto. }
                { rewrite SNode.update_outbox_length. ss. nia. }
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
          }
          { (* On, Off *)
            econs; eauto.
            - econs 5; eauto.
              + unfold is_stuttering. destruct st0; ss. des_ifs.
              + destruct st0. ss.
              + apply active_eq. destruct st0. ss.
              + erewrite SNode.update_outbox_in; ss; try nia.
                { rewrite SNode.update_outbox_length. ss. }
                { apply sanitize_ctrl. ss. }
                { unfold SNode.get_actual_dest. condtac; ss. eauto. }
                { rewrite SNode.update_outbox_length. ss. nia. }
                { unfold SNode.get_actual_dest. condtac; ss.
                  unfold SNode.check_available. ss.
                  destruct grant_src as [[]|]; cycle 1.
                  { rewrite SNode.update_outbox_None. ss. }
                  rewrite SNode.update_outbox_check_available; ss.
                  exploit grant_tid; eauto. i. des; subst; ss; nia.
                }
              + destruct st0. ss.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
              + unguardH OUT. des; subst; ss.
              + unguardH OUT. des; subst; ss.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
              + unguardH OUT. des; subst; ss.
              + unguardH OUT. des; subst; ss.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
              + unguardH OUT. des; subst; ss.
              + unguardH OUT. des; subst; ss.
          }
        }

        { (* Off, On *)
          inv OUT0; des; subst; ss.
          destruct (classic (
                        outb1 =
                        SNode.update_outbox sntz 6 mcasts
                                            (SNode.update_outbox sntz 6 mcasts (SNode.init_box 6) grant_src)
                                            (Some (Z.to_nat (3 - Z.of_nat 1), CtrlState.to_bytes (active st0))) \/
                        (CtrlState.timeout st0 =? SpecController.MAX_TIMEOUT)%Z = false)).
          { (* normal *)
            exploit next_state_snode_step_normal; eauto. intro STEP_SRC.
            esplits; eauto; [econs 1; eauto|..].
            econs; eauto.
            - econs 6; eauto.
              + unfold is_stuttering. des; subst.
                * erewrite SNode.update_outbox_in; ss; try nia.
                  { rewrite SNode.update_outbox_length. ss. }
                  { unfold SNode.get_actual_dest. condtac; ss. eauto. }
                  { rewrite SNode.update_outbox_length. ss. nia. }
                  { unfold SNode.get_actual_dest. condtac; ss.
                    unfold SNode.check_available. ss.
                    destruct grant_src as [[]|]; cycle 1.
                    { rewrite SNode.update_outbox_None. ss. }
                    rewrite SNode.update_outbox_check_available; ss.
                    exploit grant_tid; eauto. i. des; subst; ss; nia.
                  }
                * des_ifs.
              + congr.
              + rewrite <- MODE. rewrite MODE2.
                clear H. unguardH OUT. des; subst.
                * ss.
                * ss.
                * destruct grant_src as [[]|]; cycle 1.
                  { rewrite SNode.update_outbox_None. ss. }
                  erewrite SNode.update_outbox_not_in; ss; try nia.
                  exploit grant_tid; eauto. i.
                  unfold SNode.get_actual_dest.
                  des; subst; condtac; ss; nia.
                * erewrite SNode.update_outbox_in; ss; try nia.
                  { unfold resize_bytes.
                    rewrite to_bytes_length; ss.
                    rewrite app_nil_r.
                    replace 8 with (length (CtrlState.to_bytes (active st0)))
                      by (apply to_bytes_length; ss).
                    rewrite firstn_all.
                    rewrite of_bytes_to_bytes; ss.
                    apply active_eq. destruct st0; ss.
                  }
                  { rewrite SNode.update_outbox_length. ss. }
                  { unfold SNode.get_actual_dest. condtac; ss. nia. }
                  { rewrite SNode.update_outbox_length. ss. nia. }
                  { unfold SNode.get_actual_dest. condtac; ss.
                    unfold SNode.check_available. ss.
                    destruct grant_src as [[]|]; cycle 1.
                    { rewrite SNode.update_outbox_None. ss. }
                    rewrite SNode.update_outbox_check_available; ss.
                    exploit grant_tid; eauto. i. des; subst; ss; nia.
                  }
              + erewrite SNode.update_outbox_in; ss; try nia.
                { apply sanitize_ctrl. ss. }
                { unfold SNode.get_actual_dest. condtac; ss. eauto. }
                { rewrite SNode.update_outbox_length. ss. nia. }
            - des; subst.
              + rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                unfold sim_grant. des_ifs.
              + exploit GRANT_SRC; eauto. i. subst.
                rewrite SNode.update_outbox_None.
                unguardH OUT. des; subst; ss.
            - des; subst.
              + rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                unfold sim_grant. des_ifs.
              + exploit GRANT_SRC; eauto. i. subst.
                rewrite SNode.update_outbox_None.
                unguardH OUT. des; subst; ss.
            - des; subst.
              + rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                unfold sim_grant. des_ifs.
              + exploit GRANT_SRC; eauto. i. subst.
                rewrite SNode.update_outbox_None.
                unguardH OUT. des; subst; ss.
          }

          { (* stutter *)
            destruct (CtrlState.timeout st0 =? SpecController.MAX_TIMEOUT)%Z eqn:TOUT; cycle 1.
            { exfalso. eauto. }
            unguardH OUT. inv OUT.
            { (* stutter no send *)
              exploit next_state_snode_step_stutter; eauto.
              { destruct st0. ss. }
              intro STEP_SRC.
              esplits; eauto; [econs 1; eauto|..].
              econs; eauto.
              - econs 6; eauto.
                + unfold is_stuttering.
                  rewrite <- MODE. rewrite MODE2. condtac; ss.
                  des; subst; ss.
                + congr.
                + rewrite <- MODE. rewrite MODE2. des; subst; ss.
                + erewrite SNode.update_outbox_in; ss; try nia.
                  { apply sanitize_ctrl. ss. }
                  { unfold SNode.get_actual_dest. condtac; ss. eauto. }
                  { rewrite SNode.update_outbox_length. ss. nia. }
              - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                unfold sim_grant. des; subst; des_ifs.
              - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                unfold sim_grant. des; subst; des_ifs.
              - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                unfold sim_grant. des; subst; des_ifs.
            }

            { (* stutter send *)
              des; cycle 1.
              { exfalso. eauto. }
              clear H. subst.
              exploit next_state_snode_step_stutter_send; eauto.
              { destruct st0. ss. }
              intro STEP_SRC.
              esplits; eauto; [econs 1; eauto|..].
              econs; eauto.
              - econs 6; eauto.
                + unfold is_stuttering.
                  rewrite <- MODE. rewrite MODE2.
                  destruct grant_src as [[]|]; cycle 1.
                  { rewrite SNode.update_outbox_None. ss. }
                  rewrite SNode.update_outbox_not_in; ss; try nia.
                  exploit grant_tid; eauto. i.
                  unfold SNode.get_actual_dest.
                  des; subst; condtac; ss; try nia.
                + congr.
                + rewrite <- MODE. rewrite MODE2.
                  destruct grant_src as [[]|]; cycle 1.
                  { rewrite SNode.update_outbox_None. ss. }
                  erewrite SNode.update_outbox_not_in; ss; try nia.
                  exploit grant_tid; eauto. i.
                  unfold SNode.get_actual_dest.
                  des; subst; condtac; ss; nia.
                + erewrite SNode.update_outbox_in; ss; try nia.
                  { apply sanitize_ctrl. ss. }
                  { unfold SNode.get_actual_dest. condtac; ss. eauto. }
                  { rewrite SNode.update_outbox_length. ss. nia. }
              - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                rewrite SNode.update_outbox_None. ss.
                unfold sim_grant. des_ifs.
              - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                rewrite SNode.update_outbox_None. ss.
                unfold sim_grant. des_ifs.
              - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                rewrite SNode.update_outbox_None. ss.
                unfold sim_grant. des_ifs.
            }
          }
        }
      }

      { (* Standby, Active *)
        rewrite NEXT in PURE_STEP0. inv PURE_STEP0.
        erewrite update_queue_active in NEXT; ss.
        remember (update_queue st1_tgt inb1_src) as ust. guardH Hequst.
        exploit update_queue_mode; try exact Hequst. i.
        exploit update_owner_inv; eauto. i. des. unguardH Hequst. subst.
        exploit standby_grant_None; eauto. i. subst.
        clear GRANT_TGT1 GRANT_TGT2.
        symmetry in MODE. erewrite update_queue_mode in MODE; eauto.
        unguardH Heqst_src. subst.
        replace (active st1_tgt) with (active (active (st1_tgt))) in NEXT0; cycle 1.
        { rewrite active_eq; ss. }

        inv OUT0; des; subst.
        { exploit next_state_snode_step_normal; eauto. intro STEP_SRC.
          esplits; eauto; [econs 1; eauto|..].
          inv OUT; des; subst.
          { (* On, On *)
            econs; eauto.
            - econs 9; eauto.
              + rewrite <- MODE. rewrite MODE1. destruct st2; ss.
              + erewrite SNode.update_outbox_in; ss; try nia.
                { apply sanitize_ctrl. ss. }
                { unfold SNode.get_actual_dest. condtac; ss. eauto. }
                { rewrite SNode.update_outbox_length. ss. nia. }
              + erewrite SNode.update_outbox_in; ss; try nia.
                { rewrite SNode.update_outbox_length. ss. }
                { apply sanitize_ctrl. ss. }
                { unfold SNode.get_actual_dest. condtac; ss. eauto. }
                { rewrite SNode.update_outbox_length. ss. nia. }
                { unfold SNode.get_actual_dest. condtac; ss.
                  unfold SNode.check_available. ss.
                  destruct grant_src as [[]|]; cycle 1.
                  { rewrite SNode.update_outbox_None. ss. }
                  rewrite SNode.update_outbox_check_available; ss.
                  exploit grant_tid; eauto. i. des; subst; ss; nia.
                }
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
          }
          { (* Off, On *)
            econs; eauto.
            - econs 6; eauto.
              + unfold is_stuttering. destruct st2; ss. des_ifs.
              + destruct st2. ss.
              + apply active_eq. destruct st2. ss.
              + destruct st2. ss.
              + erewrite SNode.update_outbox_in; ss; try nia.
                { rewrite SNode.update_outbox_length. ss. }
                { apply sanitize_ctrl. ss. }
                { unfold SNode.get_actual_dest. condtac; ss. eauto. }
                { rewrite SNode.update_outbox_length. ss. nia. }
                { unfold SNode.get_actual_dest. condtac; ss.
                  unfold SNode.check_available. ss.
                  destruct grant_src as [[]|]; cycle 1.
                  { rewrite SNode.update_outbox_None. ss. }
                  rewrite SNode.update_outbox_check_available; ss.
                  exploit grant_tid; eauto. i. des; subst; ss; nia.
                }
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
              + unguardH OUT. des; subst; ss.
              + unguardH OUT. des; subst; ss.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
              + unguardH OUT. des; subst; ss.
              + unguardH OUT. des; subst; ss.
            - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
              { unfold SNode.get_actual_dest. condtac; ss. nia. }
              unfold sim_grant. des_ifs.
              + unguardH OUT. des; subst; ss.
              + unguardH OUT. des; subst; ss.
          }
        }

        { (* On, Off *)
          inv OUT; des; subst; ss.
          destruct (classic (
                        outb2 =
                        SNode.update_outbox sntz 6 mcasts
                                            (SNode.update_outbox sntz 6 mcasts (SNode.init_box 6) grant_src)
                                            (Some (Z.to_nat (3 - Z.of_nat 2), CtrlState.to_bytes (active st2))) \/
                        (CtrlState.timeout st2 =? SpecController.MAX_TIMEOUT)%Z = false)).
          { (* normal *)
            exploit next_state_snode_step_normal; eauto. intro STEP_SRC.
            esplits; eauto; [econs 1; eauto|..].
            econs; eauto.
            - econs 5; eauto.
              + unfold is_stuttering. des; subst.
                * erewrite SNode.update_outbox_in; ss; try nia.
                  { rewrite SNode.update_outbox_length. ss. }
                  { unfold SNode.get_actual_dest. condtac; ss. eauto. }
                  { rewrite SNode.update_outbox_length. ss. nia. }
                  { unfold SNode.get_actual_dest. condtac; ss.
                    unfold SNode.check_available. ss.
                    destruct grant_src as [[]|]; cycle 1.
                    { rewrite SNode.update_outbox_None. ss. }
                    rewrite SNode.update_outbox_check_available; ss.
                    exploit grant_tid; eauto. i. des; subst; ss; nia.
                  }
                * des_ifs.
              + congr.
              + erewrite SNode.update_outbox_in; ss; try nia.
                { apply sanitize_ctrl. ss. }
                { unfold SNode.get_actual_dest. condtac; ss. eauto. }
                { rewrite SNode.update_outbox_length. ss. nia. }
              + rewrite <- MODE. rewrite MODE1.
                clear H. unguardH OUT0. des; subst.
                * ss.
                * ss.
                * destruct grant_src as [[]|]; cycle 1.
                  { rewrite SNode.update_outbox_None. ss. }
                  erewrite SNode.update_outbox_not_in; ss; try nia.
                  exploit grant_tid; eauto. i.
                  unfold SNode.get_actual_dest.
                  des; subst; condtac; ss; nia.
                * erewrite SNode.update_outbox_in; ss; try nia.
                  { unfold resize_bytes.
                    rewrite to_bytes_length; ss.
                    rewrite app_nil_r.
                    replace 8 with (length (CtrlState.to_bytes (active st2)))
                      by (apply to_bytes_length; ss).
                    rewrite firstn_all.
                    rewrite of_bytes_to_bytes; ss.
                    apply active_eq. destruct st2; ss.
                  }
                  { rewrite SNode.update_outbox_length. ss. }
                  { unfold SNode.get_actual_dest. condtac; ss. nia. }
                  { rewrite SNode.update_outbox_length. ss. nia. }
                  { unfold SNode.get_actual_dest. condtac; ss.
                    unfold SNode.check_available. ss.
                    destruct grant_src as [[]|]; cycle 1.
                    { rewrite SNode.update_outbox_None. ss. }
                    rewrite SNode.update_outbox_check_available; ss.
                    exploit grant_tid; eauto. i. des; subst; ss; nia.
                  }
            - des; subst.
              + rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                unfold sim_grant. des_ifs.
              + exploit GRANT_SRC; eauto. i. subst.
                rewrite SNode.update_outbox_None.
                unguardH OUT0. des; subst; ss.
            - des; subst.
              + rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                unfold sim_grant. des_ifs.
              + exploit GRANT_SRC; eauto. i. subst.
                rewrite SNode.update_outbox_None.
                unguardH OUT0. des; subst; ss.
            - des; subst.
              + rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 2)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                unfold sim_grant. des_ifs.
              + exploit GRANT_SRC; eauto. i. subst.
                rewrite SNode.update_outbox_None.
                unguardH OUT0. des; subst; ss.
          }
          { (* stutter *)
            destruct (CtrlState.timeout st2 =? SpecController.MAX_TIMEOUT)%Z eqn:TOUT; cycle 1.
            { exfalso. eauto. }
            unguardH OUT0. inv OUT0.
            { (* stutter no send *)
              exploit next_state_snode_step_stutter; eauto.
              { destruct st2. ss. }
              intro STEP_SRC.
              esplits; eauto; [econs 1; eauto|..].
              econs; eauto.
              - econs 5; eauto.
                + unfold is_stuttering.
                  rewrite <- MODE. rewrite MODE1. condtac; ss.
                  des; subst; ss.
                + congr.
                + erewrite SNode.update_outbox_in; ss; try nia.
                  { apply sanitize_ctrl. ss. }
                  { unfold SNode.get_actual_dest. condtac; ss. eauto. }
                  { rewrite SNode.update_outbox_length. ss. nia. }
                + des; subst; ss; des_ifs.
              - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                unfold sim_grant. des; subst; des_ifs.
              - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                unfold sim_grant. des; subst; des_ifs.
              - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                unfold sim_grant. des; subst; des_ifs.
            }

            { (* stutter send *)
              des; cycle 1.
              { exfalso. eauto. }
              clear H. subst.
              exploit next_state_snode_step_stutter_send; eauto.
              { destruct st2. ss. }
              intro STEP_SRC.
              esplits; eauto; [econs 1; eauto|..].
              econs; eauto.
              - econs 5; eauto.
                + unfold is_stuttering.
                  rewrite <- MODE. rewrite MODE1.
                  destruct grant_src as [[]|]; cycle 1.
                  { rewrite SNode.update_outbox_None. ss. }
                  rewrite SNode.update_outbox_not_in; ss; try nia.
                  exploit grant_tid; eauto. i.
                  unfold SNode.get_actual_dest.
                  des; subst; condtac; ss; try nia.
                + congr.
                + erewrite SNode.update_outbox_in; ss; try nia.
                  { apply sanitize_ctrl. ss. }
                  { unfold SNode.get_actual_dest. condtac; ss. eauto. }
                  { rewrite SNode.update_outbox_length. ss. nia. }
                + rewrite <- MODE. rewrite MODE1.
                  destruct grant_src as [[]|]; cycle 1.
                  { rewrite SNode.update_outbox_None. ss. }
                  erewrite SNode.update_outbox_not_in; ss; try nia.
                  exploit grant_tid; eauto. i.
                  unfold SNode.get_actual_dest.
                  des; subst; condtac; ss; nia.
              - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                rewrite SNode.update_outbox_None. ss.
                unfold sim_grant. des_ifs.
              - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                rewrite SNode.update_outbox_None. ss.
                unfold sim_grant. des_ifs.
              - rewrite SNode.update_outbox_not_in with (tid2 := Z.to_nat (3 - Z.of_nat 1)); cycle 1.
                { unfold SNode.get_actual_dest. condtac; ss. nia. }
                rewrite SNode.update_outbox_None. ss.
                unfold sim_grant. des_ifs.
            }
          }
        }
      }
    }
  Qed.

  Lemma sim_device_inbox_sync
        inb_src inb_tgt dev
        (SIM: sim_device_inbox inb_src inb_tgt):
    sync_dev_state inb_src dev = sync_dev_state inb_tgt dev.
  Proof.
    inv SIM. unfold sim_grant in *.
    des_ifs; des;
      unfold sync_dev_state, DevState.set_owner_status;
      try rewrite Heq;
      try rewrite Heq0;
      try rewrite Heq1;
      try rewrite MSG2;
      try refl.
  Qed.

  Lemma sim_device_step
        tid
        dev1_src
        tm dev1_tgt es outb dev2_tgt
        (SIM1: sim_device tid dev1_src dev1_tgt)
        (STEP: SNode.step sntz 6 mcasts tm dev1_tgt es outb dev2_tgt):
    exists dev2_src,
      (<<STEP: SNode.step sntz 6 mcasts tm dev1_src es outb dev2_src>>) /\
      (<<SIM2: sim_device tid dev2_src dev2_tgt>>)  /\
      (<<OUTB: nth 1 outb None = nth 2 outb None>>).
  Proof.
    inv SIM1. inv STEP; existT_elim; subst.
    { esplits; [econs 1|..]; eauto. econs. ss. }
    { esplits; [econs 2|..]; eauto. econs. ss. }

    esplits; [econs 3|..]; eauto; try by (econs; ss).
    { inv RUN_PERIOD; [econs 1|].
      econs 2; eauto.
      inv PERIOD_BEGIN. ss.
      econs; eauto. ss.
      unfold dev_job, job_device_itree.
      erewrite <- sim_device_inbox_sync; eauto.
    }

    inv RUN_PERIOD; ss.
    inv PERIOD_BEGIN; ss.
    unfold dev_job, job_device_itree in *.

    destruct ast2.(DevState.owner_status); cycle 1.
    { inv STAR; ss. inv ASTEP.
      { inv TAU_STEP. ss. }
      { inv AT_EVENT. existT_elim. subst. ss. }
      inv AT_EVENT. existT_elim. subst. ss.
      revert OBS. simpl_itree_goal. ss. i. inv OBS. existT_elim. subst.
      inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

      inv ASTAR'; ss. inv ASTEP; cycle 2.
      { inv AT_EVENT. existT_elim. subst. ss. }
      { inv TAU_STEP. ss. }
      inv AT_EVENT. existT_elim. subst. ss.
      revert OBS. simpl_itree_goal. ss. i. inv OBS. existT_elim. subst.
      inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

      inv ASTAR'0; ss. inv ASTEP.
      - inv TAU_STEP. ss.
      - inv AT_EVENT. ss.
      - inv AT_EVENT. ss.
    }

    unfold update_demand in *.
    revert STAR. condtac; ss; cycle 1.
    { simpl_itree_goal.
      destruct (DevState.owner_status (sync_dev_state inb_tgt ast2)); cycle 1.
      { i. inv STAR; ss. inv ASTEP.
        - inv TAU_STEP. ss.
        - inv AT_EVENT. ss.
        - inv AT_EVENT. ss.
      }

      condtac; ss; cycle 1.
      { simpl_itree_goal. i.
        inv STAR; ss. inv ASTEP; cycle 2.
        { inv AT_EVENT. existT_elim. subst. ss. }
        { inv TAU_STEP. ss. }
        inv AT_EVENT. existT_elim. subst. ss.
        revert OBS. simpl_itree_goal. ss. i. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

        inv ASTAR'; ss. inv ASTEP.
        - inv TAU_STEP. ss.
        - inv AT_EVENT. ss.
        - inv AT_EVENT. ss.
      }

      unfold run_device. condtac; ss.
      { do 2 simpl_itree_goal. i.
        inv STAR; ss. inv ASTEP; cycle 2.
        { inv AT_EVENT. existT_elim. subst. ss. }
        { inv TAU_STEP. ss. }
        inv AT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

        revert ASTAR'. simpl_itree_goal. condtac; ss; cycle 1.
        { simpl_itree_goal. i.
          inv ASTAR'; ss. inv ASTEP; cycle 2.
          { inv AT_EVENT. existT_elim. subst. ss. }
          { inv TAU_STEP. ss. }
          inv AT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.
          inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

          inv ASTAR'0; ss. inv ASTEP.
          - inv TAU_STEP. ss.
          - inv AT_EVENT. ss.
          - inv AT_EVENT. ss.
        }

        simpl_itree_goal. i.
        inv ASTAR'; ss. inv ASTEP.
        { inv TAU_STEP. ss. }
        { inv AT_EVENT. existT_elim. subst. ss. }
        inv AT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

        inv ASTAR'0; ss. inv ASTEP; cycle 2.
        { inv AT_EVENT. existT_elim. subst. ss. }
        { inv TAU_STEP. ss. }
        inv AT_EVENT. existT_elim. subst. ss.
        revert OBS. simpl_itree_goal. i. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

        inv ASTAR'; ss. inv ASTEP.
        - inv TAU_STEP. ss.
        - inv AT_EVENT. ss.
        - inv AT_EVENT. ss.
      }

      simpl_itree_goal. condtac; ss.
      simpl_itree_goal. i.
      inv STAR; ss. inv ASTEP; cycle 2.
      { inv AT_EVENT. existT_elim. subst. ss. }
      { inv TAU_STEP. ss. }
      inv AT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.
      inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

      inv ASTAR'; ss. inv ASTEP.
      - inv TAU_STEP. ss.
      - inv AT_EVENT. ss.
      - inv AT_EVENT. ss.
    }

    unfold get_new_demand.
    do 3 simpl_itree_goal. i.

    inv STAR; ss. inv ASTEP; cycle 2.
    { inv AT_EVENT. existT_elim. subst. ss. }
    { inv TAU_STEP. ss. }
    inv AT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.
    inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

    revert ASTAR'. simpl_itree_goal.
    remember (if 0 <? (if MAX_TIMEOUT <? Z.to_nat (Int.signed r) then MAX_TIMEOUT else Z.to_nat (Int.signed r))
              then
                (DevState.set_demand
                   (if MAX_TIMEOUT <? Z.to_nat (Int.signed r) then MAX_TIMEOUT else Z.to_nat (Int.signed r))
                   (sync_dev_state inb_tgt ast2), true)
              else (sync_dev_state inb_tgt ast2, false)) as dev.
    clear Heqdev. destruct dev.
    simpl_itree_goal.

    destruct (DevState.owner_status t); cycle 1.
    { i. inv ASTAR'; ss. inv ASTEP.
      - inv TAU_STEP. ss.
      - inv AT_EVENT. ss.
      - inv AT_EVENT. ss.
    }

    condtac; ss.
    { unfold run_device. condtac; ss.
      { do 2 simpl_itree_goal. i.
        inv ASTAR'; ss. inv ASTEP; cycle 2.
        { inv AT_EVENT. existT_elim. subst. ss. }
        { inv TAU_STEP. ss. }
        inv AT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

        revert ASTAR'0. simpl_itree_goal. condtac; ss; cycle 1.
        { simpl_itree_goal. i.
          inv ASTAR'0; ss. inv ASTEP; cycle 2.
          { inv AT_EVENT. existT_elim. subst. ss. }
          { inv TAU_STEP. ss. }
          inv AT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.
          inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

          inv ASTAR'; ss. inv ASTEP.
          - inv TAU_STEP. ss.
          - inv AT_EVENT. ss.
          - inv AT_EVENT. ss.
        }

        simpl_itree_goal. i.
        inv ASTAR'0; ss. inv ASTEP.
        { inv TAU_STEP. ss. }
        { inv AT_EVENT. existT_elim. subst. ss. }
        inv AT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

        inv ASTAR'; ss. inv ASTEP; cycle 2.
        { inv AT_EVENT. existT_elim. subst. ss. }
        { inv TAU_STEP. ss. }
        inv AT_EVENT. existT_elim. subst. ss.
        revert OBS. simpl_itree_goal. i. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

        inv ASTAR'0; ss. inv ASTEP.
        - inv TAU_STEP. ss.
        - inv AT_EVENT. ss.
        - inv AT_EVENT. ss.
      }

      simpl_itree_goal. condtac; ss.
      { simpl_itree_goal. i.
        inv ASTAR'; ss. inv ASTEP.
        { inv TAU_STEP. ss. }
        { inv AT_EVENT. existT_elim. subst. ss. }
        inv AT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

        revert ASTAR'0. simpl_itree_goal. i.
        inv ASTAR'0; ss. inv ASTEP; cycle 2.
        { inv AT_EVENT. existT_elim. subst. ss. }
        { inv TAU_STEP. ss. }
        inv AT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.
        inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

        inv ASTAR'; ss. inv ASTEP.
        - inv TAU_STEP. ss.
        - inv AT_EVENT. ss.
        - inv AT_EVENT. ss.
      }

      simpl_itree_goal. i.
      inv ASTAR'; ss. inv ASTEP; cycle 2.
      { inv AT_EVENT. existT_elim. subst. ss. }
      { inv TAU_STEP. ss. }
      inv AT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.
      inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

      inv ASTAR'0; ss. inv ASTEP.
      - inv TAU_STEP. ss.
      - inv AT_EVENT. ss.
      - inv AT_EVENT. ss.
    }

    condtac; ss.
    { simpl_itree_goal. i.
      inv ASTAR'; ss. inv ASTEP.
      { inv TAU_STEP. ss. }
      { inv AT_EVENT. existT_elim. subst. ss. }
      inv AT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.
      inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

      revert ASTAR'0. simpl_itree_goal. i.
      inv ASTAR'0; ss. inv ASTEP; cycle 2.
      { inv AT_EVENT. existT_elim. subst. ss. }
      { inv TAU_STEP. ss. }
      inv AT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.
      inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

      inv ASTAR'; ss. inv ASTEP.
      - inv TAU_STEP. ss.
      - inv AT_EVENT. ss.
      - inv AT_EVENT. ss.
    }

    do 2 simpl_itree_goal. i.
    inv ASTAR'; ss. inv ASTEP; cycle 2.
    { inv AT_EVENT. existT_elim. subst. ss. }
    { inv TAU_STEP. ss. }
    inv AT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.
    inv AFT_EVENT. existT_elim. subst. ss. inv OBS. existT_elim. subst.

    inv ASTAR'0; ss. inv ASTEP.
    - inv TAU_STEP. ss.
    - inv AT_EVENT. ss.
    - inv AT_EVENT. ss.
  Qed.

  Lemma node_is_on_accept_msgs msgs node:
    node_is_on (Some (SNode.accept_msgs msgs node)) =
    node_is_on (Some node).
  Proof.
    destruct node; ss.
  Qed.

  Theorem single_controller_ref: fmsim obsE sys_src sys_tgt.
  Proof.
    econs. s. i. subst.
    esplits; eauto.

    remember (SyncSysNB.init_state tm_init sync_sys_src) as st_src.
    remember (SyncSysNB.init_state tm_init sync_sys_tgt) as st_tgt.
    assert (SIM: sim_states st_src st_tgt).
    { subst. unfold SyncSysNB.init_state. ss. econs. econs; ss.
      econs; eauto; econs; ss.
    }
    clear Heqst_src Heqst_tgt.
    revert st_src st_tgt SIM.
    pcofix CIH. i.

    pfold. econs.
    { ss. }
    i. inv SIM.
    hexploit sim_nodes_length; eauto. i. des.
    inv STEPS. inv MSTEPS_REST. inv STEP.
    { (* wait *)
      esplits; ss.
      - econs 2.
        + econs; eauto.
        + rewrite H, H0 in *. eauto.
        + econs 1. ss.
        + unfold SyncSysNB.num_sites in *. ss.
          rewrite H, H0 in *. eauto.
      - apply Forall2_tes_equiv_refl.
      - right. eapply CIH. econs; eauto.
    }

    revert FILTER_NB. condtac; i.
    { (* NB step *)
      exploit Forall4_length; eauto. i. des.
      rewrite H0 in *. destruct ess; ss.
    }

    (* non-NB step *)
    inv NODES. ss. clear H H0.
    inv STEPS. rename P_HOLDS into STEP_CON.
    inv FORALL_T. rename P_HOLDS into STEP_CTRL1.
    inv FORALL_T0. rename P_HOLDS into STEP_CTRL2.
    inv FORALL_T. rename P_HOLDS into STEP_DEV1.
    inv FORALL_T0. rename P_HOLDS into STEP_DEV2.
    inv FORALL_T. rename P_HOLDS into STEP_DEV3.
    inv FORALL_T0. ss.

    exploit sim_console_step; eauto. i. des.
    exploit sim_controller_step; eauto.
    { unfold nb_tgt, ctrl_fail_tgt in *.
      Opaque node_is_on no_hb_recieved. ss.
      Transparent node_is_on no_hb_recieved.
      repeat rewrite node_is_on_accept_msgs in *. auto.
    }
    i. des. subst.
    exploit sim_device_step; try exact DEV1; eauto. i. des.
    exploit sim_device_step; try exact DEV2; eauto. i. des.
    exploit sim_device_step; try exact DEV3; eauto. i. des.

    esplits.
    - ss.
    - econs.
      + econs 2.
        * ss.
        * repeat (econs; eauto).
        * ss.
        * ss.
      + condtac; eauto.
        revert NONB COND0.
        unfold ctrl_fail_src, node_is_on. des_ifs.
      + econs. ss.
      + eauto.
    - apply Forall2_tes_equiv_refl.
    - right. apply CIH. econs.
      econs; eauto.
      + inv SIM2. ss.
      + inv SIM0. ss.
        repeat rewrite SNode.get_outbox_msg_nth. ss.
        econs; eauto; ss.
      + inv SIM1. inv SIM0.
        econs. econs; ss.
        repeat rewrite SNode.get_outbox_msg_nth. ss.
      + inv SIM3. inv SIM0.
        econs. econs; ss.
        repeat rewrite SNode.get_outbox_msg_nth. ss.
      + inv SIM4. inv SIM0.
        econs. econs; ss.
        repeat rewrite SNode.get_outbox_msg_nth. ss.
  Qed.
End SingleControllerRef.
