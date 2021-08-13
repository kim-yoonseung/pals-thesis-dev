From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Linking.

Require Import sflib.
Require Import StdlibExt.

Require Import NWSysModel.
Require Import RTSysEnv.
Require main_prm config_prm.
Require Import LinkLemmas.

Set Nested Proofs Allowed.

Local Open Scope Z_scope.

Local Opaque Z.of_nat Byte.unsigned nth.
(* main_p.ip_init_data *)

Local Transparent Linker_program Linker_prog Linker_def Linker_fundef Linker_varinit Ctypes.Linker_fundef Linker_vardef Linker_types.
Local Transparent external_function_eq calling_convention_eq signature_eq typ_eq rettype_eq.

Local Opaque in_dec zeq.


Lemma link_v_IP_ADDR
      nt nmc ip_bs
  : link_vardef (main_prm.v_IP_ADDR nt nmc)
                (config_prm.v_IP_ADDR nt nmc ip_bs) =
    Some (config_prm.v_IP_ADDR nt nmc ip_bs).
Proof.
  unfold main_prm.v_IP_ADDR, config_prm.v_IP_ADDR.
  unfold link_vardef. ss.
  destruct (zeq (nt + nmc) (nt + nmc)); ss.
Qed.

Lemma link_v_MCAST_MEMBER
      mnt mnmc mfs
  : link_vardef (main_prm.v_MCAST_MEMBER mnt mnmc)
                (config_prm.v_MCAST_MEMBER mnt mnmc mfs) =
    Some (config_prm.v_MCAST_MEMBER mnt mnmc mfs).
Proof.
  unfold main_prm.v_MCAST_MEMBER, config_prm.v_MCAST_MEMBER.
  simpl.
  unfold link_vardef. ss.
  destruct (zeq mnmc mnmc); ss.
  destruct (zeq mnt mnt); ss.
Qed.


Section PROGRAMS_OF_SYSTEM.

  Context `{SystemEnv}.

  Definition main_prog: Clight.program :=
    main_prm.prog (Z.of_nat msg_size_k)
                  (Z.of_nat max_num_tasks)
                  (Z.of_nat max_num_mcasts).

  Definition config_prog: Clight.program :=
    config_prm.prog
      (Z.of_nat max_num_tasks) (Z.of_nat max_num_mcasts)
      (Z.of_nat period) (Z.of_nat max_clock_skew) (Z.of_nat max_nw_delay)
      (Z.of_nat num_tasks) (Z.of_nat num_mcasts) (Z.of_nat msg_size)
      (Z.of_nat port) dest_ips_brep mcast_memflags.

  Lemma main_config_link_check_ok
        dm1 dm2
        (DM1: dm1 = prog_defmap main_prog)
        (DM2: dm2 = prog_defmap config_prog)
    : PTree_Properties.for_all
        dm1 (link_prog_check main_prog config_prog) = true.
  Proof.
    apply PTree_Properties.for_all_correct.
    intros id gd SOME.
    rewrite DM1 in SOME.
    unfold prog_defmap in SOME. ss.
    apply PTree_Properties.in_of_list in SOME. ss.
    des; clarify.
    - unfold link_prog_check.
      unfold prog_defmap. ss.

      assert (IN_PUB1: In main_prm._IP_ADDR
                          main_prm.public_idents).
      { unfold main_prm.public_idents. ss.
        repeat match goal with
               | |- ?a = ?b \/ _ =>
                 match a with
                 | b => left
                 | _ => right
                 end
               end.
        reflexivity. }

      assert (IN_PUB2: In main_prm._IP_ADDR
                          config_prm.public_idents).
      { unfold config_prm.public_idents. ss.
        repeat match goal with
               | |- ?a = ?b \/ _ =>
                 match a with
                 | config_prm._IP_ADDR => left
                 | _ => right
                 end
               end.
        reflexivity. }
      desf.

      rewrite link_v_IP_ADDR in *.
      congruence.
    - unfold link_prog_check.
      unfold prog_defmap. ss.

      assert (IN_PUB1: In main_prm._MCAST_MEMBER
                          main_prm.public_idents).
      { unfold main_prm.public_idents. ss.
        repeat match goal with
               | |- ?a = ?b \/ _ =>
                 match a with
                 | b => left
                 | _ => right
                 end
               end.
        reflexivity. }

      assert (IN_PUB2: In main_prm._MCAST_MEMBER
                          config_prm.public_idents).
      { unfold config_prm.public_idents. ss.
        repeat match goal with
               | |- ?a = ?b \/ _ =>
                 match a with
                 | config_prm._MCAST_MEMBER => left
                 | _ => right
                 end
               end.
        reflexivity. }
      desf.

      rewrite link_v_MCAST_MEMBER in *.
      congruence.
  Qed.

  (* Set Debug Cbv. *)
  (* Local Opaque Bool.bool_dec eq_ind eq_ind_r. *)
  (* Local Opaque link_prog_merge. *)

  Definition mw_AST_prog: AST.program Clight.fundef type :=
    let p1 := main_prog in
    let p2 := config_prog in
    let dm1 := prog_defmap p1 in
    let dm2 := prog_defmap p2 in
    {|
    AST.prog_defs := PTree.elements (PTree.combine link_prog_merge dm1 dm2);
    AST.prog_public := AST.prog_public p1 ++ AST.prog_public p2;
    AST.prog_main := AST.prog_main p1 |}.

  Lemma mw_AST_prog_linked
    : link_prog main_prog config_prog = Some mw_AST_prog.
  Proof.
    unfold link_prog.
    erewrite main_config_link_check_ok; eauto.
  Qed.

  Arguments Z.mul: simpl nomatch.

  Definition prog_mw_types : list composite_definition.
  Proof.
    let k := eval cbn in (link_composite_defs
                            (prog_types main_prog)
                            (prog_types config_prog)) in
        match k with
        | Some ?a => exact a
        end.
  Defined.

  Lemma prog_mw_types_linked
    : link_composite_defs (prog_types main_prog)
                          (prog_types config_prog) =
      Some prog_mw_types.
  Proof. ss. Qed.

  Definition prog_mw: Clight.program :=
    let p1 := main_prog in
    let p2 := config_prog in
    mkprogram prog_mw_types
              (PTree.elements (PTree.combine link_prog_merge (prog_defmap p1) (prog_defmap p2)))
              (AST.prog_public p1 ++ AST.prog_public p2)
              (AST.prog_main p1)
              I
  .

  Lemma prog_mw_linked
    : link_program main_prog config_prog = Some prog_mw.
  Proof.
    apply link_program_eq; ss.
    apply mw_AST_prog_linked.
  Qed.

End PROGRAMS_OF_SYSTEM.
