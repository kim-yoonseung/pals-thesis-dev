From compcert Require Import
     AST Memory Globalenvs
     Linking Ctypes Maps
     Clight Clightdefs.
From compcert Require Coqlib.

Require Import sflib.
Require Import StdlibExt.
Require Import RTSysEnv.

Require Import LinkLemmas.
Require Import config_prm main_prm.
Require Import SystemProgs.

Require Import VerifProgBase.

(**)
Require Import IntegersExt.
Require Import IPModel.
Require Import NWSysModel.

(* Set Nested Proofs Allowed. *)

(**)

Require Import ZArith String List Lia.



Local Transparent Linker_def Linker_vardef Linker_types.


Lemma Coqlib_zeq_refl a
  : exists pf, Coqlib.zeq a a = left pf.
Proof.
  destruct (Coqlib.zeq _ _); ss.
  esplits; eauto.
Qed.

Lemma align_exact
      (a x: Z)
      (AMT_POS: (0 < a)%Z)
      (DIV: (a | x)%Z)
  : Coqlib.align x a = x.
Proof.
  r in DIV. des.
  unfold Coqlib.align.
  rewrite DIV.
  replace (z * a + a - 1)%Z with (z * a + (a - 1))%Z by nia.
  erewrite Coqlib.Zdiv_unique; eauto.
  nia.
Qed.


Module MainIListSound.

  Section MW.
    Import Linking.

    Context `{SystemEnv}.
    Variable tid: nat.

    Lemma link_ip_addr
          mnt mnmc ips
      : link_vardef (main_prm.v_IP_ADDR mnt mnmc)
                    (config_prm.v_IP_ADDR mnt mnmc ips) =
        Some (config_prm.v_IP_ADDR mnt mnmc ips).
    Proof.
      unfold link_vardef.
      ss. cbn.
      generalize (Coqlib_zeq_refl (mnt + mnmc)).
      intro REFL. des.
      rewrite REFL. ss.
    Qed.

    Lemma link_mcast_member
          mnt mnmc mflg
      : link_vardef (main_prm.v_MCAST_MEMBER mnt mnmc)
                    (config_prm.v_MCAST_MEMBER mnt mnmc mflg) =
        Some (config_prm.v_MCAST_MEMBER mnt mnmc mflg).
    Proof.
      unfold link_vardef.
      ss. cbn.
      generalize (Coqlib_zeq_refl mnt).
      intro REFL1. des.
      rewrite REFL1. ss.
      generalize (Coqlib_zeq_refl mnmc).
      intro REFL2. des.
      rewrite REFL2. ss.
    Qed.

    Lemma check_gvar
          id gv
          (ID_NEQ: id <> _TASK_ID)
          (IN_ILIST: In (id, gv) (main_gvar_ilist tid))
      : In (id, Gvar gv) (prog_defs prog_mw).
    Proof.
      simpl in IN_ILIST.
      des;
        try (by exfalso; clarify);
        try (by inv IN_ILIST;
             change (prog_defs prog_mw) with
                 (PTree.elements (PTree.combine
                                    link_prog_merge
                                    (prog_defmap main_prog)
                                    (prog_defmap config_prog)));
             apply PTree.elements_correct;
             apply PTree.gcombine; ss).

      - inv IN_ILIST.
        change (prog_defs prog_mw) with
            (PTree.elements (PTree.combine
                               link_prog_merge
                               (prog_defmap main_prog)
                               (prog_defmap config_prog))).
        apply PTree.elements_correct.
        rewrite PTree.gcombine by ss.
        s. rewrite link_ip_addr. ss.
      - inv IN_ILIST.
        change (prog_defs prog_mw) with
            (PTree.elements (PTree.combine
                               link_prog_merge
                               (prog_defmap main_prog)
                               (prog_defmap config_prog))).
        apply PTree.elements_correct.
        rewrite PTree.gcombine by ss.
        s. rewrite link_mcast_member. ss.
    Qed.


    Lemma check_cenv
          id co
          (IN_ILIST: In (id, co) main_cenv_ilist)
      : (prog_comp_env prog_mw) ! id = Some co.
    Proof.
      pose proof (prog_comp_env_eq prog_mw) as BUILD_CENV.
      change (prog_types prog_mw) with prog_mw_types in BUILD_CENV.

      hexploit (link_build_composite_env
                  (prog_types main_prog)
                  (prog_types config_prog)
                  prog_mw_types).
      { eapply prog_comp_env_eq. }
      { eapply prog_comp_env_eq. }
      { apply prog_mw_types_linked. }

      destruct 1 as(env & EQ & C1 & C2).
      rewrite EQ in BUILD_CENV.

      assert (ENV_EQ: env = prog_comp_env prog_mw).
      { clear - BUILD_CENV.
        assert (AUX: forall T (x y:T), Errors.OK x = Errors.OK y ->
                             x = y).
        { intros ? x y EQ. inv EQ. reflexivity. }
        apply AUX.
        apply BUILD_CENV.
      }
      rewrite <- ENV_EQ.
      clear BUILD_CENV ENV_EQ EQ.

      simpl in IN_ILIST. des.
      - clarify. apply C1. s.
        clear C1 C2 env.

        unfold co_pals_msg_t.
        f_equal.
        apply composite_eq; eauto.
        + fold noattr.
          fold tulong.
          fold tschar.
          replace (8 * Z.of_nat msg_size_k + 7)%Z with
              (Z.of_nat max_msg_size).
          2: { unfold max_msg_size. nia. }
          reflexivity.
        + unfold align_attr. s.
          rewrite Z.max_r by nia.
          rewrite Z.max_l.
          2: { rewrite Z.max_r by nia.
               rewrite Z.max_r by nia.
               unfold Archi.align_int64.
               nia. }
          replace (Coqlib.align 9 1) with 9%Z.
          2: { compute. reflexivity. }
          unfold Archi.align_int64.
          rewrite Z.mul_1_l.

          rewrite align_exact; cycle 1.
          { nia. }
          { replace (9 + (8 * Z.of_nat msg_size_k + 7))%Z with
                (2 * 8 + 8 * Z.of_nat msg_size_k)%Z by nia.
            solve_divide. }

          unfold max_pld_size, max_msg_size. nia.
      - clarify. apply C1. s.
        clear C1 C2 env.

        unfold co_msg_entry_t.
        f_equal.
        apply composite_eq; eauto.
        + fold noattr.
          fold tulong.
          fold tschar.
          replace (8 * Z.of_nat msg_size_k + 7)%Z with
              (Z.of_nat max_msg_size).
          2: { unfold max_msg_size. nia. }
          reflexivity.
        + unfold align_attr. s.
          rewrite Z.max_r by nia.
          rewrite Z.max_r by nia.
          rewrite Z.max_r by nia.

          replace (Coqlib.align 1 1) with 1%Z.
          2: { compute. reflexivity. }
          rewrite Z.mul_1_l.

          rewrite align_exact; cycle 1.
          { nia. }
          { replace (1 + (8 * Z.of_nat msg_size_k + 7))%Z with
                (8 + 8 * Z.of_nat msg_size_k)%Z by nia.
            solve_divide. }

          unfold mentry_nsz, max_msg_size. nia.
      - clarify. apply C1. s.
        clear C1 C2 env.

        unfold co_inbox_t.
        f_equal.
        apply composite_eq; eauto.
        + unfold align_attr. s.
          repeat rewrite Z.max_r by nia.
          replace (Coqlib.align 1 1) with 1%Z.
          2: { compute. reflexivity. }
          rewrite Z.mul_1_l.

          rewrite align_exact; cycle 1.
          { nia. }
          { solve_divide. }

          rewrite align_exact; cycle 1.
          { nia. }
          { solve_divide. }

          unfold inb_nsz, mentry_nsz.
          unfold max_msg_size. nia.
      - clarify. apply C1. s.
        clear C1 C2 env.

        unfold co_msg_store_t.
        f_equal.
        apply composite_eq; eauto.
        + unfold align_attr. s.
          repeat rewrite Z.max_r by nia.
          rewrite Z.max_l by nia.
          replace (Coqlib.align 4 1) with 4%Z.
          2: { compute. reflexivity. }
          replace (Coqlib.align 1 1) with 1%Z.
          2: { compute. reflexivity. }

          rewrite Z.mul_1_l.

          rewrite (align_exact 1); cycle 1.
          { nia. }
          { solve_divide. }

          rewrite (align_exact 1); cycle 1.
          { nia. }
          { solve_divide. }

          rewrite align_exact; cycle 1.
          { nia. }
          { replace (1 + (8 * Z.of_nat msg_size_k + 7))%Z with
                (8 + 8 * Z.of_nat msg_size_k)%Z by nia.
            solve_divide. }

          unfold inb_nsz, mentry_nsz.
          unfold max_msg_size. nia.

      - contradiction.
    Qed.

    Lemma check_gfun
          id gf
          (IN_ILIST: In (id, gf) main_gfun_ilist)
      : In (id, Gfun gf) (prog_defs prog_mw).
    Proof.
      simpl in IN_ILIST.
      des;
        try (by exfalso; clarify);
        try (by inv IN_ILIST;
             change (prog_defs prog_mw) with
                 (PTree.elements (PTree.combine
                                    link_prog_merge
                                    (prog_defmap main_prog)
                                    (prog_defmap config_prog)));
             apply PTree.elements_correct;
             apply PTree.gcombine; ss).
    Qed.

  End MW.

End MainIListSound.


Local Opaque Linker_def Linker_fundef Ctypes.Linker_fundef.

Lemma init_data_list_aligned_app
      p i1 i2
      (ALGN1: Genv.init_data_list_aligned p i1)
      (ALGN2: Genv.init_data_list_aligned (p + init_data_list_size i1) i2)
  : Genv.init_data_list_aligned p (i1 ++ i2).
Proof.
  depgen p.
  induction i1 as [| h1 t1 IH]; i; ss.
  { rewrite Z.add_0_r in *. ss. }
  destruct ALGN1 as [ALGN_HD ALGN1'].
  split; ss.
  apply IH; eauto.
  rewrite <- Z.add_assoc. ss.
Qed.

Lemma link_prog_merge_gfun_gvar_absurd_aux
      (ogd1 ogd2: (globdef fundef type)?) v
      (LINK: link_prog_merge ogd1 ogd2 = Some (Gvar v))
      (GFUN: exists f, ogd1 = Some (Gfun f) \/ ogd2 = Some (Gfun f))
  : False.
Proof.
  des; subst.
  - ss. desf.
    eapply link_def_gfun_gvar_absurd_aux; eauto.
  - destruct ogd1; ss.
    eapply link_def_gfun_gvar_absurd_aux; eauto.
Qed.

(* Require Import IntegersExt. *)
(* Require Import IPModel. *)

Lemma aligned_ips_aux
      k ips
      (IPS_LENGTH: Forall (fun ip => length ip <= 16) ips)
      (OFS: (16 | k)%Z)
  : Genv.init_data_list_aligned
      k (flat_map ip_init_data ips).
Proof.
  depgen k.
  induction ips as [| ip1 ips IH]; i.
  { ss. }
  ss.
  splits; try solve_divide.
  eapply IH.
  { inv IPS_LENGTH. ss. }
  r in OFS. des.
  r. exists (z + 1)%Z.
  nia.
Qed.

Lemma aligned_memflags_aux
      k mnt flgs
  : Genv.init_data_list_aligned
      k (flat_map (mcmem_init_data mnt) flgs).
Proof.
  depgen k.
  induction flgs as [| h t IH]; i; ss.
  apply init_data_list_aligned_app.
  { unfold mcmem_init_data.
    desf.
    - apply init_data_list_aligned_app; ss.
      + clear. depgen k.
        induction h; i; ss.
        split; ss.
        solve_divide.
      + split; ss.
        solve_divide.
    - rewrite app_nil_r.
      clear.
      depgen k.
      induction h; i; ss.
      split; ss.
      solve_divide.
  }
  apply IH.
Qed.


Lemma link_period
      prd
  : link_vardef v_PALS_PERIOD
                (config_prm.v_PALS_PERIOD prd) =
    Some (config_prm.v_PALS_PERIOD prd).
Proof. ss. Qed.

Lemma link_max_cskew
      sk
  : link_vardef v_MAX_CSKEW
                (config_prm.v_MAX_CSKEW sk) =
    Some (config_prm.v_MAX_CSKEW sk).
Proof. ss. Qed.

Lemma link_max_nwdelay
      nd
  : link_vardef v_MAX_NWDELAY
                (config_prm.v_MAX_NWDELAY nd) =
    Some (config_prm.v_MAX_NWDELAY nd).
Proof. ss. Qed.

Lemma link_msg_size
      msz
  : link_vardef v_MSG_SIZE
                (config_prm.v_MSG_SIZE msz) =
    Some (config_prm.v_MSG_SIZE msz).
Proof. ss. Qed.

Lemma link_num_tasks
      nt
  : link_vardef v_NUM_TASKS
                (config_prm.v_NUM_TASKS nt) =
    Some (config_prm.v_NUM_TASKS nt).
Proof. ss. Qed.

Lemma link_num_mcasts
      nmc
  : link_vardef v_NUM_MCASTS
                (config_prm.v_NUM_MCASTS nmc) =
    Some (config_prm.v_NUM_MCASTS nmc).
Proof. ss. Qed.

Lemma link_port
      prt
: link_vardef v_PORT
              (config_prm.v_PORT prt) =
  Some (config_prm.v_PORT prt).
Proof. ss. Qed.

Local Transparent Linker_varinit.

Lemma link_ip_addr
      mnt mnmc ips
  : link_vardef (v_IP_ADDR mnt mnmc)
                (config_prm.v_IP_ADDR mnt mnmc ips) =
    Some (config_prm.v_IP_ADDR mnt mnmc ips).
Proof.
  unfold v_IP_ADDR.
  unfold config_prm.v_IP_ADDR.
  remember (tarray (tarray tschar 16) (mnt + mnmc)) as ty.
  clear Heqty.
  unfold link_vardef. ss.
  desf.
Qed.

Lemma link_mcast_member
      mnt mnmc mflgs
  : link_vardef (v_MCAST_MEMBER mnt mnmc)
                (config_prm.v_MCAST_MEMBER mnt mnmc mflgs) =
    Some (config_prm.v_MCAST_MEMBER mnt mnmc mflgs).
Proof.
  unfold v_MCAST_MEMBER.
  unfold config_prm.v_MCAST_MEMBER.
  remember (tarray (tarray tschar mnt) mnmc) as ty.
  clear Heqty.
  unfold link_vardef. ss.
  desf.
Qed.

Local Opaque Linker_varinit.


Local Transparent Linker_def.

Lemma prog_mw_gvar_init `{SystemEnv}
      id v
      (DEFMAP: (prog_defmap prog_mw) ! id = Some (Gvar v))
  : Genv.init_data_list_aligned 0 (gvar_init v) /\
    (forall i o, ~ In (Init_addrof i o) (gvar_init v)).
Proof.
  erewrite get_linked_prog_defs in DEFMAP
    by apply prog_mw_linked.

  destruct ((prog_defmap main_prog) ! id) as [gd1|] eqn:GD1.
  - apply in_prog_defmap in GD1.
    simpl in GD1.
    des; inv GD1;
      try by exfalso;
      eapply link_prog_merge_gfun_gvar_absurd_aux; eauto.
    +

      assert (v = config_prm.v_PALS_PERIOD (Z.of_nat period)).
      { ss.
        rewrite link_period in DEFMAP. clarify.
      }
      subst v. clear.
      split.
      * ss. split; ss. solve_divide.
      * ii. ss. des; ss.
    + assert (v = config_prm.v_MAX_CSKEW (Z.of_nat max_clock_skew)).
      { ss.

        rewrite link_max_cskew in DEFMAP. clarify.
      }
      subst v. clear.
      split.
      * ss. split; ss. solve_divide.
      * ii. ss. des; ss.
    + assert (v = config_prm.v_MAX_NWDELAY (Z.of_nat max_nw_delay)).
      {
        ss. rewrite link_max_nwdelay in DEFMAP. clarify. }
      subst v. clear.
      split.
      * ss. split; ss. solve_divide.
      * ii. ss. des; ss.
    + assert (v = config_prm.v_MSG_SIZE (Z.of_nat msg_size)).
      { ss. rewrite link_msg_size in DEFMAP. clarify. }

      subst v. clear.
      split.
      * ss. split; ss. solve_divide.
      * ii. ss. des; ss.
    + assert (v = config_prm.v_NUM_TASKS (Z.of_nat num_tasks)).
      { ss. rewrite link_num_tasks in DEFMAP. clarify. }

      subst v. clear.
      split.
      * ss. split; ss. solve_divide.
      * ii. ss. des; ss.
    + assert (v = config_prm.v_NUM_MCASTS (Z.of_nat num_mcasts)).
      { ss. rewrite link_num_mcasts in DEFMAP. clarify. }
      subst v. clear.
      split.
      * ss. split; ss. solve_divide.
      * ii. ss. des; ss.
    + assert (v = config_prm.v_PORT (Z.of_nat port)).
      { ss. rewrite link_port in DEFMAP. clarify. }
      subst v. clear.
      split.
      * ss. split; ss. solve_divide.
      * ii. ss. des; ss.
    + assert (v = config_prm.v_IP_ADDR (Z.of_nat max_num_tasks)
                                       (Z.of_nat max_num_mcasts)
                                       dest_ips_brep).
      { ss. rewrite link_ip_addr in DEFMAP. clarify. }
      subst v. clear.

      split.
      2: {
        intros id ofs IN.
        apply in_app_or in IN. des.
        - apply in_flat_map in IN.
          destruct IN as [b [IN_IPS IN_INIT]].
          unfold ip_init_data in IN_INIT.
          apply In_nth_error in IN_INIT.
          des.
          rewrite imap_nth_error_iff in IN_INIT.
          destruct (nth_error (repeat tt 16) n) as [u|]; ss.
        - ss. des; ss.
      }
      apply init_data_list_aligned_app.
      *
        apply aligned_ips_aux.
        2: { solve_divide. }

        apply Forall_forall. intros ip_bs IP_BS_IN.
        cut (exists ip, IP.convert_brep ip_bs = Some ip).
        { i. des.
          hexploit IP.valid_ip_brep_spec; eauto.
          i. des.
          unfold IP.max_byte_length in *. nia.
        }
        unfold dest_ips_brep in IP_BS_IN.
        apply in_app_or in IP_BS_IN. des.
        { apply In_nth_error in IP_BS_IN. des.
          pose proof task_ips_convert_brep as CONVS.
          rewrite Forall2_nth in CONVS.
          specialize (CONVS n).
          fold bytes in *.
          rewrite IP_BS_IN in CONVS.
          inv CONVS. esplits; eauto.
        }
        { apply In_nth_error in IP_BS_IN. des.
          pose proof mcast_ips_convert_brep as CONVS.
          rewrite Forall2_nth in CONVS.
          specialize (CONVS n).
          fold bytes in *.

          rewrite map_nth_error_iff in IP_BS_IN. des.
          rewrite IP_BS_IN in CONVS.
          inv CONVS. esplits; eauto.
        }
      * ss. split; ss.
        solve_divide.
    + clarify.
      ss. des; clarify.

      assert (v = config_prm.v_MCAST_MEMBER
                    (Z.of_nat max_num_tasks)
                    (Z.of_nat max_num_mcasts)
                    mcast_memflags).
      {
        ss. rewrite link_mcast_member in DEFMAP. clarify.
      }
      subst v. clear.
      split.
      2: {
        intros id ofs IN.
        apply in_app_or in IN. des.
        - apply in_flat_map in IN.
          destruct IN as [b [IN_FLGS IN_INIT]].
          unfold mcmem_init_data in IN_INIT.
          apply in_app_or in IN_INIT. des.
          + apply in_map_iff in IN_INIT. des; ss.
          + desf. ss.
            des; ss.
        - ss. des; ss.
      }

      ss.
      apply init_data_list_aligned_app.
      * apply aligned_memflags_aux.
      * ss. split; ss. solve_divide.
    + ss. clarify.
    + ss. clarify.
      split.
      * ss. split; ss. solve_divide.
      * ii. ss. des; ss.
    + ss. clarify.
      split.
      * ss. split; ss. solve_divide.
      * ii. ss. des; ss.
    + ss. clarify.
      split.
      * ss. split; ss. solve_divide.
      * ii. ss. des; ss.
    + ss. clarify.
      split.
      * ss. split; ss. solve_divide.
      * ii. ss. des; ss.
    + ss. clarify.
      split.
      * ss. split; ss. solve_divide.
      * ii. ss. des; ss.

  - destruct ((prog_defmap config_prog) ! id) as [gd2|] eqn:GD2.
    2: { ss. }
    ss. clarify.

    apply in_prog_defmap in GD2. ss.
    des; clarify.
Qed.


Lemma prog_mw_defmap_task_id `{SystemEnv}
  : (prog_defmap prog_mw) ! _TASK_ID =
    Some (Gvar main_prm.v_TASK_ID).
Proof.
  erewrite get_linked_prog_defs by apply prog_mw_linked.
  ss.
Qed.
