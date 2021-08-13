From compcert Require Import Maps AST Values Memory Globalenvs Ctypes.
From compcert Require Coqlib Clight Clightdefs.

Require Import String List ZArith Lia.

Require Import sflib.
Require Import StdlibExt IntegersExt.
Require Import IPModel IntByteModel.

Require Import NWSysModel.
Require Import RTSysEnv.
Require Import MWITree.

Require Import VerifProgBase.
Require Import config_prm main_prm SystemProgs.

Local Open Scope Z.
Local Opaque Z.of_nat Z.to_nat.
Arguments Z.add: simpl nomatch.

Section INIT_DATA_LEMMAS.
  Context `{SystemEnv}.

  Variable p: Clight.program.
  Let ge := Genv.globalenv p.

  Variable m: Mem.mem.
  Hypothesis INIT_MEM: Genv.init_mem p = Some m.

  Section TASK_ID.
    (* App is responsible to define TASK_ID  *)

    Variable tid: nat.
    Hypothesis RANGE_TID: (Z.of_nat tid <= Byte.max_signed)%Z.

    Hypothesis DEFMAP: (prog_defmap p) ! main_prm._TASK_ID =
                       Some (Gvar (v_TASK_ID_p (Z.of_nat tid))).

    Lemma _init_mem_tid
      : exists b_tid,
        Genv.find_symbol ge main_prm._TASK_ID = Some b_tid /\
        (b_tid < Genv.genv_next ge)%positive /\
        Mem.load Mint8signed m b_tid 0%Z =
        Some (Vint (IntNat.of_nat tid)).
    Proof.
      apply Genv.find_def_symbol in DEFMAP.
      destruct DEFMAP as (b & FSYMB & FDEF).

      esplits; eauto.
      { eapply Genv.genv_symb_range. eauto. }

      eapply Genv.init_mem_characterization_gen in FDEF; eauto.
      destruct FDEF as (RANGE_PERM & PERM_ORDER &
                        LOAD_STORE & LOADBYTES).

      hexploit LOAD_STORE.
      { ss. }
      clear LOAD_STORE. clear - RANGE_TID.
      intro LOAD_STORE. ss. des.
      rewrite Mem.load_int8_signed_unsigned.
      rewrite LOAD_STORE. ss.

      repeat f_equal.
      rewrite Int.sign_ext_zero_ext by ss.

      apply sign_ext_byte_range.
      r. split; ss.
      etransitivity.
      - instantiate (1:= 0%Z). ss.
      - nia.
    Qed.
  End TASK_ID.

  (** ** pals_period *)

  Section PALS_PERIOD.
    Hypothesis DEFMAP:
      (prog_defmap p) ! main_prm._PALS_PERIOD =
      Some (Gvar (config_prm.v_PALS_PERIOD (Z.of_nat period))).

    Lemma _init_mem_pals_period
      : exists b_pprd,
        Genv.find_symbol ge main_prm._PALS_PERIOD = Some b_pprd /\
        (b_pprd < Genv.genv_next ge)%positive /\
        Mem.load Mint64 m b_pprd 0%Z =
        Some (Vlong (IntNat.of_nat64 period)).
    Proof.
      apply Genv.find_def_symbol in DEFMAP.
      destruct DEFMAP as (b & FSYMB & FDEF).

      esplits; eauto.
      { eapply Genv.genv_symb_range. eauto. }

      eapply Genv.init_mem_characterization_gen in FDEF; eauto.
      destruct FDEF as (RANGE_PERM & PERM_ORDER &
                        LOAD_STORE & LOADBYTES).

      hexploit LOAD_STORE.
      { ss. }
      clear LOAD_STORE.
      intro LOAD_STORE. ss. des.
      rewrite LOAD_STORE. ss.
    Qed.
  End PALS_PERIOD.

  Section MAX_CSKEW.
    Hypothesis DEFMAP:
      (prog_defmap p) ! main_prm._MAX_CSKEW =
      Some (Gvar (config_prm.v_MAX_CSKEW (Z.of_nat max_clock_skew))).

    Lemma _init_mem_max_cskew
      : exists b_sk,
        Genv.find_symbol ge main_prm._MAX_CSKEW = Some b_sk /\
        (b_sk < Genv.genv_next ge)%positive /\
        Mem.load Mint64 m b_sk 0%Z =
        Some (Vlong (IntNat.of_nat64 max_clock_skew)).
    Proof.
      apply Genv.find_def_symbol in DEFMAP.
      destruct DEFMAP as (b & FSYMB & FDEF).

      esplits; eauto.
      { eapply Genv.genv_symb_range. eauto. }

      eapply Genv.init_mem_characterization_gen in FDEF; eauto.
      destruct FDEF as (RANGE_PERM & PERM_ORDER &
                        LOAD_STORE & LOADBYTES).

      hexploit LOAD_STORE.
      { ss. }
      clear LOAD_STORE.
      intro LOAD_STORE. ss. des.
      rewrite LOAD_STORE. ss.
    Qed.
  End MAX_CSKEW.


  Section MAX_NWDELAY.
    Hypothesis DEFMAP:
      (prog_defmap p) ! main_prm._MAX_NWDELAY =
      Some (Gvar (config_prm.v_MAX_NWDELAY (Z.of_nat max_nw_delay))).

    Lemma _init_mem_max_nwdelay
      : exists b_nd,
        Genv.find_symbol ge main_prm._MAX_NWDELAY = Some b_nd /\
        (b_nd < Genv.genv_next ge)%positive /\
        Mem.load Mint64 m b_nd 0%Z =
        Some (Vlong (IntNat.of_nat64 max_nw_delay)).
    Proof.
      apply Genv.find_def_symbol in DEFMAP.
      destruct DEFMAP as (b & FSYMB & FDEF).

      esplits; eauto.
      { eapply Genv.genv_symb_range. eauto. }

      eapply Genv.init_mem_characterization_gen in FDEF; eauto.
      destruct FDEF as (RANGE_PERM & PERM_ORDER &
                        LOAD_STORE & LOADBYTES).

      hexploit LOAD_STORE.
      { ss. }
      clear LOAD_STORE.
      intro LOAD_STORE. ss. des.
      rewrite LOAD_STORE. ss.
    Qed.
  End MAX_NWDELAY.

  Section NUM_TASKS.
    Hypothesis DEFMAP:
      (prog_defmap p) ! main_prm._NUM_TASKS =
      Some (Gvar (config_prm.v_NUM_TASKS (Z.of_nat num_tasks))).

    Lemma _init_mem_num_tasks
      : exists b_nt,
        Genv.find_symbol ge main_prm._NUM_TASKS = Some b_nt /\
        (b_nt < Genv.genv_next ge)%positive /\
        Mem.load Mint32 m b_nt 0%Z =
        Some (Vint (IntNat.of_nat num_tasks)).
    Proof.
      apply Genv.find_def_symbol in DEFMAP.
      destruct DEFMAP as (b & FSYMB & FDEF).

      esplits; eauto.
      { eapply Genv.genv_symb_range. eauto. }

      eapply Genv.init_mem_characterization_gen in FDEF; eauto.
      destruct FDEF as (RANGE_PERM & PERM_ORDER &
                        LOAD_STORE & LOADBYTES).

      hexploit LOAD_STORE.
      { ss. }
      clear LOAD_STORE.
      intro LOAD_STORE. ss. des.
      rewrite LOAD_STORE. ss.
    Qed.
  End NUM_TASKS.

  Section NUM_MCASTS.
    Hypothesis DEFMAP:
      (prog_defmap p) ! main_prm._NUM_MCASTS =
      Some (Gvar (config_prm.v_NUM_MCASTS (Z.of_nat num_mcasts))).

    Lemma _init_mem_num_mcasts
      : exists b_nmc,
        Genv.find_symbol ge main_prm._NUM_MCASTS = Some b_nmc /\
        (b_nmc < Genv.genv_next ge)%positive /\
        Mem.load Mint32 m b_nmc 0%Z =
        Some (Vint (IntNat.of_nat num_mcasts)).
    Proof.
      apply Genv.find_def_symbol in DEFMAP.
      destruct DEFMAP as (b & FSYMB & FDEF).

      esplits; eauto.
      { eapply Genv.genv_symb_range. eauto. }

      eapply Genv.init_mem_characterization_gen in FDEF; eauto.
      destruct FDEF as (RANGE_PERM & PERM_ORDER &
                        LOAD_STORE & LOADBYTES).

      hexploit LOAD_STORE.
      { ss. }
      clear LOAD_STORE.
      intro LOAD_STORE. ss. des.
      rewrite LOAD_STORE. ss.
    Qed.
  End NUM_MCASTS.

  Section MSG_SIZE.
    Hypothesis DEFMAP:
      (prog_defmap p) ! main_prm._MSG_SIZE =
      Some (Gvar (config_prm.v_MSG_SIZE (Z.of_nat msg_size))).

    Lemma _init_mem_msg_size
      : exists b_msz,
        Genv.find_symbol ge main_prm._MSG_SIZE = Some b_msz /\
        (b_msz < Genv.genv_next ge)%positive /\
        Mem.load Mint32 m b_msz 0%Z =
        Some (Vint (IntNat.of_nat msg_size)).
    Proof.
      apply Genv.find_def_symbol in DEFMAP.
      destruct DEFMAP as (b & FSYMB & FDEF).

      esplits; eauto.
      { eapply Genv.genv_symb_range. eauto. }

      eapply Genv.init_mem_characterization_gen in FDEF; eauto.
      destruct FDEF as (RANGE_PERM & PERM_ORDER &
                        LOAD_STORE & LOADBYTES).

      hexploit LOAD_STORE.
      { ss. }
      clear LOAD_STORE.
      intro LOAD_STORE. ss. des.
      rewrite LOAD_STORE. ss.
    Qed.
  End MSG_SIZE.


  Section PORT.
    Hypothesis DEFMAP:
      (prog_defmap p) ! main_prm._PORT =
      Some (Gvar (config_prm.v_PORT (Z.of_nat port))).

    Lemma _init_mem_port
      : exists b_pn,
        Genv.find_symbol ge main_prm._PORT = Some b_pn /\
        (b_pn < Genv.genv_next ge)%positive /\
        Mem.load Mint32 m b_pn 0%Z =
        Some (Vint (IntNat.of_nat port)).
    Proof.
      apply Genv.find_def_symbol in DEFMAP.
      destruct DEFMAP as (b & FSYMB & FDEF).

      esplits; eauto.
      { eapply Genv.genv_symb_range. eauto. }

      eapply Genv.init_mem_characterization_gen in FDEF; eauto.
      destruct FDEF as (RANGE_PERM & PERM_ORDER &
                        LOAD_STORE & LOADBYTES).

      hexploit LOAD_STORE.
      { ss. }
      clear LOAD_STORE.
      intro LOAD_STORE. ss. des.
      rewrite LOAD_STORE. ss.
    Qed.
  End PORT.

  Section IP_ADDR.
    Let v_IP_ADDR_i: globvar type :=
      config_prm.v_IP_ADDR (Z.of_nat max_num_tasks)
                           (Z.of_nat max_num_mcasts)
                           dest_ips_brep.

    Hypothesis DEFMAP: (prog_defmap p) ! main_prm._IP_ADDR =
                       Some (Gvar v_IP_ADDR_i).

    Lemma _init_mem_ip_addr
      : exists b_ip_addr,
        Genv.find_symbol ge main_prm._IP_ADDR = Some b_ip_addr /\
        (b_ip_addr < Genv.genv_next ge)%positive /\
        iForall (fun n ip_bs =>
                   Mem.loadbytes
                     m b_ip_addr (Z.of_nat (n * 16))
                     (Zlength ip_bs + 1) =
                   Some (inj_bytes (snoc ip_bs Byte.zero)))
                0 (task_ips_brep ++ (map fst mcasts))
    .
    Proof.
      apply Genv.find_def_symbol in DEFMAP.
      destruct DEFMAP as (b & FSYMB & FDEF).

      eexists. split; eauto.
      split.
      { eapply Genv.genv_symb_range. eauto. }

      eapply Genv.init_mem_characterization_gen in FDEF; eauto.
      destruct FDEF as (RANGE_PERM & PERM_ORDER &
                        LOAD_STORE & LOADBYTES).

      hexploit LOADBYTES.
      { eauto. }

      clear - ge.
      replace (init_data_list_size (gvar_init v_IP_ADDR_i))
        with (Z.of_nat (max_num_tasks + max_num_mcasts) * 16)%Z.
      2: { ss.
           rewrite init_data_list_size_app. ss.
           rewrite flat_map_concat_map.
           erewrite init_data_list_size_concat.
           2: { i. rewrite in_map_iff in IN. des.
                unfold ip_init_data in IN. subst.
                ss. }
           rewrite Zlength_correct.
           rewrite map_length.

           assert (length dest_ips_brep <= max_num_tasks + max_num_mcasts)%nat.
           { pose proof num_tasks_bound as NT.
             pose proof num_mcasts_bound as NMC.
             pose proof task_ips_convert_brep as CONV_T.
             pose proof mcast_ips_convert_brep as CONV_M.
             apply Forall2_length in CONV_T.
             apply Forall2_length in CONV_M.

             unfold dest_ips_brep.
             rewrite app_length. rewrite map_length.
             unfold bytes in *. nia.
           }
           unfold bytes in *.
           rewrite Zlength_correct. nia.
      }

      ss.
      clear. intros LOADBYTES.

      apply iForall_nth. i. r.
      destruct (nth_error (task_ips_brep ++ map fst mcasts) n)
        as [ip_bs| ] eqn: IP_BS.
      2: { desf.
           exfalso.
           unfold bytes in *.
           congruence. }
      fold bytes in *.
      rewrite IP_BS. ss.

      assert (LEN_IP: Forall (fun ip_bs' => (length ip_bs' < 16)%nat) dest_ips_brep).
      { apply Forall_forall.
        unfold dest_ips_brep.
        intros bs IN.
        apply in_app_or in IN.
        des.
        - apply In_nth_error in IN. des.
          pose proof task_ips_convert_brep as CONV.
          eapply Forall2_nth1 in CONV; eauto. des.
          hexploit IP.valid_ip_brep_spec; eauto. i. des.
          unfold IP.max_byte_length in *. ss.
        - apply In_nth_error in IN. des.
          pose proof mcast_ips_convert_brep as CONV.
          apply map_nth_error_iff in IN. des.
          destruct a as [ip' mbrs]. ss. subst.

          eapply Forall2_nth1 in CONV; eauto. des.
          hexploit IP.valid_ip_brep_spec; eauto. i. des.
          unfold IP.max_byte_length in *. ss.
      }


      eapply Mem_loadbytes_sublist with
          (n1:= Z.of_nat (n * 16)) (n2:= (Zlength ip_bs + 1)%Z)
        in LOADBYTES; cycle 1.
      { nia. }
      { rewrite Zlength_correct. nia. }
      { match goal with
        | |- (?lhs <= _)%Z => replace lhs with (Z.of_nat (n * 16 + S (length ip_bs)))
        end.
        2: { rewrite Zlength_correct. nia. }

        assert (length ip_bs < 16)%nat.
        { rewrite Forall_nth in LEN_IP.
          specialize (LEN_IP n). r in LEN_IP.
          unfold dest_ips_brep in LEN_IP.
          unfold bytes in *.
          rewrite IP_BS in LEN_IP. ss. }
        assert (n < max_num_tasks + max_num_mcasts)%nat.
        { apply nth_error_Some1' in IP_BS.
          rewrite app_length in IP_BS.
          rewrite map_length in IP_BS.

          pose proof task_ips_convert_brep as CONV_T.
          apply Forall2_length in CONV_T.
          pose proof mcast_ips_convert_brep as CONV_M.
          apply Forall2_length in CONV_M.

          pose proof num_tasks_bound.
          pose proof num_mcasts_bound.
          unfold bytes in *. nia.
        }
        nia.
      }
      ss.
      rewrite LOADBYTES.
      f_equal.
      clear LOADBYTES.
      fold dest_ips_brep in IP_BS.

      match goal with
      | |- context[flat_map _ _ ++ ?x] => generalize x as rest
      end.

      revert n IP_BS LEN_IP.
      generalize dest_ips_brep.
      intro l.

      induction l as [| h t IH]; i.
      { exfalso.
        destruct n; ss. }

      destruct n as [| n'].
      { simpl in IP_BS. clarify. ss.
        assert (LEN_IP_BS: (length ip_bs < 16)%nat).
        { inv LEN_IP. ss. }
        clear LEN_IP IH.
        rewrite Zlength_correct. ss.

        match goal with
        | |- context [firstn ?n] => replace n with (length ip_bs + 1)%nat by nia
        end.

        repeat rewrite Int.unsigned_repr by apply ubyte_in_uint_range.
        repeat rewrite simpl_init_byte.
        destruct ip_bs as [| h1 tl]; ss.
        do 15 (destruct tl as [| ? tl]; ss; []).
        exfalso. nia.
      }
      { simpl in IP_BS.
        hexploit IH; eauto.
        { inv LEN_IP. ss. }
        intro FN.
        rewrite flat_map_concat_map. ss.
        replace (S n' * 16)%nat with (16 + n' * 16)%nat by ss.

        repeat rewrite Int.unsigned_repr by apply ubyte_in_uint_range.
        repeat rewrite simpl_init_byte. ss.
        rewrite Nat2Z.id. ss.
        rewrite <- flat_map_concat_map.
        rewrite Nat2Z.id in FN.  eauto.
      }
    Qed.
  End IP_ADDR.


  Lemma load_store_init_data_mcmem
        b ofs
        mip_bs mbrs tid'
        (VALID_TID: (tid' < num_tasks)%nat)
        (MCMEM: Genv.load_store_init_data
                  ge m b ofs (mcmem_init_data
                                (Z.of_nat max_num_tasks)
                                (group_memflags (mip_bs, mbrs))))
    : Mem.load Mint8signed m b (ofs + Z.of_nat tid') =
      Some (Vint (if existsb (Nat.eqb tid') mbrs
                  then Int.one else Int.zero)).
  Proof.
    unfold group_memflags in MCMEM. ss.
    unfold mcmem_init_data in *.
    apply load_store_init_data_app in MCMEM. des.

    clear MCMEM0.

    assert (AUX: forall nt ofs' tid' i
                   (TID: (tid' < nt)%nat)
                   (MCMEM : Genv.load_store_init_data
                              ge m b ofs'
                              (map (fun b: bool =>
                                      Init_int8 (Int.repr (if b then 1 else 0)))
                                   (imap (fun n _ => existsb (Nat.eqb n) mbrs)
                                         i (repeat tt nt))))
             ,
               Mem.load Mint8signed m b (ofs' + Z.of_nat tid') =
               Some (Vint (if existsb (Nat.eqb (i + tid')) mbrs
                           then Int.one else Int.zero))).
    { clear.
      intro nt.
      induction nt as [| nt' IH]; i; ss.
      { nia. }
      destruct tid' as [| tid']; ss.
      { des.
        rewrite plus_0_r. rewrite Z.add_0_r.
        rewrite Mem.load_int8_signed_unsigned.
        rewrite MCMEM. ss.
        desf. }
      des.

      hexploit (IH (ofs' + 1)%Z tid' (S i)).
      { nia. }
      { eauto. }
      intro LOAD.

      replace (Z.of_nat (S tid')) with (1 + Z.of_nat tid')%Z by nia.
      replace (i + S tid')%nat with (S i + tid')%nat by nia.
      rewrite Z.add_assoc. apply LOAD.
    }
    hexploit AUX; eauto.
  Qed.


  Lemma mcmem_init_data_list_size
        ginfo
    : init_data_list_size
        (mcmem_init_data (Z.of_nat max_num_tasks)
                         (group_memflags ginfo)) =
      (Z.of_nat max_num_tasks).
  Proof.
    assert (LEN_GMFS: length (group_memflags ginfo) = num_tasks).
    { unfold group_memflags.
      rewrite imap_length.
      apply repeat_length. }

    unfold mcmem_init_data.
    rewrite init_data_list_size_app.

    match goal with
    | |- (init_data_list_size (map ?f ?l) + _)%Z = _ =>
      replace (init_data_list_size (map f l)) with (Zlength l)
    end.
    2: { clear.
         induction (group_memflags ginfo) as [| h t IH]; ss.
         rewrite Zlength_cons.
         rewrite <- IH. nia. }

    rewrite Zlength_correct.
    rewrite LEN_GMFS.

    assert (NT_BOUND: (num_tasks <= max_num_tasks)%nat).
    { pose proof num_tasks_bound.
      unfold num_tasks. ss. }

    destruct (Z.ltb_spec (Z.of_nat num_tasks)
                         (Z.of_nat max_num_tasks)) as [LT|GE].
    - ss. nia.
    - ss. nia.
  Qed.


  Lemma load_store_init_data_flatmap_mcmem
        b ofs mcasts'
        midx mip_bs mbrs tid'
        (MCMEM: Genv.load_store_init_data
                  ge m b ofs
                  (flat_map (mcmem_init_data
                               (Z.of_nat max_num_tasks))
                            (map group_memflags mcasts')))
        (MIDX: nth_error mcasts' midx = Some (mip_bs, mbrs))
        (* (MAX_NUM_MEMBERS: (length mbrs <= num_tasks)%nat) *)
        (TID': (tid' < num_tasks)%nat)
    : Mem.load Mint8signed m b
               (ofs + Z.of_nat ((max_num_tasks * midx + tid'))) =
      Some (Vint (if existsb (Nat.eqb tid') mbrs
                  then Int.one else Int.zero)).
  Proof.
    depgen ofs. revert midx MIDX.
    induction mcasts' as [| h_mc t_mc IH]; i; ss.
    { destruct midx; ss. }

    destruct midx as [| midx]; ss.
    { clarify.
      apply load_store_init_data_app in MCMEM. des.
      rewrite Nat.mul_0_r. ss.
      eapply load_store_init_data_mcmem; eauto.
    }
    apply load_store_init_data_app in MCMEM. des.

    rewrite mcmem_init_data_list_size in *.
    hexploit IH; eauto. intro LOAD.
    match goal with
    | LOAD: Mem.load _ m b ?ofs1 = Some ?a |-
      Mem.load _ m b ?ofs2 = Some ?a =>
      replace ofs2 with ofs1 by nia
    end.
    congruence.
  Qed.

  Section MCAST_MEMBER.
    Hypothesis DEFMAP:
      (prog_defmap p) ! main_prm._MCAST_MEMBER =
      Some (Gvar (config_prm.v_MCAST_MEMBER
                    (Z.of_nat max_num_tasks)
                    (Z.of_nat max_num_mcasts)
                    mcast_memflags)).

    Lemma _init_mem_mcm
      : exists b_mcm,
        Genv.find_symbol ge main_prm._MCAST_MEMBER = Some b_mcm /\
        (b_mcm < Genv.genv_next ge)%positive /\
        (forall mid midx tid' mip_bs mbrs
           (MCAST_ID: mid = (num_tasks + midx)%nat)
           (MCASTS_MID: nth_error mcasts midx = Some (mip_bs, mbrs))
           (RANGE_TID: (tid' < num_tasks)%nat),
            Mem.load Mint8signed m b_mcm
                     (Z.of_nat (max_num_tasks * midx + tid')) =
            Some (Vint (if existsb (Nat.eqb tid') mbrs
                        then Int.one else Int.zero)))
    .
    Proof.
      apply Genv.find_def_symbol in DEFMAP.
      destruct DEFMAP as (b & FSYMB & FDEF).

      eexists.
      split; eauto.
      split.
      { eapply Genv.genv_symb_range. eauto. }

      eapply Genv.init_mem_characterization_gen in FDEF; eauto.
      destruct FDEF as (RANGE_PERM & PERM_ORDER &
                        LOAD_STORE & LOADBYTES).
      ss.
      hexploit LOAD_STORE.
      { ss. }
      clear LOAD_STORE. clear LOADBYTES.
      intro LOAD_STORE.
      apply load_store_init_data_app in LOAD_STORE. des.

      i. hexploit load_store_init_data_flatmap_mcmem; eauto.
    Qed.
  End MCAST_MEMBER.


  (* writable *)

  Section SEND_BUF.
    Hypothesis DEFMAP:
      (prog_defmap p) ! main_prm._send_buf =
      Some (Gvar (main_prm.v_send_buf (Z.of_nat msg_size_k))).

    Lemma _init_mem_send_buf
      : exists b_sbuf,
        Genv.find_symbol ge main_prm._send_buf = Some b_sbuf /\
        (b_sbuf < Genv.genv_next ge)%positive /\
        Mem.loadbytes m b_sbuf 0 8 = Some (inj_bytes (IntByte.to_bytes64 Int64.zero)) /\
        (* Mem.load Mint64 m b_sbuf 0 = Some (Vlong Int64.zero) /\ *)
        Mem.load Mint8signed m b_sbuf 8 = Some (Vint Int.zero) /\
        Mem.loadbytes m b_sbuf 9 (Z.of_nat msg_size) =
        Some (inj_bytes (List.repeat Byte.zero msg_size)) /\
        Mem.range_perm m b_sbuf 0 (Z.of_nat pld_size) Cur Writable
    .
    Proof.
      apply Genv.find_def_symbol in DEFMAP.
      destruct DEFMAP as (b & FSYMB & FDEF).

      eexists.
      split; eauto.
      split.
      { eapply Genv.genv_symb_range. eauto. }

      eapply Genv.init_mem_characterization_gen in FDEF; eauto.
      destruct FDEF as (RANGE_PERM & PERM_ORDER &
                        LOAD_STORE & LOADBYTES).

      hexploit LOADBYTES; ss.
      clear LOADBYTES.

      assert (STRT_SZ_EQ: msg_struct_sz (Z.of_nat msg_size_k) =
                          Z.of_nat max_pld_size).
      { unfold msg_struct_sz, max_pld_size.
        unfold max_msg_size. nia. }
      rewrite STRT_SZ_EQ in *.
      rewrite Z.max_l in * by nia.
      rewrite Z.add_0_r in *.
      rewrite app_nil_r.
      rewrite Nat2Z.id.
      rewrite list_repeat_eq.

      intro LOADBYTES.
      assert (SIZE_DIV: exists rest,
                 (max_pld_size = 8 + (1 + (msg_size + rest)))%nat).
      { clear.
        unfold max_pld_size.
        exists (max_msg_size - msg_size)%nat.
        unfold max_msg_size.
        pose proof msg_size_bound. nia. }
      des.
      rewrite SIZE_DIV in LOADBYTES.

      rewrite Nat2Z.inj_add in LOADBYTES.
      eapply Mem_loadbytes_split' in LOADBYTES; cycle 1.
      { nia. }
      { nia. }

      replace (Z.of_nat 8) with 8%Z in * by ss.
      replace (Z.to_nat 8) with 8%nat in * by ss.

      destruct LOADBYTES as [LOAD_TIME LOADBYTES].
      split.
      { erewrite LOAD_TIME. ss. }

      rewrite Nat2Z.inj_add in LOADBYTES.
      eapply Mem_loadbytes_split' in LOADBYTES; ss.
      2: { nia. }

      destruct LOADBYTES as [LOAD_TID LOADBYTES].
      split.
      { erewrite Mem.loadbytes_load; eauto; ss.
        solve_divide. }

      rewrite Nat2Z.inj_add in LOADBYTES.
      replace (Z.of_nat 1) with 1%Z in * by ss.
      replace (Z.to_nat 1) with 1%nat in * by ss.
      eapply Mem_loadbytes_split' in LOADBYTES; cycle 1.
      { nia. }
      { nia. }
      destruct LOADBYTES as [LOADBYTES LOADBYTES_REST].

      split; ss.
      { rewrite LOADBYTES. f_equal.
        rewrite Nat2Z.id.
        unfold inj_bytes.
        rewrite map_repeat.
        rewrite repeat_app.
        rewrite firstn_app_exact.
        2: { rewrite repeat_length. ss. }
        ss.
      }
      clear - RANGE_PERM.

      assert (pld_size <= max_pld_size)%nat.
      { unfold max_pld_size, pld_size.
        unfold max_msg_size.
        pose proof msg_size_bound. nia. }

      unfold v_send_buf in RANGE_PERM.
      unfold Genv.perm_globvar in RANGE_PERM. ss.

      ii. apply RANGE_PERM. nia.
    Qed.
  End SEND_BUF.



  Lemma _init_Mem_msg_entries
        b ofs
        (LBS: Mem.loadbytes m b ofs inb_sz =
              Some (repeat (Byte Byte.zero) inb_nsz))
    : iForall (Mem_msg_entry m b ofs) 0
              (repeat None num_tasks).
  Proof.
    apply iForall_nth. ss. i.
    destruct (lt_ge_dec n num_tasks).
    2: { rewrite repeat_nth_error_None; ss. }
    rewrite repeat_nth_error_Some by ss.
    ss.

    erewrite Mem_loadbytes_sublist; eauto; cycle 1.
    { nia. }
    { nia. }
    { hexploit (within_inb_nsz2 n mentry_ensz); eauto.
      { apply range_mentry_ensz. }
      unfold mentry_ensz. nia. }

    f_equal.
    rewrite Nat2Z.id.

    pose proof num_tasks_bound' as NT_BOUND.
    replace inb_nsz with (mentry_nsz * n +
                          mentry_nsz * (max_num_tasks - n))%nat.
    2: { unfold inb_nsz. nia. }

    rewrite repeat_app.
    rewrite skipn_app_exact.
    2: { rewrite repeat_length. nia. }

    destruct (max_num_tasks - n)%nat as [|n'] eqn: SUB.
    { exfalso. nia. }

    replace (mentry_nsz * S n')%nat with
        (S (max_msg_size + mentry_nsz * n'))%nat.
    2: { unfold mentry_nsz. nia. }
    ss.
  Qed.

  (* assert (MENTRY_SZ_DIV: exists rest, *)
  (*            (mentry_nsz = mentry_ensz + rest)%nat). *)
  (* { exists (mentry_nsz - mentry_ensz)%nat. *)
  (*   clear. *)
  (*   pose proof range_mentry_ensz. nia. } *)

  (*   des. rewrite MENTRY_SZ_DIV. *)

  (*   rewrite <- Nat.add_assoc. *)
  (*   rewrite repeat_app. *)
  (*   rewrite firstn_app_exact. *)
  (*   2: { rewrite repeat_length. ss. } *)

  (*   unfold inj_bytes, mentry_to_bytes. ss. *)
  (*   unfold mentry_ensz. rewrite plus_comm. ss. *)
  (*   rewrite map_repeat. ss. *)
  (* Qed. *)


  Section MSTORE.
    Hypothesis DEFMAP:
      (prog_defmap p) ! main_prm._mstore =
      Some (Gvar (main_prm.v_mstore (Z.of_nat msg_size_k)
                                    (Z.of_nat max_num_tasks))).

    Lemma _init_mem_mstore
      : exists b_mst,
        Genv.find_symbol ge main_prm._mstore = Some b_mst /\
        (b_mst < Genv.genv_next ge)%positive /\
        Mem.load Mint32 m b_mst 0 = Some (Vint Int.zero) /\
        Mem.range_perm m b_mst 0 4 Cur Writable /\
        Mem_inbox m b_mst 4 (List.repeat None num_tasks) /\
        Mem_inbox m b_mst (4 + inb_sz) (List.repeat None num_tasks)
    .
    Proof.
      apply Genv.find_def_symbol in DEFMAP.
      destruct DEFMAP as (b & FSYMB & FDEF).

      eexists.
      split; eauto.
      split.
      { eapply Genv.genv_symb_range. eauto. }

      eapply Genv.init_mem_characterization_gen in FDEF; eauto.
      destruct FDEF as (RANGE_PERM & PERM_ORDER &
                        LOAD_STORE & LOADBYTES).

      (* assert (INBOX_SZ_NNEG: 0 <= inb_sz). *)
      (* { apply range_inb_sz_precise. } *)

      hexploit LOADBYTES; ss.
      rewrite <- inb_sz_eq.

      clear LOADBYTES.
      rewrite Z.max_l by nia.
      rewrite app_nil_r.
      rewrite list_repeat_eq.
      rewrite Z2Nat.inj_add by nia.
      rewrite Z.add_0_r in *.
      (* rewrite <- Z2Nat.inj_add by nia. *)

      intro LOADBYTES.
      eapply Mem_loadbytes_split' in LOADBYTES; ss.
      2: { nia. }

      rewrite repeat_app in LOADBYTES.
      rewrite firstn_app_exact in LOADBYTES.
      2: { rewrite repeat_length. ss. }
      rewrite skipn_app_exact in LOADBYTES.
      2: { rewrite repeat_length. ss. }

      change (Z.to_nat 4) with 4%nat in LOADBYTES.
      destruct LOADBYTES as [LOAD_RCV LOADBYTES].

      split.
      { erewrite Mem.loadbytes_load; eauto; ss.
        solve_divide. }
      split.
      { ii. apply RANGE_PERM.
        rewrite <- inb_sz_eq.
        rewrite Z.max_l by nia.
        nia. }

      rewrite <- Zplus_diag_eq_mult_2 in LOADBYTES.
      eapply Mem_loadbytes_split' in LOADBYTES; try nia.
      rewrite Z2Nat.inj_add in LOADBYTES by nia.
      rewrite repeat_app in LOADBYTES.
      rewrite firstn_app_exact in LOADBYTES.
      2: { rewrite repeat_length. ss. }
      rewrite skipn_app_exact in LOADBYTES.
      2: { rewrite repeat_length. ss. }

      rewrite Nat2Z.id in LOADBYTES by ss.
      destruct LOADBYTES as [LOAD_INB1 LOAD_INB2].

      split.
      - clear LOAD_INB2.
        r. splits; ss; cycle 1.
        { (* unfold empty_msg_entry. *)
          rewrite repeat_length. ss. }
        { clear - RANGE_PERM.
          ii. apply RANGE_PERM.
          rewrite <- inb_sz_eq. nia. }
        eapply _init_Mem_msg_entries; eauto.
      - clear LOAD_INB1.
        r. splits; ss; cycle 1.
        { (* unfold empty_msg_entry. *)
          rewrite repeat_length. ss. }
        { clear - RANGE_PERM.
          ii. apply RANGE_PERM.
          rewrite <- inb_sz_eq. nia. }
        eapply _init_Mem_msg_entries; eauto.
    Qed.

  End MSTORE.

  Section SEND_HIST.
    Hypothesis DEFMAP:
      (prog_defmap p) ! main_prm._send_hist =
      Some (Gvar (main_prm.v_send_hist (Z.of_nat max_num_tasks))).

    Lemma _init_mem_send_hist
      : exists b_sh,
        Genv.find_symbol ge main_prm._send_hist = Some b_sh /\
        (b_sh < Genv.genv_next ge)%positive /\
        Mem.loadbytes m b_sh 0 (Z.of_nat num_tasks) =
        Some (map bool2memval (List.repeat false num_tasks)) /\
        Mem.range_perm m b_sh 0 (Z.of_nat num_tasks) Cur Writable
    .
    Proof.
      apply Genv.find_def_symbol in DEFMAP.
      destruct DEFMAP as (b & FSYMB & FDEF).

      eexists.
      split; eauto.
      split.
      { eapply Genv.genv_symb_range. eauto. }

      eapply Genv.init_mem_characterization_gen in FDEF; eauto.
      destruct FDEF as (RANGE_PERM & PERM_ORDER &
                        LOAD_STORE & LOADBYTES).
      ss.
      assert (MAX_NT_DIV: exists rst, (max_num_tasks = num_tasks + rst)%nat).
      { clear. pose proof num_tasks_bound'.
        exists (max_num_tasks - num_tasks)%nat. nia. }
      des.

      split.
      - hexploit LOADBYTES; eauto.
        rewrite Z.max_l by nia.
        rewrite Z.add_0_r.
        rewrite MAX_NT_DIV.
        rewrite Nat2Z.inj_add.
        rewrite list_repeat_eq.
        rewrite Z2Nat.inj_add by nia.
        rewrite app_nil_r.
        rewrite repeat_app.

        intro LB1.
        apply Mem_loadbytes_split' in LB1; try nia.
        destruct LB1 as [LB LB_R].
        rewrite Nat2Z.id in *.
        rewrite firstn_app_exact in LB.
        2: { rewrite repeat_length. ss. }

        rewrite LB. f_equal.
        rewrite map_repeat. ss.
      - ii. apply RANGE_PERM.
        rewrite Z.max_l by nia.
        rewrite Z.add_0_r. nia.
    Qed.

  End SEND_HIST.

  Section TXS.
    Hypothesis DEFMAP:
      (prog_defmap p) ! main_prm._txs =
      Some (Gvar (main_prm.v_txs)).

    Lemma _init_mem_txs
      : exists b_txs,
        Genv.find_symbol ge main_prm._txs = Some b_txs /\
        (b_txs < Genv.genv_next ge)%positive /\
        Mem.load Mint32 m b_txs 0%Z = Some (Vint Int.zero) /\
        Mem.range_perm m b_txs 0%Z 4 Cur Writable.
    Proof.
      apply Genv.find_def_symbol in DEFMAP.
      destruct DEFMAP as (b & FSYMB & FDEF).

      eexists.
      split; eauto.
      split.
      { eapply Genv.genv_symb_range. eauto. }

      eapply Genv.init_mem_characterization_gen in FDEF; eauto.
      destruct FDEF as (RANGE_PERM & PERM_ORDER &
                        LOAD_STORE & LOADBYTES).

      hexploit LOAD_STORE.
      { ss. }
      clear LOAD_STORE.
      intro LOAD_STORE. ss. des.
      splits; eauto.
      rr in LOAD_STORE.
      rewrite LOAD_STORE; ss.
      solve_divide.
    Qed.
  End TXS.

  Section RXS.
    Hypothesis DEFMAP:
      (prog_defmap p) ! main_prm._rxs =
      Some (Gvar (main_prm.v_rxs)).

    Lemma _init_mem_rxs
      : exists b_rxs,
        Genv.find_symbol ge main_prm._rxs = Some b_rxs /\
        (b_rxs < Genv.genv_next ge)%positive /\
        Mem.load Mint32 m b_rxs 0%Z = Some (Vint Int.zero) /\
        Mem.range_perm m b_rxs 0%Z 4 Cur Writable.
    Proof.
      apply Genv.find_def_symbol in DEFMAP.
      destruct DEFMAP as (b & FSYMB & FDEF).

      eexists.
      split; eauto.
      split.
      { eapply Genv.genv_symb_range. eauto. }

      eapply Genv.init_mem_characterization_gen in FDEF; eauto.
      destruct FDEF as (RANGE_PERM & PERM_ORDER &
                        LOAD_STORE & LOADBYTES).

      hexploit LOAD_STORE.
      { ss. }
      clear LOAD_STORE.
      intro LOAD_STORE. ss. des.
      splits; eauto.
      rr in LOAD_STORE.
      rewrite LOAD_STORE; ss.
      solve_divide.
    Qed.
  End RXS.

End INIT_DATA_LEMMAS.


Section INIT_MEM_INVERSION.
  Import Clight.
  Context `{SystemEnv}.
  (* Context `{CProgSysEvent}. *)
  Variable cprog: Clight.program.
  Variable m_i: mem.
  Let ge := globalenv cprog.

  Hypothesis INIT_MEM: Genv.init_mem cprog = Some m_i.
  (* Variable gvars: list (ident * cglobvar). *)
  Variable tid: nat.
  Variable gfuns: list (ident * fundef).
  Variable cenvs: list (ident * composite).
  Hypothesis RANGE_TID: (tid < num_tasks)%nat.

  Context `{genv_props ge (main_gvar_ilist tid) gfuns cenvs}.

  (* (* init_mem_inversion *) *)
  (* Let glob_init: Genv.globals_initialized ge ge m_i. *)
  (* Proof. *)
  (*   apply Genv.init_mem_characterization_gen; eauto. *)
  (* Qed. *)

  Lemma main_gvar_find_def
        i gv b
        (FSYMB: Genv.find_symbol ge i = Some b)
        (IN: In (i, gv) (main_gvar_ilist tid))
    : Genv.find_def ge b = Some (Gvar gv).
  Proof.
    hexploit (in_gvar_ilist i); eauto.
    i. des. clarify.
    apply Genv.find_var_info_iff; eauto.
  Qed.

  Lemma bytes_of_init_data_list_map
        (ge': genv) l
    : Genv.bytes_of_init_data_list ge' l =
      concat (map (Genv.bytes_of_init_data ge') l).
  Proof.
    induction l as [| h t IH]; ss.
    rewrite IH. ss.
  Qed.

  (* Lemma loadbytes_ip_aux *)
  (*       (ge': genv) m (ip_bs: bytes) b ofs *)
  (*       (LEN_BD: length ip_bs < 16) *)
  (*       (LBS: Mem.loadbytes m b ofs 16 = *)
  (*             Some (concat (map (Genv.bytes_of_init_data ge') *)
  (*                               (ip_init_data ip_bs)))) *)
  (*   : Mem.loadbytes m b ofs (Zlength ip_bs + 1)%Z = *)
  (*     Some (inj_bytes (snoc ip_bs Byte.zero)). *)
  (* Proof. *)
  (*   ss. unfold encode_int in *. ss. *)
  (*   repeat rewrite rev_if_be_single in *. ss. *)
  (*   unfold app in LBS. *)
  (*   repeat (rewrite Int.unsigned_repr in LBS *)
  (*            by eapply ubyte_in_uint_range). *)
  (*   repeat rewrite Byte.repr_unsigned in LBS. *)

  (*   pose (k:= (16 - (Zlength ip_bs + 1))%Z). *)
  (*   assert (k >= 0)%Z. *)
  (*   { subst k. rewrite Zlength_correct. nia. } *)

  (*   replace 16%Z with (Zlength ip_bs + 1 + k)%Z in LBS. *)
  (*   2: { subst k. nia. } *)
  (*   apply Mem.loadbytes_split in LBS; ss. *)
  (*   2: { rewrite Zlength_correct. nia. } *)

  (*   des. rewrite LBS. *)
  (*   apply Mem.loadbytes_length in LBS. *)

  (*   unfold snoc. unfold inj_bytes. *)
  (*   rewrite map_app. *)
  (*   f_equal. *)
  (*   eapply (ip_bytes_aux ip_bs 16). *)
  (*   { ss. rewrite LBS1. eauto. } *)
  (*   { rewrite LBS. *)
  (*     rewrite Zlength_correct. nia. } *)
  (* Qed. *)

  Lemma init_mem_consts: mem_consts ge m_i tid.
  Proof.
    (* r in glob_init. *)
    econs.
    - i. ss.
      hexploit _init_mem_tid; eauto.
      { instantiate (1:= tid).
        pose proof range_num_tasks.
        range_stac. }
      { apply Genv.find_def_symbol.
        esplits; eauto.
        eapply main_gvar_find_def; eauto.
        sIn. }
      i. des. fold fundef in *. clarify.
    - i. ss.
      hexploit _init_mem_pals_period; eauto.
      { apply Genv.find_def_symbol.
        esplits; eauto.
        eapply main_gvar_find_def; eauto.
        sIn. }
      i. des. fold fundef in *. clarify.
    - i. ss.
      hexploit _init_mem_max_cskew; eauto.
      { apply Genv.find_def_symbol.
        esplits; eauto.
        eapply main_gvar_find_def; eauto.
        sIn. }
      i. des. fold fundef in *. clarify.
    - i. ss.
      hexploit _init_mem_max_nwdelay; eauto.
      { apply Genv.find_def_symbol.
        esplits; eauto.
        eapply main_gvar_find_def; eauto.
        sIn. }
      i. des. fold fundef in *. clarify.
    - i. ss.
      hexploit _init_mem_num_tasks; eauto.
      { apply Genv.find_def_symbol.
        esplits; eauto.
        eapply main_gvar_find_def; eauto.
        sIn. }
      i. des. fold fundef in *. clarify.
    - i. ss.
      hexploit _init_mem_num_mcasts; eauto.
      { apply Genv.find_def_symbol.
        esplits; eauto.
        eapply main_gvar_find_def; eauto.
        sIn. }
      i. des. fold fundef in *. clarify.
    - i. ss.
      hexploit _init_mem_msg_size; eauto.
      { apply Genv.find_def_symbol.
        esplits; eauto.
        eapply main_gvar_find_def; eauto.
        sIn. }
      i. des. fold fundef in *. clarify.
    - i. ss.
      hexploit _init_mem_port; eauto.
      { apply Genv.find_def_symbol.
        esplits; eauto.
        eapply main_gvar_find_def; eauto.
        sIn. }
      i. des. fold fundef in *. clarify.
    - i. ss.
      hexploit _init_mem_ip_addr; eauto.
      { apply Genv.find_def_symbol.
        esplits; eauto.
        eapply main_gvar_find_def; eauto.
        sIn. }
      i. des. fold fundef in *. clarify.
    - i. ss.
      hexploit _init_mem_mcm; eauto.
      { apply Genv.find_def_symbol.
        esplits; eauto.
        eapply main_gvar_find_def; eauto.
        sIn. }
      intros (b_mcm' & FSYMB2 & NBLK & INIT).
      fold fundef in *. clarify.
      eapply INIT; eauto.
  Qed.

  Lemma init_mem_mstore
    : mem_mstore ge m_i
                 false 4%Z (4 + inb_sz)%Z
                 MWITree.init_inbox MWITree.init_inbox.
  Proof.
    ii.
    hexploit _init_mem_mstore; eauto.
    { apply Genv.find_def_symbol.
      esplits; eauto.
      eapply main_gvar_find_def; eauto.
      sIn. }

    i. des. ss.
    fold fundef in *. clarify.
  Qed.

  Lemma init_mem_sbuf
    : mem_sbuf ge m_i 0 0 (List.repeat Byte.zero msg_size).
  Proof.
    ii.
    hexploit _init_mem_send_buf; eauto.
    { apply Genv.find_def_symbol.
      esplits; eauto.
      eapply main_gvar_find_def; eauto.
      sIn. }

    i. des. ss.
    fold fundef in *. clarify.
  Qed.

  Lemma init_mem_sh
    : mem_sh ge m_i (List.repeat false num_tasks).
  Proof.
    ii.
    hexploit _init_mem_send_hist; eauto.
    { apply Genv.find_def_symbol.
      esplits; eauto.
      eapply main_gvar_find_def; eauto.
      sIn. }

    i. des. ss.
    fold fundef in *. clarify.
  Qed.

  Lemma init_mem_txs: mem_txs ge m_i 0.
  Proof.
    ii.
    hexploit _init_mem_txs; eauto.
    { apply Genv.find_def_symbol.
      esplits; eauto.
      eapply main_gvar_find_def; eauto.
      sIn. }

    i. des. ss.
    fold fundef in *. clarify.
  Qed.

  Lemma init_mem_rxs: mem_rxs ge m_i 0.
  Proof.
    ii.
    hexploit _init_mem_rxs; eauto.
    { apply Genv.find_def_symbol.
      esplits; eauto.
      eapply main_gvar_find_def; eauto.
      sIn. }

    i. des. ss.
    fold fundef in *. clarify.
  Qed.

End INIT_MEM_INVERSION.
