From ITree Require Import ITree.
From compcert Require Import Maps AST Values Memory Globalenvs Ctypes.
From compcert Require Coqlib Clight Clightdefs.
From Paco Require Import paco.

Require Import sflib.
Require Import Axioms StdlibExt IntegersExt.

Require Import SysSem.
Require Import IPModel DiscreteTimeModel IntByteModel.
Require Import NWSysModel OSNodes OSModel.
Require Import ProgSem.
Require Import SyncSysModel.
Require Import CProgEventSem.
Require Import ProgSim.
Require Import RTSysEnv MWITree.

(* Require Import SystemParams. *)
(* Require Import SystemDefs ITreeSpec. *)
(* Require Import SystemEventSem. *)
(* Require Import main_p main_pi. *)
Require Import config_prm main_prm SystemProgs.
Require Import LinkLemmas.

Require Export CompcertLemmas.
Require Import CProgSimLemmas.

Require Import Arith ZArith Bool.
Require Import String List Lia.

Import ITreeNotations.
Import Clight Clightdefs.

Set Nested Proofs Allowed.

Local Transparent Archi.ptr64.

Arguments Z.mul : simpl nomatch.
Arguments Z.add: simpl nomatch.
Arguments Z.sub: simpl nomatch.

Arguments Nat.add: simpl nomatch.
Arguments Nat.sub: simpl nomatch.
Arguments Nat.mul: simpl nomatch.

Arguments PTree.get : simpl nomatch.
Arguments PTree.set: simpl never.

Arguments firstn: simpl nomatch.
Arguments skipn: simpl nomatch.


(* general lemmas (TODO: move) *)


(* Local Open Scope Z. *)

Local Opaque Z.to_nat Z.of_nat Zlength.

Local Open Scope Z.


Section INBOX.
  Context `{SystemEnv}.

  (* Definition empty_msg_entry : bool * bytes := *)
  (*   (false, List.repeat Byte.zero msg_size). *)

  (* effective size *)
  Definition mentry_nsz: nat := max_msg_size + 1.
  Notation mentry_sz := (Z.of_nat mentry_nsz).

  Lemma mentry_sz_eq
    : mentry_sz = msg_entry_sz (Z.of_nat msg_size_k).
  Proof.
    (* unfold mentry_sz, msg_entry_sz. *)
    unfold msg_entry_sz.
    unfold mentry_nsz. unfold max_msg_size.
    nia.
  Qed.

  Lemma range_mentry_nsz_precise
    : (mentry_nsz < Packet.maxlen)%nat.
  Proof.
    assert (mentry_nsz < max_pld_size)%nat.
    { unfold mentry_nsz, max_pld_size. nia. }
    pose proof packet_length_bound.
    unfold max_pld_size, max_msg_size in *.
    nia.
  Qed.

  Lemma range_mentry_sz_precise
    : (0 <= mentry_sz < Z.of_nat Packet.maxlen)%Z.
  Proof.
    (* unfold mentry_sz. *)
    pose proof range_mentry_nsz_precise. nia.
  Qed.

  Lemma range_mentry_nsz
    : IntRange.sint mentry_nsz.
  Proof.
    pose proof range_mentry_nsz_precise.
    pose proof range_packet_maxlen.
    range_stac.
  Qed.

  Definition mentry_ensz: nat := (msg_size + 1).
  Notation mentry_esz := (Z.of_nat mentry_ensz).

  Lemma range_mentry_ensz
    : (0 <= mentry_ensz <= mentry_nsz)%nat.
  Proof.
    unfold mentry_ensz, mentry_nsz.
    pose proof msg_size_bound.
    fold max_msg_size in *. nia.
  Qed.

  (* = 6 * 8 = 48 *)
  Definition inb_nsz: nat := mentry_nsz * max_num_tasks.

  Notation inb_sz := (Z.of_nat inb_nsz).

  Lemma inb_sz_eq
    : inb_sz = inbox_sz (Z.of_nat msg_size_k)
                        (Z.of_nat max_num_tasks).
  Proof.
    unfold inbox_sz.
    unfold inb_nsz.
    rewrite <- mentry_sz_eq. nia.
  Qed.

  Lemma within_inb_nsz1
        i
        (VALID_TID: (i < num_tasks)%nat)
    : (mentry_nsz * i <= inb_nsz)%nat.
  Proof.
    unfold inb_nsz.
    pose proof num_tasks_bound.
    fold num_tasks in *. nia.
  Qed.

  Lemma within_inb_nsz2
        i ofs
        (VALID_TID: (i < num_tasks)%nat)
        (VALID_ENTRY_AREA: (ofs <= mentry_nsz)%nat)
    : (mentry_nsz * i + ofs <= inb_nsz)%nat.
  Proof.
    unfold inb_nsz.
    pose proof num_tasks_bound.
    fold num_tasks in *.
    unfold mentry_nsz in *. nia.
  Qed.

  Lemma maxlen_byte_aux
    : (Z.of_nat Packet.maxlen * Byte.max_signed
       < Int.max_signed)%Z.
  Proof.
    unfold Packet.maxlen.
    rewrite Z2Nat.id by nia. ss.
  Qed.

  Lemma range_inb_sz_precise
    : (inb_sz < Z.of_nat Packet.maxlen * Byte.max_signed)%Z.
  Proof.
    unfold inb_nsz.
    pose proof range_max_num_tasks as R_MNT.
    pose proof range_mentry_nsz_precise as PR_ENT.
    pose proof maxlen_byte_aux.
    range_stac.
  Qed.

  Lemma range_inb_nsz
    : IntRange.sint inb_nsz.
  Proof.
    r.
    pose proof range_inb_sz_precise.
    pose proof maxlen_byte_aux.
    range_stac.
  Qed.

  Lemma ptr_range_inb_sz
    : (0 <= inb_sz < Ptrofs.max_unsigned)%Z.
  Proof.
    pose proof range_inb_nsz.
    range_stac.
  Qed.

  Lemma ptr_range_mstore
    : (Z.of_nat (4 + inb_nsz + inb_nsz) <= Ptrofs.max_unsigned)%Z.
  Proof.
    pose proof range_inb_sz_precise.
    pose proof maxlen_byte_aux.
    assert (4 + Int.max_signed + Int.max_signed <
            Ptrofs.max_unsigned)%Z by ss.
    nia.
  Qed.

  (* Definition mentry_to_bytes (ment: bool * bytes): bytes := *)
  (*   let (rcv, cont) := ment in *)
  (*   let b_hd := if rcv then Byte.one else Byte.zero in *)
  (*   b_hd :: cont. *)

End INBOX.

Notation cglobvar := (globvar type).
Notation mentry_sz := (Z.of_nat mentry_nsz).
Notation mentry_esz := (Z.of_nat mentry_ensz).
Notation inb_sz := (Z.of_nat inb_nsz).


Class genv_props (ge: genv)
      (gvar_ilist: list (ident * cglobvar))
      (gfun_ilist: list (ident * fundef))
      (cenv_ilist: list (ident * composite))
  : Prop :=
  { in_gvar_ilist: forall i gv,
      In (i, gv) gvar_ilist -> exists b_gvar,
        <<GVAR_SYMB: Genv.find_symbol ge i = Some b_gvar>> /\
        <<GVAR_VINFO: Genv.find_var_info ge b_gvar = Some gv>> ;

    (* in_gvar_ids: forall i, *)
    (*   In i gvar_ids -> exists b_gvar, *)
    (*     Genv.find_symbol ge i = Some b_gvar; *)

    in_gfun_ilist: forall i fd,
        In (i, fd) gfun_ilist -> exists b_fdef,
          <<FDEF_SYMB: Genv.find_symbol ge i = Some b_fdef>> /\
          <<FDEF_FPTR: Genv.find_funct ge (Vptr b_fdef Ptrofs.zero) = Some fd>> ;

    in_cenv_ilist:
      forall i co, In (i, co) cenv_ilist ->
              (genv_cenv ge) ! i = Some co ;
  }.

Definition genv_props_incl (ge: genv)
           (gvs1 gvs2: list (ident * cglobvar))
           (gfs1 gfs2: list (ident * fundef))
           (cos1 cos2: list (ident * composite))
           (GENV_P: genv_props ge gvs2 gfs2 cos2)
           (INCL_GVS: List.incl gvs1 gvs2)
           (INCL_GFS: List.incl gfs1 gfs2)
           (INCL_COS: List.incl cos1 cos2)
  : genv_props ge gvs1 gfs1 cos1.
Proof.
  inv GENV_P.
  econs; eauto.
Qed.

Lemma in_gvar_ids ge gvs gfs ces
      `{genv_props ge gvs gfs ces}
      i
      (IN: In i (map fst gvs))
  : exists b_gvar,
    Genv.find_symbol ge i = Some b_gvar.
Proof.
  cut (exists gv, In (i, gv) gvs).
  { clear IN. i. des.
    hexploit in_gvar_ilist; eauto.
    i. des. eauto.
  }

  ss. eapply Coqlib.list_in_map_inv in IN.
  des.
  destruct x; subst. ss. eauto.
Qed.

Arguments in_gvar_ids {ge gvs gfs ces _} i.



(* tactics *)

Ltac red_idx idx' :=
  match goal with
  | |- paco3 (_sim_itree ?p) _ _ _ _ =>
    eapply (sim_itree_red_idx p) with (idx_small:= idx');
    [nia|]
  end.


Ltac fold_cenv :=
  match goal with
  | |- context[(prog_comp_env ?p)] =>
    change (prog_comp_env p) with
        (genv_cenv (globalenv p))
  end.

Ltac sIn :=
  s;
  match goal with
  | |- In _ _ => eauto
  | |- (_ = _ \/ _) =>
    try (left; eauto; fail);
    right; sIn
  | |- _ => ss; fail
  end.

Ltac solve_norepet :=
  match goal with
  | |- Coqlib.list_norepet ?l =>
    let x := eval simpl in (Coqlib.list_norepet_dec ident_eq l) in
        match x with
        | left ?P => exact P
        | _ => fail
        end
  end.

Ltac solve_disjoint :=
  try by (clear;
          r; s;
          let X := fresh "X" in
          let Y := fresh "Y" in
          intros ? ? X Y;
          des; subst; ss).

  (* match goal with *)
  (* | |- Coqlib.list_disjoint ?l1 ?l2 => *)
  (*   let x := eval simpl in (Coqlib.list_disjoint_dec ident_eq l1 l2) in *)
  (*       match x with *)
  (*       | left ?P => exact P *)
  (*       | _ => fail *)
  (*       end *)
  (* end. *)


Ltac eval_comput1 :=
  match goal with
  | |- eval_expr _ _ _ _ _ _ =>
    apply eval_expr_comput
  | |- eval_lvalue _ _ _ _ _ _ _ =>
    apply eval_lvalue_comput
  | |- eval_exprlist _ _ _ _ _ _ _ =>
    apply eval_exprlist_comput
  | |- assign_loc _ _ _ _ _ _ _ =>
    apply assign_loc_comput
  | |- Cop.sem_add _ _ _ _ _ _ = _ =>
    unfold Cop.sem_add
  | |- Cop.sem_cmp _ _ _ _ _ _  = _ =>
    unfold Cop.sem_cmp
  | |- Cop.sem_cast _ _ _ _ = _ =>
    unfold Cop.sem_cast
  | |- Cop.sem_binarith _ _ _ _ _ _ _ _ _ = _ =>
    unfold Cop.sem_binarith
  | |- context[ (?x ! ?id)] =>
    match type of x with
    | composite_env =>
      fold_cenv;
      erewrite (in_cenv_ilist id) by sIn
    | _ =>
      match goal with
      | H: ptree_equiv ?x _ |- _ => rewrite H
      end
    end
  end.

Ltac eval_comput := repeat (eval_comput1; cbn).


Ltac pre_start_func :=
  match goal with
  | H: genv_props ?ge _ _ _ |-
    context[ Callstate (Internal ?f) _ _ ?m0 ] =>
    assert (ALLOC_STACK: exists e m1 es blks_env,
               alloc_variables ge empty_env m0
                               (fn_vars f) e m1 /\
               env_equiv e es /\
               blocks_of_env ge e = blks_env)
  end.


Ltac start_func :=
  match goal with
  | H: genv_props ?ge _ _ _ |-
    paco3 _ _ _ _ (Callstate (Internal ?f) ?args ?k ?m) =>
    hexploit (clight_function_entry ge f args k m)
  end;
  [solve_norepet | solve_norepet | solve_norepet
   | solve_disjoint | eauto | ss | i; des ].

(* Omit 2nd stmt *)
Notation SeqAbbr s := (Ssequence s _).


Ltac simpl_idx :=
  repeat
    (first [rewrite <- Nat.sub_add_distr by nia |
            rewrite <- Nat.add_sub_assoc by nia]; ss).

Ltac fw :=
  eapply sim_itree_clight_silent;
  [nia| simpl in *; econs; simpl in *; eauto; try by econs |
   left; simpl_idx; simpl in *].

Ltac fw_tau idx :=
  eapply sim_itree_clight_silent_tau with (idx_n:=idx);
  [simpl in *; econs; simpl in *; eauto; try by econs | ss | left];
  simpl_idx; s.

Ltac fw_r :=
  eapply sim_itree_clight_silent;
  [nia| simpl in *; econs; simpl in *; eauto; try by econs |
   right; simpl_idx; simpl in *].

Ltac upd_lenv :=
  match goal with
  | H: lenv_equiv ?le_c _ |-
    context[State _ _ _ _ (PTree.set ?i ?v ?le_c) _] =>
    let le_p := fresh "le_p" in
    let LE := fresh "LE" in
    rename le_c into le_p;
    remember (PTree.set i v le_p) as le_c eqn: LE;
    eapply update_lenv_equiv in H;
    try (apply LE || reflexivity);
    clear dependent le_p;
    (* simpl in H *)
    cbn in H
  end.

Ltac unf_resum :=
  unfold resum, ReSum_id, id_, Id_IFun in *.

Ltac step_fptr_tac :=
  match goal with
  | |- context [Evar ?fid] =>
    hexploit (in_gfun_ilist fid); [sIn|]; [];
    intros (b_fdef & FDEF_SYMB & FDEF_FPTR); des;
    econs; [ss| eval_comput; try rewrite FDEF_SYMB; ss | eval_comput; ss | eauto | ss]
  end.


(**)

Section COMPOSITES.
  Context `{SystemEnv}.

  Program Definition co_pals_msg_t: composite :=
    {|
    co_su := Struct;
    co_members := [(_period_base_time, Tlong Unsigned {| attr_volatile := false; attr_alignas := None |});
                  (_sender, Tint I8 Signed {| attr_volatile := false; attr_alignas := None |});
                  (_content,
                   Tarray (Tint I8 Signed {| attr_volatile := false; attr_alignas := None |}) (Z.of_nat max_msg_size)
                          {| attr_volatile := false; attr_alignas := None |})];
    co_attr := {| attr_volatile := false; attr_alignas := None |};
    co_sizeof := Z.of_nat max_pld_size ; (* 16 *)
    co_alignof := 8;
    co_rank := 1;
    co_sizeof_pos := _ ;
    co_sizeof_alignof := _ ;
    |}.
  Next Obligation.
    unfold max_pld_size. nia.
  Qed.
  Next Obligation.
    exists 3%nat. ss.
  Qed.
  Next Obligation.
    unfold max_pld_size. unfold max_msg_size.
    replace (Z.of_nat (msg_size_k * 8 + 7 + 9)) with
        (Z.of_nat msg_size_k * 8 + 16)%Z by nia.
    solve_divide.
  Qed.

  Program Definition co_inbox_t: composite :=
    {|
    co_su := Struct;
    co_members := [(_entry,
                    Tarray (Tstruct _msg_entry_t {| attr_volatile := false; attr_alignas := None |})
                           (Z.of_nat max_num_tasks)
                           {| attr_volatile := false; attr_alignas := None |})];
    co_attr := {| attr_volatile := false; attr_alignas := None |};
    co_sizeof := Z.of_nat inb_nsz;
    co_alignof := 1;
    co_rank := 3;
    co_sizeof_pos := _ ;
    co_alignof_two_p := _;
    |}.
  Next Obligation.
    pose proof range_inb_sz_precise. nia.
  Qed.
  Next Obligation.
    exists O. ss.
  Qed.
  Next Obligation.
    solve_divide.
  Qed.

  Program Definition co_msg_entry_t: composite :=
    {|
    co_su := Struct;
    co_members := [(_received, Tint I8 Signed {| attr_volatile := false; attr_alignas := None |});
                  (_content,
                   Tarray (Tint I8 Signed {| attr_volatile := false; attr_alignas := None |})
                          (Z.of_nat max_msg_size)
                          {| attr_volatile := false; attr_alignas := None |})];
    co_attr := {| attr_volatile := false; attr_alignas := None |};
    co_sizeof := Z.of_nat mentry_nsz;
    co_alignof := 1;
    co_rank := 1;
    co_sizeof_pos := _ ;
    co_alignof_two_p := _ ;
    |}.
  Next Obligation.
    unfold mentry_nsz. nia.
  Qed.
  Next Obligation.
    exists O. ss.
  Qed.
  Next Obligation.
    solve_divide.
  Qed.

  Program Definition co_msg_store_t: composite :=
    {|
    co_su := Struct;
    co_members := [(_cur_idx, Tint I32 Signed {| attr_volatile := false; attr_alignas := None |});
                  (_inbox,
                   Tarray (Tstruct _inbox_t {| attr_volatile := false; attr_alignas := None |}) 2
                          {| attr_volatile := false; attr_alignas := None |})];
    co_attr := {| attr_volatile := false; attr_alignas := None |};
    co_sizeof := 4 + 2 * (Z.of_nat inb_nsz);
    co_alignof := 4;
    co_rank := 5;
    co_sizeof_pos := _ ;
    co_alignof_two_p := _ ;
    co_sizeof_alignof := _ ;
    |}.
  Next Obligation.
    nia.
  Qed.
  Next Obligation.
    exists 2%nat; ss.
  Qed.
  Next Obligation.
    unfold inb_nsz.
    rewrite Nat2Z.inj_mul.
    rewrite mentry_sz_eq.
    unfold msg_entry_sz.
    solve_divide.
  Qed.

End COMPOSITES.


Definition main_const_ids: list ident :=
  [_TASK_ID; _PALS_PERIOD; _MAX_CSKEW; _MAX_NWDELAY;
  _NUM_TASKS; _NUM_MCASTS; _MSG_SIZE;
  _PORT; _IP_ADDR; _MCAST_MEMBER].

Definition main_gvar_ids: list ident :=
  [_TASK_ID; _PALS_PERIOD; _MAX_CSKEW; _MAX_NWDELAY;
  _NUM_TASKS; _NUM_MCASTS; _MSG_SIZE;
  _PORT; _IP_ADDR; _MCAST_MEMBER;
  _send_buf; _mstore; _send_hist; _txs; _rxs].

Definition main_gfun_ids: list ident :=
  [ _get_cur_inbox; _get_nxt_inbox; _msg_copy; _check_send_hist;
  _reset_send_hist; _pals_send; _get_base_time; _mcast_join;
  _insert_msg; _fetch_msgs; _init_inbox; _switch_inbox;
  _run_task; _main;
  _pals_current_time; _pals_init_timer;  _pals_wait_timer;
  _pals_socket;  _pals_bind;  _pals_mcast_join;  _pals_sendto;
  _pals_recvfrom].

Definition main_cenv_ids: list ident :=
  [_pals_msg_t; _msg_entry_t; _inbox_t; _msg_store_t].

Definition app_unch_gvar_ids: list ident :=
  [_TASK_ID; _PALS_PERIOD; _MAX_CSKEW; _MAX_NWDELAY;
  _NUM_TASKS; _NUM_MCASTS; _MSG_SIZE;
  _PORT; _IP_ADDR; _MCAST_MEMBER;
  _mstore; _txs; _rxs].


Definition v_TASK_ID_p (tid_z: Z) :=
  {| gvar_info := tschar;
     gvar_init := [Init_int8 (Int.repr tid_z)];
     gvar_readonly := true;
     gvar_volatile := false |}.

Definition main_gvar_ilist `{SystemEnv} (tid: nat)
  : list (ident * cglobvar) :=
  [(_TASK_ID, v_TASK_ID_p (Z.of_nat tid));
  (_PALS_PERIOD, config_prm.v_PALS_PERIOD (Z.of_nat period));
  (_MAX_CSKEW, config_prm.v_MAX_CSKEW (Z.of_nat max_clock_skew));
  (_MAX_NWDELAY, config_prm.v_MAX_NWDELAY (Z.of_nat max_nw_delay));
  (_NUM_TASKS, config_prm.v_NUM_TASKS (Z.of_nat num_tasks));
  (_NUM_MCASTS, config_prm.v_NUM_MCASTS (Z.of_nat num_mcasts));
  (_MSG_SIZE, config_prm.v_MSG_SIZE (Z.of_nat msg_size));

  (_PORT, config_prm.v_PORT (Z.of_nat port));
  (_IP_ADDR, config_prm.v_IP_ADDR
               (Z.of_nat max_num_tasks)
               (Z.of_nat max_num_mcasts)
               (task_ips_brep ++ map fst mcasts)) ;
  (_MCAST_MEMBER, config_prm.v_MCAST_MEMBER
                    (Z.of_nat max_num_tasks)
                    (Z.of_nat max_num_mcasts)
                    mcast_memflags) ;

  (_send_buf, main_prm.v_send_buf (Z.of_nat msg_size_k));
  (_mstore, main_prm.v_mstore (Z.of_nat msg_size_k)
                              (Z.of_nat max_num_tasks));
  (_send_hist, main_prm.v_send_hist (Z.of_nat max_num_tasks));
  (_txs, main_prm.v_txs);
  (_rxs, main_prm.v_rxs)].

Definition main_cenv_ilist `{SystemEnv}
  : list (ident * composite) :=
  [(_pals_msg_t, co_pals_msg_t);
  (_msg_entry_t, co_msg_entry_t);
  (_inbox_t, co_inbox_t);
  (_msg_store_t, co_msg_store_t)].

Definition main_gfun_ilist `{SystemEnv}
  : list (ident * fundef) :=
  [ (_get_cur_inbox, Internal f_get_cur_inbox);
  (_get_nxt_inbox, Internal f_get_nxt_inbox);
  (_msg_copy, Internal f_msg_copy);
  (_check_send_hist, Internal (f_check_send_hist
                                 (Z.of_nat max_num_tasks)
                                 (Z.of_nat max_num_mcasts)));
  (_reset_send_hist, Internal (f_reset_send_hist (Z.of_nat max_num_tasks)));
  (_pals_send, Internal (f_pals_send (Z.of_nat msg_size_k)
                                     (Z.of_nat max_num_tasks)
                                     (Z.of_nat max_num_mcasts)));
  (_get_base_time, Internal f_get_base_time);
  (_mcast_join, Internal (f_mcast_join (Z.of_nat max_num_tasks)
                                       (Z.of_nat max_num_mcasts)));
  (_insert_msg, Internal (f_insert_msg (Z.of_nat msg_size_k)));
  (_fetch_msgs, Internal (f_fetch_msgs (Z.of_nat msg_size_k)
                                       (Z.of_nat max_num_tasks)));
  (_init_inbox, Internal (f_init_inbox (Z.of_nat max_num_tasks)));
  (_switch_inbox, Internal f_switch_inbox);
  (_run_task, Internal f_run_task);
  (_main, Internal f_main);

  (_pals_current_time,
   External get_time_ef Tnil tulong cc_default);
  (_pals_init_timer,
   External init_timer_ef Tnil tint cc_default);
  (_pals_wait_timer, External wait_timer_ef
    (Tcons tulong Tnil) tint cc_default);
  (_pals_socket, External open_socket_ef Tnil tint cc_default);
  (_pals_bind, External bind_socket_ef
    (Tcons tint (Tcons tint Tnil)) tint cc_default);
  (_pals_mcast_join, External join_socket_ef
    (Tcons tint (Tcons (tptr tschar) Tnil)) tvoid cc_default);

  (_pals_sendto,
   External sendto_ef
            (Tcons tint
                   (Tcons (tptr tschar)
                          (Tcons tint (Tcons (tptr tschar) (Tcons tint Tnil))))) tint cc_default);
  (_pals_recvfrom,
   External recvfrom_ef
            (Tcons tint (Tcons (tptr tschar) (Tcons tint Tnil))) tint cc_default)
].


Definition bool2memval (b: bool): memval :=
  Byte (if b then Byte.one else Byte.zero).


Section MATCH_MEM.
  Local Open Scope Z.

  Variable ge: genv.
  Variable tid: nat.
  Context `{SystemEnv}.
  (* Context `{ genv_props *)
  (*              ge (main_gvar_ilist tid) *)
  (*              main_gfun_ilist main_cenv_ilist }. *)

  Record mem_consts (m: mem) (tid: nat): Prop :=
    MemConsts {
        mem_consts_task_id:
          forall b_tid
            (FIND_SYMB: Genv.find_symbol
                          ge _TASK_ID = Some b_tid),
            Mem.load Mint8signed m b_tid 0%Z =
            Some (Vint (IntNat.of_nat tid)) ;

        mem_consts_pals_period:
          forall b_pprd
            (FIND_SYMB: Genv.find_symbol
                          ge _PALS_PERIOD = Some b_pprd),
          Mem.load Mint64 m b_pprd 0%Z =
          Some (Vlong (IntNat.of_nat64 period)) ;

        mem_consts_max_cskew:
          forall b_sk
            (FIND_SYMB: Genv.find_symbol
                          ge _MAX_CSKEW = Some b_sk),
            Mem.load Mint64 m b_sk 0%Z =
            Some (Vlong (IntNat.of_nat64 max_clock_skew)) ;

        mem_consts_max_nwdelay:
          forall b_nd
            (FIND_SYMB: Genv.find_symbol
                          ge _MAX_NWDELAY = Some b_nd),
            Mem.load Mint64 m b_nd 0%Z =
            Some (Vlong (IntNat.of_nat64 max_nw_delay)) ;


        mem_consts_num_tasks:
          forall b_nt
            (FIND_SYMB: Genv.find_symbol
                          ge _NUM_TASKS = Some b_nt),
            Mem.load Mint32 m b_nt 0%Z =
            Some (Vint (IntNat.of_nat num_tasks)) ;

        mem_consts_num_mcasts:
          forall b_nmc
            (FIND_SYMB: Genv.find_symbol
                          ge _NUM_MCASTS = Some b_nmc),
            Mem.load Mint32 m b_nmc 0%Z =
            Some (Vint (IntNat.of_nat num_mcasts)) ;

        mem_consts_msg_size:
          forall b_msz
            (FIND_SYMB: Genv.find_symbol
                          ge _MSG_SIZE = Some b_msz),
            Mem.load Mint32 m b_msz 0%Z =
            Some (Vint (IntNat.of_nat msg_size)) ;

        mem_consts_port:
          forall b_pn
            (FIND_SYMB: Genv.find_symbol
                          ge _PORT = Some b_pn),
            Mem.load Mint32 m b_pn 0%Z =
            Some (Vint (IntNat.of_nat port)) ;

        mem_consts_ip_addr:
          forall b_ip_addr
            (FIND_SYMB: Genv.find_symbol
                          ge _IP_ADDR = Some b_ip_addr),

            iForall (fun n ip_bs =>
                       Mem.loadbytes
                         m b_ip_addr (Z.of_nat (n * 16))
                         (Zlength ip_bs + 1) =
                       Some (inj_bytes (snoc ip_bs Byte.zero)))
                    0 (task_ips_brep ++ (map fst mcasts)) ;

        mem_consts_mcast_member:
          forall b_mcm mid midx tid'
            mip_bs mem
            (FIND_SYMB: Genv.find_symbol
                          ge _MCAST_MEMBER = Some b_mcm)
            (MCAST_ID: mid = (num_tasks + midx)%nat)
            (MCASTS_MID: nth_error mcasts midx = Some (mip_bs, mem))
            (RANGE_TID: (tid' < num_tasks)%nat)
          ,
            Mem.load Mint8signed m b_mcm
                     (Z.of_nat (max_num_tasks * midx + tid')) =
            Some (Vint (if existsb (Nat.eqb tid') mem
                        then Int.one else Int.zero)) ;
      }.

  Lemma mem_consts_unch
        m m'
        (MEM_CONSTS: mem_consts m tid)
        (UNCH: Mem.unchanged_on
                 (blocks_of ge main_const_ids) m m')
    : mem_consts m' tid.
  Proof.
    inv MEM_CONSTS.
    econs.
    - i. hexploit mem_consts_task_id0; eauto.
      intro LOAD.
      eapply Mem.load_unchanged_on; eauto.
      i. ss.
      r. esplits; eauto. sIn.
    - i. hexploit mem_consts_pals_period0; eauto.
      intro LOAD.
      eapply Mem.load_unchanged_on; eauto.
      i. ss.
      r. esplits; eauto. sIn.
    - i. hexploit mem_consts_max_cskew0; eauto.
      intro LOAD.
      eapply Mem.load_unchanged_on; eauto.
      i. ss.
      r. esplits; eauto. sIn.
    - i. hexploit mem_consts_max_nwdelay0; eauto.
      intro LOAD.
      eapply Mem.load_unchanged_on; eauto.
      i. ss.
      r. esplits; eauto. sIn.
    - i. hexploit mem_consts_num_tasks0; eauto.
      intro LOAD.
      eapply Mem.load_unchanged_on; eauto.
      i. ss.
      r. esplits; eauto. sIn.
    - i. hexploit mem_consts_num_mcasts0; eauto.
      intro LOAD.
      eapply Mem.load_unchanged_on; eauto.
      i. ss.
      r. esplits; eauto. sIn.
    - i. hexploit mem_consts_msg_size0; eauto.
      intro LOAD.
      eapply Mem.load_unchanged_on; eauto.
      i. ss.
      r. esplits; eauto. sIn.
    - i. hexploit mem_consts_port0; eauto.
      intro LOAD.
      eapply Mem.load_unchanged_on; eauto.
      i. ss.
      r. esplits; eauto. sIn.
    - i. hexploit mem_consts_ip_addr0; eauto.
      intro LOAD_FA.
      eapply iForall_nth. i.
      rewrite iForall_nth in LOAD_FA.
      specialize (LOAD_FA n).

      fold bytes in *.
      destruct (nth_error (task_ips_brep ++ map fst mcasts) n); ss.
      eapply Mem.loadbytes_unchanged_on; eauto.
      i. ss.
      r. esplits; eauto. sIn.
    - i. hexploit mem_consts_mcast_member0; eauto.
      intro LOAD.
      eapply Mem.load_unchanged_on; eauto.
      i. ss.
      r. esplits; eauto. sIn.
  Qed.

  Lemma mem_consts_unch_diffblk
        m m' b_ch
        (MEM_CONSTS: mem_consts m tid)
        (MEM_CHB: mem_changed_block b_ch m m')
        (BLK_NOT_CONSTS: forall id,
            In id main_const_ids ->
            Genv.find_symbol ge id <> Some b_ch)
    : mem_consts m' tid.
  Proof.
    eapply mem_consts_unch; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    unfold blocks_of.
    ii. subst. des.
    hexploit BLK_NOT_CONSTS; eauto.
  Qed.

  Let fsymb (id: ident) (bpred: block -> Prop): Prop :=
    forall b (FIND_SYMB: Genv.find_symbol ge id = Some b),
      bpred b.

  Record mem_sbuf_blk (m: mem) (nsytm: nat) (tid: nat) (mcont: bytes)
         (b_sbuf: block): Prop :=
    MemSBuf {
        mem_sbuf_next_sync_time:
            Mem.loadbytes m b_sbuf 0 8 =
            Some (inj_bytes (IntByte.to_bytes64 (IntNat.of_nat64 nsytm))) ;

        mem_sbuf_task_id:
          Mem.load Mint8signed m b_sbuf 8 =
          Some (Vint (IntNat.of_nat tid)) ;

        mem_sbuf_content:
          Mem.loadbytes m b_sbuf 9 (Z.of_nat msg_size) =
          Some (inj_bytes mcont) ;

        mem_sbuf_writable:
          Mem.range_perm m b_sbuf 0 (Z.of_nat pld_size)
                         Cur Writable;
      }.

  Lemma mem_sbuf_next_sync_time'
        (m: mem) (nsytm: nat) (tid': nat) (mcont: bytes)
        (b_sbuf: block)
        (MEM_SBUF_BLK: mem_sbuf_blk m nsytm tid' mcont b_sbuf)
    : Mem.load Mint64 m b_sbuf 0 =
      Some (Vlong (IntNat.of_nat64 nsytm)).
  Proof.
    erewrite Mem.loadbytes_load;
      try (eapply mem_sbuf_next_sync_time; eauto).
    2: { solve_divide. }
    f_equal.
    unfold decode_val.
    rewrite proj_inj_bytes. f_equal.

    unfold IntByte.to_bytes64.
    rewrite decode_encode_int_8. ss.
  Qed.

  Definition mem_sbuf (m: mem)
             (nsytm: nat) (tid: nat) (mcont: bytes): Prop :=
    fsymb _send_buf (mem_sbuf_blk m nsytm tid mcont).

  Lemma mem_sbuf_unch
        m m' nsytm mcont
        (MEM_SBUF: mem_sbuf m nsytm tid mcont)
        (UNCH: Mem.unchanged_on
                 (fun b _ => Genv.find_symbol ge _send_buf = Some b)
                 m m')
    : mem_sbuf m' nsytm tid mcont.
  Proof.
    ii. rr in MEM_SBUF.
    hexploit MEM_SBUF; eauto. intro MEM_SBUF_BLK.
    clear MEM_SBUF.

    inv MEM_SBUF_BLK.
    econs.
    - eapply Mem.loadbytes_unchanged_on; eauto.
    - eapply Mem.load_unchanged_on; eauto.
    - eapply Mem.loadbytes_unchanged_on; eauto.
    - ii. eapply Mem.perm_unchanged_on; eauto.
  Qed.

  Lemma mem_sbuf_unch_diffblk
        b_ch m m' nsytm mcont
        (MEM_SBUF: mem_sbuf m nsytm tid mcont)
        (MEM_CHB: mem_changed_block b_ch m m')
        (CHB_NOT_SBUF: Genv.find_symbol ge _send_buf <> Some b_ch)
    : mem_sbuf m' nsytm tid mcont.
  Proof.
    eapply mem_sbuf_unch; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    unfold blocks_of.
    ii. subst. eauto.
  Qed.

  Definition Mem_msg_entry (mem: Mem.mem)
             (b: block) (ofs: Z)
             (idx: nat) (ment: bytes?): Prop :=
    match ment with
    | None =>
      Mem.loadbytes mem b (ofs + Z.of_nat (mentry_nsz * idx)) 1 =
      Some ([Byte Byte.zero])
    | Some cont =>
      Mem.loadbytes mem b (ofs + Z.of_nat (mentry_nsz * idx)) mentry_esz =
      Some (inj_bytes (Byte.one :: cont))
    end.

  Definition Mem_inbox (mem: Mem.mem)
             (b: block) (ofs: Z)
             (ments: list (bytes?)): Prop :=
    <<MSG_ENTRIES: iForall (Mem_msg_entry mem b ofs) 0 ments>> /\
    <<NUM_ENTRIES: length ments = num_tasks>> /\
                 (* ments (incr_nlist 0 num_tasks) /\ *)
    <<INBOX_PERM: Mem.range_perm mem b ofs (ofs + inb_sz)
                                 Cur Writable>>.
  (* (align_chunk Mint8signed | ofs)%Z. *)

  Record mem_mstore_blk
         (m: mem) (cflg: bool)
         (ofsc ofsn: Z)
         (inbc inbn: list (bytes?))
         (b_mst: block): Prop :=
    MemMStore {
        mem_mst_curflag:
          Mem.load Mint32 m b_mst 0 =
          Some (Vint (if cflg then Int.one else Int.zero)) ;

        mem_mst_curflag_writable:
          Mem.range_perm m b_mst 0 4 Cur Writable;

        mst_match_ofs_cur:
          ofsc = if cflg then 4 + inb_sz else 4 ;
        mst_match_ofs_nxt:
          ofsn = if cflg then 4 else (4 + inb_sz)%Z ;

        mem_mst_inbox_cur: Mem_inbox m b_mst ofsc inbc ;
        mem_mst_inbox_nxt: Mem_inbox m b_mst ofsn inbn ;
      }.


  Lemma Mem_msg_entry_unch
        m m' b ofs ment (i: nat)
        (MEM_MENT: Mem_msg_entry m b ofs i ment)
        (MEM_UNCH: Mem.unchanged_on
                     (fun b' ofs' =>
                        b' = b /\
                        (ofs + Z.of_nat (mentry_nsz * i) <= ofs' <
                         ofs + Z.of_nat (mentry_nsz * i + mentry_nsz))%Z)
                     m m')
    : Mem_msg_entry m' b ofs i ment.
  Proof.
    rr in MEM_MENT. rr.
    destruct ment.
    - eapply Mem.loadbytes_unchanged_on; try apply MEM_MENT.
      { eauto. }
      i. ss.
      split; ss.
      pose proof range_mentry_ensz.
      nia.
    - eapply Mem.loadbytes_unchanged_on; try apply MEM_MENT.
      { eauto. }
      i. ss.
      split; ss.
      cut (1 <= mentry_nsz)%nat.
      { nia. }
      unfold mentry_nsz. nia.
  Qed.

  Lemma iForall_Mem_msg_entry_unch
        m m' b ofs ments (i j: nat)
        (MEM_MENT: iForall (Mem_msg_entry m b ofs) i ments)
        (LEN_MENTS: j = length ments)
        (MEM_UNCH: Mem.unchanged_on
                     (fun b' ofs' =>
                        b' = b /\
                        (ofs + Z.of_nat (mentry_nsz * i) <= ofs' <
                         ofs + Z.of_nat (mentry_nsz * (i + j)))%Z)
                     m m')
    : iForall (Mem_msg_entry m' b ofs) i ments.
  Proof.
    subst j.
    induction MEM_MENT; ss.
    { econs. }

    econs.
    { eapply Mem_msg_entry_unch; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      clear. intros b' ofs' [? OFS]. clarify.
      unfold mentry_nsz in *. nia.
    }

    apply IHMEM_MENT.
    eapply Mem.unchanged_on_implies; eauto.
    clear. intros b' ofs' [? OFS]. clarify.
    split; ss.
    nia.
  Qed.

  Lemma Mem_inbox_unch
        m m' b ofs inb
        (MEM_INB: Mem_inbox m b ofs inb)
        (MEM_UNCH: Mem.unchanged_on
                     (fun b' ofs' =>
                        b' = b /\
                        (ofs <= ofs' < ofs + inb_sz)%Z)
                     m m')
    : Mem_inbox m' b ofs inb.
  Proof.
    r. r in MEM_INB. des.
    esplits; ss.
    - eapply iForall_Mem_msg_entry_unch; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      (* rewrite mentry_sz_eq. *)
      rewrite NUM_ENTRIES. ss.
      ii. des. subst.
      split; ss.

      pose proof range_mentry_sz_precise.
      assert (0 < num_tasks)%nat by nia.

      assert (exists x, num_tasks = S x).
      { destruct num_tasks; ss.
        - nia.
        - esplits; eauto. }
      des.

      hexploit (within_inb_nsz2 x mentry_nsz).
      { nia. }
      { nia. }
      unfold inb_nsz.
      nia.
    - ii. eapply Mem.perm_unchanged_on; eauto.
      ss.
  Qed.

  Definition mem_mstore m cflg ofsc ofsn inbc inbn :=
    fsymb _mstore (mem_mstore_blk m cflg ofsc ofsn inbc inbn).

  Lemma mem_mstore_unch
        m m' cf
        ofsc ofsn inbc inbn
        (MEM_MSTORE: mem_mstore m cf ofsc ofsn inbc inbn)
        (UNCH: Mem.unchanged_on
                 (fun b _ => Genv.find_symbol ge _mstore = Some b)
                 m m')
    : mem_mstore m' cf ofsc ofsn inbc inbn.
  Proof.
    ii. rr in MEM_MSTORE.
    hexploit MEM_MSTORE; eauto. intro MEM_MSTORE_BLK.
    clear MEM_MSTORE.

    inv MEM_MSTORE_BLK.
    econs.
    - eapply Mem.load_unchanged_on; eauto.
    - ii. eapply Mem.perm_unchanged_on; eauto.
    - ss.
    - ss.
    - eapply Mem_inbox_unch; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      ii. ss. des. subst. ss.
    - eapply Mem_inbox_unch; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      ii. ss. des. subst. ss.
  Qed.

  Lemma mem_mstore_unch_diffblk
        b_ch m m' cf
        ofsc ofsn inbc inbn
        (MEM_SBUF: mem_mstore m cf ofsc ofsn inbc inbn)
        (MEM_CHB: mem_changed_block b_ch m m')
        (CHB_NOT_MST: Genv.find_symbol ge _mstore <> Some b_ch)
    : mem_mstore m' cf ofsc ofsn inbc inbn.
  Proof.
    eapply mem_mstore_unch; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    unfold blocks_of.
    ii. subst. eauto.
  Qed.


  Record mem_sh_blk (m: mem) (sh: list bool) (b_sh: block): Prop :=
    MemSendHist {
        (* mem_sh_length: length sh = num_tasks ; *)
        mem_sh_loadbytes:
          Mem.loadbytes m b_sh 0 (Z.of_nat num_tasks) =
          Some (map bool2memval sh);

        mem_sh_writable:
          Mem.range_perm m b_sh 0 (Z.of_nat num_tasks) Cur Writable ;
      }.

  Lemma mem_sh_blk_length
        m sh b
        (MEM_SH_BLK: mem_sh_blk m sh b)
    : length sh = num_tasks.
  Proof.
    inv MEM_SH_BLK.
    hexploit Mem.loadbytes_length; eauto.
    rewrite map_length. rewrite Nat2Z.id. ss.
  Qed.

  Definition mem_sh m (sh: list bool): Prop :=
    fsymb _send_hist (mem_sh_blk m sh).

  Lemma mem_sh_unch
        m m' sh
        (MEM_SH: mem_sh m sh)
        (UNCH: Mem.unchanged_on
                 (fun b _ => Genv.find_symbol ge _send_hist = Some b)
                 m m')
    : mem_sh m' sh.
  Proof.
    ii. rr in MEM_SH.
    hexploit MEM_SH; eauto. intro MEM_SH_BLK.
    clear MEM_SH.

    inv MEM_SH_BLK.
    econs.
    - eapply Mem.loadbytes_unchanged_on; eauto.
    - ii. eapply Mem.perm_unchanged_on; eauto.
  Qed.

  Lemma mem_sh_unch_diffblk
        b_sh m m' sh
        (MEM_SH: mem_sh m sh)
        (MEM_CHB: mem_changed_block b_sh m m')
        (CHB_DIFF: Genv.find_symbol ge _send_hist <> Some b_sh)
    : mem_sh m' sh.
  Proof.
    eapply mem_sh_unch; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    unfold blocks_of.
    ii. subst. eauto.
  Qed.


  Record mem_skt_blk (m: mem) (sid: nat) (b_sid: block): Prop :=
    MemSocket {
        mem_skt_id:
          Mem.load Mint32 m b_sid 0 =
          Some (Vint (IntNat.of_nat sid));
        mem_skt_writable:
          Mem.range_perm m b_sid 0 4 Cur Writable ;
      }.

  Definition mem_txs m txs :=
    fsymb _txs (mem_skt_blk m txs).

  Definition mem_rxs m rxs :=
    fsymb _rxs (mem_skt_blk m rxs).

  Lemma mem_txs_unch
        m m' txs
        (MEM_SKT: mem_txs m txs)
        (UNCH: Mem.unchanged_on
                 (fun b _ => Genv.find_symbol ge _txs = Some b)
                 m m')
    : mem_txs m' txs.
  Proof.
    ii. rr in MEM_SKT.
    hexploit MEM_SKT; eauto.
    clear MEM_SKT. intro MEM_SKT_BLK.
    inv MEM_SKT_BLK.
    econs.
    - eapply Mem.load_unchanged_on; eauto.
    - ii. eapply Mem.perm_unchanged_on; eauto.
  Qed.

  Lemma mem_txs_unch_diffblk
        b_ch m m' txs
        (MEM_SBUF: mem_txs m txs)
        (MEM_CHB: mem_changed_block b_ch m m')
        (CHB_NOT_MST: Genv.find_symbol ge _txs <> Some b_ch)
    : mem_txs m' txs.
  Proof.
    eapply mem_txs_unch; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    unfold blocks_of.
    ii. subst. eauto.
  Qed.

  Lemma mem_rxs_unch
        m m' rxs
        (MEM_SKT: mem_rxs m rxs)
        (UNCH: Mem.unchanged_on
                 (fun b _ => Genv.find_symbol ge _rxs = Some b)
                 m m')
    : mem_rxs m' rxs.
  Proof.
    ii. rr in MEM_SKT.
    hexploit MEM_SKT; eauto.
    clear MEM_SKT. intro MEM_SKT_BLK.
    inv MEM_SKT_BLK.
    econs.
    - eapply Mem.load_unchanged_on; eauto.
    - ii. eapply Mem.perm_unchanged_on; eauto.
  Qed.

  Lemma mem_rxs_unch_diffblk
        b_ch m m' rxs
        (MEM_SBUF: mem_rxs m rxs)
        (MEM_CHB: mem_changed_block b_ch m m')
        (CHB_NOT_MST: Genv.find_symbol ge _rxs <> Some b_ch)
    : mem_rxs m' rxs.
  Proof.
    eapply mem_rxs_unch; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    unfold blocks_of.
    ii. subst. eauto.
  Qed.

End MATCH_MEM.



Lemma mem_sbuf_loadbytes `{SystemEnv}
      m sytm tid mcont b_sbuf
      (RANGE_SYTM: IntRange.uint64 sytm)
      (RANGE_TID: (tid < num_tasks)%nat)
      (MEM_SBUF: mem_sbuf_blk m sytm tid mcont b_sbuf)
  :
    Mem.loadbytes m b_sbuf 0%Z (Z.of_nat pld_size) =
    Some (inj_bytes (IntByte.to_bytes64
                       (IntNat.of_nat64 sytm) ++
                       [Byte.repr (Z.of_nat tid)] ++ mcont)).
Proof.
  replace (Z.of_nat pld_size) with
      (8 + (1 + Z.of_nat msg_size)).
  2: { unfold pld_size. nia. }

  erewrite Mem.loadbytes_concat; try nia.
  { unfold inj_bytes.
    rewrite map_app. reflexivity. }
  { eapply mem_sbuf_next_sync_time; eauto. }
  s.
  erewrite Mem.loadbytes_concat; try nia.
  { rewrite rw_cons_app. reflexivity. }
  { hexploit Mem.load_loadbytes.
    { eapply mem_sbuf_task_id; eauto. }
    i. des.
    ss.
    hexploit Mem.loadbytes_length; eauto. i.
    destruct bytes as [| b []]; ss.
    destruct b; ss.
    hexploit (decode_byte_one_inv (Z.of_nat tid)); eauto.
    { split.
      - transitivity 0.
        { eapply Z.lt_le_incl. ss. }
        nia.
      - cut (Z.of_nat num_tasks < Int.max_signed)%Z.
        { nia. }
        generalize range_num_tasks.
        inversion 1.
        assert (Byte.max_signed < Int.max_signed)%Z by ss.
        nia.
    }
    i. subst.
    ss.
  }
  apply MEM_SBUF.
Qed.

Lemma ip_in_mem_exists `{SystemEnv}
      ge tid tid_r b_ips m
      (MEM_CONSTS: mem_consts ge m tid)
      (FSYMB_IPS: Genv.find_symbol ge _IP_ADDR =
                  Some b_ips)
      (TID: (tid_r < num_tasks + num_mcasts)%nat)
  : exists ip_dest,
    ip_in_mem ip_dest m b_ips
              (Ptrofs.repr (16 * Z.of_nat tid_r)) /\
    dest_id_ip tid_r ip_dest /\
    IntRange.uint ip_dest.
Proof.
  hexploit mem_consts_ip_addr; eauto.
  intro IPS.
  rewrite iForall_nth in IPS.
  specialize (IPS tid_r).

  assert (LEN_TIPS: length task_ips_brep = length task_ips).
  { pose proof task_ips_convert_brep as CONV_TASK_IPS.
    apply Forall2_length in CONV_TASK_IPS. ss. }


  hexploit (nth_error_Some2 _ (task_ips_brep ++ map fst mcasts) tid_r).
  { rewrite app_length.
    rewrite map_length.
    rewrite <- num_mcasts_eq.
    fold bytes in *.
    rewrite LEN_TIPS.
    fold num_tasks. ss.
  }
  i. des.
  renames e1 NTH_EX into ip_bs IP_BS.
  rewrite IP_BS in IPS. ss.

  assert (exists ip,
             <<CONV_IP: IP.convert_brep ip_bs = Some ip>> /\
             <<DEST_ID_IP: dest_id_ip tid_r ip>>).
  { destruct (lt_ge_dec tid_r (length task_ips_brep)) as [LT|GE].
    - rewrite nth_error_app1 in IP_BS by ss.
      pose proof task_ips_convert_brep as CONV_IPS.
      eapply Forall2_nth1 in CONV_IPS; eauto.
      des.
      esplits; eauto.
      r. unfold dest_ips.
      rewrite nth_error_app1 by nia.
      ss.

    - rewrite nth_error_app2 in IP_BS by ss.
      pose proof mcast_ips_convert_brep as CONV_IPS.
      (* hexploit Forall2_length; eauto. i. *)

      apply map_nth_error_iff in IP_BS. des.
      destruct a as (ip_bs' & mbrs). ss. clarify.

      eapply Forall2_nth1 in CONV_IPS; eauto.
      des.
      esplits; eauto.
      r. unfold dest_ips.
      rewrite nth_error_app2 by nia.
      rewrite <- LEN_TIPS. ss.
  }
  des.

  hexploit IP.valid_ip_brep_spec; eauto.
  intros (BS_NONZERO & IP_BS_LEN & IP_SINT).

  exists ip.
  splits; ss.
  2: { range_stac. }

  econs; eauto.
  rewrite Ptrofs.unsigned_repr.
  2: { split; [nia|].
       cut (Z.of_nat tid_r <= Byte.max_signed)%Z.
       { intro TID_R.
         transitivity (16 * Byte.max_signed).
         { nia. }
         eapply Z.lt_le_incl. ss.
       }
       pose proof range_valid_dest_ids as RANGE_D.
       fold num_tasks num_mcasts in *.
       range_stac.
  }
  replace (16 * Z.of_nat tid_r) with (Z.of_nat (tid_r * 16)) by nia.
  rewrite IPS.
  unfold snoc.
  unfold inj_bytes. rewrite map_app. ss.
Qed.


Lemma Mem_msg_entry_inv2 `{SystemEnv}
      m b ofs_inb idx ment
      (MEM_MENT: Mem_msg_entry m b ofs_inb idx ment)
  : <<MENT_RCV: Mem.load Mint8signed m b (ofs_inb + Z.of_nat (mentry_nsz * idx)) =
                Some (if ment then Vtrue else Vfalse)>> /\
                <<MENT_CONT: forall mcont, ment = Some mcont ->
                                      Mem.loadbytes m b (ofs_inb + Z.of_nat (mentry_nsz * idx) + 1) (Z.of_nat msg_size) =
                                      Some (inj_bytes mcont)>>.
Proof.
  r in MEM_MENT. ss.
  destruct ment as [mcont|]; ss.
  - unfold mentry_ensz in MEM_MENT.
    replace (Z.of_nat (msg_size + 1))%nat with
        (1 + Z.of_nat msg_size)%Z in MEM_MENT by nia.
    rewrite rw_cons_app in MEM_MENT.
    apply Mem.loadbytes_split in MEM_MENT; [|nia..].
    destruct MEM_MENT as (mvs1 & mvs2 & LBS_HB1 & LBS_HB2 & BS_EQ).
    hexploit Mem.loadbytes_length; try apply LBS_HB1.
    intro LEN_MVS1.
    destruct mvs1 as [| rcv_hb []]; ss.
    clarify.
    split; ss.
    + r.
      erewrite Mem.loadbytes_load; cycle 1.
      { apply LBS_HB1. }
      { ss. solve_divide. }
      ss.
    + r. intros mcont' AUX.
      symmetry in AUX. inv AUX.
      ss.
  - split; ss.
    r.
    erewrite Mem.loadbytes_load; cycle 1.
    { ss. apply MEM_MENT. }
    { ss. solve_divide. }
    ss.
Qed.



(* Import AppMod. *)

(* Definition progE {sysE: Type -> Type} : Type -> Type := *)
(*   osE +' tlimE +' sysE. *)

(* Notation progE sysE := (osE +' tlimE +' sysE). *)

Existing Instance cprog_event_instance.

Class SimApp
      `{SystemEnv}
      (* {sysE: Type -> Type} *)
      (* `{@CProgSysEvent sysE} *)
      (tid: nat)
      (cprog: Clight.program)
      (app_mod: @AppMod.t obsE bytes)
  : Type :=
  { app_gvar_ilist: list (ident * cglobvar) ;
    app_gfun_ilist: list (ident * fundef) ;
    app_cenv_ilist: list (ident * composite) ;
    app_gvar_ids := map fst app_gvar_ilist ;
    app_gfun_ids := map fst app_gfun_ilist ;
    app_cenv_ids := map fst app_cenv_ilist ;

    main_app_gvar_ids_disj:
      Coqlib.list_disjoint main_gvar_ids app_gvar_ids ;
    main_app_gfun_ids_disj:
      Coqlib.list_disjoint main_gfun_ids app_gfun_ids ;
    main_app_cenv_ids_disj:
      Coqlib.list_disjoint main_cenv_ids app_cenv_ids ;

    (* astate_t: Type ; *)
    inv_app: genv -> AppMod.abst_state_t app_mod -> mem -> Prop ;

    (* itree_app: nat -> list bytes ? -> astate_t -> *)
    (*            itree (sysE +' bsendE) astate_t ; *)

    job_func: Clight.function ;
    job_func_type: type_of_function job_func = Tfunction (Tcons tulong (Tcons (tptr (Tstruct _inbox_t noattr)) Tnil)) tvoid cc_default ;
    job_func_in_app_gfun_ilist:
      In (_job, Internal job_func) app_gfun_ilist;

    idx_job: nat ;

    ge := globalenv cprog;

    (* tid: nat ; *)
    range_tid: (tid < num_tasks)%nat ;

    (* task_id_in_app_gvar_ilist: *)
    (*   In (_TASK_ID, v_TASK_ID_p (Z.of_nat tid)) app_gvar_ilist; *)

    inv_app_dep_app_blocks:
      forall (* ge *) ast m m'
        (INV_APP: inv_app ge ast m)
        (UNCH_APP: Mem.unchanged_on
                     (blocks_of ge app_gvar_ids) m m'),
        inv_app ge ast m' ;

    inv_app_init:
      forall m_i (INIT_MEM: Genv.init_mem cprog = Some m_i),
      inv_app ge (AppMod.init_abst_state app_mod) m_i;

    sim_job_func:
      forall (r: nat -> itree progE unit -> Clight.state -> Prop)
        b_mst txs
        idx' ast ki m kp sytm
        cflg ofsc ofsn inbc inbn
        (mcont: bytes)
        (CALL_CONT: is_call_cont kp)
        (RANGE_SYTM: IntRange.uint64 sytm)
        (RANGE_SYTM2: IntRange.uint64 (sytm + period))

        (RANGE_TXS: IntRange.sint txs)
        (INV_APP: inv_app ge ast m)
        (FSYMB_MST: Genv.find_symbol ge _mstore = Some b_mst)
        (MEM_CONSTS: mem_consts ge m tid)
        (MEM_SBUF: mem_sbuf ge m (sytm + period) tid mcont)
        (MEM_MSTORE: mem_mstore ge m cflg
                                ofsc ofsn inbc inbn)
        (MEM_SH: mem_sh ge m (repeat false num_tasks))
        (MEM_TXS: mem_txs ge m txs)
        (SIM_REST:
           forall sh' ast' m' mcont'
             (UNCH_MAIN: Mem.unchanged_on
                           (blocks_of ge app_unch_gvar_ids) m m')
             (* (main_appinv_region cprog) m m') *)
             (MEM_SH: mem_sh ge m' sh')
             (MEM_SBUF: mem_sbuf ge m' (sytm + period)%nat tid mcont')
             (INV_APP': inv_app ge ast' m'),
             paco3 (_sim_itree (prog_of_clight cprog))
                   r idx' (ki (sh', ast'))
                   (Clight.Returnstate Vundef kp m'))
      ,
        paco3 (_sim_itree (prog_of_clight cprog)) r
              (idx' + idx_job)%nat
              (ret <- MWITree.interp_send
                       tid app_mod txs sytm
                       (repeat false num_tasks)
                       ast inbc;;
               ki ret)
              (Clight.Callstate
                 (Internal job_func)
                 [Vlong (IntNat.of_nat64 sytm);
                 Vptr b_mst (Ptrofs.repr ofsc)] kp m)
    ;
  }.

Section SIM_APP_LEMMAS.
  (* Variable cprog: Clight.program. *)
  Variable (* tid *) txs rxs: nat.

  Context `{SimApp}.
  Let prog: Prog.t := prog_of_clight cprog.
  Let ge := globalenv cprog.

  Lemma inv_app_unch_diffblk
        id ast b m m'
        (INV_APP: inv_app ge ast m)
        (MEM_CH: mem_changed_block b m m')
        (IN_MAIN: In id main_gvar_ids)
        (FIND_SYMB_CH: Genv.find_symbol ge id = Some b)
    : inv_app ge ast m'.
  Proof.
    eapply inv_app_dep_app_blocks; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros b_app ofs_app BLKS_OF_APP ?. simpl.
    rr in BLKS_OF_APP. des.
    eapply Genv.global_addresses_distinct; eauto.
    apply not_eq_sym.
    eapply main_app_gvar_ids_disj; eauto.
  Qed.

End SIM_APP_LEMMAS.



Lemma eval_max_time `{SystemEnv}
  : Int64.sub (Int64.repr (-1))
              (Int64.repr (10 * Z.of_nat period)) =
    Int64.repr (Z.of_nat MAX_TIME).
Proof.
  fold Int64.mone.
  rewrite Int64_mone_max_unsigned.
  unfold Int64.sub.
  rewrite Int64.unsigned_repr by ss.
  rewrite Int64.unsigned_repr.
  2: { pose proof period_mul_10_lt_max. nia. }
  rewrite Z.mul_comm.
  fold MAX_TIME_Z.
  rewrite max_time_to_z. ss.
Qed.
