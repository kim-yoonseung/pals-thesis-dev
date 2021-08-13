From ITree Require Import ITree Eq EqAxiom.
Require Import sflib.

Require Import StdlibExt IntegersExt ITreeTac.
Require Import IPModel IntByteModel.
Require Import NWSysModel.
Require Import OSModel OSNodes.

Require Import RTSysEnv.
Require Import SyncSysModel.


Require Import List ZArith Lia.

Generalizable Variable sysE.

Import ITreeNotations.


Module MWITree.

  (* Inductive jobE: Type -> Type := *)
  (*   JobEvent : jobE unit. *)

  Section DEF.
    Context `{sysE: Type -> Type}.
    Context `{SystemEnv}.
    Let progE := (osE +' sysE).

    (* Variable (tid: Tid). *)

    (* Let osAppE : Type -> Type := (osE +' tlimE +' sysE). *)

    Definition inbox_t: Type := (* list (bool * bytes). *)
      list bytes?.
    Definition mstore_t: Type := inbox_t * inbox_t.
    Definition init_inbox : inbox_t :=
      List.repeat (* (false, List.repeat Byte.zero msg_size) *)
        None num_tasks.

    Definition init_mstore: mstore_t :=
      (init_inbox, init_inbox).

    (* Definition inbox_t2 : Type := list (bytes?). *)

    Fixpoint insert_msg (inbox: inbox_t)
             (tid: Tid) (bs: bytes)
      : inbox_t :=
      match inbox with
      | ment :: inbox' =>
        match tid with
        | O => (Some bs) :: inbox'
          (* match ment with *)
          (* | (false, _) => ((true, bs) :: inbox') *)
          (* | (true, _) => inbox *)
          (* end *)
        | S tid' =>
          (ment :: insert_msg inbox' tid' bs)
        end
      | [] => []
      end.

    Definition insert_msg_cur (mst: mstore_t)
               (tid: Tid) (bs: bytes)
      : mstore_t :=
      let (mst_c, mst_n) := mst in
      (insert_msg mst_c tid bs, mst_n).

    Definition insert_msg_nxt (mst: mstore_t)
               (tid: Tid) (bs: bytes)
      : mstore_t :=
      let (mst_c, mst_n) := mst in
      (mst_c, insert_msg mst_n tid bs).

    (* Definition inbox_to_opt: inbox_t -> inbox_t2 := *)
    (*   List.map (fun (ment: bool * bytes) => *)
    (*               let (rcv, mcont) := ment in *)
    (*               if rcv then Some mcont else None). *)

    Section ITREE.
      (* Variable mcast_groups: list (ip_t * list Tid). *)
      Variable tid: Tid.
      (* Variable mips: list Tid. *)

      Variable app_mod: @AppMod.t sysE bytes.

      Let astate_t: Type := AppMod.abst_state_t app_mod.
      Let job_itree : Z -> list bytes? -> astate_t ->
                      itree (sysE +' bsendE) astate_t :=
        AppMod.job_itree app_mod.

      Section JOB.
        Variable (txs: nat) (sytm: nat).

        Definition bsendE_itree
                   (sh: list bool)
                   (tid_dest: Tid) (msg: bytes)
          : itree progE (list bool * unit) :=
          match check_send_hist sh tid_dest with
          | None => Ret (sh, tt)
          | Some sh' =>
            let payload := serialize_msg
                             (sytm + period) tid
                             (resize_bytes msg_size msg) in
            trigger (OSSendto txs payload
                              (tid2ip tid_dest) port);;
            Ret (sh', tt)
          end.

        Definition send_handler
                   (R: Type) (e: (sysE +' bsendE) R)
          : Monads.stateT (list bool) (itree progE) R :=
          match e with
          | inl1 se =>
            fun sh => (r <- trigger se;; Ret (sh, r))
          | inr1 ps =>
            match ps with
            | AbstSendEvent tid_dest msg =>
              fun sh => bsendE_itree sh tid_dest msg
            end
          end.

        Definition interp_send
                   (sh: list bool) (ast: astate_t)
                   (inbox: list bytes?)
          : itree progE (list bool * astate_t) :=
          interp send_handler
                 (job_itree (Z.of_nat sytm) inbox ast) sh.

        Lemma unfold_interp_tau
              (itr itr': itree (sysE +' bsendE) astate_t)
              (OBS: observe itr = TauF itr')
              (sh: list bool)
          : interp send_handler itr sh =
            Tau (interp send_handler itr' sh).
        Proof.
          apply bisimulation_is_eq.
          unfold interp. unfold Basics.iter, MonadIter_stateT0.
          unfold Basics.iter, MonadIter_itree.
          ss.
          rewrite unfold_iter.
          rewrite bind_bind. ss.
          desf.
          rewrite bind_ret_l. ss.
          rewrite bind_ret_l. ss.
          reflexivity.
        Qed.

        Lemma unfold_interp_ret
              ast sh
              (itr : itree (sysE +' bsendE) astate_t)
              (OBS: observe itr = RetF ast)
          : interp send_handler itr sh = Ret (sh, ast).
        Proof.
          apply bisimulation_is_eq.
          unfold interp. unfold Basics.iter, MonadIter_stateT0.
          unfold Basics.iter, MonadIter_itree.
          ss.
          rewrite unfold_iter.
          rewrite bind_bind. ss.
          desf.
          rewrite bind_ret_l. ss.
          rewrite bind_ret_l. ss.
          reflexivity.
        Qed.

        Lemma unfold_interp_vis_sys
              R (sys_ec: sysE R) (k: R -> itree _ _)
              (itr: itree (sysE +' bsendE) astate_t)
              (sh: list bool)
              (OBS: observe itr = VisF (inl1 sys_ec) k)
          : interp send_handler itr sh =
            Vis (subevent _ sys_ec)
                (fun r => Tau (interp send_handler (k r) sh)).
        Proof.
          apply bisimulation_is_eq.
          unfold interp.
          unfold Basics.iter, MonadIter_stateT0.
          unfold Basics.iter, MonadIter_itree.
          rewrite unfold_iter.
          repeat change (fun x => ?h x) with h in *.

          desf; ss.
          { exfalso. congruence. }
          { exfalso. congruence. }
          rewrite Heq in OBS. clarify.
          existT_elim. subst.

          rewrite bind_bind.
          unfold ITree.map.
          rewrite bind_bind. ss.
          rewrite bind_bind.
          setoid_rewrite bind_ret_l. ss.
          setoid_rewrite bind_ret_l. ss.
          setoid_rewrite bind_ret_l. ss.
          rewrite bind_trigger. ss.
          reflexivity.
        Qed.

        Lemma unfold_interp_vis_send
              tid_d bs
              (k: unit -> itree _ _)
              (itr: itree (sysE +' bsendE) astate_t)
              (sh: list bool)
              (OBS: observe itr = VisF (inr1 (BSendEvent tid_d bs)) k)
          : interp send_handler itr sh =
            x <- send_handler _ (inr1 (BSendEvent tid_d bs)) sh ;;
            Tau (interp send_handler (k (snd x)) (fst x)).
        Proof.
          apply bisimulation_is_eq.
          unfold interp.
          unfold Basics.iter, MonadIter_stateT0.
          unfold Basics.iter, MonadIter_itree.

          rewrite unfold_iter. ss.
          repeat change (fun x => ?h x) with h.
          rewrite OBS.
          unfold ITree.map.
          rewrite bind_bind.
          rewrite bind_bind. ss.
          setoid_rewrite bind_ret_l.
          setoid_rewrite bind_ret_l.
          unfold ITree.iter. ss.
          reflexivity.
        Qed.

      End JOB.

      Section LOOP.
        Variable valid_time: nat -> bool.
        Variable txs rxs: nat.

        Section LOOP_BODY.
          Variable sytm: nat.
          Let nsytm: nat := sytm + period.

          Definition fetch_msg (pld: bytes) (mst: mstore_t)
            : mstore_t :=
            if negb (length pld =? pld_size)%nat then mst else
              match parse_msg pld with
              | None => mst
              | Some (dtm, tid_s, bs) =>
                if (dtm =? sytm)%nat then
                  (insert_msg_cur mst tid_s bs)
                else
                  if (dtm =? nsytm)%nat then
                    (insert_msg_nxt mst tid_s bs)
                  else mst
              end.

          Fixpoint fetch_msg_loop (n: nat)
                   (mst: mstore_t)
            : itree progE mstore_t :=
            match n with
            | O => Ret mst
            | S n' =>
              obs <- trigger (OSRecvfrom rxs pld_size) ;;
              match obs with
              | None => Ret mst
              | Some pld =>
                let mst' := fetch_msg pld mst in
                fetch_msg_loop n' mst'
              end
            end.

          Definition fetch_msgs (mst: mstore_t)
            : itree progE mstore_t :=
            fetch_msg_loop (num_tasks * 4) mst.

          Definition reset_inbox (inb: inbox_t): inbox_t :=
            List.map (fun x => None) inb.

          Definition loop_body (mst: mstore_t) (ast: astate_t)
            : itree progE (mstore_t * astate_t) :=
            let (inbc, inbn) := mst in
            trigger (OSWaitTimer sytm);;
            '(inbc', inbn') <- fetch_msgs (inbc, inbn) ;;
            '(_, ast') <- interp_send
                           txs sytm
                           (repeat false num_tasks)
                           ast inbc' ;;
            let sytm' := sytm + period in
            let inbc_r := reset_inbox inbc' in
            Ret ((inbn', inbc_r), ast')
          .

        End LOOP_BODY.


        (* Definition loop_cond_body *)
        (*            (st: mstore_t * astate_t * nat) *)
        (*   : itree (callE (mstore_t * astate_t * nat) unit +' progE) unit := *)
        (*   let '(mst, ast, sytm) := st in *)
        (*   if valid_time sytm then *)
        (*     st' <- translate subevent (loop_body sytm mst ast) ;; *)
        (*     call st' *)
        (*   else Ret tt. *)

        (* Not to Import RecursionFacts *)
        CoFixpoint main_loop
                   (mst: mstore_t)
                   (* (inbc inbn: inbox_t) *)
                   (ast: astate_t) (sytm: nat)
          : itree progE unit :=
          if valid_time sytm then
            '(mst', ast') <- loop_body sytm mst ast ;;
            let sytm' := sytm + period in
            Tau (main_loop mst' ast' sytm')
          else Ret tt.

        Lemma observe_main_loop mst ast sytm
          : observe (main_loop mst ast sytm) =
            observe (if valid_time sytm then
                       '(mst', ast') <-
                       loop_body sytm mst ast ;;
                       let sytm' := sytm + period in
                       Tau (main_loop mst' ast' sytm')
                     else Ret tt).
        Proof. ss. Qed.

        Lemma unfold_main_loop
              mst ast sytm
          : main_loop mst ast sytm =
            if valid_time sytm then
              '(mst', ast') <- loop_body sytm mst ast ;;
              let sytm' := sytm + period in
              Tau (main_loop mst' ast' sytm')
            else Ret tt.
        Proof.
          apply bisimulation_is_eq.
          rewrite (itree_eta (main_loop mst ast sytm)).
          rewrite observe_main_loop.

          destruct (valid_time sytm) eqn: VALID_TIME; ss.
          2: { reflexivity. }

          rewrite <- itree_eta. reflexivity.
        Qed.

      End LOOP.

      Definition ltb_max_time (tm: nat): bool :=
        (tm <? MAX_TIME)%nat.

      Definition run_task (txs rxs: nat)
                 (* (ast0: astate_t) *) (sytm: nat)
        : itree progE unit :=
        main_loop ltb_max_time txs rxs
                  init_mstore
                  (AppMod.init_abst_state app_mod)
                  sytm.

      Fixpoint mcast_join (rxs: nat)
               (mid_hd: nat)
               (mcasts_members: list (list Tid))
        : itree progE unit :=
        match mcasts_members with
        | [] => Ret tt
        | mbrs :: mcs_mbrs =>
          (if (existsb (Nat.eqb tid) mbrs) then
             (trigger (OSJoinSocket rxs (tid2ip mid_hd)))
           else Ret tt);;
          mcast_join rxs (S mid_hd) mcs_mbrs
        end.
        (* if is_ctrl_tid tid then *)
        (*   trigger (OSJoinSocket rxs ip_mcast) *)
        (* else Ret tt. *)

      (* Let ast0: astate_t := *)
      (*   AppMod.init_abst_state _ app_mod. *)

      Definition main_itree
        : itree progE unit :=
        ret_it <- trigger OSInitTimer ;;
        if (ret_it <? 0)%Z then Ret tt else
          tm_z <- trigger OSGetTime ;;
          let tm := Z.to_nat tm_z in
          if orb (tm =? O) (negb (tm <? MAX_TIME)) then Ret tt else
            let nsytm := base_time period tm + 2 * period in
            txs_z <- trigger OSOpenSocket ;;
            rxs_z <- trigger OSOpenSocket ;;
            if orb (txs_z <? 0)%Z (rxs_z <? 0)%Z then Ret tt else
                let txs := Z.to_nat txs_z in
                let rxs := Z.to_nat rxs_z in
                trigger (OSWaitTimer nsytm) ;;
                ret <- trigger (OSBindSocket rxs port) ;;
                if (ret <? 0)%Z then Ret tt else
                  mcast_join rxs num_tasks (map snd mcasts) ;;
                  let nsytm' := nsytm + period * 2 in
                  run_task txs rxs nsytm'
      .

    End ITREE.

  End DEF.
End MWITree.
