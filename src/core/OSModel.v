From ITree Require Import ITree.
(* From compcert Require Import Integers. *)
From compcert Require Coqlib.
From Paco Require Import paco.

Require Import List.
Require Import Arith ZArith Lia.


Require Import sflib.
Require Import StdlibExt IntegersExt.

Require Import SysSem.
Require Import IPModel.
Require Import DiscreteTimeModel.
Require Import NWSysModel.
Require Import RTSysEnv.


(** * OS Model *)
(** *)
(** *)


(** ** Events handled by OS *)

Local Opaque Int.max_signed Int.max_unsigned Int64.max_unsigned.

(* the maximum size of IP packet *)


Inductive osE: Type -> Type :=
(* Socket API *)
| OSOpenSocket: osE Z
| OSBindSocket (sid: nat) (port: nat): osE Z
| OSJoinSocket (sid: nat) (mip: nat): osE unit
| OSCloseSocket (sid: nat): osE Z

(* | OSSendto (sid: nat) (bs: bytes) (sz: nat) *)
(*            (ip: ip_t) (port: nat): osE Z *)
| OSSendto (sid: nat) (bs: bytes)
           (ip: ip_t) (port: nat): osE Z
| OSRecvfrom (sid: nat) (sz: nat)
  : osE (bytes?)

(* Timer API *)
| OSGetTime: osE Z
| OSInitTimer: osE Z
| OSWaitTimer (tm: nat): osE Z
| OSCloseTimer: osE Z
.

(* (* precondition for safe execution of OS event handler *) *)
(* Inductive precond_osE : forall {R}, osE R -> Prop := *)
(* | Precond_OpenSocket: precond_osE OSOpenSocket *)
(* | Precond_BindSocket *)
(*     sid port *)
(*     (SID_RANGE: IntRange.sint sid) *)
(*     (PORT_RANGE: IntRange.sint port) *)
(*   : precond_osE (OSBindSocket sid port) *)
(* | Precond_JoinSocket *)
(*     sid mip *)
(*     (SID_RANGE: IntRange.sint sid) *)
(*     (MIP_RANGE: IntRange.uint mip) *)
(*   : precond_osE (OSJoinSocket sid mip) *)
(* | Precond_CloseSocket *)
(*     sid (SID_RANGE: IntRange.sint sid) *)
(*   : precond_osE (OSCloseSocket sid) *)

(* | Precond_Sendto *)
(*     sid dest_ip dest_port bs *)
(*     (SID_RANGE: IntRange.sint sid) *)
(*     (BUFSIZE_RANGE: IntRange.sint (length bs)) *)
(*     (DIP_RANGE: IntRange.uint dest_ip) *)
(*     (DPORT_RANGE: IntRange.sint dest_port) *)
(*   : precond_osE (OSSendto sid bs dest_ip dest_port) *)

(* | Precond_RecvMsg *)
(*     sid sz *)
(*     (SID_RANGE: IntRange.sint sid) *)
(*     (SZ_RANGE: IntRange.sint sz) *)
(*   : precond_osE (OSRecvfrom sid sz) *)

(* | Precond_GetTime: precond_osE OSGetTime *)
(* | Precond_InitTimer: precond_osE OSInitTimer *)
(* | Precond_WaitTimer *)
(*     tm (TM_RANGE: IntRange.uint64 tm) *)
(*   : precond_osE (OSWaitTimer tm) *)
(* | Precond_CloseTimer: precond_osE OSCloseTimer *)
(* . *)

Inductive rsp_cond_osE: forall {R}, osE R -> R -> Prop :=
| RspCond_OpenSocket
    r (RET_RANGE: IntRange.sintz r)
  : rsp_cond_osE OSOpenSocket r
| RspCond_BindSocket
    sid port
    r (RET_RANGE: IntRange.sintz r)
  : rsp_cond_osE (OSBindSocket sid port) r
| RspCond_JoinSocket
    sid mip
  : rsp_cond_osE (OSJoinSocket sid mip) tt
| RspCond_CloseSocket
    sid
    r (RET_RANGE: IntRange.sintz r)
  : rsp_cond_osE (OSCloseSocket sid) r

| RspCond_Sendto
    sid dest_ip dest_port bs
    r (RET_RANGE: IntRange.sintz r)
  : rsp_cond_osE (OSSendto sid bs dest_ip dest_port) r
| RspCond_RecvMsg
    sid sz
    obs
    (RET_BYTES: obs = None \/
                (exists bs, obs = Some bs /\
                       length bs <= sz /\
                       length bs <= Packet.maxlen))
  : rsp_cond_osE (OSRecvfrom sid sz) obs

| RspCond_GetTime
    r (RET_RANGE: IntRange.uintz64 r)
  : rsp_cond_osE OSGetTime r
| RspCond_InitTimer
    r (RET_RANGE: IntRange.sintz r)
  : rsp_cond_osE OSInitTimer r
| RspCond_WaitTimer
    tm r (RET_RANGE: IntRange.sintz r)
  : rsp_cond_osE (OSWaitTimer tm) r
| RspCond_CloseTimer
    r (RET_RANGE: IntRange.sintz r)
  : rsp_cond_osE OSCloseTimer r
.

Module Socket.
  Record t : Type :=
    mk { socket_id: nat;
         bound_port: nat ? ;
         socket_buffer : list Packet.msg_t ;
       }.

  Inductive wf (skt: t): Prop :=
    Wf
      (* { (* socket_id_range: IntRange.sint (socket_id skt) ; *) *)
      (*    (* port_num_range: option_rel1 IntRange.sint (bound_port skt) ; *) *)
      (MSGS_WF: List.Forall Packet.msg_wf (socket_buffer skt))
  .

  Definition set_t : Type := list t.

  Inductive set_wf (skts: set_t): Prop :=
    SetWf
        (EACH_SOCKET_WF: List.Forall wf skts)
        (SOCKET_ID_UNIQUE:
           List.NoDup (List.map socket_id skts))
        (BOUND_PORT_NUM_UNIQUE:
           List.NoDup (filtermap bound_port skts))
  .

  (* Record set_wf (skts: set_t): Prop := *)
  (*   SetWf { *)
  (*       each_socket_wf: List.Forall wf skts ; *)
  (*       socket_id_unique: *)
  (*         List.NoDup (List.map socket_id skts); *)
  (*       bound_port_num_unique: *)
  (*         List.NoDup (filtermap bound_port skts); *)
  (*     }. *)

  (** *** interaction with application *)

  Definition new_socket (new_id: nat) : t :=
    mk new_id None [].

  Lemma wf_new_socket new_id
        (NEW_ID_RANGE: IntRange.sint new_id)
    : wf (new_socket new_id).
  Proof. econs; ss. Qed.

  Inductive create
    : set_t -> set_t -> Z -> Prop :=
  | CreateSocket_Success
      ssocks (* res *)
      id_new
      (ID_RANGE: IntRange.sint id_new)
      (ID_FRESH: forall sock, List.In sock ssocks ->
                         socket_id sock <> id_new)
    : create ssocks
             (snoc ssocks (new_socket id_new))
             (Z.of_nat id_new)

  | CreateSocket_Fail (* may fail for unknown reason *)
      ssocks
    : create ssocks ssocks Z_mone
  .

  Lemma wf_create
        skts skts' oid
        (WFS: set_wf skts)
        (CREATE: create skts skts' oid)
    : set_wf skts'.
  Proof.
    inv CREATE; ss.
    unfold snoc.
    econs.
    - apply Forall_app.
      + inv WFS; eauto.
      + econs; eauto.
        econs; ss.
    - rewrite map_app. ss.
      inv WFS.
      apply nodup_snoc; eauto.
      intro IN.
      apply Coqlib.list_in_map_inv in IN. des.
      hexploit ID_FRESH; eauto.
    - rewrite filtermap_app. ss.
      rewrite app_nil_r.
      inv WFS. ss.
  Qed.

  Definition _bind_socket (port: nat) (skt: t): t * bool :=
    match bound_port skt with
    | None =>
      ({| socket_id := socket_id skt ;
          bound_port := Some port ;
          socket_buffer := socket_buffer skt ;
       |}, true)
    | Some _ =>
      (skt, false)
    end.

  Definition is_bound_port (port: nat) (sock: Socket.t): bool :=
    match Socket.bound_port sock with
    | None => false
    | Some bport => (bport =? port)%nat
    end.

  Definition check_port_unbound (port: nat) (skts: set_t): bool :=
    match find (is_bound_port port) skts with
    | None => true
    | Some _ => false
    end.

  Definition _bind (skts: set_t) (sid port: nat)
    : set_t * bool :=
    if andb (Z.of_nat port <? Int.max_signed)%Z
            (check_port_unbound port skts) then
      let (skts', res) :=
          repl_byid socket_id (_bind_socket port) sid skts in
      let res' := match res with
                  | None => false
                  | Some b => b
                  end
      in (skts', res')
    else (skts, false).

  Inductive bind (skts: set_t)
            (sid port: nat)
    : set_t -> Z -> Prop :=
    Bind
      skts' is_ok r
      (* (SID_RANGE: IntRange.sint sid) *)
      (* (DPORT_RANGE: IntRange.sint port) *)
      (BIND: _bind skts sid port = (skts', is_ok))
      (RETURN: r = if is_ok then Z0 else Z_mone)
    : bind skts sid port skts' r.

  Lemma wf_bind_socket
        p skt skt' b
        (BIND: _bind_socket p skt = (skt', b))
        (* (RANGE_PORT: IntRange.sint p) *)
        (WF_SKT: wf skt)
    : wf skt'.
  Proof.
    destruct skt as [sid opn buf].
    inv WF_SKT. ss.
    unfold _bind_socket in BIND. ss.
    destruct opn; clarify.
  Qed.

  Lemma wf_bind
        skts sid port skts' r
        (WF: set_wf skts)
        (* (SID_RANGE: IntRange.sint sid) *)
        (* (DPORT_RANGE: IntRange.sint port) *)
        (BIND: bind skts sid port skts' r)
    : set_wf skts'.
  Proof.
    inv BIND. rename BIND0 into BIND.
    unfold _bind in BIND.
    destruct (Z.ltb_spec (Z.of_nat port) Int.max_signed); ss.
    2: { clarify. }
    unfold check_port_unbound in BIND.

    destruct (find (is_bound_port port) skts) eqn:IS_BOUND; ss.
    { clarify. }

    hexploit (repl_byid_spec
                t _ socket_id (_bind_socket port) sid skts).
    i. des.
    { rewrite REPL_NONE in BIND. clarify. }
    rewrite REPL_SOME in BIND. clarify.
    renames a a' into skt skt'.

    inv WF.
    apply Forall_app_inv in EACH_SOCKET_WF.
    destruct EACH_SOCKET_WF as [WF1 WF'].
    apply Forall_app_inv in WF'.
    destruct WF' as [WF_A WF2].

    econs.
    - apply Forall_app; eauto.
      econs; eauto.
      inv WF_A. ss.
      eapply wf_bind_socket; eauto.
    - replace (map socket_id (l1 ++ skt' :: l2))
        with (map socket_id (l1 ++ [skt] ++ l2)).
      { ss. }

      repeat rewrite map_app. ss.
      cut (socket_id skt = socket_id skt').
      { congruence. }
      unfold _bind_socket in *. desf.
    - rewrite rw_cons_app.
      repeat rewrite filtermap_app in *. ss.
      destruct skt as [id1 obp1 buf1].
      destruct skt' as [id2 obp2 buf2]. ss.
      unfold _bind_socket in REPL_A. ss.

      destruct obp1 as [bp1|]; ss.
      { clarify. }

      clarify.
      rewrite NoDup_Add.
      2: { ss. apply Add_app. }
      split; ss.
      intro PORT_IN.
      apply in_app_or in PORT_IN. des.
      + apply filtermap_in in PORT_IN.
        destruct PORT_IN as [skt [SKT_IN PORT]].

        eapply find_none in IS_BOUND.
        2: { apply in_or_app. eauto. }
        unfold is_bound_port in IS_BOUND.
        rewrite PORT in IS_BOUND.
        rewrite Nat.eqb_refl in IS_BOUND. ss.
      + apply filtermap_in in PORT_IN.
        destruct PORT_IN as [skt [SKT_IN PORT]].

        eapply find_none in IS_BOUND.
        2: { apply in_or_app. ss. eauto. }
        unfold is_bound_port in IS_BOUND.
        rewrite PORT in IS_BOUND.
        rewrite Nat.eqb_refl in IS_BOUND. ss.
  Qed.

  Definition _close (skts: set_t) (sid: nat)
    : set_t * bool :=
    match remove_byid socket_id sid skts with
    | Some skts' => (skts', true)
    | None => (skts, false)
    end.

  Inductive close (skts: set_t) (sid: nat)
    : set_t -> Z -> Prop :=
    Close
      skts' is_ok r
      (* (SID_RANGE: IntRange.sint sid) *)
      (CLOSE_COMP: _close skts sid = (skts', is_ok))
      (RETURN: r = if is_ok then Z0 else Z_mone)
    : close skts sid skts' r.

  Lemma wf_close
        skts sid skts' r
        (WF: set_wf skts)
        (* (SID_RANGE: IntRange.sint sid) *)
        (CLOSE: close skts sid skts' r)
    : set_wf skts'.
  Proof.
    inv CLOSE.
    unfold _close in *.
    destruct (remove_byid_spec _ socket_id sid skts); ss.
    - des.
      rewrite REMOVE_FAILED in *. clarify.
    - des.
      rewrite REMOVE_SUCC in *. clarify.
      inv WF.
      econs.
      + apply Forall_app_inv in EACH_SOCKET_WF.
        destruct EACH_SOCKET_WF as [WF1 WF'].
        inv WF'.
        apply Forall_app; eauto.
      + rewrite NoDup_Add in SOCKET_ID_UNIQUE.
        2: { rewrite map_app. ss.
             apply Add_app. }
        rewrite map_app.
        des. eauto.
      + rewrite filtermap_app.
        rewrite filtermap_app in BOUND_PORT_NUM_UNIQUE. ss.
        destruct (bound_port a); ss.
        rewrite NoDup_Add in BOUND_PORT_NUM_UNIQUE.
        2: { apply Add_app. }
        des. eauto.
  Qed.

  (* (* model only add_membership *) *)
  Definition make_mcast_pkt (local_ip: ip_t)
             (skts: set_t) (sid: nat) (mip: ip_t)
    : Packet.t? :=
    if negb (IP.mcast_ip mip) then None else
      match find_byid socket_id sid skts with
      | None => None
      | Some _ => Some (Packet.MCast (mip, local_ip))
      end.

  Inductive mcast_join (local_ip: ip_t)
            (skts: set_t) (sid: nat) (mip: ip_t)
    : Packet.t? -> Prop :=
    MCastJoin
      opkt
      (* (SID_RANGE: IntRange.sint sid) *)
      (* (MIP_RANGE: IntRange.uint mip) *)
      (SOCKET_EXISTS: opkt = make_mcast_pkt local_ip skts sid mip)
    : mcast_join local_ip skts sid mip opkt.

  Definition _sendto (local_ip: ip_t)
             (skts: set_t) (sid: nat)
             (* (bs: bytes) (sz: nat) *)
             (bs: bytes) (dip dport: nat)
    : (Packet.msg_t)? :=
    (* let bs_eff : bytes := firstn sz bs in *)
    match find_byid socket_id sid skts with
    | None => None
    | Some _ =>
      if (length bs <? Packet.maxlen)%nat then
        Some (Packet.mkMsg local_ip dip dport bs)
      else None
    end.

  Inductive sendto (local_ip: ip_t) (skts: set_t)
            (sid: nat) (bs: bytes)
            (dest_ip: nat) (dest_port: nat)
    : Packet.t? -> Z -> Prop :=
    Sendto
      (* sid sz dest_ip dest_port *)
      omsg opkt ret
      (* (SID_INPUT: Z.of_nat sid = sid_z) *)
      (* (SZ_INPUT: Z.of_nat sz = sz_z) *)
      (* (DIP_INPUT: Z.of_nat dest_ip = dest_ip_z) *)
      (* (DPORT_INPUT: Z.of_nat dest_port = dest_port_z) *)

      (* (SID_RANGE: IntRange.sint sid) *)
      (* (SZ_RANGE: IntRange.sint (length bs)) *)
      (* (DIP_RANGE: IntRange.uint dest_ip) *)
      (* (DPORT_RANGE: IntRange.sint dest_port) *)

      (SENDTO: _sendto local_ip skts sid bs
                       dest_ip dest_port = omsg)
      (RETURN: ret = match omsg with
                     | Some _ => Z.of_nat (length bs)
                     | None => Z_mone
                     end)
      (OPT_PACKET: option_map Packet.Msg omsg = opkt)
    : sendto local_ip skts sid bs
             dest_ip dest_port opkt ret.

  Definition _recvfrom_skt (skt: t)
    : t * (bytes)? :=
    match socket_buffer skt with
    | [] => (skt, None)
    | m::ms =>
      ({| socket_id := socket_id skt ;
          bound_port := bound_port skt ;
          socket_buffer := ms |},
       Some (Packet.payload m))
    end.

  Definition flatten_opt {A} (x: A??): A? :=
    match x with
    | Some x => x
    | None => None
    end.

  Definition _recvfrom_skts (skts: set_t) (sid: nat)
    : set_t * (bytes)? :=
    let (skt', r) := repl_byid socket_id _recvfrom_skt sid skts in
    (skt', flatten_opt r).

  Inductive recvfrom (skts: set_t) (sid: nat) (sz: nat)
    : set_t -> bytes? -> Prop :=
    Recvfrom
      skts' obs obs_read
      (* (SID_RANGE: IntRange.sint sid) *)
      (* (SZ_RANGE: IntRange.sint sz) *)
      (RECVFROM: _recvfrom_skts skts sid = (skts', obs))
      (BYTES_READ: obs_read =
                   match obs with
                   | None => None
                   | Some bs =>
                     let bs_read := firstn sz bs in
                     Some bs_read
                   end)
    : recvfrom skts sid sz skts' obs_read.

  Lemma wf_recvfrom
        skts sid sz skts' obs
        (WF: set_wf skts)
        (* (SID_RANGE: IntRange.sint sid) *)
        (* (SZ_RANGE: IntRange.sint sz) *)
        (RECVFROM_W: recvfrom skts sid sz skts' obs)
    : set_wf skts'.
  Proof.
    inv WF.
    inv RECVFROM_W.
    unfold _recvfrom_skts in RECVFROM.
    generalize (repl_byid_spec _ _ socket_id
                               _recvfrom_skt sid skts).
    i. des.
    { rewrite REPL_NONE in RECVFROM. clarify. }
    rewrite REPL_SOME in RECVFROM. clarify.
    clear REPL_SOME.

    unfold _recvfrom_skt in REPL_A.
    destruct (socket_buffer a) as [|bh bt] eqn:BUF; ss.
    { clarify. }
    clarify.

    apply Forall_app_inv in EACH_SOCKET_WF.
    destruct EACH_SOCKET_WF as [WF1 WF'].
    inv WF'.

    assert (WF_A: wf a) by ss.
    inv WF_A.
    destruct a as [? ? ?]. ss.

    econs.
    - apply Forall_app; eauto.
      econs; eauto.
      rewrite BUF in MSGS_WF. inv MSGS_WF.
      econs; eauto.
    - clear - SOCKET_ID_UNIQUE.
      rewrite map_app in SOCKET_ID_UNIQUE. ss.
      rewrite map_app. ss.
    - clear - BOUND_PORT_NUM_UNIQUE.
      rewrite filtermap_app in BOUND_PORT_NUM_UNIQUE.
      rewrite filtermap_app. ss.
  Qed.


  (** *** interaction with outer environment *)

  Definition insert_msgs (sock: t)
             (ms: list Packet.msg_t)
    : Socket.t :=
    let 'Socket.mk sid bport sbuf := sock in
    Socket.mk sid bport (sbuf ++ ms).

  (* Definition check_dest *)
  (*            (skt: Socket.t) (msg: Packet.msg_t) : bool := *)
  (*   Socket.is_bound_port (Packet.dest_port msg) skt. *)

  Definition accept_msgs
             (msgs: list Packet.msg_t) (skt: Socket.t)
    : Socket.t :=
    match Socket.bound_port skt with
    | None => skt
    | Some pn =>
      let msgs_skt :=
          List.filter (fun msg => (Packet.dest_port msg =? pn)%nat) msgs in
      insert_msgs skt msgs_skt
    end.

  Definition set_accept_msgs
             (msgs: list Packet.msg_t) (skts: list Socket.t)
    : list Socket.t :=
    List.map (accept_msgs msgs) skts.

  Lemma wf_accept_msgs
        skt msgs
        (WF: wf skt)
        (MSGS_WF: List.Forall Packet.msg_wf msgs)
    : wf (accept_msgs msgs skt).
  Proof.
    inv WF.
    destruct skt as [? [] buf]; ss.
    unfold accept_msgs. ss.
    econs. ss.
    apply Forall_app; eauto.

    apply Forall_forall.
    intros x IN.
    apply filter_In in IN. des.
    rewrite Forall_forall in MSGS_WF.
    eauto.
  Qed.


  Lemma wf_set_accept_msgs
        skts msgs
        (WF: set_wf skts)
        (MSGS_WF: List.Forall Packet.msg_wf msgs)
    : set_wf (set_accept_msgs msgs skts).
  Proof.
    inv WF.
    econs.
    - unfold set_accept_msgs.
      apply Forall_forall.
      intros skt IN_MAP.
      apply in_map_iff in IN_MAP. des.
      subst.
      apply wf_accept_msgs; eauto.
      rewrite Forall_forall in EACH_SOCKET_WF. eauto.
    - cut (map socket_id (set_accept_msgs msgs skts) =
           map socket_id skts).
      { congruence. }
      clear.
      induction skts as [| h t IH]; ss.
      rewrite IH. f_equal.
      unfold accept_msgs. desf.
      unfold insert_msgs. desf.
    - cut (filtermap bound_port (set_accept_msgs msgs skts) =
           filtermap bound_port skts).
      { congruence. }
      clear.
      induction skts as [| h t IH]; ss.

      replace (bound_port (accept_msgs msgs h))
        with (bound_port h).
      2: { unfold accept_msgs. desf.
           unfold insert_msgs. desf. }
      desf.
      rewrite IH. eauto.
  Qed.

End Socket.


Module Timer.

  Inductive t : Type :=
  | Uninit
  | Init
  .

  Inductive init_timer: t -> t -> Z -> Prop :=
  | InitTimer_Fail
    : init_timer Uninit Uninit Z_mone
  | InitTimer_Succ
    : init_timer Uninit Init Z0
  | InitTimer_AlreadyInit
    : init_timer Init Init Z0
  .

  (* not used *)
  (* Inductive set_timer: t -> nat -> Z -> Prop := *)
  (* | SetTimer_Uninit *)
  (*     tm (RANGE: IntRange.uint64 tm) *)
  (*   : set_timer Uninit tm Z_mone *)
  (* | SetTiemr_Init *)
  (*     tm (RANGE: IntRange.uint64 tm) *)
  (*   : set_timer Init tm Z0 *)
  (* . *)

  (* Definition set_timer (tmr: t) (tm: nat): bool := *)
  (*   match tmr with *)
  (*   | Uninit => false *)
  (*   | Init => true *)
  (*   end. *)

  (* (* ret true means loop_end *) *)
  (* Definition check_timer (tmr: t) (ltm: nat): bool := *)
  (*   match tmr with *)
  (*   | Uninit => true (* unreachable *) *)
  (*   | Init None => true (* unreachable *) *)
  (*   | Init (Some tm) => (tm <? ltm)%nat *)
  (*   end. *)

  Inductive close_timer: t -> t -> Z -> Prop :=
  | CloseTimer_OK
    : close_timer Init Uninit Z0
  | CloseTimer_Fail
    : close_timer Uninit Uninit Z_mone
  .

End Timer.

(* Definition in_time_skew_limit (gtm: ATime.t) (ltm: nat) : Prop := *)
(*   nat_diff (ATime.to_ns_rd gtm) ltm <= MAX_TIME_SKEW. *)
(* (* ATime.le (ATime.diff gtm (ATime.of_ns ltm)) *) *)
(* (*        (ATime.of_ns MAX_TIME_SKEW). *) *)


(* OSModel with Our PALS LibAPI *)
Module OS.

  Inductive status: Type :=
  | Idle
  | Proc {R: Type} (os_evt: osE R)
  | Ret {R: Type} (os_evt: osE R) (r: R)
  | Waiting (wtm: nat)
  .

  Inductive status_wf : status -> Prop :=
  | StatusWf_Idle: status_wf Idle
  | StatusWf_Proc
      R (os_e: osE R)
      (* (PRECOND_EVT_CALL: precond_osE os_evc) *)
    : status_wf (Proc os_e)
  | StatusWf_Ret
      R (os_e: osE R) (r: R)
      (RSP_COND: rsp_cond_osE os_e r)
      (* (POSTCOND_EVT_CALL: postcond_osE os_evc r) *)
    : status_wf (Ret os_e r)
  | StatusWf_Waiting
      wtm
    : status_wf (Waiting wtm)
  .

  Definition status2oscall (sts: status)
    : (event_call osE)? :=
    match sts with
    | Idle => None
    | Proc R os_evt => Some (EventCall os_evt)
    | Ret R os_evt r => Some (EventCall os_evt)
    | Waiting wtm => Some (EventCall (OSWaitTimer wtm))
    end.

  Coercion Proc : osE >-> status.

  Inductive state : Type :=
    State {
        (* local_ip: ip_t; *)
        (* local_time: nat; *)

        sockets: Socket.set_t;
        timer: Timer.t;
        tlim: option nat;

        cur_status: status;
      }.

  Definition running_state (st: state): bool :=
    match (cur_status st) with
    | Idle => false
    | _ => true
    end.

  Definition init_state: state :=
    State [] Timer.Uninit None Idle.

  Inductive wf (st: state) : Prop :=
    Wf (WF_SOCKETS: Socket.set_wf (sockets st))
       (WF_STATUS: status_wf (cur_status st))
  .

  Lemma wf_init: wf init_state.
  Proof.
    econs; ss.
    - econs; ss; econs.
    - econs.
  Qed.

  Section OS_SEM.
    Context `{SystemEnv}.

    Inductive call: state -> event_call osE -> state -> Prop :=
      Call
        R (os_e: osE R)
        skts tmr tlim
      : call (State skts tmr tlim Idle) (EventCall os_e)
             (State skts tmr tlim (Proc os_e))
    .

    Lemma wf_call
          R (os_e: osE R)
          (st st': state)
          (WF: wf st)
          (* (PRECOND: precond_osE os_e) *)
          (CALL: call st (EventCall os_e) st')
      : wf st'.
    Proof.
      inv CALL. existT_elim. clarify.
      inv WF.
      econs; eauto.
      econs.
    Qed.

    Inductive step (local_ip: ip_t) (ltm: nat)
      : state -> Packet.t? -> state -> Prop :=
    (* socket events *)
    | Step_CreateSocket
        tmr0 tlim0 skts0 os_evt
        skts1 r
        (OS_EVT: os_evt = OSOpenSocket)
        (CREATE: Socket.create skts0 skts1 r)
      : step local_ip ltm (State skts0 tmr0 tlim0 os_evt) None
             (State skts1 tmr0 tlim0 (Ret os_evt r))
    | Step_BindSocket
        tmr0 tlim0 skts0 os_evt
        skts1 sid port r
        (OS_EVT: os_evt = OSBindSocket sid port)
        (BIND: Socket.bind skts0 sid port skts1 r)
      : step local_ip ltm (State skts0 tmr0 tlim0 os_evt) None
             (State skts1 tmr0 tlim0 (Ret os_evt r))
    | Step_JoinSocket
        tmr0 tlim0 skts0 os_evt
        sid mip opkt
        (OS_EVT: os_evt = OSJoinSocket sid mip)
        (JOIN_PKT: Socket.mcast_join
                     local_ip skts0 sid mip opkt)
      : step local_ip ltm (State skts0 tmr0 tlim0 os_evt) opkt
             (State skts0 tmr0 tlim0 (Ret os_evt tt))
    | Step_CloseSocket
        tmr0 tlim0 skts0 os_evt
        skts1 sid r
        (OS_EVT: os_evt = OSCloseSocket sid)
        (CLOSE: Socket.close skts0 sid skts1 r)
      : step local_ip ltm (State skts0 tmr0 tlim0 os_evt) None
             (State skts1 tmr0 tlim0 (Ret os_evt r))

    | Step_Sendto
        tmr0 tlim0 skts0 os_evt
        sid bs dip dport
        r opkt
        (OS_EVT: os_evt = OSSendto sid bs dip dport)
        (SENDTO: Socket.sendto local_ip skts0
                               sid bs dip dport opkt r)
      : step local_ip ltm (State skts0 tmr0 tlim0 os_evt) opkt
             (State skts0 tmr0 tlim0 (Ret os_evt r))
    | Step_Recvfrom
        tmr0 tlim0 skts0 skts1 os_evt
        sid sz obs
        (OS_EVT: os_evt = OSRecvfrom sid sz)
        (RECVFROM: Socket.recvfrom skts0 sid sz
                                   skts1 obs)
      : step local_ip ltm (State skts0 tmr0 tlim0 os_evt) None
             (State skts1 tmr0 tlim0 (Ret os_evt obs))

    (* Timer *)
    | Step_GetTime
        skts0 tmr0 tlim0 os_evt r
        (OS_EVT: os_evt = OSGetTime)
        (RET: r = if (ltm <=? Z.to_nat Int64.max_unsigned)%nat
                  then Z.of_nat ltm else Z0)
      : step local_ip ltm (State skts0 tmr0 tlim0 os_evt) None
             (State skts0 tmr0 (Some (ltm + period - DELTA - max_wait_delay)) (Ret os_evt r))
    | Step_InitTimer
        skts0 tmr0 tlim0 os_evt
        tmr1 r
        (OS_EVT: os_evt = OSInitTimer)
        (CREATE: Timer.init_timer tmr0 tmr1 r)
      : step local_ip ltm (State skts0 tmr0 tlim0 os_evt) None
             (State skts0 tmr1 tlim0 (Ret os_evt r))

    | Step_WaitTimer_Uninit
        tlim0 skts0 os_evt tm
        (OS_EVT: os_evt = OSWaitTimer tm)
      : step local_ip ltm (State skts0 Timer.Uninit tlim0 os_evt) None
             (State skts0 Timer.Uninit tlim0 (Ret os_evt Z_mone))
    | Step_WaitTimer_Init
        tlim0 skts0 os_evt tm
        (OS_EVT: os_evt = OSWaitTimer tm)
        (WAIT: ltm <= tm)
      : step local_ip ltm (State skts0 Timer.Init tlim0 os_evt) None
             (State skts0 Timer.Init tlim0 (Waiting tm))
    | Step_WaitTimer_Ret
        tlim0 skts0 os_evt tm
        (OS_EVT: os_evt = OSWaitTimer tm)
        (TIME_EXPIRED: tm < ltm)
      : step local_ip ltm (State skts0 Timer.Init tlim0 os_evt) None
             (State skts0 Timer.Init tlim0 (Ret os_evt Z0))
    | Step_WaitTimer_Waiting
        tlim0 skts0 tm
        (WAIT: ltm < tm + max_wait_delay)
      : step local_ip ltm (State skts0 Timer.Init tlim0 (Waiting tm)) None
             (State skts0 Timer.Init tlim0 (Waiting tm))
    | Step_WaitTimer_Expired
        tlim0 skts0 os_evt tm
        (OS_EVT: os_evt = OSWaitTimer tm)
        (TIME_EXPIRED: tm < ltm)
        (TIME_MAX: ltm < tm + max_wait_delay)
      : step local_ip ltm (State skts0 Timer.Init tlim0 (Waiting tm)) None
             (State skts0 Timer.Init (Some (ltm + period - DELTA - max_wait_delay)) (Ret os_evt Z0))

    | Step_CloseTimer
        skts0 tmr0 tlim0 os_evt
        tmr1 r
        (OS_EVT: os_evt = OSCloseTimer)
        (CLOSE_TIMER: Timer.close_timer tmr0 tmr1 r)
      : step local_ip ltm (State skts0 tmr0 tlim0 os_evt) None
             (State skts0 tmr1 tlim0 (Ret os_evt r))
    .

    Lemma progress
          R nip ltm st
          skts tmr tlim (os_evc: osE R)
          (IS_LOCAL_IP: IP.local_ip nip = true)
          (STATE: st = State skts tmr tlim (Proc os_evc))
          (* (WF: wf st) *)
      : exists op st',  step nip ltm st op st'.
    Proof.
      subst.
      destruct os_evc.
      - exists None.
        assert (exists skts' r, Socket.create skts skts' r).
        { (* always it may fail *)
          exists skts, Z_mone. econs. }
        des.
        eexists.
        econs 1; eauto.
      - (* hexploit (wf_status _ WF). ss. *)
        (* inversion 1. existT_elim. *)
        (* inv PRECOND_EVT_CALL. ss. *)

        assert (BIND_EXISTS: exists skts1 r, Socket.bind skts sid port skts1 r).
        { esplits. econs; eauto.
          rewrite surjective_pairing at 1. ss. }
        des.

        esplits; eauto.
        econs 2; eauto.
      - esplits. econs; eauto.
        econs; eauto.
      - esplits. econs 4; eauto.
        econs; eauto. eapply surjective_pairing.
      - esplits. econs 5; eauto.
        econs; eauto.
      - esplits. econs 6; eauto.
        econs; eauto. eapply surjective_pairing.

      - esplits. econs 7; eauto.
      - esplits. econs 8; eauto.
        destruct tmr; econs.
      - destruct tmr.
        + esplits. econs 9; eauto.
        + destruct (le_lt_dec ltm tm).
          * esplits. econs 10; eauto.
          * esplits. econs 11; eauto.
      - destruct tmr.
        + esplits. econs 14; eauto. econs.
        + esplits. econs 14; eauto. econs.
    Qed.

    Lemma wf_recvfrom_skt
          skt skt' obs
          (RF: Socket._recvfrom_skt skt = (skt', obs))
          (WF: Socket.wf skt)
      : Socket.wf skt' /\
        option_rel1 (fun bs => length bs < Packet.maxlen) obs.
    Proof.
      unfold Socket._recvfrom_skt in RF.
      destruct (Socket.socket_buffer skt) eqn:BUF.
      - clarify.
      - clarify.
        split.
        + inv WF. econs. ss.
          rewrite BUF in MSGS_WF. inv MSGS_WF. ss.
        + ss.
          inv WF.
          rewrite BUF in MSGS_WF.

          assert (WF_M: Packet.msg_wf m).
          { inv MSGS_WF. ss. }
          apply WF_M.
    Qed.

    Lemma wf_preserve
          nip ltm st op st'
          (IS_LOCAL_IP: IP.local_ip nip = true)
          (WF: wf st)
          (STEP: step nip ltm st op st')
      : <<WF_NXT: wf st'>> /\
        (* <<WF_PKT: option_rel1 (Packet.wf_sender nip) op>>. *)
        <<WF_PKT: option_rel1 Packet.wf op>>.
    Proof.
      inv STEP;
        try (split; [| by econs]).
      - (* create *)
        econs; ss.
        + eapply Socket.wf_create; eauto.
          apply WF.
        + econs. inv CREATE.
          * econs. ss.
          * econs. ss.
      - (* bind *)
        econs; ss.
        + inv WF. ss.
          inv WF_STATUS.
          existT_elim. clarify.
          (* inv PRECOND_EVT_CALL; ss. *)
          eapply Socket.wf_bind; try apply BIND; eauto.
        + econs. inv BIND.
          desf; econs; ss.
      - (* mcast_join *)
        split.
        { econs; ss.
          + apply WF.
          + econs. econs. }
        { inv JOIN_PKT.
          unfold Socket.make_mcast_pkt. desf.
          ss. r.
          econs; ss.
          econs; ss.
          destruct (IP.mcast_ip mip); ss.
        }
      - (* close *)
        inv WF.
        econs; ss.
        + eapply Socket.wf_close; eauto.
        + inv CLOSE.
          desf.
          * econs. econs. ss.
          * econs. econs. ss.
      - (* sendto *)
        inv WF. ss.
        esplits.
        + econs; ss.
          inv SENDTO.
          inv WF_STATUS. existT_elim. subst.
          unfold Socket._sendto. desf.
          * econs. econs. r.
            split.
            { etransitivity.
              - instantiate (1:=0%Z). ss.
              - nia. }
            { etransitivity.
              - eapply Z.lt_le_incl.
                instantiate (1:= Z.of_nat Packet.maxlen).
                apply Nat2Z.inj_lt.
                destruct (Nat.ltb_spec (length bs)
                                       Packet.maxlen); ss.
              - unfold Packet.maxlen.
                rewrite Z2Nat.id; ss.
            }
          * econs. econs. ss.
          * econs. econs. ss.
        + inv SENDTO.
          unfold Socket._sendto.
          desf. ss.
          econs. econs.

          destruct (Nat.ltb_spec (length bs) Packet.maxlen).
          2: { congruence. }
          eauto.

      - (* recvfrom *)
        inv WF. inv RECVFROM. ss.
        rename RECVFROM0 into RECVFROM.

        unfold Socket._recvfrom_skts in RECVFROM.
        generalize (repl_byid_spec
                      _ _ Socket.socket_id
                      Socket._recvfrom_skt sid skts0).
        i. des.
        { rewrite REPL_NONE in RECVFROM. clarify.
          econs; ss.
          econs. econs. eauto.
        }
        rewrite REPL_SOME in RECVFROM. ss. clarify.
        clear REPL_SOME.

        inv WF_SOCKETS.
        apply Forall_app_inv in EACH_SOCKET_WF.
        destruct EACH_SOCKET_WF as [WF1 WF'].
        inv WF'.
        hexploit wf_recvfrom_skt; eauto. i. des.

        econs; ss.
        + econs.
          { apply Forall_app; eauto. }
          { replace (map Socket.socket_id (l1 ++ a' :: l2))
              with (map Socket.socket_id (l1 ++ a :: l2)).
            { ss. }
            do 2 rewrite map_app. f_equal.
            ss. f_equal.
            unfold Socket._recvfrom_skt in REPL_A.
            desf.
          }
          { replace (filtermap Socket.bound_port (l1 ++ a' :: l2))
              with (filtermap Socket.bound_port (l1 ++ a :: l2)).
            { ss. }
            rewrite rw_cons_app with (t := l2).
            rewrite rw_cons_app with (t := l2).
            do 4 rewrite filtermap_app.
            f_equal. f_equal. ss.

            unfold Socket._recvfrom_skt in REPL_A.
            desf. ss. clarify.
          }
        + destruct obs0; ss.
          2: { econs. econs. eauto. }
          econs. econs. right.
          esplits; eauto.
          { rewrite firstn_length. nia. }
          { rewrite firstn_length. nia. }

      - inv WF.
        econs; eauto.
        econs. econs.

        destruct (Nat.leb_spec ltm (Z.to_nat Int64.max_unsigned)) as [LE|?]; ss.
        r. split.
        { nia. }
        apply Nat2Z.inj_le in LE.
        rewrite Z2Nat.id in LE.
        2: { clear. ss. }
        apply LE.

      - inv WF.
        econs; eauto.
        econs. econs.
        inv CREATE; ss.

      - inv WF.
        econs; eauto.
        econs. econs. ss.
      - inv WF.
        econs; eauto. econs.
      - inv WF.
        econs; eauto.
        econs. econs. ss.
      - eauto.
      - inv WF.
        econs; eauto.
        econs. econs. ss.

      - inv WF. ss.
        inv CLOSE_TIMER.
        + econs; eauto. ss.
          econs. econs. ss.
        + econs; eauto. ss.
          econs. econs. ss.
    Qed.


    Inductive ret: state -> event osE -> state -> Prop :=
      OSReturn
        R skts tmr tlim (os_e: osE R) r sts
        (RET_STATUS: sts = Ret os_e r)
      : ret (State skts tmr tlim sts)
            (Event os_e r)
            (State skts tmr tlim Idle).

    Lemma wf_ret
          R (ose: osE R) (r: R) st st'
          (WF: wf st)
          (RET: ret st (Event ose r) st')
      : wf st' /\ rsp_cond_osE ose r.
    Proof.
      inv RET. existT_elim. clarify.
      econs.
      - econs.
        + apply WF.
        + ss. econs.
      - inv WF. ss. inv WF_STATUS.
        existT_elim. clarify.
    Qed.

    Definition accept_msgs
               (dpms: list Packet.msg_t)
               (ost: OS.state)
      : OS.state :=
      match ost with
      | OS.State skts0 tmr0 tlim0 sts =>
        let skts1 := Socket.set_accept_msgs dpms skts0 in
        OS.State skts1 tmr0 tlim0 sts
      end.

    Lemma wf_accept_msgs
          dpms ost ost'
          (WF: OS.wf ost)
          (WF_DPMS: Forall Packet.msg_wf dpms)
          (ACCEPT: accept_msgs dpms ost = ost')
      : OS.wf ost'.
    Proof.
      destruct ost as [skts tmr sts]. ss. subst.
      econs; ss.
      - apply Socket.wf_set_accept_msgs; eauto.
        apply WF.
      - apply WF.
    Qed.

  End OS_SEM.
End OS.
