From Paco Require Import paco.
From ITree Require Import ITree.

Require Import ZArith Streams List Lia.

Require Import sflib.
Require Import StdlibExt IntegersExt.
Require Import SysSem.
Require Import SyncSysModel.
Require Import CProgEventSem.
Require Import MSteps FMSim FMSim_Switch.
Require Import PALSSystem.

(* Require console ctrl dev. *)

(* Require Import AcStSystem. *)
(* Require Import SpecConsole SpecController SpecDevice. *)
(* Require Import VerifConsole VerifController VerifDevice. *)

(* Require Import CProgEventSem. *)
(* Require Import AcStSystem AcStRefinement. *)

Local Opaque Z.of_nat Z.to_nat.

(* Import ActiveStandby. *)

Set Nested Proofs Allowed.


(* Generali lemmas *)


Create HintDb app_pf.

Hint Extern 1 (Nat.divide ?X ?X) =>
apply Nat.divide_refl: app_pf.

Hint Extern 1 (Nat.divide ?X (?Y * ?Z)) =>
apply Nat.divide_mul_r: app_pf.

Hint Extern 1 (Nat.divide ?X (?Y * ?Z)) =>
apply Nat.divide_mul_l: app_pf.

Hint Extern 1 (Nat.divide ?X (?Y + ?Z)) =>
apply Nat.divide_add_r: app_pf.


Lemma Nat2Z_inj_divide
      n1 n2
      (DIV: Nat.divide n1 n2)
  : (Z.of_nat n1 | Z.of_nat n2)%Z.
Proof.
  r. r in DIV.
  destruct DIV as [n DIV].
  exists (Z.of_nat n). nia.
Qed.



Lemma Forall_stream_app_div A
      (P: A -> Prop)
      l s
      (SFA: Forall_stream P (stream_app l s))
  : <<FA_LIST: Forall P l>> /\
    <<FA_STR: Forall_stream P s>>.
Proof.
  induction l as [| h t IH]; i; ss.
  { esplits; eauto. }
  punfold SFA. inv SFA. pclearbot.
  hexploit IH; eauto. i. des.
  esplits.
  - econs; eauto.
  - ss.
Qed.


(* colist_In and stream_In *)

Inductive colist_In {A}: A -> colist A -> Prop :=
| ColistIn_Head
    h t
  : colist_In h (ccons h t)
| ColistIn_Tail
    a h t
    (IN: colist_In a t)
  : colist_In a (ccons h t)
.


Lemma colist_In_app_or A
      (a: A) l c
      (CO_IN: colist_In a (colist_app l c))
  : In a l \/ colist_In a c.
Proof.
  induction l as [| h t IH]; eauto; ss.
  inv CO_IN.
  { eauto. }
  hexploit IH; eauto. i. des; eauto.
Qed.

Lemma colist_In_or_app A
      (a: A) l c
      (OR: In a l \/ colist_In a c)
  : colist_In a (colist_app l c).
Proof.
  induction l as [| h t IH]; eauto; ss.
  { des; ss. }
  des; subst.
  - econs.
  - econs 2. eauto.
  - econs 2; eauto.
Qed.



Inductive stream_In {A} (a: A): stream A -> Prop :=
| StreamIn_Here t
  : stream_In a (Cons a t)
| StreamIn_Later
    h t
    (IN_LATER: stream_In a t)
  : stream_In a (Cons h t)
.

(* Str_nth *)

(* Notation stream_nth s n := (Str_nth n s) (only parsing). *)

(* Fixpoint colist_nth_error {A} (cl: colist A) (n: nat) : A? := *)
(*   match cl with *)
(*   | cnil => None *)
(*   | ccons h t => *)
(*     match n with *)
(*     | O => Some h *)
(*     | S n' => colist_nth_error t n' *)
(*     end *)
(*   end. *)


Lemma stream_In_or_app A
      a l (s: stream A)
      (IN: In a l \/ stream_In a s)
  : stream_In a (stream_app l s).
Proof.
  induction l; ss.
  { des; ss. }
  des; subst; ss.
  - econs.
  - econs 2. eauto.
  - econs 2. eauto.
Qed.

Lemma stream_In_app_or A
      a l (s: stream A)
      (SIN: stream_In a (stream_app l s))
  : In a l \/ stream_In a s.
Proof.
  induction l; ss.
  { eauto. }
  inv SIN.
  { eauto. }
  hexploit IHl; eauto. i. des; eauto.
Qed.


Lemma colist_In_app_ex A
      (a: A) c
      (CO_IN: colist_In a c)
  : exists pre c',
    c = colist_app pre (ccons a c').
Proof.
  induction CO_IN; ss.
  { exists []. esplits; ss. }
  des. subst.
  exists (h :: pre). esplits; ss.
Qed.

Lemma stream_In_app_ex A
      (a: A) s
      (SIN: stream_In a s)
  : exists pre s',
    s = stream_app pre (Cons a s').
Proof.
  induction SIN; ss.
  { exists []. esplits; ss. }
  des. subst.
  exists (h :: pre). esplits; ss.
Qed.


Lemma Forall_stream_forall A
      (P: A -> Prop) s
      (FA: Forall_stream P s)
  : forall a (IN: stream_In a s), P a.
Proof.
  i. apply stream_In_app_ex in IN. des. subst.
  eapply Forall_stream_app_div in FA.
  des; ss.
  punfold FA_STR. inv FA_STR. ss.
Qed.


Lemma colist_app_eq_cases A
      (l1 l2: list A) c1 c2
      (CO_EQ: colist_app l1 c1 = colist_app l2 c2)
  : (exists l1_r,
        <<L1_DIV: l1 = l2 ++ l1_r>> /\
        <<L1_R_NONNIL: 0 < length l1_r>> /\
        <<C2_EQ: c2 = colist_app l1_r c1>>) \/
    (exists l2_r,
        <<L2_DIV: l2 = l1 ++ l2_r>> /\
        <<C1_EQ: c1 = colist_app l2_r c2>>).
Proof.
  depgen l2.
  induction l1 as [| h1 t1 IH]; i; ss.
  { right. esplits; eauto. }
  destruct l2 as [| h2 t2].
  { ss. subst.
    left. esplits; eauto.
    ss. nia. }

  ss. inv CO_EQ.
  hexploit IH; eauto. i. des.
  - left. esplits; eauto. clarify.
  - right. esplits; eauto. clarify.
Qed.


Lemma stream_app_eq_cases A
      (l1 l2: list A) c1 c2
      (SEQ: stream_app l1 c1 = stream_app l2 c2)
  : (exists l1_r,
        <<L1_DIV: l1 = l2 ++ l1_r>> /\
        <<L1_R_NONNIL: 0 < length l1_r>> /\
        <<C2_EQ: c2 = stream_app l1_r c1>>) \/
    (exists l2_r,
        <<L2_DIV: l2 = l1 ++ l2_r>> /\
        <<C1_EQ: c1 = stream_app l2_r c2>>).
Proof.
  eapply stream_app_3ways in SEQ. des.
  - right. esplits; eauto.
  - left. esplits; eauto.
  - subst. right.
    exists []. esplits; eauto.
    rewrite app_nil_r. ss.
Qed.

Lemma stream_app_inv_eqlen A
      (l1 l2: list A) s1' s2'
      (DIV1: stream_app l1 s1' = stream_app l2 s2')
      (LEN: length l1 = length l2)
  : l1 = l2 /\ s1' = s2'.
Proof.
  depgen l2.
  induction l1 as [| h1 t1 IH]; i; ss.
  { subst.
    destruct l2; ss. }
  destruct l2 as [| h2 t2]; ss.
  clarify.
  hexploit IH; eauto.
  i. des.
  esplits; eauto. congruence.
Qed.


(* Strong induction over lists *)

Lemma list_str_ind A
      (P: list A -> Prop)
      (IND_CASE:
         forall (l: list A)
           (IH: forall l', length l' < length l -> P l'),
           P l)
  : forall l, P l.
Proof.
  assert (forall n, forall l, length l <= n -> P l).
  { induction n as [| n' IH]; i; ss.
    { destruct l; ss.
      2: { nia. }
      apply IND_CASE.
      ii. ss. nia. }

    apply IND_CASE.
    i. eapply IH. nia.
  }
  eauto.
Qed.


Definition sapp_each_rel {A}
           (hds: list (list A)) (tls: list (stream A))
  : list (stream A) -> Prop :=
  Forall3 (fun h t l => stream_app h t = l) hds tls.

Definition capp_each_rel {A}
           (hds: list (list A)) (tls: list (colist A))
  : list (colist A) -> Prop :=
  Forall3 (fun h t l => colist_app h t = l) hds tls.

(* end general *)


(* Lemmas about behaviors *)




(* Events in behavior/execution *)

Inductive event_in_beh {sysE: Type -> Type}
          (tid: nat) (tevt: Z * event sysE)
          (beh: behav_t sysE) : Prop :=
  EventInBehav
    lbeh
    (LOCAL_BEHAV: nth_error beh tid = Some lbeh)
    (IN_LBEH: colist_In tevt lbeh)
.


Inductive event_in_exec {E} (tid: nat) (t: Z) (e: event E)
          (exec: exec_t E): Prop :=
  EventInExec
    exec_n es
    (LOCAL_EXEC: nth_error exec tid = Some exec_n)
    (EVTS_AT_T: stream_In (t, es) exec_n)
    (IN_EVTS: In e es)
.


Inductive event_in_tr {E} (tid: nat) (t: Z) (e: event E)
          (tr: list (list (Z *  events E))): Prop :=
  EventInTrace
    tr_n es
    (LOCAL_EXEC: nth_error tr tid = Some tr_n)
    (EVTS_AT_T: In (t, es) tr_n)
    (IN_EVTS: In e es)
.


Lemma local_exec_beh_divbeh E
      (exec: lexec_t E) fb beh
      (LEXEC_BEH: local_exec_behav exec (colist_app fb beh))
: exists fe fb' exec' beh',
  <<EXEC_DIV: exec = stream_app fe exec'>> /\
  <<FINITE_PART_EQ: flatten_tes fe = fb ++ fb'>> /\
  <<BEH_DIV: beh = colist_app fb' beh'>> /\
  <<LEXEC_BEH': local_exec_behav exec' beh'>>.
Proof.
  revert exec LEXEC_BEH.
  pattern fb. revert fb.
  apply list_str_ind. intro fb. i.

  punfold LEXEC_BEH. inv LEXEC_BEH.
  { destruct fb; ss. subst.
    exists []. esplits; eauto; ss.
    pfold. econs 1. eauto. }

  apply colist_app_eq_cases in BEHAVIOR. des.
  - pclearbot.
    hexploit (IH l1_r); eauto.
    { destruct es; ss.
      subst fb. ss.
      rewrite app_length. rewrite map_length. nia. }
    { subst beh'. eauto. }
    i. des.
    clarify.
    esplits; try apply LEXEC_BEH'.
    + instantiate (1:= tr_tau ++ (ts, es) :: fe).
      rewrite stream_app_assoc. ss.
    + instantiate (1:= fb').
      rewrite flatten_tes_app. ss.
      apply flatten_silent_local_trace_iff in TRACE_TAU.
      rewrite TRACE_TAU. ss.
      rewrite <- app_assoc.
      rewrite <- FINITE_PART_EQ. ss.
    + ss.

  - clarify.
    pclearbot.
    exists (tr_tau ++ [(ts, es)]), l2_r, lexec', beh'.
    esplits; eauto.
    + rewrite stream_app_assoc. ss.
    + rewrite flatten_tes_app.
      apply flatten_silent_local_trace_iff in TRACE_TAU.
      rewrite TRACE_TAU. ss.
      rewrite <- L2_DIV.
      unfold flatten_tes. ss.
      rewrite app_nil_r. ss.
Qed.


Lemma local_event_in_beh_exec E
      t e beh (exec: lexec_t E)
      (LEXEC_BEH: local_exec_behav exec beh)
      (EINB: colist_In (t, e) beh)
: exists es, stream_In (t, es) exec /\ In e es.
Proof.
  eapply colist_In_app_ex in EINB. des. subst.
  replace (colist_app pre (ccons (t, e) c')) with
      (colist_app (pre ++ [(t, e)]) c') in LEXEC_BEH.
  2: { rewrite colist_app_assoc. ss. }

  apply local_exec_beh_divbeh in LEXEC_BEH. des. clarify.

  unfold flatten_tes in FINITE_PART_EQ.
  rewrite <- flat_map_concat_map in FINITE_PART_EQ.

  assert (IN_FM: In (t, e) (flat_map flatten_te fe)).
  { rewrite FINITE_PART_EQ.
    apply in_or_app. left.
    apply in_or_app. right. ss. eauto. }

  apply in_flat_map in IN_FM.
  destruct IN_FM as [[t' es] [IN_FE IN_FLTN]].
  unfold flatten_te in IN_FLTN.
  apply in_map_iff in IN_FLTN. ss.
  des; clarify.

  exists es. split; ss.
  apply stream_In_or_app. eauto.
Qed.


Lemma event_in_beh_exec E
      tid t e beh (exec: exec_t E)
      (EXEC_BEH: exec_behav exec beh)
      (EINB: event_in_beh tid (t, e) beh)
: event_in_exec tid t e exec.
Proof.
  inv EINB.
  eapply Forall2_nth2 in EXEC_BEH; eauto. des.
  hexploit local_event_in_beh_exec; eauto. i. des.
  econs; eauto.
Qed.


Lemma local_event_in_exec_beh E
      t e es beh (exec: lexec_t E)
      (LEXEC_BEH: local_exec_behav exec beh)
      (EINB: stream_In (t, es) exec)
      (IN_ES: In e es)
: colist_In (t, e) beh.
Proof.
  eapply stream_In_app_ex in EINB. des. subst.
  revert LEXEC_BEH. revert beh.
  pattern pre. revert pre.
  apply list_str_ind. intro pre. i.

  punfold LEXEC_BEH. inv LEXEC_BEH.
  { apply inftau_lexec_pref_iff in EXEC_SILENT. des.
    punfold INFTAU. inv INFTAU. ss. clarify. }

  apply stream_app_eq_cases in LOCAL_EXEC_PREFIX.
  des; clarify.
  - destruct l1_r as [| hd tl]; ss.
    { exfalso. nia. }
    clarify.
    pclearbot.

    hexploit IH; eauto.
    { rewrite app_length. ss. nia. }
    intro CO_IN.
    eapply colist_In_or_app. right. eauto.
  - destruct l2_r as [| hd tl]; ss.
    + clarify.
      eapply colist_In_or_app. left.
      apply in_map_iff. ss.
      esplits; eauto.
    + clarify.
      exfalso.
      cut (es = []).
      { i. subst. ss. }

      eapply flatten_silent_local_trace_iff in TRACE_TAU.
      rewrite flatten_tes_app in TRACE_TAU.

      assert (FNIL: flatten_te (t, es) = []).
      { apply app_eq_nil in TRACE_TAU.
        destruct TRACE_TAU as [_ TAU].
        unfold flatten_tes in TAU. ss.
        apply app_eq_nil in TAU.
        destruct TAU as [TAU _]. ss. }

      unfold flatten_te in FNIL. ss.
      destruct es; ss.
Qed.

Lemma event_in_exec_beh E
      tid t e beh (exec: exec_t E)
      (EXEC_BEH: exec_behav exec beh)
      (EINB: event_in_exec tid t e exec)
: event_in_beh tid (t, e) beh.
Proof.
  inv EINB.
  eapply Forall2_nth1 in EXEC_BEH; eauto. des.
  hexploit local_event_in_exec_beh; eauto. i.
  econs; eauto.
Qed.


(* Section SYS_BEHAV_LEMMAS. *)
(*   Variable E: Type -> Type. *)
(*   Variable sys: @DSys.t E. *)

(*   Lemma exec_beh_div_exec *)
(*         (exec exec': exec_t E) *)
(*         (tr: list (list (nat * events E))) *)
(*         (beh: behav_t E) *)
(*         (EXEC_BEH: exec_behav exec beh) *)
(*         (EXEC_DIV: sapp_each_rel tr exec' exec) *)
(*                      (* Forall3 (fun a b c => stream_app a b = c) *) *)
(*                      (*       tr exec' exec) *) *)
(*     : exists beh', *)
(*       <<BEH_DIV: capp_each_rel (map flatten_tes tr) beh' beh>> /\ *)
(*                  (* Forall3 (fun a b c => colist_app *) *)
(*                  (*                      (flatten_tes a) b = c) *) *)
(*                  (*         tr beh' beh>> /\ *) *)
(*       <<EXEC_BEH': exec_behav exec' beh'>>. *)
(*   Proof. *)
(*     pose (len := length tr). *)
(*     unfold sapp_each_rel, capp_each_rel in *. *)

(*     cut (forall n (N_UBND: n < len), *)
(*             exists lbeh', *)
(*               (fun n lbeh' => *)
(*                  exists tr_n exec'_n exec_n lbeh, *)
(*                    nth_error tr n = Some tr_n /\ *)
(*                    nth_error exec' n = Some exec'_n /\ *)
(*                    nth_error exec n = Some exec_n /\ *)
(*                    nth_error beh n = Some lbeh /\ *)
(*                    colist_app (flatten_tes tr_n) lbeh' = lbeh /\ *)
(*                    local_exec_behav exec'_n lbeh') *)
(*                 n lbeh'). *)
(*     { intro AUX. *)
(*       apply exists_list in AUX. des. *)
(*       exists l. *)
(*       r in EXEC_BEH. *)
(*       hexploit Forall2_length; eauto. intro LEN_EQ_EB. *)
(*       hexploit Forall3_length; eauto. *)
(*       intros (LEN_EQ_EXEC' & LEN_EQ_EXEC). *)

(*       esplits. *)
(*       - apply Forall3_nth. intro n. *)
(*         rewrite Coqlib.list_map_nth. *)
(*         destruct (nth_error l n) eqn: L_N. *)
(*         2: { *)
(*           rewrite nth_error_None in L_N. *)
(*           rewrite nth_error_None2 by nia. *)
(*           rewrite nth_error_None2. *)
(*           2: { unfold lexec_t, lbehav_t in *. nia. } *)
(*           econs. *)
(*         } *)

(*         hexploit NTH_PROP; eauto. i. des. *)
(*         unfold lexec_t, lbehav_t in *. *)
(*         match goal with *)
(*         | H1: nth_error tr n = Some _, *)
(*               H2: nth_error beh n = Some _ |- _ => *)
(*           rewrite H1, H2 *)
(*         end. *)
(*         econs. ss. *)
(*       - apply Forall2_nth. intro n. *)
(*         unfold lexec_t, lbehav_t in *. *)
(*         destruct (nth_error l n) eqn: L_N. *)
(*         2: { *)
(*           rewrite nth_error_None in L_N. *)
(*           rewrite nth_error_None2 by nia. *)
(*           econs. *)
(*         } *)

(*         hexploit NTH_PROP; eauto. i. des. *)
(*         unfold lexec_t, lbehav_t in *. *)
(*         match goal with *)
(*         | H1: nth_error exec' n = Some _ |- _ => *)
(*           rewrite H1 *)
(*         end. *)
(*         econs. ss. *)
(*     } *)

(*     i. subst len. *)
(*     hexploit (nth_error_Some2 _ tr n); [nia|]. *)
(*     i. des. *)
(*     renames e1 NTH_EX into tr_n TR_N. *)
(*     eapply Forall3_nth1 in EXEC_DIV; eauto. i. des. *)
(*     renames e2 NTH2 NTH3 into exec'_n EXEC'_N EXEC_N. *)
(*     subst. *)

(*     r in EXEC_BEH. *)
(*     eapply Forall2_nth1 in EXEC_BEH; eauto. des. *)
(*     renames e2 NTH2 into lbeh LBEH. *)

(*     hexploit local_exec_beh_div; eauto. i. des. subst. *)
(*     esplits; eauto. *)
(*   Qed. *)


(*   Lemma local_exec_beh_div_behevt *)
(*         (lexec: lexec_t E) (lbeh: lbehav_t E) t e *)
(*         (LEXEC_BEH: local_exec_behav lexec lbeh) *)
(*         (IN_BEH_N: colist_In (t, e) lbeh) *)
(*     : exists tes te lexec' lbeh', *)
(*       <<LEXEC_DIV: lexec = stream_app tes (Cons te lexec')>> /\ *)
(*       <<LBEH_DIV: lbeh = colist_app (flatten_tes tes ++ flatten_te te) lbeh'>> /\ *)
(*       <<LEXEC_BEH': local_exec_behav lexec' lbeh'>> /\ *)
(*       <<TIMESTAMP_EQ: t = fst te>> /\ *)
(*       <<IN_TE: In e (snd te)>> *)
(*   . *)
(*   Proof. *)
(*     eapply colist_In_app_ex in IN_BEH_N. des. *)
(*     depgen c'. revert lexec lbeh LEXEC_BEH. *)
(*     pattern pre. revert pre. *)
(*     eapply list_str_ind. *)
(*     i. *)

(*     punfold LEXEC_BEH. inv LEXEC_BEH. *)
(*     { destruct l; ss. } *)

(*     pclearbot. *)

(*     replace (colist_app l (ccons (t, e) c')) with *)
(*         (colist_app (l ++ [(t, e)]) c') in *. *)
(*     2: { rewrite colist_app_assoc. ss. } *)

(*     assert (FLTN_TAU_NIL: flatten_tes tr_tau = []). *)
(*     { apply flatten_silent_local_trace_iff. auto. } *)

(*     eapply colist_app_eq_cases in BEHAVIOR. des. *)
(*     - hexploit des_snoc; eauto. i. des. *)
(*       rename l_h into l1_r'. subst. *)
(*       unfold snoc in *. *)
(*       rewrite app_assoc in L1_DIV. *)
(*       apply snoc_eq_inv in L1_DIV. des. subst. *)

(*       hexploit (IH l1_r'); eauto. *)
(*       { destruct es; ss. *)
(*         rewrite app_length. *)
(*         rewrite map_length. nia. } *)
(*       { rewrite colist_app_assoc. ss. } *)
(*       i. des. *)

(*       esplits; try apply TIMESTAMP_EQ; eauto. *)
(*       + instantiate (1:= tr_tau ++ [(ts, es)] ++ tes). *)
(*         ss. clarify. *)
(*         rewrite stream_app_assoc. ss. *)
(*       + ss. clarify. *)
(*         rewrite <- app_assoc. *)
(*         rewrite colist_app_assoc. *)
(*         rewrite LBEH_DIV. *)

(*         unfold flatten_tes. *)
(*         rewrite map_app. *)
(*         rewrite concat_app. s. *)
(*         rewrite <- app_assoc. *)
(*         rewrite colist_app_assoc with *)
(*             (l1 := concat (map flatten_te tr_tau)). *)

(*         fold (flatten_tes tr_tau). *)
(*         rewrite FLTN_TAU_NIL. ss. *)
(*         repeat rewrite colist_app_assoc. ss. *)

(*     - subst. *)
(*       exists (tr_tau). exists (ts, es). exists lexec'. exists beh'. *)
(*       splits; eauto. *)
(*       + rewrite L2_DIV. *)
(*         repeat rewrite colist_app_assoc. *)
(*         rewrite FLTN_TAU_NIL. ss. *)
(*       + clear - L2_DIV. *)
(*         depgen l. induction es as [| hd tl IH]; i; ss. *)
(*         { destruct l; ss. } *)
(*         unfold flatten_te in *. ss. *)
(*         destruct l as [| hd_l tl_l]; ss; clarify. *)
(*         hexploit IH; eauto. *)
(*       + clear - L2_DIV. *)
(*         depgen l. induction es as [| hd tl IH]; i; ss. *)
(*         { destruct l; ss. } *)
(*         unfold flatten_te in *. ss. *)
(*         destruct l as [| hd_l tl_l]; ss; clarify; eauto. *)
(*   Qed. *)

(*   Lemma safe_exec_beh_impl_msteps *)
(*         exec (beh: behav_t E) st *)
(*         (SAFE: DSys.safe_state st) *)
(*         (EXEC_STATE: DSys.exec_state sys st exec) *)
(*         (EXEC_BEH: exec_behav exec beh) *)
(*     : forall n, *)
(*       exists tr st' exec' beh', *)
(*         <<MSTEPS: msteps sys n st tr st'>> /\ *)
(*         <<SAFE': DSys.safe_state st'>> /\ *)
(*         <<EXEC_STATE': DSys.exec_state sys st' exec'>> /\ *)
(*         <<EXEC_BEH': exec_behav exec' beh'>> /\ *)
(*         <<EXEC_DIV: sapp_each_rel tr exec' exec>> /\ *)
(*         <<BEH_DIV: capp_each_rel (map flatten_tes tr) beh' beh>>. *)
(*   Proof. *)
(*     i. hexploit safe_exec_impl_msteps; eauto. i. des. *)
(*     hexploit exec_beh_div_exec; eauto. i. des. *)
(*     esplits; eauto. *)
(*   Qed. *)


(*   Lemma safe_exec_beh_div_behevt *)
(*         exec (beh: behav_t E) st *)
(*         n t e *)
(*         (SAFE_ST: DSys.safe_state st) *)
(*         (EXEC_STATE: DSys.exec_state sys st exec) *)
(*         (EXEC_BEH: exec_behav exec beh) *)
(*         (EVT_IN_BEH: event_in_beh n (t, e) beh) *)
(*     : exists scnt str1 st1 exec1 beh1 *)
(*         str2 st' exec' beh' *)
(*         se se_n, *)
(*       <<MSTEPS1: msteps sys scnt st str1 st1>> /\ *)
(*       <<EXEC_DIV1: sapp_each_rel str1 exec1 exec>> /\ *)
(*       <<BEH_DIV1: capp_each_rel (map flatten_tes str1) beh1 beh>> /\ *)

(*       (* <<STEP1: DSys.step sys st1 se_r st'>> /\ *) *)
(*       (* <<FILTER_NB: DSys.filter_nb_sysstep se_r = Some se>> /\ *) *)
(*       (* <<EXEC2_DIV2: Cons_each_rel se exec' exec1>> /\ *) *)

(*       <<SAFE_ST1: DSys.safe_state st1>> /\ *)
(*       <<EXEC_STATE1: DSys.exec_state sys st1 exec1>> /\ *)
(*       <<EXEC_BEH1: exec_behav exec1 beh1>> /\ *)

(*       <<MSTEPS2: msteps sys 1 st1 str2 st'>> /\ *)
(*       <<EXEC_DIV2: sapp_each_rel str2 exec' exec1>> /\ *)
(*       <<BEH_DIV2: capp_each_rel (map flatten_tes str2) beh' beh1>> /\ *)

(*       <<SAFE_ST': DSys.safe_state st'>> /\ *)
(*       <<EXEC_STATE': DSys.exec_state sys st' exec'>> /\ *)
(*       <<EXEC_BEH': exec_behav exec' beh'>> /\ *)

(*       <<STR2_EQ: str2 = map (fun x => [x]) se>> /\ *)
(*       <<SYSTEM_EVENT_N: nth_error se n = Some se_n>> /\ *)
(*       <<TIMESTAMP_EQ: fst se_n = t>> /\ *)
(*       <<EVENT_EXISTS: In e (snd se_n)>> *)
(*   . *)
(*   Proof. *)
(*     unfold sapp_each_rel, capp_each_rel in *. *)
(*     inv EVT_IN_BEH. *)
(*     r in EXEC_BEH. *)
(*     hexploit Forall2_nth2; eauto. i. des. *)
(*     renames e1 NTH1 P_FA into exec_n EXEC_N LEXEC_BEH. *)
(*     hexploit local_exec_beh_div_behevt; eauto. i. des. *)

(*     hexploit safe_exec_beh_impl_msteps; eauto. *)
(*     instantiate (1:= length tes). i. des. *)

(*     renames st' exec' beh' into st1 exec1 beh1. *)
(*     renames SAFE' EXEC_STATE' EXEC_BEH' into *)
(*             SAFE_ST1 EXEC_STATE1 EXEC_BEH1. *)
(*     renames MSTEPS EXEC_DIV BEH_DIV into *)
(*             MSTEPS1 EXEC_DIV1 BEH_DIV1. *)
(*     rename tr into tr1. *)

(*     hexploit (safe_exec_beh_impl_msteps *)
(*                 exec1 beh1 st1 *)
(*                 SAFE_ST1 EXEC_STATE1 EXEC_BEH1 1); eauto. *)
(*     i. des. *)
(*     inv MSTEPS. inv MSTEPS_REST. *)

(*     assert (TR_EQ: tr = List.map (fun x => [x]) es1). *)
(*     { r in CONS_EVENTS. *)
(*       apply nth_eq_list_eq. intro k. *)
(*       rewrite Forall3_nth in CONS_EVENTS. *)
(*       rewrite Coqlib.list_map_nth. *)

(*       specialize (CONS_EVENTS k). *)
(*       destruct (nth_error es1 k) eqn: ES1_K. *)
(*       2: { inv CONS_EVENTS. ss. } *)
(*       inv CONS_EVENTS. ss. *)
(*       hexploit nth_error_In. *)
(*       { symmetry. *)
(*         match goal with *)
(*         | H: _ = nth_error (repeat _ _) _ |- _ => apply H *)
(*         end. } *)
(*       intro IN_RPT. apply repeat_spec in IN_RPT. *)
(*       subst. ss. *)
(*     } *)
(*     clear CONS_EVENTS. *)

(*     unfold sapp_each_rel, capp_each_rel in *. *)
(*     esplits; eauto. *)
(*     - econs; eauto. *)
(*       { econs; eauto. } *)
(*       subst tr. *)

(*       apply Forall3_nth. intro k. *)
(*       rewrite Coqlib.list_map_nth. *)
(*       apply DSys_filter_nb_sysstep_inv in FILTER_NB. *)
(*       hexploit Forall2_length; try apply FILTER_NB. *)
(*       intro LEN_EQ_AUX. *)

(*       hexploit (DSys.step_prsv_num_sites sys); eauto. i. des. *)

(*       destruct (nth_error es1 k) eqn: ES1_K; ss. *)
(*       2: { *)
(*         apply nth_error_None in ES1_K. *)
(*         rewrite nth_error_None2. *)
(*         2: { rewrite repeat_length. nia. } *)
(*         econs. *)
(*       } *)
(*       rewrite repeat_nth_error_Some. *)
(*       2: { eapply nth_error_Some1' in ES1_K. nia. } *)
(*       econs. ss. *)

(*     - eapply Forall3_nth3 in EXEC_DIV1; eauto. *)
(*       des. *)
(*       renames e1 e2 into tr1_n exec1_n. *)
(*       renames NTH1 NTH2 into TR1_N EXEC1_N. *)

(*       apply stream_app_inv_eqlen in P_FA. *)
(*       2: { *)
(*         eapply msteps_trace_row_length in MSTEPS1. *)
(*         hexploit Forall_nth1; try apply MSTEPS1; eauto. *)
(*       } *)
(*       des; subst. *)

(*       eapply Forall3_nth3 in EXEC_DIV; eauto. i. des. *)
(*       apply map_nth_error_iff in NTH1. *)
(*       des. subst. ss. clarify. *)
(*   Qed. *)

(* End SYS_BEHAV_LEMMAS. *)





Lemma event_in_exec_not_in_tr E
      (exec exec': exec_t E) tr
      tid t e
      (IN_EXEC: event_in_exec tid t e exec)
      (NOT_IN_TR: ~ event_in_tr tid t e tr)
      (EXEC_DIV: sapp_each_rel tr exec' exec)
  : event_in_exec tid t e exec'.
Proof.
  inv IN_EXEC.
  eapply Forall3_nth3 in EXEC_DIV; eauto. des.
  subst.

  econs; eauto.
  apply stream_In_app_or in EVTS_AT_T.
  des; ss.
  exfalso.
  apply NOT_IN_TR.
  econs; eauto.
Qed.

Lemma event_in_tr_exec E
      (exec exec': exec_t E) tr
      tid t e
      (E_IN_TR: event_in_tr tid t e tr)
      (EXEC_DIV: sapp_each_rel tr exec' exec)
  : event_in_exec tid t e exec.
Proof.
  inv E_IN_TR.
  eapply Forall3_nth1 in EXEC_DIV; eauto. des.
  subst.
  econs; eauto.
  apply stream_In_or_app. eauto.
Qed.

Lemma event_in_later_exec E
      (exec exec': exec_t E) tr
      tid t e
      (E_IN_TR: event_in_exec tid t e exec')
      (EXEC_DIV: sapp_each_rel tr exec' exec)
  : event_in_exec tid t e exec.
Proof.
  inv E_IN_TR.
  eapply Forall3_nth2 in EXEC_DIV; eauto. des.
  subst.
  econs; eauto.
  apply stream_In_or_app. eauto.
Qed.


Definition nsteps_to_sync (prd: nat) (tm: nat): nat :=
  if tm mod prd =? 0 then 0 else prd - tm mod prd.

Lemma nsteps_to_sync_spec
      prd t nst
      (PERIOD_POS: prd <> 0)
      (NEXT_SYNC: nst = nsteps_to_sync prd t)
  : Nat.divide prd (t + nst) /\
    forall nst', nst' < nst -> ~ Nat.divide prd (t + nst').
Proof.
  unfold nsteps_to_sync in NEXT_SYNC.
  destruct (Nat.eqb_spec (t mod prd) 0).
  - subst nst.
    rewrite Nat.add_0_r.
    split.
    + apply Nat.mod_divide; ss.
    + i. nia.
  - subst nst.
    split.
    + replace (t + (prd - t mod prd)) with
          (t - t mod prd + prd).
      2: { cut (t mod prd <= t /\ t mod prd < prd).
           { nia. }
           split.
           - apply Nat.mod_le. ss.
           - apply Nat.mod_upper_bound. ss.
      }
      apply Nat.divide_add_r.
      2: { eauto with app_pf. }
      replace (t - t mod prd) with (prd * (t / prd)).
      2: {
        hexploit (Nat.mod_eq t prd).
        { nia. }
        i. nia.
      }
      eauto with app_pf.
    + intros nst' NST' DIV.
      r in DIV. des.

      assert (AUX1: (nst' + t mod prd) mod prd = 0).
      { cut ((t + nst') mod prd = 0).
        { rewrite Nat.add_mod by ss.
          intro MOD_MOD.
          rewrite Nat.add_mod_idemp_r in MOD_MOD by ss.
          rewrite Nat.add_comm.
          ss. }
        rewrite DIV.
        apply Nat.mod_mul. ss.
      }
      assert (AUX2: nst' + t mod prd < prd) by nia.
      clear z DIV.

      cut (nst' + t mod prd = 0).
      { nia. }
      apply Nat.mod_divide in AUX1; ss.
      r in AUX1. des.
      destruct z; ss.
      nia.
Qed.


Lemma nsteps_to_sync_inverse
      prd t nst
      (PRD_NZERO: prd <> 0)
      (DIV: Nat.divide prd (t + nst))
      (NDIV: forall nst', nst' < nst -> ~ Nat.divide prd (t + nst'))
  : nst = nsteps_to_sync prd t.
Proof.
  remember (nsteps_to_sync prd t) as nst'.
  hexploit (nsteps_to_sync_spec prd t nst'); eauto.
  intros (DIV' & NDIV').
  destruct (lt_eq_lt_dec nst nst') as [[A | B] | C]; ss.
  - exfalso.
    hexploit NDIV'; eauto.
  - exfalso.
    hexploit NDIV; eauto.
Qed.


Lemma nsteps_to_sync_adv
      prd t nst
      (PRD_NZERO: prd <> 0)
      (NEXT_SYNC: nst = nsteps_to_sync prd t)
  : match nst with
    | O => Nat.divide prd t
    | S n' => nsteps_to_sync prd (S t) = n'
    end.
Proof.
  hexploit nsteps_to_sync_spec; eauto.
  clear NEXT_SYNC.
  intros (DIV & NDIV).
  destruct nst as [| nst'].
  - rewrite Nat.add_0_r in DIV. ss.
  - symmetry.
    apply nsteps_to_sync_inverse.
    + ss.
    + rewrite <- plus_n_Sm in DIV. ss.
    + ii. eapply (NDIV (S nst'0)); eauto.
      { nia. }
      rewrite <- plus_n_Sm. ss.
Qed.


Fixpoint empty_ltrace {E} (t_s: Z) (nst: nat)
  : list (Z * events E) :=
  match nst with
  | O => []
  | S nst' => (t_s, []) :: empty_ltrace (1 + t_s) nst'
  end.

Definition empty_trace {E} (t_s: Z) (ns: nat) (nst: nat)
  : list (list (Z * events E)) :=
  repeat (empty_ltrace t_s nst) ns.

Lemma empty_trace_empty E
      t ns nst
  : Forall (Forall (fun x : Z * list (event E) => snd x = []))
           (empty_trace t ns nst).
Proof.
  unfold empty_trace.
  apply Forall_forall. intros l IN.
  apply Forall_forall.
  apply repeat_spec in IN. subst.
  intros [tm es] IN. ss.

  depgen t.
  induction nst; i; ss.
  des; ss.
  - clarify.
  - eapply IHnst. eauto.
Qed.


Lemma sapp_each_rel_base A
      (s: list (stream A)) n
      (LEN: length s = n)
  : sapp_each_rel (repeat [] n) s s.
Proof.
  r. apply Forall3_nth. intro m.
  destruct (lt_ge_dec m n).
  - hexploit (nth_error_Some2 _ s m); eauto.
    { nia. }
    i. des.
    rewrite NTH_EX.
    rewrite repeat_nth_error_Some by nia.
    econs. ss.
  - rewrite nth_error_None2.
    2: { rewrite repeat_length. ss. }
    rewrite nth_error_None2 by nia.
    econs.
Qed.

Definition app_each {A} (l1 l2 l: list (list A)): Prop :=
  Forall3 (fun a b c => a ++ b = c) l1 l2 l.


Lemma event_in_tr_div E
      tid t e
      (tr tr1 tr2: list (list (Z * events E)))
      (IN_TR: event_in_tr tid t e tr)
      (TR_DIV: app_each tr1 tr2 tr)
  : event_in_tr tid t e tr1 \/
    event_in_tr tid t e tr2.
Proof.
  inv IN_TR.
  eapply Forall3_nth3 in TR_DIV; eauto. des.
  subst.
  eapply in_app_or in EVTS_AT_T. des.
  - left. econs; eauto.
  - right. econs; eauto.
Qed.


(* Lemma sapp_each_rel_assoc A *)
(*       (s s1 s2: list (stream A)) *)
(*       l1 l2 *)
(*       (SAPP1: sapp_each_rel l1 s1 s) *)
(*       (SAPP2: sapp_each_rel l2 s2 s1) *)
(*   : exists l, *)
(*     app_each l1 l2 l /\ *)
(*     sapp_each_rel l s2 s. *)
(* Proof. *)
(*   cut (forall n (N_UBND: n < length s), *)
(*           exists (l: list A), *)
(*             (fun n l => *)
(*                exists l1_n l2_n, *)
(*                  nth_error l1 n = Some l1_n /\ *)
(*                  nth_error l2 n = Some l2_n /\ *)
(*                  l1_n ++ l2_n = l) *)
(*               n l). *)
(*   { intro AUX. eapply exists_list in AUX. des. *)
(*     exists l. *)

(*     split. *)
(*     - apply Forall3_nth. i. *)
(*       destruct (nth_error l n) eqn: L_N. *)
(*       2: { *)
(*         apply Forall3_length in SAPP1. *)
(*         apply Forall3_length in SAPP2. *)
(*         des. *)
(*         eapply nth_error_None in L_N. *)

(*         rewrite nth_error_None2 by nia. *)
(*         rewrite nth_error_None2 by nia. *)
(*         econs. *)
(*       } *)
(*       hexploit NTH_PROP; eauto. i. des. *)
(*       subst. *)
(*       match goal with *)
(*       | H1: nth_error l1 n = _, *)
(*             H2: nth_error l2 n = _ |- _ => rewrite H1, H2 *)
(*       end. *)
(*       econs. ss. *)
(*     - apply Forall3_nth. i. *)
(*       destruct (nth_error l n) eqn: L_N. *)
(*       2: { *)
(*         apply Forall3_length in SAPP1. *)
(*         apply Forall3_length in SAPP2. *)
(*         des. *)
(*         eapply nth_error_None in L_N. *)

(*         rewrite nth_error_None2 by nia. *)
(*         rewrite nth_error_None2 by nia. *)
(*         econs. *)
(*       } *)
(*       hexploit NTH_PROP; eauto. i. des. *)
(*       subst. *)
(*       eapply Forall3_nth1 in SAPP1; eauto. *)
(*       eapply Forall3_nth1 in SAPP2; eauto. *)
(*       des. clarify. *)
(*       rewrite NTH1, NTH2. *)
(*       econs. rewrite stream_app_assoc. ss. *)
(*   } *)

(*   i. *)
(*   hexploit (nth_error_Some2 _ s n); eauto. i. des. *)
(*   eapply Forall3_nth3 in SAPP1; eauto. i. des. *)
(*   eapply Forall3_nth3 in SAPP2; eauto. i. des. *)
(*   esplits; eauto. *)
(* Qed. *)

Lemma app_each_eq A
      (l1 l2 l l': list (list A))
      (APP_EACH1: app_each l1 l2 l)
      (APP_EACH2: app_each l1 l2 l')
  : l = l'.
Proof.
  apply nth_eq_list_eq. intro n.
  destruct (nth_error l n) eqn: L_N.
  - eapply Forall3_nth3 in APP_EACH1; eauto. des.
    eapply Forall3_nth2 in APP_EACH2; eauto. des.
    clarify.
  - apply Forall3_length in APP_EACH1.
    apply Forall3_length in APP_EACH2.
    des.
    eapply nth_error_None in L_N.
    rewrite nth_error_None2 by nia. ss.
Qed.

Lemma sapp_each_rel_assoc A
      (s s1 s2: list (stream A))
      (l l1 l2: list (list A))
      (SAPP1: sapp_each_rel l1 s1 s)
      (SAPP2: sapp_each_rel l2 s2 s1)
      (APP_EACH: app_each l1 l2 l)
  : sapp_each_rel l s2 s.
Proof.
  unfold sapp_each_rel, app_each in *.
  apply Forall3_nth. i.
  destruct (nth_error l n) eqn: L_N.
  2: {
    apply Forall3_length in SAPP1.
    apply Forall3_length in SAPP2.
    apply Forall3_length in APP_EACH.
    des.

    eapply nth_error_None in L_N.
    rewrite nth_error_None2 by nia.
    rewrite nth_error_None2 by nia.
    econs.
  }

  eapply Forall3_nth3 in APP_EACH; eauto. des.
  eapply Forall3_nth1 in SAPP1; eauto. des.
  eapply Forall3_nth1 in SAPP2; eauto. des.
  clarify.
  match goal with
  | H1: nth_error s2 n = _,
        H2: nth_error s n = _ |- _ => rewrite H1, H2
  end.
  econs.
  rewrite stream_app_assoc. ss.
Qed.



(* Lemma ind_msteps E *)
(*       (dsys: @DSys.t E) *)
(*       st exec prd *)
(*       (P: nat -> DSys.state dsys -> *)
(*           list (list (nat * events sysE)) -> exec_t E -> Prop) *)
(*       (SAFE_ST: DSys.safe_state st) *)
(*       (EXEC_ST: DSys.exec_state dsys st exec) *)
(*       (P_BASE: P 0 st (repeat [] (DSys.num_sites _ st)) exec) *)
(*       (P_IND: forall k1 st1 exec1 tr1 st2 exec2 *)
(*                 (SAFE_ST: DSys.safe_state st1) *)
(*                 (EXEC_ST: DSys.exec_state _ st1 exec1) *)
(*                 (P_HOLDS: P k1 st1 tr1 exec1) *)
(*                 (MSTEPS: msteps dsys prd st1 tr1 st2) *)
(*                 (EXEC_DIV: sapp_each_rel tr1 exec2 exec1) *)
(*         , *)
(*           P (S k1) st2 exec2) *)
(*   : forall k, exists tr st' exec', *)
(*       msteps dsys (k * prd) st tr st' /\ *)
(*       sapp_each_rel tr exec' exec /\ *)
(*       DSys.safe_state st' /\ *)
(*       DSys.exec_state _ st' exec' /\ *)
(*       P k st' exec'. *)
(* Proof. *)
(*   intro k. *)
(*   induction k as [| k' IH]. *)
(*   { exists (repeat [] (DSys.num_sites _ st)). *)
(*     exists st, exec. *)
(*     esplits; eauto. *)
(*     - rewrite Nat.mul_0_l. *)
(*       econs. ss. *)
(*     - hexploit exec_state_len; eauto. *)
(*       clear. intro LEN_EQ. *)
(*       apply sapp_each_rel_base. ss. *)
(*   } *)

(*   destruct IH as (tr1 & st1 & exec1 & *)
(*                   MSTEPS1 & SAPP1 & SAFE_ST1 & EXEC_ST1 & P1). *)
(*   hexploit (safe_exec_impl_msteps *)
(*               _ _ _ _ SAFE_ST1 EXEC_ST1 prd). *)
(*   i. des. *)

(*   hexploit msteps_concat. *)
(*   { eapply MSTEPS1. } *)
(*   { eapply MSTEPS. } *)
(*   i. des. *)

(*   exists es, st', exec'. *)
(*   splits; eauto. *)
(*   { replace (S k' * prd) with (k' * prd + prd) by nia. *)
(*     ss. } *)

(*   hexploit (sapp_each_rel_assoc _ exec exec1 exec'); eauto. *)
(*   i. des. *)

(*   assert (l = es). *)
(*   { eapply app_each_eq; eauto. } *)
(*   subst l. ss. *)
(* Qed. *)



Section SYNC_SYS_LEMMAS.

  Variable E: Type -> Type.
  Variable M: Set.
  Variable sys: @SyncSys.t E M.
  Variable tm_init: nat.
  Hypothesis PRD_NZERO: SyncSys.period sys <> 0.
  (* Variable sys': @DSys.t E. *)
  Let dsys := SyncSys.as_dsys sys tm_init.
  Let period: nat := SyncSys.period sys.

  (* Lemma sync_exec_time_order *)
  (*       (st: @SyncSys.state E M) exec *)
  (*       (SAFE: @DSys.safe_state _ dsys st) *)
  (*       (EXEC_STATE: DSys.exec_state dsys st exec) *)
  (*   : forall (n k: nat) exec_n t e, *)
  (*       nth_error exec n = Some exec_n -> *)
  (*       Str_nth k exec_n = (t, e) -> *)
  (*       t = SyncSys.time st + k. *)
  (* Proof. *)
  (*   intros n k exec_n t e EXEC_N STR_N. *)
  (*   depgen exec. depgen exec_n. depgen st. revert t. *)
  (*   induction k as [| k' IH]; i; ss. *)
  (*   { destruct exec_n as [exec1 exec_n']; ss. *)
  (*     unfold Str_nth in STR_N. ss. subst. *)
  (*     rewrite Nat.add_0_r. *)

  (*     punfold SAFE. inv SAFE. *)
  (*     punfold EXEC_STATE. inv EXEC_STATE. *)
  (*     { exfalso. eauto. } *)
  (*     clear PROGRESS. *)
  (*     ss. *)

  (*     unfold Cons_each_rel in BEH_CONS. *)
  (*     eapply Forall3_nth3 in BEH_CONS; eauto. des. *)
  (*     destruct e1 as [tsp1 evt1]. *)
  (*     renames NTH1 NTH2 into E1 EXEC'_N. *)
  (*     r in P_FA. clarify. *)

  (*     eapply FMSim_Switch.DSys_filter_nb_sysstep_inv *)
  (*       in FILTER_NOBEH. *)
  (*     eapply Forall2_nth2 in FILTER_NOBEH; eauto. *)

  (*     des. *)
  (*     renames NTH1 P_FA into ES_N FILTER_LOC. *)
  (*     destruct e1 as [t' evt1_r]. *)

  (*     apply filter_nb_localstep_inv in FILTER_LOC. ss. *)
  (*     des; subst. *)

  (*     inv STEP; ss. *)
  (*     - eapply nth_error_In in ES_N. *)
  (*       apply repeat_spec in ES_N. clarify. *)
  (*     - rewrite map_nth_error_iff in ES_N. des. clarify. *)
  (*   } *)

  (*   punfold SAFE. inv SAFE. *)
  (*   punfold EXEC_STATE. inv EXEC_STATE. *)
  (*   { exfalso. eauto. } *)
  (*   clear PROGRESS. ss. *)

  (*   r in BEH_CONS. *)
  (*   eapply Forall3_nth3 in BEH_CONS; eauto. i. des. *)
  (*   renames e1 e2 into tes1 exec'_n. *)
  (*   renames NTH1 NTH2 into TES1 EXEC'_N. *)
  (*   r in P_FA. subst. *)

  (*   replace (SyncSys.time st + S k') with *)
  (*       (SyncSys.time st' + k'). *)
  (*   2: { inv STEP; ss; nia. } *)
  (*   eapply IH. *)
  (*   { hexploit SAFE_NXT; eauto. *)
  (*     { congruence. } *)
  (*     clear. i. pclearbot. ss. } *)
  (*   { unfold Str_nth in *. ss. eauto. } *)
  (*   { r in EXEC_REST. des; ss. eauto. } *)
  (*   ss. *)
  (* Qed. *)

  Lemma sync_exec_time_props
        (tm_lb: nat)
    : forall (st: @SyncSys.state E M)
        (exec: exec_t E)
        (SAFE: @DSys.safe_state _ dsys st)
        (EXEC_STATE: DSys.exec_state dsys st exec)
        (TIME: (tm_lb <= SyncSys.time st))
    ,
      Forall (Forall_stream (fun x: Z * events _ =>
                                 (* Z.of_nat ts_n = fst x /\ *)
                                 (Z.of_nat tm_lb <= fst x)%Z /\
                                 (snd x = [] \/
                                  Z.divide (Z.of_nat (SyncSys.period sys)) (fst x))))
             exec.
  Proof.
    i.
    apply Forall_forall. intros lexec LEXEC_IN.
    revert_until st. revert st.
    pcofix CIH. i.

    punfold SAFE. inv SAFE.
    punfold EXEC_STATE. inv EXEC_STATE.
    { exfalso. eauto. }
    r in EXEC_REST. des; ss.

    r in BEH_CONS.
    eapply In_nth_error in LEXEC_IN. des.
    eapply Forall3_nth3 in BEH_CONS; eauto.
    unfold Cons_rel in BEH_CONS.
    des.
    destruct e1 as [tsp1 es1].
    renames e2 NTH1 NTH2 into exec'_n ES1 EXEC'_N. subst.

    assert (<<TSP1_UBND: (Z.of_nat tm_lb <= tsp1)%Z>> /\
            <<TSP_DIVIDE: es1 = [] \/ Z.divide (Z.of_nat (SyncSys.period sys)) tsp1>>).
    { eapply DSys_filter_nb_sysstep_inv in FILTER_NOBEH.
      eapply Forall2_nth2 in FILTER_NOBEH; eauto.
      des.
      destruct e1 as [tsp1' es1_r].
      renames NTH1 P_FA into ES_N FILTER_NB_LOC.

      inv STEP.
      - apply nth_error_In in ES_N.
        apply repeat_spec in ES_N. clarify.
        unfold DSys.filter_nb_localstep in *.
        ss. clarify.
        splits.
        + nia.
        + left. ss.
      - unfold DSys.filter_nb_localstep in *. ss.
        destruct (deopt_list (map DSys.filter_nb1 es1_r))
          as [es_f|]; ss.
        clarify.

        apply map_nth_error_iff in ES_N. des. clarify.
        esplits; eauto.
        + nia.
        + right.
          apply Nat2Z_inj_divide. ss.
    }
    nbdes.

    pfold. econs.
    { eauto. }
    right.
    eapply CIH.
    { hexploit SAFE_NXT; eauto.
      { congruence. }
      clear. i. pclearbot. eauto. }
    { eauto. }
    { inv STEP.
      - ss. nia.
      - ss. nia. }

    eapply nth_error_In; eauto.
  Qed.


  Lemma event_in_exec_must_in_tr
        (exec exec': exec_t E) tr
        tid (t:Z) e st'
        (IN_EXEC: event_in_exec tid t e exec)
        (EXEC_DIV: sapp_each_rel tr exec' exec)
        (SAFE_STATE: DSys.safe_state st')
        (EXEC_STATE: DSys.exec_state dsys st' exec')
        (TIME_BEFORE: (t < Z.of_nat (SyncSys.time st'))%Z)
    : event_in_tr tid t e tr.
  Proof.
    inv IN_EXEC.
    eapply Forall3_nth3 in EXEC_DIV; eauto. des. subst.
    apply stream_In_app_or in EVTS_AT_T. des.
    { econs; eauto. }

    exfalso.
    eapply sync_exec_time_props in SAFE_STATE; eauto.
    eapply Forall_nth1 in SAFE_STATE; eauto.

    eapply Forall_stream_forall in SAFE_STATE; eauto.
    des; ss.
    - subst. ss.
    - nia.
  Qed.


  Lemma sync_event_in_exec_synchronous
    : forall (st: @SyncSys.state E M)
        (exec: exec_t E)
        tid t e
        (SAFE: @DSys.safe_state _ dsys st)
        (EXEC_STATE: DSys.exec_state dsys st exec)
        (IN_EXEC: event_in_exec tid t e exec)
    ,
      Z.divide (Z.of_nat period) t.
  Proof.
    i.
    inv IN_EXEC.
    hexploit sync_exec_time_props; eauto.
    intro AUX.
    eapply Forall_nth1 in AUX; eauto.
    eapply stream_In_app_ex in EVTS_AT_T. des. subst.
    eapply Forall_stream_app_div in AUX. des.
    punfold FA_STR. inv FA_STR. ss.
    des.
    - exfalso. subst. ss.
    - ss.
  Qed.


  Lemma sync_msteps_time
        scnt st tr st' tm
        (TIME: tm = SyncSys.time st)
        (MSTEPS: msteps dsys scnt st tr st')
    : <<TIME': SyncSys.time st' = tm + scnt>> /\
      <<TRACE_TIME: Forall (Forall (fun te => Z.of_nat tm <= fst te < Z.of_nat (tm + scnt))%Z) tr>>.
  Proof.
    depgen tm.
    induction MSTEPS; i; ss.
    { rewrite Nat.add_0_r. esplits; eauto.
      subst es.
      apply Forall_forall. intros x IN.
      apply repeat_spec in IN. subst x.
      econs. }

    hexploit IHMSTEPS; eauto. i. des.
    clear IHMSTEPS.

    inv STEP; ss.
    - esplits; eauto.
      + nia.
      + apply Forall_nth.
        intro k.
        destruct (nth_error tr k) eqn: TR_K; ss.
        * eapply Forall3_nth3 in CONS_EVENTS; eauto.
          des. subst.
          renames e1 e2 into es1_k tr2_k.
          renames NTH1 NTH2 into ES1_K TR2_K.
          econs.
          2: {
            eapply Forall_nth1 in TRACE_TIME; eauto.
            eapply Forall_impl; eauto.
            s. i. nia.
          }
          apply DSys_filter_nb_sysstep_inv in FILTER_NB.
          eapply Forall2_nth2 in FILTER_NB; eauto. des.
          eapply nth_error_In in NTH1.
          apply repeat_spec in NTH1. subst e1.
          unfold DSys.filter_nb_localstep in P_FA.
          ss. clarify. ss. nia.

    - esplits; eauto.
      + nia.
      + apply Forall_nth.
        intro k.
        destruct (nth_error tr k) eqn: TR_K; ss.
        * eapply Forall3_nth3 in CONS_EVENTS; eauto.
          des. subst.
          renames e1 e2 into es1_k tr2_k.
          renames NTH1 NTH2 into ES1_K TR2_K.
          econs.
          2: {
            eapply Forall_nth1 in TRACE_TIME; eauto.
            eapply Forall_impl; eauto.
            s. i. nia.
          }
          apply DSys_filter_nb_sysstep_inv in FILTER_NB.
          eapply Forall2_nth2 in FILTER_NB; eauto. des.

          eapply map_nth_error_iff in NTH1. des. clarify.
          apply DSys_filter_nb_localstep_inv in P_FA. des.
          ss. nia.
  Qed.

  Lemma sync_msteps_system_time_adv
        scnt st tr st' tm
        (TIME: tm = SyncSys.time st)
        (MSTEPS: msteps dsys scnt st tr st')
    : <<TIME': SyncSys.time st' = tm + scnt>>.
  Proof.
    hexploit sync_msteps_time; eauto. i. des. ss.
  Qed.


  Lemma sync_msteps_trace_time_range
        scnt st tr st'
        tid tr_n t es
        (MSTEP: msteps dsys scnt st tr st')
        (TR_N: nth_error tr tid = Some tr_n)
        (COMPL: In (t, es) tr_n)
    : (Z.of_nat (SyncSys.time st) <= t < Z.of_nat (SyncSys.time st'))%Z.
  Proof.
    hexploit sync_msteps_time; eauto. i. des.
    eapply Forall_nth1 in TRACE_TIME; eauto.
    eapply In_nth_error in COMPL. des.
    eapply Forall_nth1 in TRACE_TIME; eauto.
    ss. nia.
  Qed.


  Lemma sync_nonsync_msteps_det
        st tm nst tr st_f
        (SYS_TIME: SyncSys.time st = tm)
        (* (NONSYNC: ~ Nat.divide period tm) *)
        (NST: nst = nsteps_to_sync period (SyncSys.time st))
        (EMPTY_TRACE: tr = empty_trace
                             (Z.of_nat tm) (SyncSys.num_sites st) nst)
        (ST_F: st_f = SyncSys.State (tm + nst)
                                    (SyncSys.node_states st))
    : <<PROG: msteps dsys nst st tr st_f>> /\
      <<DET: forall tr' st_f'
               (MSTEPS': msteps dsys nst st tr' st_f'),
        tr' = tr /\ st_f' = st_f>>.
  Proof.
    depgen tm. depgen st. depgen tr.
    induction nst as [| nst']; i; ss.
    - subst.
      rewrite Nat.add_0_r.
      split.
      { destruct st. ss. econs; ss. }
      r. i. inv MSTEPS'. ss.
      split; ss.
      destruct st_f'; ss.

    - destruct st; ss. subst.

      assert (TM_NONSYNC: ~ Nat.divide period tm).
      { hexploit (nsteps_to_sync_spec period); eauto.
        intros (_ & NS).
        hexploit (NS O).
        { nia. }
        rewrite Nat.add_0_r. ss. }

      hexploit IHnst'; eauto.
      { instantiate (1:= SyncSys.State (S tm) node_states).
        ss.
        hexploit (nsteps_to_sync_adv
                    period tm (S nst')); eauto. }
      { ss. f_equal. nia. }
      i. des.

      split.
      + econs.
        * econs 1; eauto.
        * unfold DSys.filter_nb_sysstep.
          apply deopt_list_Some_iff.
          instantiate (1:= repeat (Z.of_nat tm, []) (length (node_states))).
          apply nth_eq_list_eq.
          i. unfold DSys.filter_nb_localstep.
          do 2 rewrite Coqlib.list_map_nth.

          destruct (lt_ge_dec n (length node_states)).
          2: {
            rewrite nth_error_None2.
            2: { rewrite repeat_length. ss. }
            rewrite nth_error_None2.
            2: { rewrite repeat_length. ss. }
            ss.
          }
          rewrite repeat_nth_error_Some by ss.
          rewrite repeat_nth_error_Some by ss.
          ss.
        * eauto.
        * ss. clear. r.
          unfold SyncSys.num_sites. ss.
          apply Forall3_nth. i.
          unfold empty_trace.

          destruct (lt_ge_dec n (length node_states)).
          2: {
            rewrite nth_error_None2.
            2: { rewrite repeat_length. ss. }
            rewrite nth_error_None2.
            2: { rewrite repeat_length. ss. }
            rewrite nth_error_None2.
            2: { rewrite repeat_length. ss. }
            econs.
          }

          rewrite repeat_nth_error_Some; eauto.
          rewrite repeat_nth_error_Some; eauto.
          rewrite repeat_nth_error_Some; eauto.
          econs. ss.
          f_equal. f_equal. nia.
      + r. clear PROG.
        i. inv MSTEPS'.
        unfold SyncSys.num_sites in *. ss.
        inv STEP; ss.
        apply DSys_filter_nb_sysstep_inv in FILTER_NB.

        hexploit DET; eauto. i. des.
        split; ss.

        subst.
        unfold empty_trace in *.
        clear - FILTER_NB CONS_EVENTS.
        apply nth_eq_list_eq.

        intro n.
        hexploit Forall3_length; try apply CONS_EVENTS.
        rewrite repeat_length.
        intros (LEN1 & LEN2).

        destruct (lt_ge_dec n (length node_states)).
        2: {
          rewrite nth_error_None2 by nia.
          rewrite nth_error_None2.
          2: { rewrite repeat_length. ss. }
          ss.
        }

        eapply Forall2_nth1 with (n:=n) in FILTER_NB.
        2: { apply repeat_nth_error_Some. ss. }
        des.
        unfold DSys.filter_nb_localstep in P_FA. ss. clarify.
        eapply Forall3_nth1 in CONS_EVENTS; eauto. des.
        clarify.
        rewrite repeat_nth_error_Some by ss.
        rewrite repeat_nth_error_Some in NTH0 by ss. clarify.
        rewrite NTH3. f_equal. f_equal. f_equal. nia.
  Qed.

End SYNC_SYS_LEMMAS.
