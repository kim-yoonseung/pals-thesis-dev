Require Import sflib.
Require Import StdlibExt.

Require Import Arith Lia.

(* Discrete time model signature *)
Module Type DTimeModelSig.

  (* For simplicity, we assume that the time unit divides 1 nanosecond. *)
  Parameter units_per_ns: nat.
  Axiom units_per_ns_pos: 0 < units_per_ns.

  Record t: Type := mk { units: nat }.

  Definition of_ns (ns: nat): t :=
    mk (ns * units_per_ns).

  (* round down *)
  Definition to_ns_rd (atm: t): nat :=
    (units atm) / units_per_ns.

  Definition to_ns_exact (atm: t): nat? :=
    if ((units atm) mod units_per_ns =? 0)%nat
    then Some (to_ns_rd atm)
    else None
  .

  Definition succ (atm: t): t :=
    mk (S (units atm)).

  Definition uadd (atm: t) (us: nat): t :=
    mk (units atm + us).

  Definition usub (atm: t) (us: nat): t :=
    mk (units atm - us).

End DTimeModelSig.

Declare Module DTime : DTimeModelSig.
Coercion DTime.units : DTime.t >-> nat.

Lemma DTime_of_ns_inv ns
  : DTime.to_ns_rd (DTime.of_ns ns) = ns.
Proof.
  unfold DTime.to_ns_rd, DTime.of_ns. ss.
  pose proof DTime.units_per_ns_pos.
  eapply Nat.div_mul. nia.
Qed.

Lemma DTime_of_ns_inv_exact ns
  : DTime.to_ns_exact (DTime.of_ns ns) = Some ns.
Proof.
  unfold DTime.to_ns_exact.
  unfold DTime.of_ns at 1. ss.
  pose proof DTime.units_per_ns_pos.
  rewrite Nat.mod_mul by nia.

  desf.
  erewrite DTime_of_ns_inv; eauto.
Qed.


Lemma DTime_uadd_zero tm
  : DTime.uadd tm 0 = tm.
Proof.
  unfold DTime.uadd, DTime.succ.
  rewrite plus_0_r. destruct tm; ss.
Qed.

Lemma DTime_uadd_one tm
  : DTime.uadd tm 1 = DTime.succ tm.
Proof.
  unfold DTime.uadd, DTime.succ.
  rewrite plus_comm. ss.
Qed.


Lemma DTime_uadd_assoc
      tm n m
  : DTime.uadd (DTime.uadd tm n) m =
    DTime.uadd tm (n + m).
Proof.
  unfold DTime.uadd. ss.
  rewrite plus_assoc. ss.
Qed.

Lemma DTime_to_ns_rd_le_mono
      (tm1 tm2: DTime.t)
      (LE: tm1 <= tm2)
  : DTime.to_ns_rd tm1 <= DTime.to_ns_rd tm2.
Proof.
  unfold DTime.to_ns_rd.
  generalize DTime.units_per_ns_pos. i.
  eapply Nat.div_le_mono; eauto. nia.
Qed.



Lemma DTime_to_ns_rd_spec
      t n
      (TO_NS_RD: DTime.to_ns_rd t = n)
  : exists r,
    DTime.units t = n * DTime.units_per_ns + r /\
    0 <= r < DTime.units_per_ns.
Proof.
  unfold DTime.to_ns_rd in *. subst n.
  exists (t mod DTime.units_per_ns).
  pose proof DTime.units_per_ns_pos.

  splits.
  - rewrite Nat.mul_comm.
    apply Nat.div_mod. nia.
  - nia.
  - apply Nat.mod_bound_pos; ss. nia.
Qed.


Lemma DTime_to_ns_rd_iff
      t n
  : DTime.to_ns_rd t = n <->
    (exists r,
        DTime.units t = n * DTime.units_per_ns + r /\
        0 <= r < DTime.units_per_ns).
Proof.
  split.
  { apply DTime_to_ns_rd_spec. }
  { intros (r1 & EQ1 & RANGE1).
    hexploit (DTime_to_ns_rd_spec t); eauto.
    intros (r2 & EQ2 & RANGE2).
    nia. }
Qed.


Lemma DTime_to_ns_rd_eq_exact
      n (t: DTime.t)
      (TIME_EXACT: (t:nat) = n * DTime.units_per_ns)
  : DTime.to_ns_rd t = n.
Proof.
  apply DTime_to_ns_rd_iff.
  exists 0. splits; ss.
  - nia.
  - apply DTime.units_per_ns_pos.
Qed.

Lemma DTime_to_ns_exact_spec
      n (t: DTime.t)
  : (t:nat) = n * DTime.units_per_ns <->
    DTime.to_ns_exact t = Some n.
Proof.
  split; ss.
  - intro T_EQ.
    destruct t as [u]; ss. subst u. ss.
    apply DTime_of_ns_inv_exact.
  - pose proof DTime.units_per_ns_pos.
    intros EXACT.
    unfold DTime.to_ns_exact in EXACT.
    desf.
    hexploit beq_nat_true; eauto.
    intros MOD_Z.
    apply Nat.mod_divide in MOD_Z.
    2: { nia. }
    unfold DTime.to_ns_rd.
    r in MOD_Z. des.
    destruct t as [u]; ss. subst u.
    erewrite Nat.div_mul by nia.
    ss.
Qed.

Lemma DTime_to_ns_exact_None_iff
      (t: DTime.t)
  : DTime.to_ns_exact t = None <->
    exists tm_ns r,
      DTime.units t = tm_ns * DTime.units_per_ns + r /\
      tm_ns = DTime.to_ns_rd t /\
      0 < r < DTime.units_per_ns.
Proof.
  destruct (DTime.to_ns_exact t) eqn:EXACT.
  - apply DTime_to_ns_exact_spec in EXACT.
    split; ss.
    i. des.
    unfold DTime.to_ns_rd in *.
    destruct t as [u]; ss. subst.
    rewrite Nat.div_mul in * by nia.
    nia.
  - split; ss. intros _.
    unfold DTime.to_ns_exact in EXACT.
    destruct (Nat.eqb_spec (t mod DTime.units_per_ns) 0)
      as [| MOD_Z]; ss.
    exists (t / DTime.units_per_ns), (t mod DTime.units_per_ns).
    pose proof DTime.units_per_ns_pos.
    (* rewrite Nat.mod_divide in MOD_Z. *)

    splits.
    + rewrite Nat.mul_comm. apply Nat.div_mod. nia.
    + ss.
    + nia.
    + apply Nat.mod_bound_pos; ss. nia.
Qed.


Lemma DTime_units_eq
      (t1 t2: DTime.t)
      (UEQ: DTime.units t1 = DTime.units t2)
  : t1 = t2.
Proof.
  destruct t1, t2; ss. congruence.
Qed.
