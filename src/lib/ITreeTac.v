From ITree Require Import ITree Eq EqAxiom.
Require Import sflib.

Import ITreeNotations.

Ltac cbv_resum :=
  match goal with
  | H: context[resum] |- _ => cbv in H
  end.

Ltac unf_resum :=
  unfold resum, ReSum_id, id_, Id_IFun in *.

Ltac simpl_itree ITR :=
  match type of ITR with
  | _ ≅ ?t =>
    match t with
    | x <- Ret _ ;; _ =>
      rewrite bind_ret_l in ITR
    | x <- Tau _ ;; _ =>
      rewrite bind_tau in ITR
    | x <- Vis _ _ ;; _ =>
      rewrite bind_vis in ITR

    | trigger _ ;; _ =>
      rewrite bind_trigger in ITR
    | (_;;_);;_ =>
      rewrite bind_bind in ITR
    | _ ;; Ret _ =>
      rewrite bind_ret_r in ITR
    end
  end.

Lemma eq_is_bisim E R
      (t1 t2: itree E R)
      (EQ: t1 = t2)
  : t1 ≅ t2.
Proof. subst. reflexivity. Qed.

Ltac capture_itree_goal ITR_EQ :=
  match goal with
  | |- context[?tr] =>
    match type of tr with
    | itree ?E ?R =>
      (* let itr_n := fresh "itr" in *)
      (* let ITR_EQ := fresh "ITR" in *)
      remember tr eqn:ITR_EQ
    end
  end.

Ltac capture_itree_hyp HYP ITR_EQ :=
  match type of HYP with
  | context[?tr] =>
    match type of tr with
    | itree ?E ?R =>
      (* let itr_n := fresh "itr" in *)
      (* let ITR_EQ := fresh "ITR" in *)
      remember tr eqn:ITR_EQ
    end
  end.


Ltac subst_itree ITR :=
  match type of ITR with
  | ?itr = _ => subst itr
  end.

Ltac simpl_itree_goal :=
  let ITR_EQ := fresh in
  (capture_itree_goal ITR_EQ;
   apply eq_is_bisim in ITR_EQ;
   simpl_itree ITR_EQ;
   apply bisimulation_is_eq in ITR_EQ;
   subst_itree ITR_EQ).

Ltac simpl_itree_hyp HYP :=
  let ITR_EQ := fresh in
  (capture_itree_hyp HYP ITR_EQ;
   apply eq_is_bisim in ITR_EQ;
   simpl_itree ITR_EQ;
   apply bisimulation_is_eq in ITR_EQ;
   subst_itree ITR_EQ).




Inductive itree_tau_star {E R}
  : itree E R -> itree E R -> Prop :=
| ITreeTauStar_Refl itr
  : itree_tau_star itr itr
| ITreeTauStar_Step
    itr0 itr1 itr2
    (STEP: observe itr0 = TauF itr1)
    (TAUS: itree_tau_star itr1 itr2)
  : itree_tau_star itr0 itr2
.

Lemma itree_tau_star_trans E R
      (itr1 itr2 itr3: itree E R)
      (STAR1: itree_tau_star itr1 itr2)
      (STAR2: itree_tau_star itr2 itr3)
  : itree_tau_star itr1 itr3.
Proof.
  induction STAR1; ss.
  econs; eauto.
Qed.

Definition itree_tau_plus {E R}
  (itr1 itr2: itree E R): Prop :=
  exists itr', itree_tau_star itr1 itr' /\
          observe itr' = TauF itr2.

Lemma itree_tau_plus2 E R
      (itr1 itr' itr2: itree E R)
      (OBS: observe itr1 = TauF itr')
      (TAU_STAR: itree_tau_star itr' itr2)
  : itree_tau_plus itr1 itr2.
Proof.
  depgen itr1.
  induction TAU_STAR; i; ss.
  { rr. esplits; eauto. econs. }

  hexploit IHTAU_STAR; eauto. intro PLUS.
  rr in PLUS. des.
  rr. esplits; eauto.
  econs 2; eauto.
Qed.

Lemma itree_tau_plus_inv2 E R
      (itr1 itr2: itree E R)
      (PLUS: itree_tau_plus itr1 itr2)
  : exists itr',
      observe itr1 = TauF itr' /\
      itree_tau_star itr' itr2.
Proof.
  rr in PLUS. des.
  induction PLUS; ss.
  - esplits; eauto. econs.
  - esplits; eauto.
    eapply itree_tau_star_trans; eauto.
    econs 2; eauto. econs.
Qed.

Lemma itree_tau_plus_star E R
      (itr1 itr2: itree E R)
      (PLUS: itree_tau_plus itr1 itr2)
  : itree_tau_star itr1 itr2.
Proof.
  inv PLUS. des.
  eapply itree_tau_star_trans; eauto.
  econs 2; eauto.
  econs 1.
Qed.

Lemma itree_tau_plus_star_plus E R
      (itr1 itr2 itr3: itree E R)
      (PLUS: itree_tau_plus itr1 itr2)
      (STAR: itree_tau_star itr2 itr3)
  : itree_tau_plus itr1 itr3.
Proof.
  eapply itree_tau_plus_inv2 in PLUS. des.
  eapply itree_tau_plus2; eauto.
  eapply itree_tau_star_trans; eauto.
Qed.

Lemma itree_tau_star_plus_plus E R
      (itr1 itr2 itr3: itree E R)
      (STAR: itree_tau_star itr1 itr2)
      (PLUS: itree_tau_plus itr2 itr3)
  : itree_tau_plus itr1 itr3.
Proof.
  rr in PLUS. des.
  rr. esplits.
  2: { eauto. }
  eapply itree_tau_star_trans; eauto.
Qed.

Lemma itree_tau_plus_app E R
      (itr1 itr2 itr3: itree E R)
      (PLUS1: itree_tau_plus itr1 itr2)
      (PLUS2: itree_tau_plus itr2 itr3)
  : itree_tau_plus itr1 itr3.
Proof.
  eapply itree_tau_star_plus_plus; eauto.
  eapply itree_tau_plus_star. eauto.
Qed.
