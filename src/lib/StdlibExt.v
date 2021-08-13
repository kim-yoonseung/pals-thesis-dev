From Paco Require Import paco.
(* From compcert Require Coqlib. *)
Require Import sflib.
Require Import Axioms.

Require Import Arith ZArith.
Require Import Streams Bool List.
Require Import Lia.

Import ListNotations.

Definition admit_t {T}: T.
Admitted.


Lemma lt_ge_dec
      n m
  : { n < m } + { m <= n }.
Proof.
  destruct (le_lt_dec m n).
  - right. ss.
  - left. ss.
Qed.

(** * nat_diff *)

Definition nat_diff (n m: nat) : nat :=
  if (n <=? m)%nat then m - n else n - m.

Lemma nat_diff_eq n
  : nat_diff n n = O.
Proof.
  induction n; ss.
Qed.

Lemma nat_diff_spec1
      a b
      (LE: a <= b)
  : nat_diff a b = b - a.
Proof.
  unfold nat_diff.
  destruct (Nat.leb_spec a b); ss. nia.
Qed.

Lemma nat_diff_spec2
      a b
      (LE: b <= a)
  : nat_diff a b = a - b.
Proof.
  unfold nat_diff.
  destruct (Nat.leb_spec a b); ss. nia.
Qed.

(** * Option Types *)

Notation "A ?" := (option A) (at level 9).

Definition option_get {A} (d: A) (o: A?) : A :=
  match o with
  | None => d
  | Some a => a
  end.


Definition opt2list {A} (o: A?): list A :=
  match o with
  | None => []
  | Some a => [a]
  end.


Lemma Some_not_None {A} (o: A?)
  : (exists a, o = Some a) <-> o <> None.
Proof.
  split; intro HYP.
  - des. congruence.
  - destruct o; ss.
    esplits; eauto.
Qed.


Definition option_rel1 {A} (P: A -> Prop) (oa: A?): Prop :=
  match oa with
  | None => True
  | Some a => P a
  end.

(* compcert Coqlib.option_rel *)
Inductive option_rel2 {A B: Type}
          (R: A -> B -> Prop)
  : option A -> option B -> Prop :=
| option_rel2_none: option_rel2 R None None
| option_rel2_some: forall x y,
    R x y -> option_rel2 R (Some x) (Some y).

Inductive option_rel3 {A B C: Type}
          (R: A -> B -> C -> Prop)
  : option A -> option B -> option C -> Prop :=
| option_rel3_none: option_rel3 R None None None
| option_rel3_some: forall x y z,
    R x y z -> option_rel3 R (Some x) (Some y) (Some z).

Inductive option_rel4 {A B C D: Type}
          (R: A -> B -> C -> D -> Prop)
  : option A -> option B -> option C -> option D -> Prop :=
| option_rel4_none: option_rel4 R None None None None
| option_rel4_some: forall x y z w,
    R x y z w -> option_rel4 R (Some x) (Some y) (Some z) (Some w).

(** * List types *)


Lemma nth_error_None2
  : forall (A : Type) (l : list A) (n : nat),
    length l <= n ->
    nth_error l n = None.
Proof.
  apply nth_error_None.
Qed.

Lemma nth_error_Some1
  : forall (A : Type) (l : list A) (n : nat),
    nth_error l n <> None -> n < length l.
Proof.
  apply nth_error_Some.
Qed.


Lemma nth_error_Some1' A
      (l: list A) n e1
      (NTH_EQ: nth_error l n = Some e1)
  : n < length l.
Proof.
  eapply nth_error_Some1. congruence.
Qed.


Lemma nth_error_Some2 A
      (l: list A) n
      (LEN: n < length l)
  : exists e1, <<NTH_EX: nth_error l n = Some e1>>.
Proof.
  apply Some_not_None.
  apply nth_error_Some. ss.
Qed.


(* A better version (for induction) of List.last *)
Fixpoint last' {A: Type}
         (l: list A) (d: A): A :=
  match l with
  | [] => d
  | h::t => last' t h
  end.

Definition last_opt {A: Type}
         (l: list A): A? :=
  match l with
  | [] => None
  | h::t => Some (last' t h)
  end.


(* List.filter_map is a lemma *)
Fixpoint filtermap {A B} (f: A -> B?) (l: list A) : list B :=
  match l with
  | [] => []
  | h::t =>
    match f h with
    | None => filtermap f t
    | Some h' => h'::filtermap f t
    end
  end.


Lemma filtermap_app A B
      (f: A -> B?) (l1 l2: list A)
  : filtermap f (l1 ++ l2) =
    filtermap f l1 ++ filtermap f l2.
Proof.
  induction l1 as [| h t IH]; i; ss.
  desf.
  rewrite IH. ss.
Qed.



Lemma filtermap_nil A B
      (f: A -> B?)
      (l: list A)
      (ALL_NONE: forall a, In a l -> f a = None)
  : filtermap f l = [].
Proof.
  revert ALL_NONE.
  induction l as [| h t]; i; ss.
  hexploit (ALL_NONE h); eauto.
  intro R. rewrite R.
  eapply IHt; eauto.
Qed.


Lemma filtermap_in A B
      (f: A -> B?)
      l b
      (IN_F: In b (filtermap f l))
  : exists a, In a l /\ f a = Some b.
Proof.
  revert b IN_F.
  induction l as [|h t IH]; i; ss.
  destruct (f h) eqn: F_H; ss.
  - des.
    + subst. exists h. esplits; eauto.
    + hexploit IH; eauto. i. des.
      esplits; eauto.
  - hexploit IH; eauto. i. des.
    esplits; eauto.
Qed.


Lemma in_filtermap A B
      (f: A -> B?)
      (l: list A)
      (a: A) (b: B)
      (F_A: f a = Some b)
      (IN_A: In a l)
  : In b (filtermap f l).
Proof.
  induction l as [| h t IH]; ss.
  des.
  - subst h. rewrite F_A. ss. eauto.
  - destruct (f h); ss.
    + right. eauto.
    + eauto.
Qed.



Fixpoint replace_nth {A}
         (l: list A) (idx: nat) (r: A)
  : list A :=
  match l with
  | [] => []
  | h::t =>
    match idx with
    | O => (r::t)
    | S idx' =>
      h:: replace_nth t idx' r
    end
  end.



Lemma replace_nth_spec A
      l n (a: A)
  : (length l <= n /\
     replace_nth l n a = l) \/
    (exists l1 p l2,
        l = l1 ++ [p] ++ l2 /\
        length l1 = n /\
        replace_nth l n a = l1 ++ [a] ++ l2).
Proof.
  depgen n.
  induction l as [| h t IH]; i; ss.
  { left. split; ss. nia. }
  destruct n as [| n']; ss.
  { right.
    exists []. esplits; ss. }
  { specialize (IH n').
    des.
    - left. split.
      + nia.
      + congruence.
    - right.
      exists (h::l1). ss.
      esplits; eauto.
      + rewrite IH. eauto.
      + rewrite IH1; eauto.
  }
Qed.



Lemma replace_nth_length A
      l n (a: A)
  : length (replace_nth l n a) = length l.
Proof.
  hexploit (replace_nth_spec _ l n a).
  i. des.
  - congruence.
  - match goal with
    | H1: replace_nth _ _ _ = _,
          H2: l = _ |- _ =>
      rewrite H1; rewrite H2
    end.
    repeat rewrite app_length. ss.
Qed.

Lemma replace_nth_gss A
      l n (a: A)
      (VALID_N: n < length l)
  : nth_error (replace_nth l n a) n = Some a.
Proof.
  generalize (replace_nth_spec _ l n a).
  intros [[LEN_OB ?] | X].
  { nia. }
  destruct X as (l1 & p & l2 & L_EQ & LEN1 & REPL_EQ).
  rewrite REPL_EQ.
  rewrite nth_error_app2 by nia.
  rewrite LEN1. rewrite Nat.sub_diag. ss.
Qed.

Lemma replace_nth_gso A
      l n (a: A) m
      (VALID_N: n <> m)
  : nth_error (replace_nth l n a) m =
    nth_error l m.
Proof.
  generalize (replace_nth_spec _ l n a).
  intros [[LEN_OB REPL_EQ] | X].
  - rewrite REPL_EQ. ss.
  - destruct X as (l1 & p & l2 & L_EQ & LEN1 & REPL_EQ).
    rewrite REPL_EQ.
    rewrite L_EQ.

    destruct (lt_ge_dec m n).
    { do 2 rewrite nth_error_app1 by nia. ss. }

    do 2 rewrite nth_error_app2 with (l:= l1) by nia.
    destruct (m - length l1) eqn: IDX.
    { exfalso. nia. }
    ss.
Qed.


Fixpoint list_divide {A} (l: list A) (n: nat) {struct n}
  : (list A * list A)? :=
  match n with
  | O => Some ([], l)
  | S n' =>
    match l with
    | [] => None
    | h::t =>
      match list_divide t n' with
      | None => None
      | Some (t1, t2) => Some (h::t1, t2)
      end
    end
  end.

Lemma list_divide_succ A (l1 l2: list A) n
      (LEN_EQ: length l1 = n)
  : list_divide (l1 ++ l2) n = Some (l1, l2).
Proof.
  depgen l1.
  induction n as [| n' IH]; i; ss.
  { destruct l1; ss. }

  destruct l1 as [| h1 t1]; ss.
  inv LEN_EQ.
  rewrite IH; ss.
Qed.

Definition snoc {A} (l: list A) (a: A) : list A :=
  l ++ [a].

Lemma snoc_nth_last {A}
      l (a: A) n
      (LEN: n = length l)
  : nth_error (snoc l a) n = Some a.
Proof.
  depgen n. unfold snoc.
  induction l as [| h t IH]; i; ss.
  { subst. ss. }
  destruct n as [| n']. ss. eauto.
Qed.

Lemma nodup_snoc A
      (l: list A) (a: A)
      (NODUP: List.NoDup l)
      (NOTIN: ~ List.In a l)
  : List.NoDup (snoc l a).
Proof.
  induction l as [| h t IH]; ss.
  { unfold snoc. ss. econs; ss. }

  inv NODUP.
  unfold snoc. ss.
  econs.
  { rewrite List.in_app_iff. ii.
    ss. des; ss.
    subst. eauto. }

  apply IH; ss.
  ii. eauto.
Qed.


Lemma snoc_eq_inv A
      l1 l2 (a1 a2: A)
      (SNOC_EQ: snoc l1 a1 = snoc l2 a2)
  : l1 = l2 /\ a1 = a2.
Proof.
  depgen l2.
  unfold snoc.
  induction l1 as [|h1 t1 IH]; i; ss.
  { destruct l2 ; ss.
    { clarify. }
    destruct l2; ss. }

  destruct l2 as [| h2 t2]; ss.
  { destruct t1; ss. }
  inv SNOC_EQ.
  hexploit IH; eauto. i. des.
  subst. split; eauto.
Qed.



(* de-optionalize list *)
Fixpoint deopt_list {A} (l: list A?) : (list A)? :=
  match l with
  | [] => Some []
  | h::t =>
    match h, deopt_list t with
    | Some a, Some t' => Some (a::t')
    | _, _ => None
    end
  end.

Lemma deopt_list_length A
      (l: list A?) l'
      (DEOPT_SOME: deopt_list l = Some l')
  : length l = length l'.
Proof.
  depgen l'.
  induction l as [| h t IH]; i; ss.
  { destruct l'; ss. }
  desf. ss. eauto.
Qed.


Lemma deopt_list_app A
      (l1 l2: list (A?))
      l1' l2'
      (DEOPT1: deopt_list l1 = Some l1')
      (DEOPT2: deopt_list l2 = Some l2')
  : deopt_list (l1 ++ l2) = Some (l1' ++ l2').
Proof.
  depgen l1'.
  induction l1 as [| [h1| ] t1 IH]; i; ss.
  { clarify. }
  destruct (deopt_list t1) eqn: DEOPT_T1; ss.
  clarify.
  hexploit IH; eauto.
  intro R. rewrite R. ss.
Qed.


(* (* works when [length lnew <= length lold] *) *)
(* Definition list_overwrite {A} *)
(*            (lnew: list A) (lold: list A) *)
(*   : list A := *)
(*   lnew ++ skipn (length lnew) lold. *)

Fixpoint partition_map {A P Q}
         (f: A -> P + Q)
         (l:list A) : list P * list Q :=
  match l with
  | nil => (nil, nil)
  | x :: tl =>
    let (g,d) := partition_map f tl in
    match f x with
    | inl p => (p::g, d)
    | inr q => (g, q::d)
    end
  end.

Lemma in_partition_map_l_iff A P Q
      (f: A -> P + Q)
      (l: list A) (p: P)
  : (exists a, In a l /\ f a = inl p) <->
    In p (fst (partition_map f l)).
Proof.
  split.
  - intro IN.
    induction l as [|h t IH]; ss.
    { des; ss. }
    destruct IN as [a [[?| A_IN] F_A]].
    + subst.
      rewrite F_A. desf. ss. eauto.
    + hexploit IH; eauto.
      destruct (partition_map f t) as [hp tp]; ss.
      intro R.
      destruct (f h); ss. eauto.
  - intro IN_P.
    induction l as [| h t IH]; ss.
    destruct (partition_map f t) as [hp tp]; ss.
    destruct (f h) eqn: F_H; ss.
    2: { hexploit IH; eauto. i. des.
         esplits; eauto. }
    des.
    { subst. esplits; eauto. }
    { hexploit IH; eauto. i. des.
      esplits; eauto. }
Qed.


Corollary in_partition_map_l1 A P Q
          (f: A -> P + Q)
          (l: list A) ps qs
          (p: P) (a: A)
          (IN: In a l)
          (PART: partition_map f l = (ps, qs))
          (FA: f a = inl p)
  : In p ps.
Proof.
  cut (In p (fst (partition_map f l))).
  { rewrite PART. ss. }
  apply in_partition_map_l_iff. eauto.
Qed.

Corollary in_partition_map_l2 A P Q
          (f: A -> P + Q)
          (l: list A) ps qs
          (p: P)
          (PART: partition_map f l = (ps, qs))
          (IN: In p ps)
  : exists a, In a l /\ f a = inl p.
Proof.
  apply in_partition_map_l_iff; eauto.
  rewrite PART. ss.
Qed.


Lemma in_partition_map_r_iff A P Q
      (f: A -> P + Q)
      (l: list A) (q: Q)
  : (exists a, In a l /\ f a = inr q) <->
    In q (snd (partition_map f l)).
Proof.
  split.
  - intro IN.
    induction l as [|h t IH]; ss.
    { des; ss. }
    destruct IN as [a [[?| A_IN] F_A]].
    + subst.
      rewrite F_A. desf. ss. eauto.
    + hexploit IH; eauto.
      destruct (partition_map f t) as [hp tp]; ss.
      intro R.
      destruct (f h); ss. eauto.
  - intro IN_P.
    induction l as [| h t IH]; ss.
    destruct (partition_map f t) as [hp tp]; ss.
    destruct (f h) eqn: F_H; ss.
    { hexploit IH; eauto. i. des.
      esplits; eauto. }
    des.
    { subst. esplits; eauto. }
    { hexploit IH; eauto. i. des.
      esplits; eauto. }
Qed.

Corollary in_partition_map_r1 A P Q
          (f: A -> P + Q)
          (l: list A) ps qs
          (q: Q) (a: A)
          (IN: In a l)
          (FA: f a = inr q)
          (PART: partition_map f l = (ps, qs))
  : In q qs.
Proof.
  cut (In q (snd (partition_map f l))).
  { rewrite PART. ss. }
  apply in_partition_map_r_iff. eauto.
Qed.

Corollary in_partition_map_r2 A P Q
          (f: A -> P + Q)
          (l: list A) ps qs
          (q: Q)
          (PART: partition_map f l = (ps, qs))
          (IN: In q qs)
  : exists a, In a l /\ f a = inr q.
Proof.
  apply in_partition_map_r_iff; eauto.
  rewrite PART. ss.
Qed.




Lemma app_eqlen_inv A
      (l1 l2 m1 m2: list A)
      (LEN_EQ: length l1 = length m1)
      (APP_EQ: l1 ++ l2 = m1 ++ m2)
  : l1 = m1 /\ l2 = m2.
Proof.
  depgen m1.
  induction l1 as [| h1 t1 IH]; i; ss.
  { destruct m1; ss. }

  destruct m1; ss.
  inv APP_EQ.
  hexploit IH; try eassumption.
  { nia. }
  i. des; subst. ss.
Qed.


Fixpoint incr_nlist (cur len: nat): list nat :=
  match len with
  | O => []
  | S len' =>
    cur :: incr_nlist (S cur) len'
  end.

Lemma rw_cons_app A
      (h: A) t
  : h::t = [h] ++ t.
Proof. ss. Qed.


Fixpoint process_firstn {S A}
         (f: A -> S -> S)
         (l: list A) (s0: S) (fuel: nat)
  : S * list A :=
  match fuel with
  | O => (s0, l)
  | S fuel' =>
    match l with
    | [] => (s0, [])
    | h :: t => process_firstn f t (f h s0) fuel'
    end
  end.

Lemma process_firstn_spec A S
      (f: A -> S -> S)
      (l: list A) (s0: S) n
  : process_firstn f l s0 n =
    (List.fold_left (flip f) (firstn n l) s0,
     skipn n l).
Proof.
  depgen n. depgen s0.
  induction l as [| h t IH]; i; ss.
  { destruct n; ss. }
  destruct n; ss.
Qed.


(* Compute incr_nlist 3 4. *)

Lemma list_eq A
  : forall (h1 h2: A) t1 t2,
    h1 = h2 -> t1 = t2 -> h1::t1 = h2::t2.
Proof. i. subst. ss. Qed.

Lemma list_eq_inv A
      h1 h2 (t1 t2: list A)
      (LIST_EQ: h1::t1 = h2::t2)
  : t1 = t2 /\ h1 = h2.
Proof.
  inv LIST_EQ. ss.
Qed.

Ltac list_eq_inv_tac :=
  repeat
    match goal with
    | H : _ :: _ = _ :: _ |- _ =>
      apply list_eq_inv in H; des
    end.


(** ** Forall_n *)

Inductive Forall3 {A B C: Type}
          (P: A -> B -> C -> Prop)
  : list A -> list B -> list C -> Prop :=
| Forall3_nil : Forall3 P [] [] []
| Forall3_cons :
    forall a b c l1 l2 l3
      (P_HOLDS: P a b c)
      (FORALL_T: Forall3 P l1 l2 l3),
      Forall3 P (a::l1) (b::l2) (c::l3)
.

Inductive Forall4 {A B C D: Type}
          (P: A -> B -> C -> D -> Prop)
  : list A -> list B -> list C -> list D -> Prop :=
| Forall4_nil : Forall4 P [] [] [] []
| Forall4_cons :
    forall a b c d l1 l2 l3 l4
      (P_HOLDS: P a b c d)
      (FORALL_T: Forall4 P l1 l2 l3 l4),
      Forall4 P (a::l1) (b::l2) (c::l3) (d::l4)
.


Lemma Forall_app {A}
      (l1 l2: list A)
      (P: A -> Prop)
      (FA1: List.Forall P l1)
      (FA2: List.Forall P l2)
  : List.Forall P (l1 ++ l2).
Proof.
  induction l1 as [| h t IH]; i; ss.
  inv FA1.
  econs; eauto.
Qed.

Lemma Forall_app_inv A
      P (l1 l2: list A)
      (FA: Forall P (l1 ++ l2))
  : Forall P l1 /\ Forall P l2.
Proof.
  induction l1 as [| h t IH]; ss.
  inv FA. hexploit IH; eauto. i. des.
  split; ss.
  econs; eauto.
Qed.


Lemma Forall2_length A B
      (P: A -> B -> Prop)
      l1 l2
      (FA: Forall2 P l1 l2)
  : length l1 = length l2.
Proof.
  induction FA; ss. eauto.
Qed.

Lemma Forall3_length A B C
      (P: A -> B -> C -> Prop)
      l1 l2 l3
      (FA: Forall3 P l1 l2 l3)
  : length l1 = length l2 /\
    length l1 = length l3.
Proof.
  induction FA; ss. des.
  split; eauto.
Qed.

Lemma Forall4_length A B C D
      (P: A -> B -> C -> D -> Prop)
      l1 l2 l3 l4
      (FA: Forall4 P l1 l2 l3 l4)
  : <<LEN12: length l1 = length l2>> /\
    <<LEN13: length l1 = length l3>> /\
    <<LEN14: length l1 = length l4>>.
Proof.
  induction FA; ss.
  des. splits; eauto.
Qed.

Lemma Forall2_nth A B
      (P: A -> B -> Prop)
      la lb
  : Forall2 P la lb <->
    (forall n, (option_rel2 P)
            (nth_error la n) (nth_error lb n)).
Proof.
  split.
  - intro FA.
    induction FA; i; ss.
    { destruct n; ss; econs. }
    destruct n; ss.
    econs; eauto.
  - intro OPT.
    depgen lb.

    induction la as [|ha ta]; i; ss.
    { specialize (OPT 0). inv OPT.
      destruct lb; ss. }

    hexploit (OPT 0). intro OPT_ZERO.

    destruct lb as [|hb tb]; inv OPT_ZERO.
    econs; eauto.
    hexploit IHta; eauto.
    i. specialize (OPT (S n)). ss.
Qed.


Lemma Forall3_nth A B C
      (P: A -> B -> C -> Prop)
      la lb lc
  : Forall3 P la lb lc <->
    (forall n, (option_rel3 P)
            (nth_error la n)
            (nth_error lb n)
            (nth_error lc n)).
Proof.
  split.
  - intro FA.
    induction FA; i; ss.
    { destruct n; ss; econs. }
    destruct n; ss.
    econs; eauto.
  - intro OPT.
    depgen lc. depgen lb.

    induction la as [|ha ta]; i; ss.
    { specialize (OPT 0). inv OPT.
      destruct lb; destruct lc; ss. econs. }

    hexploit (OPT 0). intro OPT_ZERO.

    destruct lb as [|hb tb];
      destruct lc as [|hc tc]; inv OPT_ZERO.
    econs; eauto.
    hexploit IHta; eauto.
    i. specialize (OPT (S n)). ss.
Qed.


Lemma Forall4_nth A B C D
      (P: A -> B -> C -> D -> Prop)
      la lb lc ld
  : Forall4 P la lb lc ld <->
    (forall n, (option_rel4 P)
            (nth_error la n) (nth_error lb n)
            (nth_error lc n) (nth_error ld n)).
Proof.
  split.
  - intro FA.
    induction FA; i; ss.
    { destruct n; ss; econs. }
    destruct n; ss.
    econs; eauto.
  - intro OPT.
    depgen ld. depgen lc. depgen lb.

    induction la as [|ha ta]; i; ss.
    { specialize (OPT 0). inv OPT.
      destruct lb; destruct lc; destruct ld; ss. econs. }

    hexploit (OPT 0). intro OPT_ZERO.

    destruct lb; destruct lc; destruct ld; inv OPT_ZERO.
    econs; eauto.
    hexploit IHta; eauto.
    i. specialize (OPT (S n)). ss.
Qed.



Lemma Forall4_app A B C D
      (P: A -> B -> C -> D -> Prop)
      a1 a2 b1 b2 c1 c2 d1 d2
      (FA1: Forall4 P a1 b1 c1 d1)
      (FA2: Forall4 P a2 b2 c2 d2)
  : Forall4 P (a1 ++ a2) (b1 ++ b2)
            (c1 ++ c2) (d1 ++ d2).
Proof.
  induction FA1; ss.
  econs; eauto.
Qed.

Lemma Forall4_app_inv1 A B C D
      (P: A -> B -> C -> D -> Prop)
      a1 a2 b c d
      (FA: Forall4 P (a1 ++ a2) b c d)
  : exists b1 b2 c1 c2 d1 d2,
    b = b1 ++ b2 /\
    c = c1 ++ c2 /\
    d = d1 ++ d2 /\
    Forall4 P a1 b1 c1 d1 /\
    Forall4 P a2 b2 c2 d2.
Proof.
  depgen b. depgen c. depgen d.
  induction a1 as [ | ha1 ta1 IH]; i; ss.
  { exists [], b, [], c, [], d.
    splits; ss. econs. }

  inv FA.
  hexploit IH; eauto. i. des.
  esplits; eauto; cycle 3.
  { econs; eauto. }
  { ss; congruence. }
  { ss; congruence. }
  { ss; congruence. }
Qed.


Lemma Forall2_nth' A B
      (P : A -> B -> Prop)
      (la : list A) (lb : list B)
  : Forall2 P la lb <->
    (length la = length lb /\
     (forall n a b
        (NTH_A: nth_error la n = Some a)
        (NTH_B: nth_error lb n = Some b),
         P a b)).
Proof.
  split.
  - intro FA.
    hexploit Forall2_length; eauto. i. des.
    splits; ss.
    i. eapply Forall2_nth in FA.
    rewrite NTH_A, NTH_B in FA.
    inv FA; ss.
  - intros (LEN1 & NTH_P).
    apply Forall2_nth. i.
    destruct (lt_ge_dec n (length la)).
    2: {
      rewrite nth_error_None2 by nia.
      rewrite nth_error_None2 by nia.
      econs.
    }
    hexploit (nth_error_Some2 _ la n).
    { nia. }
    i. des. rename NTH_EX into NTH1.
    hexploit (nth_error_Some2 _ lb n).
    { nia. }
    i. des. rename NTH_EX into NTH2.
    rewrite NTH1, NTH2. econs.
    eapply NTH_P; eauto.
Qed.


Lemma Forall3_nth' A B C
      (P : A -> B -> C -> Prop)
      (la : list A) (lb : list B) (lc : list C)
  : Forall3 P la lb lc <->
    (length la = length lb /\
     length la = length lc /\
     (forall n a b c
        (NTH_A: nth_error la n = Some a)
        (NTH_B: nth_error lb n = Some b)
        (NTH_C: nth_error lc n = Some c),
         P a b c)).
Proof.
  split.
  - intro FA.
    hexploit Forall3_length; eauto. i. des.
    splits; ss.
    i. eapply Forall3_nth in FA.
    rewrite NTH_A, NTH_B, NTH_C in FA.
    inv FA; ss.
  - intros (LEN1 & LEN2 & NTH_P).
    apply Forall3_nth. i.
    destruct (lt_ge_dec n (length la)).
    2: {
      rewrite nth_error_None2 by nia.
      rewrite nth_error_None2 by nia.
      rewrite nth_error_None2 by nia.
      econs.
    }
    hexploit (nth_error_Some2 _ la n).
    { nia. }
    i. des. rename NTH_EX into NTH1.
    hexploit (nth_error_Some2 _ lb n).
    { nia. }
    i. des. rename NTH_EX into NTH2.
    hexploit (nth_error_Some2 _ lc n).
    { nia. }
    i. des. rename NTH_EX into NTH3.
    rewrite NTH1, NTH2, NTH3. econs.
    eapply NTH_P; eauto.
Qed.


(** ** List Lookup *)
(** * List Lookup *)

(* lookup with boolean function *)

(* find *)
(* Fixpoint ffind {A} (f: A -> bool) (l: list A): A? := *)
(*   match l with *)
(*   | [] => None *)
(*   | h::t => if f h then Some h else flookup f t *)
(*   end. *)

(* find by id *)

Class EqBool A: Type :=
  {
  (* eq_dec: forall x y: A, {x = y} + {x <> y} ; *)
  eqb: A -> A -> bool ;
  eqb_true_iff: forall x y, eqb x y = true <-> x = y ;
  }.

Lemma eqb_refl {A} `{EqBool A}
  : forall a, eqb a a = true.
Proof.
  i. assert (EQ_REFL: a = a) by ss.
  apply eqb_true_iff in EQ_REFL. ss.
Qed.


Lemma eqb_false_iff {A} `{EqBool A}
      a b
  : eqb a b = false <-> a <> b.
Proof.
  split.
  - intros EQB_F ?. subst.
    rewrite eqb_refl in EQB_F. ss.
  - i. destruct (eqb a b) eqn: EQB; ss.
    apply eqb_true_iff in EQB. ss.
Qed.

Lemma eqb_sym {A} `{EqBool A}
  : forall a b, eqb a b = eqb b a.
Proof.
  i.
  destruct (eqb b a) eqn: EQ.
  - apply eqb_true_iff.
    apply eqb_true_iff in EQ. ss.
  - apply eqb_false_iff.
    apply eqb_false_iff in EQ. eauto.
Qed.

Lemma eqb_spec {A} `{EqBool A} a b
  : Bool.reflect (a = b) (eqb a b).
Proof.
  destruct (eqb a b) eqn: EQB.
  - econs. apply eqb_true_iff. ss.
  - econs. apply eqb_false_iff. ss.
Qed.

Global Program Instance nat_EqBool: EqBool nat :=
  {| eqb := Nat.eqb |}.
Next Obligation.
  apply Nat.eqb_eq.
Qed.

Global Program Instance pos_EqBool: EqBool positive :=
  {| eqb := Pos.eqb |}.
Next Obligation.
  apply Pos.eqb_eq.
Qed.


Section LIST_SEARCH.
  Context {I: Type}.
  Context `{EqBool I}.

  Definition find_byid {A}
             (get_id: A -> I)
             (id_seek: I) (l: list A) : A? :=
    find (fun a => (eqb (get_id a) id_seek)) l.

  (* find by nat index *)
  Definition find_ilist {A}
             (id_seek: I) (l: list (I * A)) : A? :=
    option_map snd (find_byid fst id_seek l).

  Lemma find_byid_Some A
        get_id
        i_s (a: A) l
    : (exists l1 l2,
          <<GET_ID_A: get_id a = i_s >> /\
          <<LIST_DIV: l = l1 ++ a :: l2>> /\
          <<PREF_NONE: List.Forall (fun x => get_id x <> i_s) l1>>) <->
      find_byid get_id i_s l = Some a.
  Proof.
    split.
    - induction l as [| h t IH]; ss.
      { i. des. destruct l1; ss. }
      i. des.
      destruct l1 as [| h1 t1]; ss.
      { clarify. rewrite eqb_refl. ss. }
      clarify.
      inv PREF_NONE.
      destruct (eqb_spec (get_id h1) (get_id a)); ss.
      rewrite IH; ss.
      esplits; eauto.
    - induction l as [| h t IH]; ss.
      destruct (eqb_spec (get_id h) i_s) as [EQ|NEQ].
      + clear IH.
        inversion 1. subst.
        esplits; eauto; ss.
      + i. hexploit IH; eauto. i. des. clarify.
        exists (h::l1), l2.
        splits; eauto.
  Qed.

  Lemma find_byid_None A
        get_id
        i_s (l: list A)
    : List.Forall (fun x => get_id x <> i_s) l <->
      find_byid get_id i_s l = None.
  Proof.
    induction l as [| h t IH]; ss.
    split.
    - intro FA. inv FA.
      destruct (eqb_spec (get_id h) i_s); ss.
      apply IH. ss.
    - destruct (eqb_spec (get_id h) i_s); ss.
      intro NONE.
      econs; ss.
      apply IH. ss.
  Qed.

  Lemma find_ilist_Some A
        i_s (a: A) l
    : (exists l1 l2,
          <<LIST_DIV: l = l1 ++ (i_s, a) :: l2>> /\
          <<PREF_NONE: List.Forall (fun x => fst x <> i_s) l1>>) <->
      find_ilist i_s l = Some a.
  Proof.
    unfold find_ilist.
    split.
    - i. des.
      cut (find_byid fst i_s l = Some (i_s, a)).
      { intro F. rewrite F. ss. }
      eapply find_byid_Some.
      esplits; eauto.
    - i.
      destruct (find_byid fst i_s l)
        as [[i_s' a']|] eqn: FIND; ss.
      clarify.
      eapply find_byid_Some in FIND.
      des. ss. clarify.
      esplits; eauto.
  Qed.

  Lemma find_ilist_None A
        i_s (l: list (I * A))
    : List.Forall (fun x => fst x <> i_s) l <->
      find_ilist i_s l = None.
  Proof.
    unfold find_ilist.
    split.
    - intro FA.
      eapply find_byid_None in FA.
      rewrite FA. ss.
    - intro NONE.
      destruct (find_byid fst i_s l) eqn: FIND; ss.
      apply find_byid_None. ss.
  Qed.

  (* (* find and replace *) *)
  (* Fixpoint repl_byf {A R} (f: A -> bool) *)
  (*          (repl: A -> A * R) *)
  (*          (l: list A) : (list A * R)? := *)
  (*   match l with *)
  (*   | [] => None *)
  (*   | h::t => *)
  (*     if f h then *)
  (*       let res := repl h in *)
  (*       Some (fst res :: t, snd res) *)
  (*     else *)
  (*       match repl_byf f repl t with *)
  (*       | Some (t, r) => Some (h::t, r) *)
  (*       | None => None *)
  (*       end *)
  (*   end. *)

  Fixpoint repl_byid' {A R}
           (get_id: A -> I) (repl: A -> A * R)
           (id_seek: I) (l: list A)
    : (list A * R)? :=
    match l with
    | [] => None
    | h::t =>
      if eqb (get_id h) id_seek then
        let res := repl h in
        Some (fst res :: t, snd res)
      else
        match repl_byid' get_id repl id_seek t with
        | Some (t, r) => Some (h::t, r)
        | None => None
        end
    end.

  Definition repl_byid {A R}
             (get_id: A -> I) (repl: A -> A * R)
             (id_seek: I) (l: list A)
    : list A * R? :=
    match repl_byid' get_id repl id_seek l with
    | None => (l, None)
    | Some (l', r) => (l', Some r)
    end.

  Lemma repl_byid'_spec A R
        get_id (repl: A -> A * R) id_seek l
    : (<<IDS_DIFF: Forall (fun a => get_id a <> id_seek) l>> /\
       <<REPL_NONE: repl_byid' get_id repl id_seek l = None>>) \/
      (exists l1 a l2 a' r,
          <<L_DIV: l = l1 ++ [a] ++ l2>> /\
          <<IDS_DIFF1: Forall (fun a => get_id a <> id_seek) l1>> /\
          <<ID_FOUND: get_id a = id_seek>> /\
          <<REPL_A: repl a = (a', r)>> /\
          <<REPL_SOME: repl_byid' get_id repl id_seek l =
                       Some (l1 ++ [a'] ++ l2, r)>>).
  Proof.
    induction l as [| h t IH]; ss.
    { left. esplits; eauto. }

    destruct (eqb_spec (get_id h) id_seek) as [EQ|NEQ].
    - right. exists []. ss.
      esplits; eauto.
      apply surjective_pairing.
    - desH IH.
      + left. esplits.
        * econs; eauto.
        * rewrite REPL_NONE. ss.
      + right.
        exists (h :: l1).
        esplits; eauto; ss.
        { subst. ss. }
        rewrite REPL_SOME. ss.
  Qed.


  Lemma repl_byid_spec A R
        get_id (repl: A -> A * R) id_seek l
    : (<<IDS_DIFF: Forall (fun a => get_id a <> id_seek) l>> /\
       <<REPL_NONE: repl_byid get_id repl id_seek l = (l, None)>>) \/
      (exists l1 a l2 a' r,
          <<L_DIV: l = l1 ++ [a] ++ l2>> /\
          <<IDS_DIFF1: Forall (fun a => get_id a <> id_seek) l1>> /\
          <<ID_FOUND: get_id a = id_seek>> /\
          <<REPL_A: repl a = (a', r)>> /\
          <<REPL_SOME: repl_byid get_id repl id_seek l =
                       (l1 ++ [a'] ++ l2, Some r)>>).
  Proof.
    hexploit (repl_byid'_spec _ _ get_id repl id_seek l); eauto.
    unfold repl_byid.
    i. des.
    - left.
      esplits; eauto.
      rewrite REPL_NONE. ss.
    - right.
      esplits; eauto.
      rewrite REPL_SOME. ss.
  Qed.

  (* Lemma repl_byid'_spec A R *)
  (*       get_id (repl: A -> A * R) *)
  (*       i_r l *)
  (*       (REPL_ID_INV: forall a, *)
  (*           get_id (fst (repl a)) = get_id a) *)
  (*   : match find_byid get_id i_r l with *)
  (*     | None => *)
  (*       repl_byid' get_id repl i_r l = None *)
  (*     | Some a => *)
  (*       exists l', *)
  (*       <<REPL_SOME: repl_byid' get_id repl i_r l = *)
  (*                    Some (l', snd (repl a))>> /\ *)
  (*       <<FIND_ANY: forall i_s, *)
  (*           find_byid get_id i_s l' = *)
  (*           if eqb i_r i_s then Some (fst (repl a)) *)
  (*           else find_byid get_id i_s l>> *)
  (*     end. *)
  (* Proof. *)
  (*   induction l as [| h t IH]; ss. *)
  (*   destruct (eqb_spec (get_id h) i_r) as [EQ|NEQ]; ss. *)
  (*   - clear IH. *)
  (*     esplits. *)
  (*     + unfold repl_byid'. ss. *)
  (*       rewrite EQ. rewrite eqb_refl. ss. *)
  (*     + i. ss. *)
  (*       rewrite REPL_ID_INV. rewrite EQ. *)
  (*       desf. *)
  (*   - apply eqb_false_iff in NEQ. *)
  (*     destruct (find_byid get_id i_r t) eqn: FIND_T. *)
  (*     2: { unfold repl_byid' in *. ss. *)
  (*          rewrite IH. rewrite NEQ. ss. } *)
  (*     des. *)
  (*     esplits. *)
  (*     + unfold repl_byid' in *. ss. *)
  (*       rewrite NEQ. rewrite REPL_SOME. *)
  (*       eauto. *)
  (*     + i. ss. *)
  (*       desf. *)
  (*       exfalso. *)
  (*       assert (i_r = i_s) by (apply eqb_true_iff; ss). *)
  (*       subst i_s. congruence. *)
  (* Qed. *)

  (* Lemma repl_byid'_spec A R *)
  (*       get_id (repl: A -> A * R) *)
  (*       (REPL_ID_INV: forall a, *)
  (*           get_id (fst (repl a)) = get_id a) *)
  (*       i l *)
  (*   : match repl_byid' get_id repl i l with *)
  (*     | None => *)
  (*       find_byid get_id i l = None *)
  (*     | Some (l', res) => *)
  (*       exists a, *)
  (*       find_byid get_id i l = Some a /\ *)
  (*       let (a', r) := repl a in *)
  (*       res = r /\ *)
  (*       forall i', find_byid get_id i' l' = *)
  (*             if eqb i i' then Some a' *)
  (*             else find_byid get_id i' l *)
  (*     end. *)
  (* Proof. *)
  (*   induction l as [| h t IH]; ss. *)
  (*   unfold repl_byid' in *. ss. *)
  (*   destruct (eqb_spec (get_id h) i). *)
  (*   - clear IH. ss. *)
  (*     hexploit (REPL_ID_INV h). intro ID_REPL. *)
  (*     subst i. *)
  (*     esplits; eauto. *)
  (*     destruct (repl h) eqn: REPL_H. ss. *)
  (*     split; ss. i. *)
  (*     desf; congruence. *)
  (*   - match goal with *)
  (*     | |- context[repl_byf ?f ?r ?l] => *)
  (*       remember (repl_byf f r l) *)
  (*         as repl_result eqn: REPL *)
  (*     end. *)
  (*     destruct repl_result as [[l' res]|]; ss. *)
  (*     des. esplits; eauto. *)
  (*     specialize (REPL_ID_INV a). *)
  (*     destruct (repl a) as [a' res'] eqn: REPL_A. *)
  (*     des. clarify. *)
  (*     splits; eauto. *)
  (*     i. destruct (eqb_spec (get_id h) i'); ss. *)
  (*     destruct (eqb_spec i i'); ss. *)
  (*     subst. contradiction. *)
  (* Qed. *)

  Definition repl_ilist' {A R}
             (repl: A -> A * R)
             (id_seek: I) (l: list (I * A))
    : (list (I * A) * R)? :=
    repl_byid'
      fst (fun ielt =>
             let res := repl (snd ielt) in
             ((fst ielt, fst res), snd res))
      id_seek l.

  Definition repl_ilist {A R}
             (repl: A -> A * R)
             (id_seek: I) (l: list (I * A))
    : list (I * A) * R? :=
    match repl_ilist' repl id_seek l with
    | None => (l, None)
    | Some (l', r) => (l', Some r)
    end.

  Lemma repl_ilist'_spec A R
        (repl: A -> A * R) id_seek l
    : (<<IDS_DIFF: Forall (fun a => fst a <> id_seek) l>> /\
       <<REPL_NONE: repl_ilist' repl id_seek l = None>>) \/
      (exists l1 a l2 a' r,
          <<L_DIV: l = l1 ++ [(id_seek, a)] ++ l2>> /\
          <<IDS_DIFF1: Forall (fun a => fst a <> id_seek) l1>> /\
          <<REPL_A: repl a = (a', r)>> /\
          <<REPL_SOME: repl_ilist' repl id_seek l =
                       Some (l1 ++ [(id_seek, a')] ++ l2, r)>>).
  Proof.
    unfold repl_ilist'.
    generalize (repl_byid'_spec
                  _ _ fst
                  (fun ielt =>
                     let res := repl (snd ielt) in
                     ((fst ielt, fst res), snd res))
                  id_seek l).
    i. des.
    - left. eauto.
    - destruct a, a'. ss. clarify.
      right. esplits; eauto.
      apply surjective_pairing.
  Qed.

  Lemma repl_ilist_spec A R
        (repl: A -> A * R) id_seek l
    : (<<IDS_DIFF: Forall (fun a => fst a <> id_seek) l>> /\
       <<REPL_NONE: repl_ilist repl id_seek l = (l, None)>>) \/
      (exists l1 a l2 a' r,
          <<L_DIV: l = l1 ++ [(id_seek, a)] ++ l2>> /\
          <<IDS_DIFF1: Forall (fun a => fst a <> id_seek) l1>> /\
          <<REPL_A: repl a = (a', r)>> /\
          <<REPL_SOME: repl_ilist repl id_seek l =
                       (l1 ++ [(id_seek, a')] ++ l2, Some r)>>).
  Proof.
    hexploit (repl_ilist'_spec _ _ repl id_seek l); eauto.
    unfold repl_ilist.
    i. des.
    - left.
      esplits; eauto.
      rewrite REPL_NONE. ss.
    - right.
      esplits; eauto.
      rewrite REPL_SOME. ss.
  Qed.


  (* Lemma repl_ilist_None_find A R *)
  (*       (repl: A -> A * R) *)
  (*       i l l' *)
  (*       (REPL: repl_ilist repl i l = (l', None)) *)
  (*   : find_ilist i l = None /\ l' = l. *)
  (* Proof. *)
  (*   unfold repl_ilist, repl_byid in *. *)
  (*   unfold find_ilist. *)
  (*   desf. *)
  (*   hexploit repl_byid'_spec. *)
  (*   2: { *)
  (*     rewrite Heq. *)
  (*     intro FIND_NONE. *)
  (*     rewrite FIND_NONE. ss. *)
  (*   } *)
  (*   ss. *)
  (* Qed. *)

  (* Lemma repl_ilist'_spec A R *)
  (*       i l res *)
  (*       (repl: A -> A * R) *)
  (*       (REPL_RES: repl_ilist' repl i l = res) *)
  (*   : match find_ilist i l with *)
  (*     | None => res = None *)
  (*     | Some a => *)
  (*       exists l', *)
  (*       <<REPL_OK: res = Some (l', snd (repl a))>> /\ *)
  (*       <<FIND_ANY: *)
  (*         forall i', find_ilist i' l' = *)
  (*               if eqb i i' then Some (fst (repl a)) *)
  (*               else find_ilist i' l>> *)
  (*     end. *)
  (* Proof. *)
  (*   subst. *)
  (*   unfold find_ilist, repl_ilist'. *)
  (*   hexploit (repl_byid'_spec *)
  (*               (I * A) R fst *)
  (*               (fun ia => (fst ia, fst (repl (snd ia)), *)
  (*                        snd (repl (snd ia)))) i l). *)
  (*   { ss. } *)
  (*   destruct (find_byid fst i l) *)
  (*     as [(i', a)|] eqn: FIND; ss. *)
  (*   i. des. *)
  (*   rewrite REPL_SOME. *)
  (*   esplits; eauto. *)
  (*   intro i_s. *)
  (*   rewrite FIND_ANY. *)
  (*   desf. *)
  (* Qed. *)

  (* Lemma repl_ilist'_Some_find A R *)
  (*       (repl: A -> A * R) *)
  (*       i l l' res *)
  (*       (REPL: repl_ilist' repl i l = Some (l' res)) *)
  (*   : exists a, *)
  (*     <<FIND_A: find_ilist i l = Some a>> /\ *)
  (*     <<RES_EQ: res = snd (repl a)>> /\ *)

  (*     <<FIND_ANY: *)
  (*       forall i', find_ilist i' l' = *)
  (*             if eqb i i' then Some (fst (repl a)) *)
  (*             else find_ilist i' l>> *)
  (* . *)
  (* Proof. *)
  (*   i. unfold repl_ilist, repl_byid in REPL. *)
  (*   match type of REPL with *)
  (*   | match ?e with _ => _ end = _ => *)
  (*     remember e as repl_result eqn:REPL_BYID *)
  (*   end. *)
  (*   unfold find_ilist. *)
  (*   destruct repl_result as [[lm rv]|]; ss. *)
  (*   clarify. *)

  (*   hexploit repl_byid'_spec. *)
  (*   2: { *)
  (*     rewrite <- REPL_BYID. *)
  (*     intros SOME. des. *)
  (*     destruct a as [i' a']. clarify. ss. *)
  (*     rewrite SOME. ss. *)
  (*     esplits; eauto. *)

  (*     intros i_seek. *)
  (*     rewrite SOME1. *)
  (*     destruct (eqb_spec i i_seek); ss. *)
  (*   } *)
  (*   ss. *)
  (* Qed. *)



  (* Lemma repl_ilist_Some_find A R *)
  (*       (repl: A -> A * R) *)
  (*       i l l' res *)
  (*       (REPL: repl_ilist repl i l = (l', Some res)) *)
  (*   : exists a, *)
  (*     <<FIND_A: find_ilist i l = Some a>> /\ *)
  (*     <<RES_EQ: res = snd (repl a)>> /\ *)

  (*     <<FIND_ANY: *)
  (*       forall i', find_ilist i' l' = *)
  (*             if eqb i i' then Some (fst (repl a)) *)
  (*             else find_ilist i' l>> *)
  (* . *)
  (* Proof. *)
  (*   i. unfold repl_ilist, repl_byid in REPL. *)
  (*   match type of REPL with *)
  (*   | match ?e with _ => _ end = _ => *)
  (*     remember e as repl_result eqn:REPL_BYID *)
  (*   end. *)
  (*   unfold find_ilist. *)
  (*   destruct repl_result as [[lm rv]|]; ss. *)
  (*   clarify. *)

  (*   hexploit repl_byid'_spec. *)
  (*   2: { *)
  (*     rewrite <- REPL_BYID. *)
  (*     intros SOME. des. *)
  (*     destruct a as [i' a']. clarify. ss. *)
  (*     rewrite SOME. ss. *)
  (*     esplits; eauto. *)

  (*     intros i_seek. *)
  (*     rewrite SOME1. *)
  (*     destruct (eqb_spec i i_seek); ss. *)
  (*   } *)
  (*   ss. *)
  (* Qed. *)

  (* Lemma repl_ilist_find A R *)
  (*       (repl: A -> A * R) *)
  (*       i l l' res *)
  (*       (REPL: repl_ilist repl i l = (l', res)) *)
  (*   : forall i', *)
  (*     find_ilist i' l' = *)
  (*     if eqb i i' then *)
  (*       option_map (fun a => fst (repl a)) (find_ilist i l) *)
  (*     else *)
  (*       find_ilist i' l. *)
  (* Proof. *)
  (*   i. destruct res as [res| ]. *)
  (*   - hexploit repl_ilist_Some_find; eauto. *)
  (*     intros (a & FIND_I & RES_EQ & FIND). des. subst. *)
  (*     rewrite FIND. rewrite FIND_I. ss. *)
  (*   - hexploit repl_ilist_None_find; eauto. *)
  (*     intros FIND. des. clarify. *)
  (*     rewrite FIND. ss. *)
  (*     destruct (eqb_spec i i'); ss. *)
  (*     subst. ss. *)
  (* Qed. *)

  (* remove by decision function *)
  (* Fixpoint remove_byf {A} (f: A -> bool) *)
  (*          (l: list A): (list A)? := *)
  (*   match l with *)
  (*   | [] => None *)
  (*   | h::t => if f h then Some t else *)
  (*             option_map (fun t' => h::t') (remove_byf f t) *)
  (*   end. *)

  Fixpoint remove_byid {A} (get_id: A -> I) (i: I)
           (l: list A): (list A)? :=
    match l with
    | [] => None
    | h::t => if eqb (get_id h) i then Some t else
              option_map (fun t' => h::t') (remove_byid get_id i t)
    end.

  Lemma remove_byid_spec A
        get_id id_rem (l: list A)
    : (<<ID_NEQ: Forall (fun a => get_id a <> id_rem) l>> /\
       <<REMOVE_FAILED: remove_byid get_id id_rem l = None>>) \/
      (exists l1 a l2,
          <<L_DIV: l = l1 ++ [a] ++ l2>> /\
          <<ID_NEQ1: Forall (fun a => get_id a <> id_rem) l1>> /\
          <<ID_A_EQ: get_id a = id_rem>> /\
          <<REMOVE_SUCC: remove_byid get_id id_rem l = Some (l1 ++ l2)>>).
  Proof.
    induction l as [| h t IH]; ss.
    { left. eauto. }
    destruct (eqb_spec (get_id h) id_rem) as [EQ | NEQ].
    - right.
      exists []. esplits; ss.
    - desH IH.
      + left. esplits; ss.
        { econs; eauto. }
        rewrite REMOVE_FAILED. ss.
      + right.
        exists (h::l1).
        esplits; eauto; ss.
        { subst. ss. }
        rewrite REMOVE_SUCC. ss.
  Qed.

  Definition remove_ilist' {A} (i: I) (l: list (I * A))
    : (list (I * A))? :=
    remove_byid fst i l.

  Lemma remove_ilist'_spec A i (l: list (I * A))
    : (<<ID_NEQ: Forall (fun a => fst a <> i) l>> /\
       <<REMOVE_FAILED: remove_ilist' i l = None>>) \/
      (exists l1 a l2,
          <<L_DIV: l = l1 ++ [(i, a)] ++ l2>> /\
          <<ID_NEQ1: Forall (fun a => fst a <> i) l1>> /\
          <<REMOVE_SUCC: remove_ilist' i l = Some (l1 ++ l2)>>).
  Proof.
    unfold remove_ilist'.
    generalize (remove_byid_spec _ fst i l). i. des.
    - left.
      esplits; eauto.
    - right.
      destruct a as [i' a']. ss. clarify.
      esplits; eauto; ss.
  Qed.

  Definition remove_ilist {A} (i: I) (l: list (I * A))
    : list (I * A) :=
    match remove_ilist' i l with
    | None => l
    | Some l' => l'
    end.

  Lemma remove_ilist_spec A i (l: list (I * A))
    : (<<ID_NEQ: Forall (fun a => fst a <> i) l>> /\
       <<REMOVE_FAILED: remove_ilist i l = l>>) \/
      (exists l1 a l2,
          <<L_DIV: l = l1 ++ [(i, a)] ++ l2>> /\
          <<ID_NEQ1: Forall (fun a => fst a <> i) l1>> /\
          <<REMOVE_SUCC: remove_ilist i l = (l1 ++ l2)>>).
  Proof.
    unfold remove_ilist.
    generalize (remove_ilist'_spec _ i l). i. des.
    - left.
      esplits; eauto. desf.
    - right.
      esplits; eauto. desf.
  Qed.


  (** update *)
  Definition update_ilist {A}
             (i: I) (a: A) (l: list (I * A))
    : list (I * A) :=
    match repl_ilist' (fun _ => (a, tt)) i l with
    | None => (i, a) :: l
    | Some (l', _) => l'
    end.

  Lemma find_ilist_cons A
        i (a:A) l i'
    : find_ilist i' ((i, a) :: l) =
      if eqb i i' then Some a else find_ilist i' l.
  Proof.
    unfold find_ilist. ss. desf.
  Qed.

  Lemma update_ilist_new_id A
        i (a: A) l
        (FNONE: find_ilist i l = None)
    : update_ilist i a l = (i, a) :: l.
  Proof.
    unfold update_ilist.
    apply find_ilist_None in FNONE.
    hexploit (repl_ilist'_spec _ _ (fun _: A => (a, tt)) i l); eauto.
    i. des.
    - rewrite REPL_NONE. ss.
    - exfalso.
      clarify.
      apply Forall_app_inv in FNONE.
      destruct FNONE as [_ FNONE'].
      apply Forall_app_inv in FNONE'.
      destruct FNONE' as [FNONE _].
      inv FNONE. ss.
  Qed.

  Lemma update_ilist_find A
        i (a: A) l
    : forall i', find_ilist i' (update_ilist i a l) =
            if eqb i i' then Some a
            else find_ilist i' l.
  Proof.
    i. unfold update_ilist.
    rename a into a0.
    generalize (repl_ilist'_spec _ unit (fun _ => (a0, tt)) i l).
    i. des.
    - rewrite REPL_NONE.
      unfold find_ilist. ss.
      destruct (eqb_spec i i'); ss.
    - symmetry in REPL_A. clarify.
      rewrite REPL_SOME. ss.
      destruct (eqb_spec i i'); ss.
      + subst.
        apply find_ilist_Some.
        esplits; eauto.
      + induction l1 as [|h1 t1 IH]; ss.
        { unfold find_ilist. ss.
          destruct (eqb_spec i i'); ss. }
        inv IDS_DIFF1.
        hexploit IH; eauto.
        { clear IH.
          unfold repl_ilist' in *. ss.
          destruct (eqb_spec (fst h1) i); ss.
          desf. }

        intro EQ_TAILS.
        unfold find_ilist in *. ss.
        destruct (eqb_spec (fst h1) i'); ss.
  Qed.

End LIST_SEARCH.


(** * Streams and Colists *)

Notation stream := Stream.

CoInductive colist (A: Type): Type :=
| cnil: colist A
| ccons (h: A) (t: colist A): colist A.

Arguments cnil {A}.
Arguments ccons {A}.


Lemma unfold_colist A
      (c: colist A)
  : c = match c with
        | cnil => cnil
        | ccons h t => ccons h t
        end.
Proof.
  destruct c; ss.
Qed.


(* stream_pred *)

Inductive _Forall_stream {A} (P: A -> Prop)
          (fa_str: stream A -> Prop)
  : stream A -> Prop :=
| ForallStream
    h l
    (P_HD: P h)
    (FORALL_TL: fa_str l)
  : _Forall_stream P fa_str (Cons h l).

Hint Constructors _Forall_stream: paco.

Lemma Forall_stream_monotone A P
  : monotone1 (@_Forall_stream A P).
Proof. pmonauto. Qed.

Definition Forall_stream {A} P: stream A -> Prop :=
  paco1 (_Forall_stream P) bot1.

Hint Resolve Forall_stream_monotone: paco.


(** equalities *)

Inductive _stream_eq {A} (seq: stream A -> stream A -> Prop)
  : stream A -> stream A -> Prop :=
| StreamEq
    h l1 l2
    (STR_EQ_T: seq l1 l2)
  : _stream_eq seq (Cons h l1) (Cons h l2)
.

Hint Constructors _stream_eq: paco.

Lemma stream_eq_monotone A: monotone2 (@_stream_eq A).
Proof. pmonauto. Qed.

Definition stream_eq {A}: stream A -> stream A -> Prop :=
  paco2 _stream_eq bot2.

Hint Resolve stream_eq_monotone: paco.


Inductive _colist_eq {A} (ceq: colist A -> colist A -> Prop)
  : colist A -> colist A -> Prop :=
| ColistEq_cnil
  : _colist_eq ceq cnil cnil

| ColistEq_ccons
    h l1 l2
    (CTR_EQ_T: ceq l1 l2)
  : _colist_eq ceq (ccons h l1) (ccons h l2)
.

Hint Constructors _colist_eq: paco.

Lemma colist_eq_monotone A: monotone2 (@_colist_eq A).
Proof. pmonauto. Qed.

Hint Resolve colist_eq_monotone: paco.

Definition colist_eq {A}: colist A -> colist A -> Prop :=
  paco2 _colist_eq bot2.


(** More defs *)

Definition stream_des {A} (s: stream A)
  : A * stream A :=
  match s with
  | Cons a s' => (a, s')
  end.

Definition colist_des {A} (c: colist A)
  : A? * colist A :=
  match c with
  | cnil => (None, cnil)
  | ccons a c' => (Some a, c')
  end.

CoFixpoint inftau {A} : stream (list A) :=
  Cons [] inftau.

(* CoFixpoint inftau {A} : stream (A?) := *)
(*   Cons None inftau. *)

CoFixpoint stream_map {A B}
           (f: A -> B) (str: stream A)
  : stream B :=
  match str with
  | Cons h t => Cons (f h) (stream_map f t)
  end.

Fixpoint stream_app {A}
         (l: list A) (str: stream A)
  : stream A :=
  match l with
  | [] => str
  | h::t => Cons h (stream_app t str)
  end.

CoFixpoint colist_map {A B}
           (f: A -> B) (cl: colist A)
  : colist B :=
  match cl with
  | cnil => cnil
  | ccons a cl' => ccons (f a) (colist_map f cl')
  end.

Fixpoint colist_app {A}
         (l: list A) (cl: colist A)
  : colist A :=
  match l with
  | [] => cl
  | h::t => ccons h (colist_app t cl)
  end.


Lemma colist_app_assoc A
      l1 l2 (c: colist A)
  : colist_app (l1 ++ l2) c =
    colist_app l1 (colist_app l2 c).
Proof.
  induction l1 as [| h1 t1]; ss.
  f_equal. ss.
Qed.

Lemma stream_app_assoc A
      (l1 l2: list A) s
  : stream_app (l1 ++ l2) s =
    stream_app l1 (stream_app l2 s).
Proof.
  induction l1 as [| h1 t1]; ss.
  f_equal. ss.
Qed.


Lemma _colist_eq_app A
      (r: _ -> _ -> Prop)
      (l: list A) (c1 c2: colist A)
      (R: r c1 c2)
      (L_NNIL: 0 < length l)
  : _colist_eq (upaco2 _colist_eq r) (colist_app l c1) (colist_app l c2).
Proof.
  destruct l as [| h t].
  { ss. nia. }
  clear L_NNIL.
  ss. econs.

  induction t as [| th tt IH]; ss.
  { right. eauto. }

  left. pfold. econs. eauto.
Qed.

Definition cons_each_rel {A}
           (hds: list A) (tls: list (list A))
  : list (list A) -> Prop :=
  Forall3 (fun h t l => cons h t = l) hds tls.

Ltac unfold_stream_map :=
  match goal with
  | H: _ = stream_map ?f ?s |- _ =>
    rewrite (unfold_Stream (stream_map f s)) in H
  end.

Ltac unfold_inftau :=
  match goal with
  | H: context [inftau] |- _ =>
    rewrite (unfold_Stream inftau) in H
  end.


(* Definition slist_des_each {A} *)
(*            (s: list (stream A)) *)
(*   : list A * list (stream A) := *)
(*   List.split (List.map (fun str => *)
(*                           match str with *)
(*                           | Cons h t => (h, t) *)
(*                           end) s). *)

Fixpoint stream_splitn {A} (n: nat)
         (s: stream A) : list A * stream A :=
  match n with
  | O => ([], s)
  | S n' =>
    match s with
    | Cons h t =>
      let (l', s') := stream_splitn n' t in
      (h::l', s')
    end
  end.

Definition Cons_rel {A} (h: A) (t s: stream A): Prop :=
  Cons h t = s.

Definition Cons_each_rel {A} (hs: list A) (ts ss: list (stream A)) : Prop :=
  Forall3 Cons_rel hs ts ss.


Fixpoint cons_each {A}
         (hs: list A) (ts: list (list A))
  : list (list A) :=
  match hs with
  | [] => []
  | hs_h :: hs_t =>
    match ts with
    | [] => []
    | ts_h :: ts_t => (hs_h :: ts_h) :: cons_each hs_t ts_t
    end
  end.

Definition app_each_rel {A}
           (l1 l2 l: list (list A)): Prop :=
  Forall3 (fun a b c => a ++ b = c) l1 l2 l.


Definition snoc_each_rel {A}
           (l1: list (list A)) (l2: list A) l: Prop :=
  Forall3 (fun a b c => a ++ [b] = c) l1 l2 l.

Definition sapp_each_rel {A}
           (hds: list (list A)) (tls: list (stream A))
  : list (stream A) -> Prop :=
  Forall3 (fun h t l => stream_app h t = l) hds tls.


Definition capp_each_rel {A}
           (hds: list (list A)) (tls: list (colist A))
  : list (colist A) -> Prop :=
  Forall3 (fun h t l => colist_app h t = l) hds tls.


Definition tolist_each {A}
           (l: list A)
  : list (list A) :=
  map (fun x => [x]) l.


(* Compute (@cons_each nat [1; 3; 2] [[0; 5]; [2]]). *)
(* Compute (@cons_each nat [1; 3; 2] [[0; 5]; [2] ; []; []]). *)

Lemma cons_each_impl_rel A
      (l_h: list A) l_t
      (LEN_EQ: length l_h = length l_t)
  : cons_each_rel l_h l_t (cons_each l_h l_t).
Proof.
  depgen l_t.
  induction l_h as [| h t IH]; i; ss.
  { destruct l_t; ss. econs. }
  destruct l_t as [| h_t t_t]; ss.
  econs; eauto.
  eapply IH. nia.
Qed.



Lemma cons_each_rel_det A
      (l_h: list A) l_t l
      (CONS_EACH_REL: cons_each_rel l_h l_t l)
  : l = cons_each l_h l_t.
Proof.
  depgen l_t. depgen l.
  induction l_h as [| h t IH]; i; ss.
  { inv CONS_EACH_REL. ss. }
  destruct l_t as [| h_t t_t]; ss.
  { inv CONS_EACH_REL. }
  inv CONS_EACH_REL.

  hexploit IH; eauto.
  intro R. rewrite R. ss.
Qed.


Lemma app_each_rel_det A
      (l1 l2 l l': list (list A))
      (APP1: app_each_rel l1 l2 l)
      (APP2: app_each_rel l1 l2 l')
  : l = l'.
Proof.
  depgen l1. depgen l2. depgen l'.
  induction l as [| h t IH]; i; ss.
  { inv APP1. inv APP2. ss. }
  inv APP1; ss.
  inv APP2; ss.
  hexploit IH; eauto. i. congruence.
Qed.

Lemma cons_each_nil_eq_tolist_each A
      (l: list A) n
      (LEN: n = length l)
  : cons_each l (repeat [] n) =
    tolist_each l.
Proof.
  depgen n.
  induction l as [| h t IH]; i; ss.
  destruct n; ss.
  hexploit IH; eauto.
  inv LEN.
  intro R. rewrite R. ss.
Qed.





Lemma stream_splitn_spec {A} (n: nat)
      (p: list A) s s'
  : stream_splitn n s = (p, s') <->
    (<<PREF_LENGTH: length p = n>> /\
     <<STREAM_APP: stream_app p s' = s>>).
Proof.
  split; intro P.
  - depgen s. depgen p. depgen s'.
    induction n as [| n' IH]; i; ss.
    + clarify.
    + destruct s as [h t].
      destruct (stream_splitn n' t) as (p', s'') eqn:SPL.
      clarify.
      hexploit IH; eauto. i. des. clarify.
  - des. clarify.
    induction p as [|h t IH]; ss.
    rewrite IH. ss.
Qed.

(* Lemma map_stream_des A *)
(*       (hs: list A) (ts: list (stream A)) *)
(*       (CONS: Forall3 (fun a b c => Cons a b = c) hs ts s) *)
(*   : map stream_des s = ( *)


(* Definition slist_splitn_each {A} (n: nat) *)
(*            (s: list (stream A)) *)
(*   : list (list A) * list (stream A) := *)
(*   List.split (List.map (stream_splitn n) s). *)

(* Lemma Forall3_stream_cons A *)
(*       (l: list A) (s' s: list (stream A)) *)
(*       (FA_CONS: Forall3 (c2p2 (@Cons A)) l s' s) *)
(*   : slist_des_each s = (l, s'). *)
(* Proof. *)
(*   unfold slist_des_each. *)
(*   induction FA_CONS; ss. *)
(*   destruct c as [ch ct]. *)
(*   rewrite IHFA_CONS. *)
(*   unfold c2p2 in P_HOLDS. inv P_HOLDS. ss. *)
(* Qed. *)

(* a b c *)
(* forall3 (fun a b => f a b = c) a b c *)

(* map (stream_des) c = (a, b) *)



(** * Z *)

Definition Z_to_nat2 (z: Z) : nat? :=
  if (z <? 0)%Z then None else Some (Z.to_nat z).

Definition zth {A} (z: Z) (l: list A) (d: A): A :=
  match Z_to_nat2 z with
  | None => d
  | Some n => nth n l d
  end.

Definition replace_zth {A} (l: list A) (z: Z) (a: A)
  : list A :=
  match Z_to_nat2 z with
  | None => l
  | Some n => replace_nth l n a
  end.



(** * Tactics *)

Tactic Notation "renames" ident(A) ident(B) "into" ident(X) ident(Y) :=
  rename A into X; rename B into Y.

Tactic Notation "renames" ident(A) ident(B) ident(C) "into" ident(X) ident(Y) ident(Z) :=
  rename A into X; rename B into Y; rename C into Z.

(* subst after existT_elim1 doesn't work in some cases *)
(* we don't want to call 'clarify' messing up the proof context. *)
Ltac existT_elim1 :=
  match goal with
  | H: existT _ ?T1 ?v1 = existT _ ?T2 ?v2 |- _ =>
    match T1 with
    | T2 => apply EqdepTheory.inj_pair2 in H
    | _ => assert (T1 = T2) by (apply EqdepFacts.eq_sigT_fst in H; ss);
          subst T2
    end
  end.

Ltac existT_elim := repeat existT_elim1.

(* Ltac existT_elim := *)
(*   repeat match goal with *)
(*          | H: existT _ ?T1 _ = existT _ ?T2 _ |- _ => *)
(*            match T1 with *)
(*            | T2 => apply EqdepTheory.inj_pair2 in H; clarify *)
(*            | _ => assert (T1 = T2) by (apply EqdepFacts.eq_sigT_fst in H; ss); clarify *)
(*            end *)
(*          end. *)

(* classic : forall P : Prop, P \/ ~ P *)
(* Print Assumptions EqdepTheory.inj_pair2. *)

Ltac clear_tt :=
  repeat match goal with
         | H: ?x = ?x |- _ => clear H
         end.

(* Ltac solve_divide := *)
(*   match goal with *)
(*   | |- Z.divide ?a ?b => *)
(*     (* let v := eval compute in (Z.div b a) in *) *)
(*     let v := constr:(Z.div b a) in *)
(*     (exists v; ss) *)
(*   | |- Z.divide ?a (?b1 + ?b2) => *)
(*     apply Z.divide *)
(*   end. *)


Ltac solve_divide :=
  match goal with
  | |- Z.divide 1%Z _ =>
    apply Z.divide_1_l
  | |- Z.divide ?a (?b1 + ?b2) =>
    apply Z.divide_add_r; solve_divide
  | |- Z.divide ?a (?b1 * ?b2) =>
    try (by apply Z.divide_mul_r; solve_divide);
    try (by apply Z.divide_mul_l; solve_divide)
  | |- Z.divide ?a ?b =>
    (* let v := eval compute in (Z.div b a) in *)
    let v := constr:(Z.div b a) in
    (exists v; ss)
  end.


(** TODO *)


Lemma snoc_length A
      l (a: A)
  : length (snoc l a) = S (length l).
Proof.
  unfold snoc. rewrite app_length.
  ss. nia.
Qed.






Lemma exists_list A
      (P: nat -> A -> Prop) m
      (ELEM_EX: forall n (LT: n < m),
          exists a:A, P n a)
  : exists l,
    <<LIST_LEN: length l = m>> /\
                <<NTH_PROP: forall n a (NTH: nth_error l n = Some a), P n a>>.
Proof.
  induction m as [| m'].
  { exists []. splits; ss. destruct n; ss. }

  hexploit (ELEM_EX m'); eauto.
  destruct 1 as [a PA].
  hexploit IHm'; eauto. i. des.
  exists (snoc l a).
  split.
  - r. rewrite snoc_length. nia.
  - r. unfold snoc.
    intros n b NTH.
    destruct (lt_eq_lt_dec n (length l)) as
        [[LT | EQ] | LT].
    + rewrite nth_error_app1 in NTH by ss.
      eauto.
    + rewrite nth_error_app2 in NTH by nia.
      rewrite <- EQ in NTH.
      rewrite Nat.sub_diag in NTH. ss. clarify.
    + cut (nth_error (l ++ [a]) n = None).
      { congruence. }
      apply nth_error_None.
      rewrite app_length. ss. nia.
Qed.



Lemma repeat_spec_nth A
      (a: A) n m x
      (REP_NTH: nth_error (repeat a n) m = Some x)
  : x = a.
Proof.
  eapply nth_error_In in REP_NTH.
  eapply repeat_spec in REP_NTH.
  ss.
Qed.

Lemma map_repeat A B
      (f: A -> B)
      a n
  : List.map f (repeat a n) =
    repeat (f a) n.
Proof.
  induction n as [| n' IH]; ss.
  rewrite IH. ss.
Qed.

Lemma map_id_ext
  : forall (A : Type) (l : list A)
      (f: A -> A)
      (F_ID: forall a (IN: In a l), f a = a)
  ,
    List.map f l = l.
Proof.
  i. induction l as [| h t IH]; ss.
  hexploit (F_ID h); ss.
  { eauto. }
  intro F_H. rewrite F_H.
  hexploit IH; eauto.
  congruence.
Qed.


Lemma map_nth_error_iff A B
      (f: A -> B)
      l i b
  : nth_error (List.map f l) i = Some b <->
    exists a, nth_error l i = Some a /\ f a = b.
Proof.
  split.
  - depgen i.
    induction l as [| h t IH]; ss.
    { i. destruct i; ss. }
    i. destruct i; ss.
    { clarify. eauto. }
    eauto.
  - depgen i.
    induction l as [| h t IH]; ss.
    { i. des. destruct i; ss. }
    i. des.
    destruct i; ss.
    { clarify. }
    eauto.
Qed.

Lemma map_nth_error_None_iff A B
      (f: A -> B)
      l i
  : nth_error (map f l) i = None <->
    nth_error l i = None.
Proof.
  split.
  - intro MAP_LEN.
    eapply nth_error_None in MAP_LEN.
    eapply nth_error_None.
    rewrite map_length in MAP_LEN. ss.
  - intro LEN.
    eapply nth_error_None in LEN.
    eapply nth_error_None.
    rewrite map_length. ss.
Qed.

Lemma map_nth_error_rw A B
      (f: A -> B)
      l i
  : nth_error (map f l) i = option_map f (nth_error l i).
Proof.
  depgen i.
  induction l as [| h t IH]; i; ss.
  { destruct i; ss. }
  destruct i; ss.
Qed.

(* Lemma map_nth_error_inv A B *)
(*       (f: A -> B) *)
(*       l i b *)
(*       (a: A) *)
(*       (MAP_NTH_SOME: nth_error (List.map f l) i = Some b) *)
(*   : exists a, nth_error l i = Some a /\ f a = b. *)
(* Proof. *)
(*   apply map_nth_error_iff. ss. *)
(* Qed. *)


Definition uncurry {A B C: Type}
           (f: A -> B -> C)
  : A * B -> C :=
  fun x => f (fst x) (snd x).

Definition uncurry_p {A B: Type}
           (P: A -> B -> Prop)
  : A * B -> Prop :=
  fun x => P (fst x) (snd x).


Definition opt2bool {A} (oa: option A): bool :=
  if oa then true else false.

Coercion opt2bool : option >-> bool.


Definition is_in_range (n1 n2: nat) (n: nat): bool :=
  (andb (n1 <=? n) (n <? n2))%nat.




Lemma Forall2_det A B
      (P: A -> B -> Prop)
      l l1 l2
      (FA1: Forall2 P l l1)
      (FA2: Forall2 P l l2)
      (P_DET: forall a b1 b2, P a b1 -> P a b2 -> b1 = b2)
  : l1 = l2.
Proof.
  generalize dependent l2.
  induction FA1; i; ss.
  { inv FA2. ss. }
  inv FA2.
  f_equal; eauto.
Qed.





Lemma Forall_nth A
      P (l: list A)
  : Forall P l <->
    (forall n, option_rel1 P (nth_error l n)).
Proof.
  split.
  - intro FA. induction FA; i; ss.
    { destruct n; ss. }
    destruct n; ss.
  - induction l as [|h t IH]; ss.
    intro OPTREL. econs.
    { specialize (OPTREL O). ss. }
    apply IH.
    intro n.
    specialize (OPTREL (S n)). ss.
Qed.



Lemma nodup_div A
      (l l1 l2: list A) a
      (NODUP: NoDup l)
      (L_DIV: l = l1 ++ [a] ++ l2)
  : Forall (fun x => x <> a) l1 /\
    Forall (fun x => x <> a) l2.
Proof.
  depgen l. depgen l2.
  induction l1 as [| h1 t1 IH]; i; ss.
  { subst.
    split.
    - econs.
    - inv NODUP.
      apply Forall_forall. ii. congruence.
  }
  subst.
  inv NODUP.
  hexploit IH; eauto. i. des.

  split; eauto.
  econs; eauto.
  ii. subst.

  cut (In a (t1 ++ a::l2)).
  { i. congruence. }
  apply in_or_app.
  right. ss. eauto.
Qed.


Lemma existsb_false_iff A
      (f: A -> bool) l
  : existsb f l = false <->
    Forall (fun x => f x = false) l.
Proof.
  split.
  - i.
    assert (CONT: ~ (exists x : A, In x l /\ f x = true)).
    { intro EX_TRUE.
      apply existsb_exists in EX_TRUE.
      congruence. }

    apply Forall_forall.
    intros x IN.
    destruct (f x) eqn: FX; ss.
    exfalso. apply CONT; eauto.
  - intro FA.
    induction FA; ss.
    rewrite IHFA.
    intuition.
Qed.

Lemma nth_error_eqlen_None A B
      (l1: list A) (l2: list B) n
      (EQLEN: length l1 = length l2)
  : nth_error l1 n = None -> nth_error l2 n = None.
Proof.
  depgen l2. revert n.
  induction l1 as [| h1 t1 IH]; i; ss.
  { destruct l2; destruct n; ss. }
  destruct l2 as [| h2 t2]; ss.
  destruct n; ss.
  eauto.
Qed.

Lemma nth_error_eqlen_Some A B
      (l1: list A) (l2: list B) n a
      (EQLEN: length l1 = length l2)
      (SOME1: nth_error l1 n = Some a)
  : exists b, nth_error l2 n = Some b.
Proof.
  depgen l2. depgen n.
  induction l1 as [| h1 t1 IH]; i; ss.
  { destruct l2; destruct n; ss. }
  destruct l2 as [| h2 t2]; ss.
  destruct n; ss; eauto.
Qed.



Lemma repeat_nth_error_Some A
      (a: A) n i
      (I_LT: i < n)
  : nth_error (repeat a n) i = Some a.
Proof.
  depgen i.
  induction n as [| n' IH]; i; ss.
  { inv I_LT. }
  destruct i; ss.
  apply IH. nia.
Qed.

Lemma repeat_nth_error_None A
      (a: A) n i
      (I_LT: n <= i)
  : nth_error (repeat a n) i = None.
Proof.
  depgen i.
  induction n as [| n' IH]; i; ss.
  { destruct i; ss. }
  destruct i; ss.
  { inv I_LT. }
  apply IH. nia.
Qed.


Lemma filter_all_ok A
      f (l: list A)
      (FA_OK: Forall (fun a => f a = true) l)
  : filter f l = l.
Proof.
  induction l as [| h t IH]; ss.
  inv FA_OK.
  desf. rewrite IH; eauto.
Qed.


Lemma filter_length A
      (f: A -> bool)
      l
  : length (filter f l) <= length l.
Proof.
  induction l as [| h t IH]; ss.
  desf; ss; nia.
Qed.




Lemma Forall2_nth1 A B
      (P: A -> B -> Prop)
      l1 l2 n e1
      (FA: Forall2 P l1 l2)
      (NTH1: nth_error l1 n = Some e1)
  : exists e2,
    <<NTH2: nth_error l2 n = Some e2>> /\
             <<P_FA: P e1 e2>>.
Proof.
  rewrite Forall2_nth in FA.
  specialize (FA n).
  inv FA.
  { congruence. }
  esplits; eauto. congruence.
Qed.

Lemma Forall2_nth2 A B
      (P: A -> B -> Prop)
      l1 l2 n e2
      (FA: Forall2 P l1 l2)
      (NTH2: nth_error l2 n = Some e2)
  : exists e1,
    <<NTH1: nth_error l1 n = Some e1>> /\
             <<P_FA: P e1 e2>>.
Proof.
  rewrite Forall2_nth in FA.
  specialize (FA n).
  inv FA.
  { congruence. }
  esplits; eauto. congruence.
Qed.


Section FORALL3.
  Variable A B C: Type.
  Variable P: A -> B -> C -> Prop.

  Lemma Forall3_nth1
        n e1
        l1 l2 l3
        (FA: Forall3 P l1 l2 l3)
        (NTH1: nth_error l1 n = Some e1)
    : exists e2 e3,
      <<NTH2: nth_error l2 n = Some e2>> /\
      <<NTH3: nth_error l3 n = Some e3>> /\
      <<P_FA: P e1 e2 e3>>.
  Proof.
    rewrite Forall3_nth in FA.
    specialize (FA n).
    inv FA.
    { congruence. }
    esplits; eauto.
    congruence.
  Qed.

  Lemma Forall3_nth2
        n e2
        l1 l2 l3
        (FA: Forall3 P l1 l2 l3)
        (NTH2: nth_error l2 n = Some e2)
    : exists e1 e3,
      <<NTH1: nth_error l1 n = Some e1>> /\
      <<NTH3: nth_error l3 n = Some e3>> /\
      <<P_FA: P e1 e2 e3>>.
  Proof.
    rewrite Forall3_nth in FA.
    specialize (FA n).
    inv FA.
    { congruence. }
    esplits; eauto.
    congruence.
  Qed.

  Lemma Forall3_nth3
        n e3
        l1 l2 l3
        (FA: Forall3 P l1 l2 l3)
        (NTH3: nth_error l3 n = Some e3)
    : exists e1 e2,
      <<NTH1: nth_error l1 n = Some e1>> /\
      <<NTH2: nth_error l2 n = Some e2>> /\
      <<P_FA: P e1 e2 e3>>.
  Proof.
    rewrite Forall3_nth in FA.
    specialize (FA n).
    inv FA.
    { congruence. }
    esplits; eauto.
    congruence.
  Qed.

End FORALL3.



Section FORALL4.
  Variable A B C D: Type.
  Variable P: A -> B -> C -> D -> Prop.

  Lemma Forall4_nth1
        n e1
        l1 l2 l3 l4
        (FA: Forall4 P l1 l2 l3 l4)
        (NTH1: nth_error l1 n = Some e1)
    : exists e2 e3 e4,
      <<NTH2: nth_error l2 n = Some e2>> /\
      <<NTH3: nth_error l3 n = Some e3>> /\
      <<NTH4: nth_error l4 n = Some e4>> /\
      <<P_FA: P e1 e2 e3 e4>>.
  Proof.
    rewrite Forall4_nth in FA.
    specialize (FA n).
    inv FA.
    { congruence. }
    esplits; eauto.
    congruence.
  Qed.

  Lemma Forall4_nth2
        n e2
        l1 l2 l3 l4
        (FA: Forall4 P l1 l2 l3 l4)
        (NTH2: nth_error l2 n = Some e2)
    : exists e1 e3 e4,
      <<NTH1: nth_error l1 n = Some e1>> /\
      <<NTH3: nth_error l3 n = Some e3>> /\
      <<NTH4: nth_error l4 n = Some e4>> /\
      <<P_FA: P e1 e2 e3 e4>>.
  Proof.
    rewrite Forall4_nth in FA.
    specialize (FA n).
    inv FA.
    { congruence. }
    esplits; eauto.
    congruence.
  Qed.

  Lemma Forall4_nth3
        n e3
        l1 l2 l3 l4
        (FA: Forall4 P l1 l2 l3 l4)
        (NTH3: nth_error l3 n = Some e3)
    : exists e1 e2 e4,
      <<NTH1: nth_error l1 n = Some e1>> /\
      <<NTH2: nth_error l2 n = Some e2>> /\
      <<NTH4: nth_error l4 n = Some e4>> /\
      <<P_FA: P e1 e2 e3 e4>>.
  Proof.
    rewrite Forall4_nth in FA.
    specialize (FA n).
    inv FA.
    { congruence. }
    esplits; eauto.
    congruence.
  Qed.

  Lemma Forall4_nth4
        n e4
        l1 l2 l3 l4
        (FA: Forall4 P l1 l2 l3 l4)
        (NTH4: nth_error l4 n = Some e4)
    : exists e1 e2 e3,
      <<NTH1: nth_error l1 n = Some e1>> /\
      <<NTH2: nth_error l2 n = Some e2>> /\
      <<NTH3: nth_error l3 n = Some e3>> /\
      <<P_FA: P e1 e2 e3 e4>>.
  Proof.
    rewrite Forall4_nth in FA.
    specialize (FA n).
    inv FA.
    { congruence. }
    esplits; eauto.
    congruence.
  Qed.

End FORALL4.

Lemma Forall_nth1 A
      (P: A -> Prop)
      l n e
      (FA: Forall P l)
      (NTH: nth_error l n = Some e)
  : P e.
Proof.
  rewrite Forall_forall in FA.
  apply FA.
  eapply nth_error_In; eauto.
Qed.





(**)

Inductive iForall {A}
          (P: nat -> A -> Prop)
  : nat -> list A -> Prop :=
| iForall_nil m
  : iForall P m []
| iForall_cons
    m (h: A) (t: list A)
    (P_HEAD: P m h)
    (FA: iForall P (S m) t)
  : iForall P m (h :: t)
.

Inductive iForall2 {A B}
          (P: nat -> A -> B -> Prop)
  : nat -> list A -> list B -> Prop :=
| iForall2_nil m
  : iForall2 P m [] []
| iForall2_cons
    m ha ta hb tb
    (P_HEAD: P m ha hb)
    (FA: iForall2 P (S m) ta tb)
  : iForall2 P m (ha :: ta) (hb :: tb)
.

Inductive iForall3 {A B C}
          (P: nat -> A -> B -> C -> Prop)
  : nat -> list A -> list B -> list C -> Prop :=
| iForall3_nil m
  : iForall3 P m [] [] []
| iForall3_cons
    m ha ta hb tb hc tc
    (P_HEAD: P m ha hb hc)
    (FA: iForall3 P (S m) ta tb tc)
  : iForall3 P m (ha :: ta) (hb :: tb) (hc :: tc)
.

Inductive iForall4 {A B C D}
          (P: nat -> A -> B -> C -> D -> Prop)
  : nat -> list A -> list B -> list C -> list D -> Prop :=
| iForall4_nil m
  : iForall4 P m [] [] [] []
| iForall4_cons
    m ha ta hb tb hc tc hd td
    (P_HEAD: P m ha hb hc hd)
    (FA: iForall4 P (S m) ta tb tc td)
  : iForall4 P m (ha :: ta) (hb :: tb)
             (hc :: tc) (hd :: td)
.


Section I_FORALL.
  Variable A: Type.
  Variable P: nat -> A -> Prop.

  Lemma iForall_nth m l
    : iForall P m l <->
      (forall n, option_rel1 (P (m + n)) (nth_error l n)).
  Proof.
    split.
    - intro IFA.
      induction IFA; i; ss.
      + destruct n; ss.
      + destruct n; ss.
        * rewrite plus_0_r. ss.
        * rewrite <- plus_n_Sm. eauto.
    - revert m.
      induction l as [|h t IH].
      + i. econs.
      + intros m NTH.
        hexploit (NTH 0); eauto.
        rewrite plus_0_r. ss.
        intro P_HEAD.
        econs; eauto.
        eapply IH.
        i. hexploit (NTH (S n)); eauto.
        rewrite <- plus_n_Sm. eauto.
  Qed.

  Lemma iForall_nth1 m l
        n a
        (FA: iForall P m l)
        (NTH: nth_error l n = Some a)
    : P (m + n) a.
  Proof.
    depgen n.
    induction FA; i; ss.
    { destruct n; ss. }
    destruct n; ss.
    { rewrite plus_0_r. clarify. }
    rewrite <- plus_n_Sm.
    eauto.
  Qed.

  (* Lemma iForall_Forall *)
  (*       (Q: A -> Prop) m l *)
  (*   : iForall (fun _ => Q) m l <-> Forall Q l. *)
  (* Proof. *)
  (* . *)

End I_FORALL.

Section I_FORALL2.
  Variable A B: Type.
  Variable P: nat -> A -> B -> Prop.

  Lemma iForall2_nth m la lb
    : iForall2 P m la lb <->
      (forall n, option_rel2 (P (m + n))
                        (nth_error la n)
                        (nth_error lb n)).
  Proof.
    split.
    - intro IFA.
      induction IFA; i; ss.
      + destruct n; ss; econs.
      + destruct n; ss.
        * rewrite plus_0_r. ss.
          econs. eauto.
        * rewrite <- plus_n_Sm. eauto.
    - intro NTH.
      depgen m. depgen lb.
      induction la as [|ha ta IH]; i; ss.
      + destruct lb; ss.
        * econs.
        * specialize (NTH 0); ss. inv NTH.
      + hexploit (NTH 0); eauto.
        rewrite plus_0_r. ss.
        intro P_HEAD.
        destruct lb as [| hb tb]; inv P_HEAD.

        econs; eauto.
        eapply IH. i.
        hexploit (NTH (S n)); eauto.
        rewrite <- plus_n_Sm. ss.
  Qed.

  (* Lemma iForall2_nth1 *)
  (*       m la lb *)
  (*       n a b *)
  (*       (FA: iForall2 P m la lb) *)
  (*       (NTH_A: nth_error la n = Some a) *)
  (*       (NTH_B: nth_error lb n = Some b) *)
  (*   : P (m + n) a b. *)
  (* Proof. *)
  (* . *)

  (* Lemma iForall2_Forall2 *)
  (*       (Q: A -> B -> Prop) m la lb *)
  (*   : iForall2 (fun _ => Q) m la lb <-> Forall2 Q la lb. *)
  (* Proof. *)
  (* . *)

End I_FORALL2.

Section I_FORALL3.
  Variable A B C: Type.
  Variable P: nat -> A -> B -> C -> Prop.

  Lemma iForall3_nth m la lb lc
    : iForall3 P m la lb lc <->
      (forall n, option_rel3 (P (m + n))
                        (nth_error la n)
                        (nth_error lb n)
                        (nth_error lc n)).
  Proof.
    split.
    - intro IFA.
      induction IFA; i; ss.
      + destruct n; ss; econs.
      + destruct n; ss.
        * rewrite plus_0_r. ss.
          econs. eauto.
        * rewrite <- plus_n_Sm. eauto.
    - intro NTH.
      depgen m. depgen lb. depgen lc.
      induction la as [|ha ta IH]; i; ss.
      + destruct lb; destruct lc; ss.
        * econs.
        * specialize (NTH 0); ss. inv NTH.
        * specialize (NTH 0); ss. inv NTH.
        * specialize (NTH 0); ss. inv NTH.
      + hexploit (NTH 0); eauto.
        rewrite plus_0_r. ss.
        intro P_HEAD.
        destruct lb; destruct lc; inv P_HEAD.

        econs; eauto.
        eapply IH. i.
        hexploit (NTH (S n)); eauto.
        rewrite <- plus_n_Sm. ss.
  Qed.

  (* Lemma iForall3_nth1 *)
  (*       m la lb lc *)
  (*       n a b c *)
  (*       (FA: iForall3 P m la lb lc) *)
  (*       (NTH_A: nth_error la n = Some a) *)
  (*       (NTH_B: nth_error lb n = Some b) *)
  (*       (NTH_C: nth_error lc n = Some c) *)
  (*   : P (m + n) a b c. *)
  (* Proof. *)
  (* . *)

  (* Lemma iForall3_Forall3 *)
  (*       (Q: A -> B -> C -> Prop) m la lb lc *)
  (*   : iForall3 (fun _ => Q) m la lb lc <-> *)
  (*     Forall3 Q la lb lc. *)
  (* Proof. *)
  (* . *)


  Lemma iForall3_length
        n la lb lc
        (FA: iForall3 P n la lb lc)
    : length la = length lb /\ length la = length lc.
  Proof.
    induction FA; ss.
    des. splits; nia.
  Qed.

End I_FORALL3.

(* Section I_FORALL4. *)
(*   Variable A B C D: Type. *)
(*   Variable P: nat -> A -> B -> C -> D -> Prop. *)

(*   Lemma iForall4_nth m la lb lc ld *)
(*     : iForall4 P m la lb lc ld <-> *)
(*       (forall n, option_rel4 (P (m + n)) *)
(*                         (nth_error la n) *)
(*                         (nth_error lb n) *)
(*                         (nth_error lc n) *)
(*                         (nth_error ld n)). *)
(*   Proof. *)
(*   . *)

(*   Lemma iForall4_nth1 *)
(*         m la lb lc ld *)
(*         n a b c d *)
(*         (FA: iForall4 P m la lb lc ld) *)
(*         (NTH_A: nth_error la n = Some a) *)
(*         (NTH_B: nth_error lb n = Some b) *)
(*         (NTH_C: nth_error lc n = Some c) *)
(*         (NTH_D: nth_error ld n = Some d) *)
(*     : P (m + n) a b c d. *)
(*   Proof. *)
(*   . *)

(*   Lemma iForall4_Forall4 *)
(*         (Q: A -> B -> C -> D -> Prop) *)
(*         m la lb lc ld *)
(*     : iForall4 (fun _ => Q) m la lb lc ld <-> *)
(*       Forall4 Q la lb lc ld. *)
(*   Proof. *)
(*   . *)

(* End I_FORALL4. *)


Fixpoint imap {A B} (f: nat -> A -> B) (m: nat)
           (l: list A)
  : list B :=
  match l with
  | [] => []
  | h::t => (f m h) :: imap f (S m) t
  end.

(* Lemma imap_degen A B *)
(*       (f: A -> B) *)
(*       m (l: list A) *)
(*   : map f l = imap (fun _ => f) m l. *)
(* Proof. *)
(* (* . *) *)

Lemma imap_nth_error_iff A B
      (f: nat -> A -> B) m (l: list A) n
  : nth_error (imap f m l) n =
    option_map (f (m + n)) (nth_error l n).
Proof.
  revert m n.
  induction l as [| h t IH]; i; ss.
  { destruct n; ss. }
  destruct n as [| n']; ss.
  { rewrite plus_0_r. ss. }
  rewrite IH.
  rewrite <- plus_n_Sm. ss.
Qed.

Corollary imap_nth_error1 A B
      (f: nat -> A -> B) m (l: list A) n a
      (L_N: nth_error l n = Some a)
  : nth_error (imap f m l) n = Some (f (m + n) a).
Proof.
  rewrite imap_nth_error_iff.
  rewrite L_N. ss.
Qed.

Corollary imap_nth_error_inv A B
      (f: nat -> A -> B) m (l: list A) n b
      (ML_N: nth_error (imap f m l) n = Some b)
  : exists a, <<L_N: nth_error l n = Some a>> /\
         <<APPLY_IMAPFUN: f (m + n) a = b>>.
Proof.
  rewrite imap_nth_error_iff in ML_N.
  destruct (nth_error l n); ss.
  clarify. esplits; eauto.
Qed.

Lemma imap_length A B
      (f: nat -> A -> B) m l
  : length (imap f m l) = length l.
Proof.
  revert m.
  induction l as [|h t IH]; ss; eauto.
Qed.

Definition attach_index {A} m (l: list A): list (nat * A) :=
  imap pair m l.

(* Fixpoint attach_index' {A} (n: nat) (l: list A): list (nat * A) := *)
(*   match l with *)
(*   | [] => [] *)
(*   | h::t => (n, h) :: attach_index' (S n) t *)
(*   end. *)

(* Definition attach_index {A} (l: list A) : list (nat * A) := *)
(*   attach_index' 0 l. *)

Lemma attach_index_spec A
      (m: nat) (l: list A)
  : List.map fst (attach_index m l) = incr_nlist m (length l).
Proof.
  depgen m.
  unfold attach_index.
  induction l as [| h t IH]; i; ss.
  rewrite IH. eauto.
Qed.

Lemma attach_index_nth_error A
      l i_bgn
      i i' (a: A)
  : (nth_error l i = Some a /\ i' = i_bgn + i) <->
    (nth_error (attach_index i_bgn l) i = Some (i', a)).
Proof.
  unfold attach_index.
  split.
  - intros [NTH EQ]. subst i'.
    rewrite imap_nth_error_iff.
    rewrite NTH. ss.
  - intros NTH_ATT.
    rewrite imap_nth_error_iff in NTH_ATT.
    destruct (nth_error l i); ss.
    clarify.
Qed.

Fixpoint ifilter {A} (f: nat -> A -> bool) (m: nat) (l: list A)
  : list (nat * A) :=
  match l with
  | [] => []
  | h :: t =>
    if f m h then
      (m, h) :: ifilter f (S m) t
    else
      ifilter f (S m) t
  end.


Lemma ifilter_spec A
      (f: nat -> A -> bool)
      m n a l
  : In (n, a) (ifilter f m l) <->
    (exists i,
        <<N_EQ: n = m + i>> /\
        <<NTH: nth_error l i = Some a>> /\
        <<F_TRUE: f n a = true>>).
Proof.
  split.
  - depgen m. depgen n.
    induction l as [| h t IH].
    { i. ss. }
    intros n m IN. ss.
    destruct (f m h) eqn:F_H; ss.
    2: { hexploit IH; eauto. ss.
         i. des.
         exists (S i).
         esplits; eauto.
         nia. }
    des.
    { clarify.
      exists 0.
      esplits; eauto. }
    { hexploit IH; eauto. ss.
      i. des.
      exists (S i).
      esplits; eauto.
      nia. }
  - revert n m.
    induction l as [| h t IH]; ss.
    { i. des.
      destruct i; ss. }
    i. des.

    destruct i as [| i]; ss.
    { clarify.
      rewrite plus_0_r in *.
      rewrite F_TRUE. ss. eauto. }

    hexploit (IH n (S m)); eauto.
    { exists i. esplits; eauto. nia. }
    intro IN.

    desf. ss. right. eauto.
Qed.


Fixpoint andb_all (l: list bool): bool :=
  match l with
  | [] => true
  | h :: t => andb h (andb_all t)
  end.

Lemma andb_all_true_iff l
  : andb_all l = true <->
    forall b (IN: In b l), b = true.
Proof.
  split.
  - intros ALL_TRUE.
    induction l as [| h t IH]; ss.
    apply andb_true_iff in ALL_TRUE. des.
    i. des; eauto.
  - intros FORALL_TRUE.
    induction l as [| h t IH]; ss.
    apply andb_true_iff.
    split.
    + apply FORALL_TRUE; eauto.
    + apply IH; eauto.
Qed.

Lemma andb_all_false_iff l
  : andb_all l = false <-> In false l.
Proof.
  induction l as [| h t IH]; ss.
  split; ss.
  - rewrite andb_false_iff.
    intros [? | ALL_FALSE]; eauto.
    right. apply IH; eauto.
  - rewrite andb_false_iff.
    intros [? | FALSE_IN]; eauto.
    right. apply IH; eauto.
Qed.


Lemma des_snoc A (l: list A)
      (LEN_POS: 0 < length l)
  : exists l_h x, l = snoc l_h x.
Proof.
  induction l as [|h t]; ss.
  { inv LEN_POS. }
  destruct t as [| h_t t_t]; ss.
  - exists [], h. ss.
  - hexploit IHt; eauto.
    { nia. }
    intro R. des. rewrite R.
    exists (h::l_h), x. ss.
Qed.

(* Lemma list_divide_succ A *)
(*       (l l1 l2: list A) n *)
(*       (APP: l = l1 ++ l2) *)
(*       (LEN_EQ: length l1 = n) *)
(*   : list_divide l n = Some (l1, l2). *)
(* Proof. *)
(*   depgen l1. revert n. *)
(*   induction l as [| h t IH]; i; ss. *)
(*   { destruct l1; ss. subst. ss. } *)
(*   destruct l1 as [|h1 t1]; ss. *)
(*   { subst. ss. } *)
(*   destruct n as [|n]; ss. *)
(*   inv APP. *)
(*   erewrite IH; eauto. *)
(* Qed. *)


Lemma skipn_nth A
      n l h t (d: A)
      (SKIPN_HD: skipn n l = h::t)
  : nth n l d = h.
Proof.
  revert n h t SKIPN_HD.
  induction l as [|hl tl IH]; i; ss.
  { destruct n; ss. }
  destruct n as [|n]; ss.
  - inv SKIPN_HD. ss.
  - eauto.
Qed.


Lemma skipn_nth_next A
      n l (h: A) t
      (SKIPN_HD: skipn n l = h::t)
  : skipn (S n) l = t.
Proof.
  revert n h t SKIPN_HD.
  induction l as [|hl tl IH]; i; ss.
  { destruct n; ss. }
  destruct n as [|n]; ss.
  - inv SKIPN_HD. ss.
  - eauto.
Qed.

Lemma skipn_nil_implies A
      n (l: list A)
      (SKIPN_NIL: skipn n l = [])
  : (length l <= n)%nat.
Proof.
  depgen n.
  induction l as [| h t IH]; i; ss.
  { nia. }
  destruct n; ss.
  hexploit IH; eauto. nia.
Qed.





Lemma map_firstn A B
      (f: A -> B)
      n (l: list A)
  : map f (firstn n l) = firstn n (map f l).
Proof.
  depgen n.
  induction l as [| h t IH]; i; ss.
  { destruct n; ss. }
  destruct n as [|n]; ss.
  rewrite IH. ss.
Qed.




Lemma repeat_nth_default A
      (a: A) n m
  : nth n (repeat a m) a = a.
Proof.
  revert n.
  induction m; i; ss.
  { destruct n; ss. }
  destruct n; ss.
Qed.


Lemma nth_eq_list_eq A
      (l1 l2: list A)
      (NTH_EQ: forall n, nth_error l1 n = nth_error l2 n)
  : l1 = l2.
Proof.
  depgen l2.
  induction l1 as [| h1 t1 IH]; i; ss.
  { destruct l2; ss.
    specialize (NTH_EQ O). ss. }
  destruct l2 as [| h2 t2]; ss.
  { specialize (NTH_EQ O). ss. }
  generalize (NTH_EQ O). ss. inversion 1.
  hexploit IH.
  { i. specialize (NTH_EQ (S n)).
    s in NTH_EQ. apply NTH_EQ. }
  i. congruence.
Qed.


Lemma nth_eq_list_eq' A
      (l1 l2: list A)
      (LEN_EQ: length l1 = length l2)
      (NTH_EQ: forall n a b
                 (NTH1: nth_error l1 n = Some a)
                 (NTH2: nth_error l2 n = Some b),
          a = b)
  : l1 = l2.
Proof.
  depgen l2.
  induction l1 as [| h1 t1 IH]; i; ss.
  { destruct l2; ss. }
  destruct l2 as [| h2 t2]; ss.
  hexploit (NTH_EQ 0); ss.
  intro H_EQ. subst.
  f_equal.
  eapply IH; eauto. i.
  eapply (NTH_EQ (S n)); ss.
Qed.


Lemma not_in_nil A
      (l: list A)
      (NOT_IN: forall a, ~ In a l)
  : l = [].
Proof.
  induction l as [|h t IH]; ss.
  exfalso.
  eapply NOT_IN. left; eauto.
Qed.


Lemma deopt_list_Some_iff A
      (l: list A?) (l': list A)
  : deopt_list l = Some l' <->
    map (fun x => Some x) l' = l.
Proof.
  split.
  - intro DEOPT.
    depgen l'.
    induction l as [| h t IH]; i; ss.
    { inv DEOPT. ss. }
    destruct h; ss.
    desf. ss.
    rewrite IH; eauto.
  - intro MAP.
    depgen l.
    induction l' as [|h t IH]; i; ss.
    { subst. ss. }
    destruct l as [| p q]; ss. clarify.
    rewrite IH; eauto.
Qed.





Lemma Forall_filter_id A
      (P: A -> Prop)
      (l: list A?)
  : Forall (option_rel1 P) l <->
    Forall P (filtermap id l).
Proof.
  split.
  - intro FA.
    rewrite Forall_forall in *.
    intros a IN_F.
    apply filtermap_in in IN_F.
    unfold id in IN_F. des. clarify.
    hexploit FA; eauto.
  - intro FA.
    rewrite Forall_forall in *.
    intros [a|] IN; ss.
    apply FA.
    eapply in_filtermap; eauto.
    unfold id. ss.
Qed.

Lemma constr_repeat A l n
      (a: A)
      (LEN: n = length l)
      (FA_EQ: Forall (fun x => x = a) l)
  : l = repeat a n.
Proof.
  subst n.
  induction FA_EQ; ss.
  subst. congruence.
Qed.

Lemma Forall3_app_inv3 A B C
      (P: A -> B -> C -> Prop)
      a b c1 c2
      (FA: Forall3 P a b (c1 ++ c2))
  : exists a1 a2 b1 b2,
    a = a1 ++ a2 /\
    b = b1 ++ b2 /\
    Forall3 P a1 b1 c1 /\
    Forall3 P a2 b2 c2.
Proof.
  depgen a. depgen b.
  induction c1 as [ | hc1 tc1 IH]; i; ss.
  { exists [], a, [], b.
    splits; ss. econs. }

  inv FA.
  hexploit IH; eauto. i. des.
  esplits; eauto; cycle 2.
  { econs; eauto. }
  { ss; congruence. }
  { ss; congruence. }
Qed.

Lemma Forall3_app A B C
      (P: A -> B -> C -> Prop)
      a1 a2 b1 b2 c1 c2
      (FA1: Forall3 P a1 b1 c1)
      (FA2: Forall3 P a2 b2 c2)
  : Forall3 P (a1 ++ a2) (b1 ++ b2) (c1 ++ c2).
Proof.
  induction FA1; ss.
  econs; eauto.
Qed.


Lemma repeat_app A
      (a: A)
      (n m: nat)
  : repeat a (n + m) = repeat a n ++ repeat a m.
Proof.
  induction n as [| n' IH]; ss.
  rewrite IH. eauto.
Qed.


Section TRANSPOSE.

  Inductive transpose {A: Type}
  : nat -> nat -> list (list A) -> list (list A) -> Prop :=
  | Transpose_nil
      c col
      (EMPTY_COLUMN: col = repeat [] c)
    : transpose O c [] col
  | Transpose_cons
      r c tr trT
      row trT'
      (TR: transpose r c tr trT)
      (CONS_EACH: cons_each_rel row trT trT')
    : transpose (S r) c (row :: tr) trT'
  .

  Lemma transpose_dims A
        (m m': list (list A))
        r c
        (TR: transpose r c m m')
    : <<NUM_ROWS: length m = r>> /\
      <<NUM_COLS: Forall (fun row => length row = c) m>> /\
      <<NUM_ROWS_T: length m' = c>> /\
      <<NUM_COLS_T: Forall (fun row => length row = r) m'>>.
  Proof.
    induction TR; ss.
    { subst.
      esplits; ss.
      - apply repeat_length.
      - apply Forall_forall.
        intros x IN.
        apply repeat_spec in IN.
        subst. ss.
    }
    des. subst.
    r in CONS_EACH.
    hexploit Forall3_length; eauto. i. des.

    esplits; ss.
    - econs; eauto.
    - congruence.
    - apply Forall_nth. i.
      rewrite Forall3_nth in CONS_EACH.
      destruct (nth_error trT' n) eqn:TRT'_N.
      2: { econs. }
      r. specialize (CONS_EACH n).
      rewrite TRT'_N in CONS_EACH.
      inv CONS_EACH. ss.
      rewrite Forall_nth in NUM_COLS_T.
      specialize (NUM_COLS_T n).
      r in NUM_COLS_T.
      destruct (nth_error trT n); ss.
      clarify. congruence.
  Qed.

  Lemma transpose_cons_each A
        r c (m m': list (list A))
        col1 cm
        (TR: transpose r c m m')
        (CONS_EACH_COL: cons_each_rel col1 m cm)
    : transpose r (S c) cm (col1 :: m').
  Proof.
    depgen col1. revert cm.
    induction TR; i; ss.
    { inv CONS_EACH_COL. econs. ss. }

    destruct col1 as [| h_col1 t_col1]; ss.
    { inv CONS_EACH_COL. }
    destruct cm as [| h_cm t_cm]; ss.
    { inv CONS_EACH_COL. }

    inv CONS_EACH_COL.
    econs.
    { eapply IHTR; eauto. }
    econs; ss.
  Qed.

  Lemma transpose_column A
        c (m: list (list A))
        (COL: m = repeat [] c)
    : transpose c 0 m [].
  Proof.
    depgen m.
    induction c as [| c IH]; i; ss.
    { subst. econs. ss. }
    subst.
    econs.
    2: { econs 1. }
    apply IH. ss.
  Qed.

  Lemma transpose_des_col A
        r c
        (m m': list (list A))
        (TRANSP: transpose r (S c) m m')
  : exists hs ts_m t_m',
    <<DES_M: cons_each_rel hs ts_m m>> /\
    <<DES_M': m' = hs :: t_m'>> /\
    <<TRANSP': transpose r c ts_m t_m'>>.
  Proof.
    remember (S c) as c'.
    depgen c.
    induction TRANSP.
    { i. subst.
      esplits.
      - econs.
      - ss.
      - econs. ss. }

    intros c' C. subst.
    hexploit IHTRANSP; eauto. i. des.
    subst.

    inv CONS_EACH.

    esplits.
    - econs; eauto.
    - eauto.
    - econs; eauto.
  Qed.

End TRANSPOSE.








Lemma nat_strong_ind
      (P: nat -> Prop)
      (PF: forall m (IH: forall n (N_SMALL: n < m), P n), P m)
  : forall n, P n.
Proof.
  pose (Q := fun n => forall k (K_SMALL: k < n), P k).
  intro l.

  hexploit (nat_ind Q).
  { r. ii. nia. }
  { subst Q.
    intros n IH. ss. i.
    eapply PF; eauto.
    i. eapply IH. nia. }
  instantiate (1:= l).
  subst Q. ss. eauto.
Qed.

Lemma nat_strong_rec
      (P: nat -> Set)
      (PF: forall m (IH: forall n (N_SMALL: n < m), P n), P m)
  : forall n, P n.
Proof.
  pose (Q := fun n => forall k (K_SMALL: k < n), P k).
  intro l.

  hexploit (nat_rec Q).
  { r. ii. nia. }
  { subst Q.
    intros n IH. ss. i.
    eapply PF; eauto.
    i. eapply IH. nia. }
  instantiate (1:= l).
  subst Q. ss. eauto.
Qed.


Lemma Nat_divide_dec n m
  : {Nat.divide n m} + {~ Nat.divide n m}.
Proof.
  (* revert m. *)
  (* eapply nat_strong_rec. *)
  (* i. *)
  destruct (Nat.eqb_spec n (Nat.gcd n m)) as [EQ|NEQ].
  - left.
    apply Nat.divide_gcd_iff; eauto. nia.
  - right.
    intro C.
    apply Nat.divide_gcd_iff in C.
    { congruence. }
    nia.
Qed.

Lemma Forall4_exists_list A B C D
      (R: A -> B -> C -> D -> Prop)
      l1
      (EACH_EX: forall e1 (IN: In e1 l1),
          exists e2 e3 e4, R e1 e2 e3 e4)
  : exists l2 l3 l4,
    Forall4 R l1 l2 l3 l4.
Proof.
  cut (forall (n: nat)
         (N_UBND: n < length l1),
          exists (x: B * C * D),
            (fun n x =>
               exists e1,
                 let '(e2, e3, e4) := x in
                 <<NTH1: nth_error l1 n = Some e1>> /\
                         <<REL: R e1 e2 e3 e4>>)
              n x).
  { intro AUX.
    apply exists_list in AUX. des.
    exists (map fst (map fst l)).
    exists (map snd (map fst l)).
    exists (map snd l).
    apply Forall4_nth. i.

    destruct (lt_ge_dec n (length l)).
    2: {
      rewrite nth_error_None2.
      2: { congruence. }
      rewrite nth_error_None2.
      2: { repeat rewrite map_length. ss. }
      rewrite nth_error_None2.
      2: { repeat rewrite map_length. ss. }
      rewrite nth_error_None2.
      2: { repeat rewrite map_length. ss. }
      econs.
    }

    hexploit (nth_error_Some2 _ l n); eauto. i. des.
    destruct e1 as [[b c] d].
    hexploit NTH_PROP; eauto. i. des.
    rewrite NTH1.
    erewrite map_nth_error; eauto.
    2: { erewrite map_nth_error; eauto. }
    erewrite map_nth_error; eauto.
    2: { erewrite map_nth_error; eauto. }
    erewrite map_nth_error; eauto.
    s.
    econs. ss.
  }

  i. s.
  hexploit (nth_error_Some2 _ l1 n); eauto. i. des.
  hexploit EACH_EX.
  { eapply nth_error_In; eauto. }
  i. des.
  exists (e2, e3, e4), e1.
  esplits; eauto.
Qed.

Lemma Forall_cons_ex A
      (hs: list A)
      (ts: list (list A))
      (LEN_EQ: length hs = length ts)
  : exists l, Forall3 (fun h t l => h :: t = l) hs ts l.
Proof.
  depgen ts.
  induction hs as [| h hs IH]; i; ss.
  { destruct ts; ss.
    esplits; eauto. econs. }

  destruct ts as [| t ts]; ss.
  hexploit IH; eauto. i. des.
  exists ((h :: t) :: l).
  econs; eauto.
Qed.

Lemma Forall_app_ex A
      (ls1 ls2: list (list A))
      (LEN_EQ: length ls1 = length ls2)
  : exists ls, Forall3 (fun l1 l2 l => l1 ++ l2 = l)
                  ls1 ls2 ls.
Proof.
  depgen ls2.
  induction ls1 as [| l1 ls1 IH]; i; ss.
  { destruct ls2; ss.
    esplits. econs. }
  destruct ls2 as [| l2 ls2]; ss.
  hexploit (IH ls2); eauto. i. des.
  exists ((l1 ++ l2) :: ls).
  econs; eauto.
Qed.


Lemma update_goal_lor (P P' Q: Prop)
      (PROP_IMPL: P -> P')
      (OR: P \/ Q)
  : P' \/ Q.
Proof.
  des; eauto.
Qed.


Lemma update_goal_ror (P Q Q': Prop)
      (PROP_IMPL: Q -> Q')
      (OR: P \/ Q)
  : P \/ Q'.
Proof.
  des; eauto.
Qed.








Lemma stream_app_overwrap A
      (l1 l2: list A) s1' s2'
      (DIV1: stream_app l1 s1' = stream_app l2 s2')
      (LEN: length l1 <= length l2)
  : exists l2r,
    <<L2_DIV: l2 = l1 ++ l2r>> /\
    <<S1'_DIV: s1' = stream_app l2r s2'>>.
Proof.
  depgen l2.
  induction l1 as [| h1 t1 IH]; i; ss.
  { subst. esplits; eauto. }

  destruct l2 as [| h2 t2]; ss.
  { exfalso. nia. }

  clarify.
  hexploit IH; eauto.
  { nia. }

  i. des.
  esplits; eauto. congruence.
Qed.

Lemma stream_app_3ways A
      (l1 l2: list A) (s1' s2': stream A)
      (DIV1: stream_app l1 s1' = stream_app l2 s2')
  : (exists l2r,
        <<L2R_NNIL: 0 < length l2r>> /\
        <<L2_DIV: l2 = l1 ++ l2r>> /\
        <<S1'_DIV: s1' = stream_app l2r s2'>>) \/
    (exists l1r,
        <<L1R_NNIL: 0 < length l1r>> /\
        <<L1_DIV: l1 = l2 ++ l1r>> /\
        <<S2'_DIV: s2' = stream_app l1r s1'>>) \/
    (l2 = l1 /\ s2' = s1')
.
Proof.
  destruct (lt_eq_lt_dec (length l1) (length l2)).
  2: {
    right. left.
    symmetry in DIV1.
    hexploit stream_app_overwrap; eauto.
    { nia. }
    i. des.
    esplits; eauto.
    destruct l2r; ss.
    - rewrite app_nil_r in L2_DIV. subst l2. nia.
    - nia.
  }
  destruct s.
  { left.
    hexploit stream_app_overwrap; eauto.
    { nia. }
    i. des.
    esplits; eauto.
    destruct l2r; ss.
    - rewrite app_nil_r in L2_DIV. subst l2. nia.
    - nia.
  }
  right. right.
  depgen l2.
  induction l1 as [| h1 t1 IH]; i; ss.
  { destruct l2 as [| h2 t2]; ss. }
  destruct l2 as [| h2 t2]; ss.
  clarify.
  hexploit IH; eauto. i. des.
  clarify.
Qed.




(**)

Lemma skipn_nth_error A
      (l: list A)
      n k
  : nth_error (skipn n l) k =
    nth_error l (k + n).
Proof.
  depgen k. depgen l.
  induction n as [| n' IH]; i; ss.
  { rewrite Nat.add_0_r. ss. }
  destruct l as [| h t]; ss.
  { destruct k; ss. }
  rewrite IH.
  replace (k + S n') with (S (k + n')) by nia.
  ss.
Qed.

Lemma nth_error_firstn A
      n l k (a: A)
      (NTH_FIRSTN: nth_error (firstn n l) k = Some a)
  : <<K_RANGE: k < n>> /\
               <<NTH_ERR: nth_error l k = Some a>>.
Proof.
  depgen n. depgen k.
  induction l as [| h t IH]; i; ss.
  { destruct n; destruct k; ss. }

  destruct n as [| n]; ss.
  { destruct k; ss. }
  destruct k as [| k]; ss.
  { clarify. esplits; ss. nia. }
  hexploit IH; eauto. i. des.
  esplits; ss. nia.
Qed.


Lemma iForall3_app A B C
      (P: nat -> A -> B -> C -> Prop)
      n1 n2 l1 l2 l3 l1' l2' l3'
      (IFA1: iForall3 P n1 l1 l2 l3)
      (IFA2: iForall3 P n2 l1' l2' l3')
      (N2_EQ: n2 = n1 + length l1)
  : iForall3 P n1 (l1 ++ l1') (l2 ++ l2') (l3 ++ l3').
Proof.
  subst n2.
  depgen n1. depgen l2. depgen l3.
  induction l1 as [| h1 t1 IH]; i; ss.
  { inv IFA1.
    rewrite plus_0_r in IFA2. ss. }
  inv IFA1.
  hexploit IH; eauto.
  { rewrite <- plus_n_Sm in IFA2. ss. }
  i. econs; eauto.
Qed.





Lemma cons_each_hd_tolist A
      (lh: list A) lt l
  : app_each_rel (tolist_each lh) lt l <->
    cons_each_rel lh lt l
.
Proof.
  unfold tolist_each.
  split.
  - intro APP.
    apply Forall3_nth'.
    hexploit Forall3_length; eauto.
    rewrite map_length. i. des.
    splits; ss.
    i.
    r in APP.
    rewrite Forall3_nth in APP.
    specialize (APP n).
    rewrite map_nth_error_rw in APP.
    rewrite NTH_A, NTH_B, NTH_C in APP.
    inv APP. ss.
  - intro CONS.
    apply Forall3_nth'.
    hexploit Forall3_length; eauto.
    rewrite map_length. i. des.
    splits; ss.
    i.
    r in CONS.
    rewrite Forall3_nth in CONS.
    specialize (CONS n).
    apply map_nth_error_iff in NTH_A. des. clarify.
    rewrite NTH_A, NTH_B, NTH_C in CONS.
    inv CONS. ss.
Qed.



Lemma Cons_each_tolist1 A
      (l: list A) s' s
  : Cons_each_rel l s' s <->
    sapp_each_rel (tolist_each l) s' s.
Proof.
  unfold tolist_each.
  split.
  - intro CONS.
    apply Forall3_nth'.
    splits.
    { rewrite map_length.
      apply Forall3_length in CONS. des; ss. }
    { rewrite map_length.
      apply Forall3_length in CONS. des; ss. }
    i.
    rewrite map_nth_error_iff in NTH_A. des. clarify. ss.
    eapply Forall3_nth1 in CONS; eauto. des. clarify.
  - intro SAPP.
    apply Forall3_nth'.
    splits.
    { apply Forall3_length in SAPP.
      rewrite map_length in SAPP. des; ss. }
    { apply Forall3_length in SAPP.
      rewrite map_length in SAPP. des; ss. }
    i.
    eapply Forall3_nth1 in SAPP; eauto.
    2: { eapply map_nth_error_iff. eauto. }
    des. ss. clarify.
Qed.

Lemma snoc_each_tolist2 A
      (l1 l: list (list A))
      (l2: list A)
  : snoc_each_rel l1 l2 l <->
    app_each_rel l1 (tolist_each l2) l.
Proof.
  unfold tolist_each.
  split.
  - intro SNOC.
    apply Forall3_nth'.
    splits.
    { rewrite map_length.
      apply Forall3_length in SNOC. des; ss. }
    { apply Forall3_length in SNOC. des; ss. }
    i.
    rewrite map_nth_error_iff in NTH_B. des. clarify.
    eapply Forall3_nth1 in SNOC; eauto. des. clarify.
  - intro APP.
    apply Forall3_nth'.
    splits.
    { apply Forall3_length in APP.
      rewrite map_length in APP. des; ss. }
    { apply Forall3_length in APP.
      rewrite map_length in APP. des; ss. }
    i.
    eapply Forall3_nth1 in APP; eauto.
    des.
    apply map_nth_error_iff in NTH2. des; ss.
    clarify.
Qed.

Lemma cons_each_to_nils A
      (l: list A) n
      (LEN_EQ: n = length l)
  : cons_each_rel l (repeat [] n) (tolist_each l).
Proof.
  unfold tolist_each.
  apply Forall3_nth'.
  rewrite repeat_length, map_length.
  splits; ss.
  i.
  apply repeat_spec_nth in NTH_B. subst.
  apply map_nth_error_iff in NTH_C. des; ss.
  clarify.
Qed.
