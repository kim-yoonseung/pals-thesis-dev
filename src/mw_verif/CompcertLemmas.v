From compcert Require Import Maps AST Values Memory Globalenvs Ctypes.
From compcert Require Coqlib Clight Clightdefs.

Require Import sflib.
Require Import Axioms StdlibExt IntegersExt.

Require Import Arith ZArith Bool.
Require Import String List Lia.


(* TODO: move to stdlib *)

Lemma list_repeat_eq A
      n (a: A)
  : Coqlib.list_repeat n a = repeat a n.
Proof.
  induction n; ss. congruence.
Qed.

Lemma imap_app A B
      (f: nat -> A -> B)
      n1 l1 l2
  : imap f n1 (l1 ++ l2) =
    imap f n1 l1 ++ imap f (n1 + length l1) l2.
Proof.
  depgen n1.
  induction l1 as [| h1 t1 IH]; i; ss.
  { rewrite plus_0_r. ss. }
  rewrite IH.
  rewrite <- plus_n_Sm. ss.
Qed.

Lemma iForall_app A
      (P: nat -> A -> Prop)
      n1 n2 l1 l2
      (IFA1: iForall P n1 l1)
      (IFA2: iForall P n2 l2)
      (N2_EQ: n2 = n1 + length l1)
  : iForall P n1 (l1 ++ l2).
Proof.
  subst n2.
  depgen n1.
  induction l1 as [| h1 t1 IH]; i; ss.
  { rewrite plus_0_r in IFA2. ss. }
  inv IFA1.
  hexploit IH; eauto.
  { rewrite <- plus_n_Sm in IFA2. ss. }
  i. econs; eauto.
Qed.

Lemma iForall_app_inv A
      (P: nat -> A -> Prop)
      n1 l1 l2
      (IFA: iForall P n1 (l1 ++ l2))
  : <<IFA1: iForall P n1 l1>> /\
    <<IFA2: iForall P (length l1 + n1) l2>>.
Proof.
  depgen n1.
  induction l1 as [| h1 t1]; i; ss.
  { splits; eauto. econs. }
  inv IFA.
  hexploit IHt1; eauto. i. des.
  splits.
  - econs; eauto.
  - rewrite <- plus_n_Sm in IFA2. ss.
Qed.


Lemma firstn_snoc_nth A
      (l: list A) (a d: A) n
      (LEN: (n < length l)%nat)
      (NTH: nth n l d = a)
  : firstn (S n) l = snoc (firstn n l) a.
Proof.
  unfold snoc.
  depgen n.
  induction l as [| h t IH]; i; ss.
  { inv NTH. nia. }
  destruct n as [| n']; ss.
  { inv NTH. ss. }

  hexploit IH; eauto.
  { nia. }
  intro EXP_IH. rewrite EXP_IH. ss.
Qed.





Lemma firstn_app_exact A
      (l1 l2: list A) n
      (LEN: length l1 = n)
  : firstn n (l1 ++ l2) = l1.
Proof.
  subst.
  rewrite firstn_app.
  rewrite firstn_all.
  rewrite Nat.sub_diag. ss.
  autorewrite with list. ss.
Qed.

Lemma skipn_app_exact A
      (l1 l2: list A) n
      (LEN: length l1 = n)
  : skipn n (l1 ++ l2) = l2.
Proof.
  subst.
  rewrite skipn_app.
  rewrite skipn_all.
  rewrite Nat.sub_diag. ss.
Qed.

(* general lemmas end *)

Lemma pos_of_succ_nat_eq n
  : Z.pos (Pos.of_succ_nat n) = (Z.of_nat (S n))%Z.
Proof. s. reflexivity. Qed.




(** * Integers  *)

Local Open Scope Z.


(** ** byte <-> int *)

Lemma ubyte_in_uint_range
  : forall z, 0 <= Byte.unsigned z <= Int.max_unsigned.
Proof.
  split.
  { apply Byte.unsigned_range_2. }
  etransitivity.
  { apply Byte.unsigned_range_2. }
  ss.
Qed.

Lemma Zrange_des
      z1 z2 z
      (RANGE_Z: (z1 <= z < z2)%Z)
  : (z2 <= z1 \/ z = z1 \/ (z1 + 1 <= z < z2))%Z.
Proof. nia. Qed.

Lemma sign_ext_byte_range z
      (RANGE_Z: IntRange.sintz8 z)
  :  Int.sign_ext 8 (Int.repr z) = Int.repr z.
Proof.
  assert (R: (-128 <= z < 128)%Z).
  { rr in RANGE_Z.
    unfold Byte.min_signed, Byte.max_signed in *. ss.
    nia. }

  repeat
    (apply Zrange_des in R;
     destruct R as [?|[?|R]]; [by ss| by subst; ss|ss]).
  nia.
Qed.

Lemma sign_ext_byte_range_u z
      (RANGE_Z: IntRange.sintz8 z)
  : Int.sign_ext 8 (Int.repr (Byte.unsigned (Byte.repr z))) =
    Int.repr z.
Proof.
  assert (R: (-128 <= z < 128)%Z).
  { rr in RANGE_Z.
    unfold Byte.min_signed, Byte.max_signed in *. ss.
    nia. }

  repeat
    (apply Zrange_des in R;
     destruct R as [?|[?|R]]; [by ss| by subst; ss|ss]).
  nia.
Qed.


Lemma rev_if_be_single a
  : rev_if_be [a] = [a].
Proof. ss. Qed.

Lemma simpl_init_byte bs i
  : inj_bytes (encode_int 1
      (Byte.unsigned (nth i bs Byte.zero))) =
    [Byte (nth i bs Byte.zero)].
Proof.
  unfold encode_int. ss.
  unfold rev_if_be. desf. ss.
  rewrite Byte.repr_unsigned. ss.
Qed.

Lemma decode_val_signed_byte
      (b: byte)
  : decode_val Mint8signed [Byte b] =
    Vint (Int.repr (Byte.signed b)).
Proof.
  unfold decode_val. ss.
  f_equal.
  unfold decode_int.
  rewrite rev_if_be_single. ss.
  rewrite Z.add_0_r.
  replace b with (Byte.repr (Byte.signed b)) at 1.
  2: { apply Byte.repr_signed. }
  rewrite sign_ext_byte_range_u; ss.
  r. apply Byte.signed_range.
Qed.

Lemma decode_byte_one_inv
      z b
      (RANGE_Z: (Int.min_signed <= z <= Int.max_signed)%Z)
      (DECODE_ONE: Vint (Int.repr z) =
                   decode_val Mint8signed [Byte b])
  : b = Byte.repr z.
Proof.
  unfold decode_val in *. ss.
  unfold decode_int in *.
  rewrite rev_if_be_single in *. ss.
  rewrite Z.add_0_r in *.

  rewrite <- (Byte.repr_signed b) in *.
  rewrite sign_ext_byte_range_u in *.
  2: { apply Byte.signed_range. }

  assert (EQ: Int.repr z = Int.repr (Byte.signed b)).
  { congruence. }
  clear - RANGE_Z EQ.

  assert(SINT_RANGE: IntRange.sintz (Byte.signed b)).
  { pose proof (Byte.signed_range b) as RANGE.
    split.
    - transitivity Byte.min_signed.
      { apply Z.lt_le_incl. ss. }
      apply RANGE.
    - transitivity Byte.max_signed.
      { apply RANGE. }
      { apply Z.lt_le_incl. ss. }
  }

  apply f_equal with (f:= Int.signed) in EQ.
  rewrite Int.signed_repr in *.
  2: { split; apply RANGE_Z. }

  rewrite Int.signed_repr in * by ss.
  apply f_equal with (f:= Byte.repr) in EQ.
  rewrite Byte.repr_signed in EQ.
  rewrite Byte.repr_signed. ss.
Qed.


Lemma decode_byte b
  : decode_int [b] = Byte.unsigned b.
Proof.
  unfold decode_int.
  replace (rev_if_be [b]) with [b] by ss.
  simpl. nia.
Qed.

Lemma int_and_byte_repr z
      (RANGE_Z: (Byte.min_signed <= z <=
                 Byte.max_signed)%Z)
  : Byte.repr (Int.unsigned (Int.repr z)) =
    Byte.repr z.
Proof.
  rewrite Int.unsigned_repr_eq.
  apply Byte.eqm_samerepr. r.
  eapply Zbits.eqmod_divides with (n:= Int.modulus).
  2: { solve_divide. }
  apply Zbits.eqmod_sym.
  apply Zbits.eqmod_mod. ss.
Qed.


(** ** others *)

Lemma Int64_mone_max_unsigned
  : Int64.mone = Int64.repr Int64.max_unsigned.
Proof.
  eapply Int64.eqm_samerepr.
  unfold Int64.max_unsigned.
  rr. exists (-1)%Z. ss.
Qed.


Lemma Nat2Z_inj_eqb (n1 n2: nat)
  : (Z.of_nat n1 =? Z.of_nat n2)%Z =
    (n1 =? n2)%nat.
Proof.
  destruct (Nat.eqb_spec n1 n2).
  { subst. rewrite Z.eqb_refl. ss. }
  destruct (Z.eqb_spec (Z.of_nat n1)
                       (Z.of_nat n2)); ss.
  hexploit inj_neq; eauto. ss.
Qed.

Lemma Nat2Z_inj_ltb
      (n m: nat)
  : (n <? m)%nat = (Z.of_nat n <? Z.of_nat m)%Z.
Proof.
  destruct (Z.ltb_spec (Z.of_nat n) (Z.of_nat m)) as [LT|GE];
    destruct (Nat.ltb_spec n m); ss; nia.
Qed.


(** ** Int_repr lemmas *)

Section OP_REPR_LEMMAS.
  Variable z1 z2: Z.
  Section UINT.
    Hypothesis RANGE1: IntRange.uintz z1.
    Hypothesis RANGE2: IntRange.uintz z2.

    Lemma Int_add_repr
      : Int.add (Int.repr z1) (Int.repr z2) =
        Int.repr (z1 + z2).
    Proof.
      unfold Int.add.
      do 2 (rewrite Int.unsigned_repr; ss).
    Qed.

    Lemma Int_sub_repr
      : Int.sub (Int.repr z1) (Int.repr z2) =
        Int.repr (z1 - z2).
    Proof.
      unfold Int.sub.
      do 2 (rewrite Int.unsigned_repr; ss).
    Qed.

    Lemma Int_mul_repr
      : Int.mul (Int.repr z1) (Int.repr z2) =
        Int.repr (z1 * z2).
    Proof.
      unfold Int.mul.
      do 2 (rewrite Int.unsigned_repr; ss).
    Qed.
  End UINT.

  Section UINT64.
    Hypothesis RANGE1: IntRange.uintz64 z1.
    Hypothesis RANGE2: IntRange.uintz64 z2.

    Lemma Int64_add_repr
      : Int64.add (Int64.repr z1) (Int64.repr z2)
        = Int64.repr (z1 + z2).
    Proof.
      unfold Int64.add.
      do 2 (rewrite Int64.unsigned_repr; ss).
    Qed.

    Lemma Int64_sub_repr
      : Int64.sub (Int64.repr z1) (Int64.repr z2)
        = Int64.repr (z1 - z2).
    Proof.
      unfold Int64.sub.
      do 2 (rewrite Int64.unsigned_repr; ss).
    Qed.

    Lemma Int64_mul_repr
      : Int64.mul (Int64.repr z1) (Int64.repr z2) =
        Int64.repr (z1 * z2).
    Proof.
      unfold Int64.mul.
      do 2 (rewrite Int64.unsigned_repr; ss).
    Qed.
  End UINT64.

  Section PTROFS.
    Hypothesis RANGE_Z1: (0 <= z1 <= Ptrofs.max_unsigned)%Z.
    Hypothesis RANGE_Z2: (0 <= z2 <= Ptrofs.max_unsigned)%Z.

    Lemma Ptrofs_add_repr
      : Ptrofs.add (Ptrofs.repr z1) (Ptrofs.repr z2) =
        Ptrofs.repr (z1 + z2).
    Proof.
      unfold Ptrofs.add.
      do 2 (rewrite Ptrofs.unsigned_repr; ss).
    Qed.

    Lemma Ptrofs_sub_repr
      : Ptrofs.sub (Ptrofs.repr z1) (Ptrofs.repr z2) =
        Ptrofs.repr (z1 - z2).
    Proof.
      unfold Ptrofs.sub.
      do 2 (rewrite Ptrofs.unsigned_repr; ss).
    Qed.

    Lemma Ptrofs_mul_repr
      : Ptrofs.mul (Ptrofs.repr z1) (Ptrofs.repr z2) =
        Ptrofs.repr (z1 * z2).
    Proof.
      unfold Ptrofs.mul.
      do 2 (rewrite Ptrofs.unsigned_repr; ss).
    Qed.
  End PTROFS.
End OP_REPR_LEMMAS.


Lemma Int_lt_repr z1 z2
      (RANGE1: IntRange.sintz z1)
      (RANGE2: IntRange.sintz z2)
  : Int.lt (Int.repr z1) (Int.repr z2) =
    (z1 <? z2)%Z.
Proof.
  unfold Int.lt.
  do 2 rewrite Int.signed_repr by ss.
  destruct (Z.ltb_spec z1 z2);
    destruct (Coqlib.zlt z1 z2); ss.
  nia.
Qed.

Lemma Int_eq_repr z1 z2
      (RANGE1: IntRange.uintz z1)
      (RANGE2: IntRange.uintz z2)
  : Int.eq (Int.repr z1) (Int.repr z2) =
    (z1 =? z2)%Z.
Proof.
  unfold Int.eq.
  do 2 rewrite Int.unsigned_repr by ss.
  unfold Coqlib.zeq.
  symmetry.
  desf.
  - apply Z.eqb_refl.
  - apply Z.eqb_neq. ss.
Qed.

Lemma Int64_eq_repr z1 z2
      (RANGE1: IntRange.uintz64 z1)
      (RANGE2: IntRange.uintz64 z2)
  : Int64.eq (Int64.repr z1) (Int64.repr z2) =
    (z1 =? z2)%Z.
Proof.
  unfold Int64.eq.
  do 2 rewrite Int64.unsigned_repr by ss.
  unfold Coqlib.zeq.
  symmetry.
  desf.
  - apply Z.eqb_refl.
  - apply Z.eqb_neq. ss.
Qed.

Lemma Int64_ltu_repr
      z1 z2
      (RANGE1: IntRange.uintz64 z1)
      (RANGE2: IntRange.uintz64 z2)
  : Int64.ltu (Int64.repr z1) (Int64.repr z2) =
    (z1 <? z2)%Z.
Proof.
  unfold Int64.ltu.
  rewrite Int64.unsigned_repr by range_stac.
  rewrite Int64.unsigned_repr by range_stac.
  ss.
  destruct (Coqlib.zlt z1 z2);
    destruct (Z.ltb_spec z1 z2); ss; nia.
Qed.

Lemma Int64_modu_repr
      z1 z2
      (RANGE1: IntRange.uintz64 z1)
      (RANGE2: IntRange.uintz64 z2)
  : Int64.modu (Int64.repr z1) (Int64.repr z2) =
    Int64.repr (z1 mod z2).
Proof.
  unfold Int64.modu.
  rewrite Int64.unsigned_repr by range_stac.
  rewrite Int64.unsigned_repr by range_stac.
  ss.
Qed.


Lemma Int_add_repr_signed
      z1 z2
      (RANGE1: IntRange.sintz z1)
      (RANGE2: IntRange.sintz z2)
  : Int.add (Int.repr z1) (Int.repr z2) =
    Int.repr (z1 + z2).
Proof.
  rewrite Int.add_signed.
  do 2 rewrite Int.signed_repr by ss. ss.
Qed.


Lemma Int_eq_repr_signed z1 z2
      (RANGE1: IntRange.sintz z1)
      (RANGE2: IntRange.sintz z2)
  : Int.eq (Int.repr z1) (Int.repr z2) =
    (z1 =? z2)%Z.
Proof.
  rewrite Int.signed_eq.
  do 2 rewrite Int.signed_repr by ss.
  destruct (Coqlib.zeq z1 z2).
  - destruct (Z.eqb_spec z1 z2); ss.
  - destruct (Z.eqb_spec z1 z2); ss.
Qed.

Lemma Int_repr_eq_inv
      z1 z2
      (RANGE1: IntRange.sintz z1)
      (RANGE2: IntRange.sintz z2)
      (REPR_EQ: Int.repr z1 = Int.repr z2)
  : z1 = z2.
Proof.
  rewrite <- (Int.signed_repr z1) by assumption.
  rewrite <- (Int.signed_repr z2) by assumption.
  rewrite REPR_EQ. ss.
Qed.



Ltac repr_tac0 :=
  unfold Ptrofs.of_ints, IntNat.of_nat, IntNat.of_nat64;
  match goal with
  | |- context[Int.signed (Int.repr ?n)] =>
    rewrite Int.signed_repr
  | |- context[Int.unsigned (Int.repr ?n)] =>
    rewrite Int.unsigned_repr
  | |- context[Ptrofs.unsigned (Ptrofs.repr ?n)] =>
    rewrite Ptrofs.unsigned_repr

  | |- context[Int.add (Int.repr ?z1) (Int.repr ?z2)] =>
    rewrite (Int_add_repr z1 z2)
  | |- context[Int.sub (Int.repr ?z1) (Int.repr ?z2)] =>
    rewrite (Int_sub_repr z1 z2)
  | |- context[Int.mul (Int.repr ?z1) (Int.repr ?z2)] =>
    rewrite (Int_mul_repr z1 z2)
  | |- context[Int.lt (Int.repr ?z1) (Int.repr ?z2)] =>
    rewrite (Int_lt_repr z1 z2)

  | |- context[Int64.eq (Int64.repr ?z1) (Int64.repr ?z2)] =>
    rewrite (Int64_eq_repr z1 z2)
  | |- context[Int.eq (Int.repr ?z1) (Int.repr ?z2)] =>
    rewrite (Int_eq_repr z1 z2)

  | |- context[Int64.add (Int64.repr ?z1) (Int64.repr ?z2)] =>
    rewrite (Int64_add_repr z1 z2)
  | |- context[Int64.sub (Int64.repr ?z1) (Int64.repr ?z2)] =>
    rewrite (Int64_sub_repr z1 z2)
  | |- context[Int64.mul (Int64.repr ?z1) (Int64.repr ?z2)] =>
    rewrite (Int64_mul_repr z1 z2)

  | |- context[Ptrofs.mul (Ptrofs.repr ?z1) (Ptrofs.repr ?z2)] =>
    rewrite (Ptrofs_mul_repr z1 z2)
  | |- context[Ptrofs.add (Ptrofs.repr ?z1) (Ptrofs.repr ?z2)] =>
    rewrite (Ptrofs_add_repr z1 z2)
  end.

Ltac repr_tac1 := repr_tac0; [| by range_stac..].
Ltac repr_tac := repeat repr_tac1.


Lemma signed_byte_int_unsigned_repr_eq e
  : Byte.repr e = Byte.repr (Int.unsigned (Int.repr e)).
Proof.
  apply Byte.eqm_samerepr.

  cut (Int.eqm e (Int.unsigned (Int.repr e))).
  { clear.
    generalize (Int.unsigned (Int.repr e)).
    unfold Int.eqm, Byte.eqm.
    intros z INT.
    eapply Zbits.eqmod_divides; eauto.

    unfold Byte.modulus, Int.modulus.
    r. unfold Int.wordsize, Byte.wordsize.
    unfold Wordsize_32.wordsize, Wordsize_8.wordsize.
    exists (two_power_nat 24).
    do 3 rewrite two_power_nat_equiv.
    rewrite <- Z.pow_add_r by nia.
    f_equal.
  }

  apply Int.eqm_unsigned_repr.
Qed.


(** * INIT_DATA *)

(* Arguments Z.of_nat: simpl never. *)
Local Opaque Z.of_nat Z.to_nat Zlength.

Lemma init_data_list_size_app
      i1 i2
  : init_data_list_size (i1 ++ i2) =
    init_data_list_size i1 + init_data_list_size i2.
Proof.
  induction i1 as [| h t IH]; ss.
  rewrite IH. nia.
Qed.

Lemma init_data_list_size_concat
      inits sz
      (EACH_SIZE_EQ: forall x (IN: In x inits),
          init_data_list_size x = sz)
  : init_data_list_size (concat inits) =
    (Zlength inits) * sz.
Proof.
  induction inits as [| h t IH]; ss.
  rewrite init_data_list_size_app.
  rewrite IH by eauto.
  do 2 rewrite Zlength_correct. ss.
  rewrite EACH_SIZE_EQ; eauto. nia.
Qed.

Arguments Z.add : simpl nomatch.

Lemma load_store_init_data_app F V
      (ge: Genv.t F V)
      m b ofs il1 il2
      (INIT_DATA: Genv.load_store_init_data
                    ge m b ofs (il1 ++ il2))
  : Genv.load_store_init_data
      ge m b ofs il1 /\
    Genv.load_store_init_data
      ge m b (ofs + init_data_list_size il1) il2.
Proof.
  depgen ofs.
  induction il1 as [| h1 t1 IH]; i; ss.
  { rewrite Z.add_0_r. ss. }

  destruct h1; des;
    (hexploit IH; eauto; i; des;
     splits; eauto;
     rewrite Z.add_assoc; ss).
Qed.


(** * Memory *)

(* Import Clight. *)

(** ** Memory range preds *)

Definition mem_range (b: block) (lo hi: Z)
  : block -> Z -> Prop :=
  fun b' ofs' => b' = b /\ (lo <= ofs' < hi)%Z.

Definition mem_unchanged_except
           (P: block -> Z -> Prop) (m m': mem): Prop :=
  Mem.unchanged_on (fun b ofs => ~ P b ofs) m m'.

Definition mem_changed_block (b_ch: block) (m m': mem): Prop :=
  Mem.unchanged_on (fun b _ => b <> b_ch) m m'.

Definition mem_changed_gvar_id
           {F V} (ge: Genv.t F V)
           (* (ge: genv) *)
           (gid: ident)
           (m m': mem): Prop :=
  forall b_ch
    (FSYMB: Genv.find_symbol ge gid = Some b_ch),
    Mem.unchanged_on (fun b _ => b <> b_ch) m m'.

(** ** Lemmas *)

Lemma Mem_loadbytes_split'
      m' b ofs n1 n2 bytes
      (LOADBYTES: Mem.loadbytes m' b ofs (n1 + n2) = Some bytes)
      (NNEG1: n1 >= 0)
      (NNEG2: n2 >= 0)
  : Mem.loadbytes m' b ofs n1 = Some (firstn (Z.to_nat n1) bytes) /\
    Mem.loadbytes m' b (ofs + n1) n2 = Some (skipn (Z.to_nat n1) bytes).
Proof.
  hexploit Mem.loadbytes_split; eauto.
  intros (bs1 & bs2 & LBS1 & LBS2 & BS_EQ).
  hexploit Mem.loadbytes_length; try eapply LBS1.
  intros LEN1.
  hexploit Mem.loadbytes_length; try eapply LBS2.
  intros LEN2.
  subst.
  replace (Z.to_nat n1) with (length bs1 + 0)%nat by nia.
  rewrite firstn_app_2. ss.
  split.
  { autorewrite with list. ss. }
  rewrite skipn_app.
  rewrite plus_0_r.
  rewrite skipn_all. ss.
  rewrite Nat.sub_diag. ss.
Qed.

Lemma Mem_loadbytes_sublist
      m b ofs n bs
      n1 n2
      (LBS: Mem.loadbytes m b ofs n = Some bs)
      (NNEG1: 0 <= n1)
      (NNEG2: 0 <= n2)
      (IN_RANGE: n1 + n2 <= n)
  : Mem.loadbytes m b (ofs + n1) n2 =
    Some (firstn (Z.to_nat n2) (skipn (Z.to_nat n1) bs)).
Proof.
  assert (BS_DIV: bs = firstn (Z.to_nat n1) bs ++
                              skipn (Z.to_nat n1) bs).
  { rewrite firstn_skipn. ss. }

  replace n with (n1 + (n - n1)) in LBS by nia.
  hexploit Mem.loadbytes_split; eauto.
  { nia. }
  { nia. }
  intros (bs1 & bs2 & LB1 & LB2 & BS_EQ).
  subst bs.

  hexploit Mem.loadbytes_length; try apply LBS. intro LEN_TOT.
  hexploit Mem.loadbytes_length; try apply LB1. intro LEN1.
  hexploit Mem.loadbytes_length; try apply LB2. intro LEN2.
  apply app_eqlen_inv in BS_DIV.
  2: { rewrite firstn_length_le.
       2: { rewrite LEN_TOT. nia. }
       ss. }
  rewrite skipn_app_exact by ss.

  replace (n - n1) with (n2 + (n - n1 - n2)) in LB2 by nia.
  hexploit Mem.loadbytes_split.
  { apply LB2. }
  { nia. }
  { nia. }
  intros (bytes_x & bytes3 & LBS_X & LBS3 & BS3_EQ).
  subst bs2.
  rewrite firstn_app_exact.
  2: { apply Mem.loadbytes_length in LBS_X. ss. }
  ss.
Qed.

Lemma loadbytes_nth_error
      n b_n z
      m b ofs len bs
      (LBS: Mem.loadbytes m b ofs len = Some (inj_bytes bs))
      (NTH: nth_error bs n = Some b_n)
      (Z_EQ: z = Z.of_nat n)
  : Mem.loadbytes m b (ofs + z) 1 = Some [Byte b_n].
Proof.

  assert (n < length bs)%nat.
  { apply nth_error_Some.
    congruence. }

  assert (Z.of_nat (length bs) = len).
  { apply Mem.loadbytes_length in LBS.
    unfold inj_bytes in LBS.
    rewrite map_length in LBS.
    rewrite LBS. nia. }


  eapply Mem_loadbytes_sublist
    with (n1:= z) (n2:=1) in LBS; try nia.
  rewrite LBS.
  eapply nth_error_split in NTH. des. subst.
  rewrite Nat2Z.id.
  unfold inj_bytes. rewrite map_app.
  rewrite skipn_app_exact.
  2: { apply map_length. }
  ss.
Qed.


Lemma Mem_range_perm_storebytes_1
      m m' b lo hi k p
      b_st ofs_st bs
      (UNCH: Mem.storebytes m b_st ofs_st bs = Some m')
      (RANGE_PERM: Mem.range_perm m b lo hi k p)
  : Mem.range_perm m' b lo hi k p.
Proof.
  ii. eapply Mem.perm_storebytes_1; eauto.
Qed.


Lemma Mem_range_perm_unchanged_on
      m m'
      b lo hi k p
      (UNCH: Mem.unchanged_on (mem_range b lo hi) m m')
      (RANGE_PERM: Mem.range_perm m b lo hi k p)
  : Mem.range_perm m' b lo hi k p.
Proof.
  ii. eapply Mem.perm_unchanged_on; eauto.
  rr. split; auto.
Qed.



Lemma storebytes_unchanged_on'
      m b ofs vs m'
      (SBS: Mem.storebytes m b ofs vs = Some m')
  : mem_unchanged_except
      (mem_range b ofs (ofs + Zlength vs)) m m'.
Proof.
  rewrite Zlength_correct.
  eapply Mem.storebytes_unchanged_on; eauto.
  unfold mem_range. eauto.
Qed.


Lemma store_unchanged_on'
      ch m b ofs v m'
      (STORE: Mem.store ch m b ofs v = Some m')
  : mem_unchanged_except
      (mem_range b ofs (ofs + size_chunk ch)) m m'.
Proof.
  eapply Mem.store_unchanged_on; eauto.
  unfold mem_range. eauto.
Qed.



(** * Other Lemmas *)

Section CLIGHT_LEMMAS.
  Import Clight.
  Import Clightdefs.

  Definition blocks_of (ge: genv) (ids: list ident)
             (b: block) (_: Z): Prop :=
    exists id, In id ids /\
          Genv.find_symbol ge id = Some b.

  Lemma blocks_of_ge_incl ge
        ids1 ids2 b ofs1 ofs2
        (INCL: List.incl ids1 ids2)
        (BLOCKS_OF: blocks_of ge ids1 b ofs1)
    : blocks_of ge ids2 b ofs2.
  Proof.
    unfold blocks_of in *.
    des. esplits; eauto.
  Qed.

  Lemma genv_symb_range2
        (ge: genv)
        id b m
        (FSYMB: Genv.find_symbol ge id = Some b)
        (MEM_NEXTBLOCK: (Genv.genv_next ge <=
                         Mem.nextblock m)%positive)
    : Mem.valid_block m b.
  Proof.
    eapply Genv.genv_symb_range in FSYMB.
    r. unfold Coqlib.Plt in *. nia.
  Qed.

  Lemma call_cont_is_call_cont k
        (CALL_CONT: is_call_cont k)
    : call_cont k = k.
  Proof.
    rr in CALL_CONT.
    destruct k; ss.
  Qed.

  Lemma bool_val_of_bool b m
    : Cop.bool_val (Val.of_bool b) tint m =
      Some b.
  Proof. destruct b; ss. Qed.

  Lemma global_addresses_distinct'
        (ge: genv) id b id_c
        (NOT_CONST_ID: id_c <> id)
        (GENV: Genv.find_symbol ge id = Some b)
    : Genv.find_symbol ge id_c <> Some b.
  Proof.
    ii. hexploit Genv.global_addresses_distinct; eauto.
  Qed.

End CLIGHT_LEMMAS.
