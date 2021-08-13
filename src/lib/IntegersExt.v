From compcert Require Export Integers.
Require Import sflib.

Require Import Arith ZArith Lia.

Definition bytes : Set := list byte.
Definition Z_mone: Z := (-1)%Z.
Definition Z_mtwo: Z := (-2)%Z.
Definition Byte_two: byte := Byte.repr 2%Z.
Definition Byte_mtwo: byte := Byte.repr (-2)%Z.

(* To hide them from computations *)
Module IntRange.

  Section Z_RANGES.
    Variable z: Z.

    Definition uintz8: Prop := (0 <= z <= Byte.max_unsigned)%Z.
    Definition sintz8: Prop := (Byte.min_signed <= z <= Byte.max_signed)%Z.

    Definition uintz: Prop := (0 <= z <= Int.max_unsigned)%Z.
    Definition sintz: Prop := (Int.min_signed <= z <= Int.max_signed)%Z.

    Definition uintz64: Prop := (0 <= z <= Int64.max_unsigned)%Z.
    Definition sintz64: Prop := (Int64.min_signed <= z <= Int64.max_signed)%Z.
  End Z_RANGES.

  Section NAT_RANGES.
    Variable n: nat.
    (* Wrapped by contructors in order to avoid infinite simplification *)
    Let z: Z := Z.of_nat n.

    Definition uint8: Prop := uintz8 z.
    Definition sint8: Prop := sintz8 z.
    Definition uint: Prop := uintz z.
    Definition sint: Prop := sintz z.
    Definition uint64: Prop := uintz64 z.
    Definition sint64: Prop := sintz64 z.

    (* Inductive uint8: Prop := *)
    (*   UInt8 (RANGE: (Z.of_nat n <= Byte.max_unsigned)%Z). *)
    (* Inductive sint8: Prop := *)
    (*   SInt8 (RANGE: (Z.of_nat n <= Byte.max_signed)%Z). *)

    (* Inductive uint: Prop := *)
    (*   UInt (RANGE: (n <= Z.to_nat Int.max_unsigned)%nat). *)
    (* Inductive sint: Prop := *)
    (*   SInt (RANGE: (n <= Z.to_nat Int.max_signed)%nat). *)

    (* Inductive uint64: Prop := *)
    (*   UInt64 (RANGE: (n <= Z.to_nat Int64.max_unsigned)%nat). *)
    (* Inductive sint64: Prop := *)
    (*   SInt64 (RANGE: (n <= Z.to_nat Int64.max_signed)%nat). *)


    (* Definition uint8: Prop := (n <= Z.to_nat Byte.max_unsigned)%nat. *)
    (* Definition sint8: Prop := (n <= Z.to_nat Byte.max_signed)%nat. *)

    (* Definition uint: Prop := (n <= Z.to_nat Int.max_unsigned)%nat. *)
    (* Definition sint: Prop := (n <= Z.to_nat Int.max_signed)%nat. *)

    (* Definition uint64: Prop := (n <= Z.to_nat Int64.max_unsigned)%nat. *)
    (* Definition sint64: Prop := (n <= Z.to_nat Int64.max_signed)%nat. *)
  End NAT_RANGES.


  (* Lemma uint8_uintz8 n *)
  (*       (RANGE_NAT: uint8 n) *)
  (*   : uintz8 (Z.of_nat n). *)
  (* Proof. *)
  (*   ss. *)
  (*   r. inv RANGE_NAT. *)
  (*   split. *)
  (*   { apply Nat2Z.is_nonneg. } *)
  (*   apply Nat2Z.inj_le in RANGE. *)
  (*   rewrite Z2Nat.id in RANGE by ss. *)
  (*   ss. *)
  (* Qed. *)

  (* Lemma sint8_sintz8 n *)
  (*       (RANGE_NAT: sint8 n) *)
  (*   : sintz8 (Z.of_nat n). *)
  (* Proof. *)
  (*   r. inv RANGE_NAT. *)
  (*   split. *)
  (*   { etransitivity. *)
  (*     2: { apply Nat2Z.is_nonneg. } *)
  (*     ss. } *)
  (*   apply Nat2Z.inj_le in RANGE. *)
  (*   rewrite Z2Nat.id in RANGE by ss. *)
  (*   ss. *)
  (* Qed. *)

  (* Lemma uint_uintz n *)
  (*       (RANGE_NAT: uint n) *)
  (*   : uintz (Z.of_nat n). *)
  (* Proof. *)
  (*   r. inv RANGE_NAT. *)
  (*   split. *)
  (*   { apply Nat2Z.is_nonneg. } *)
  (*   apply Nat2Z.inj_le in RANGE. *)
  (*   rewrite Z2Nat.id in RANGE. *)
  (*   2: { clear. ss. } *)
  (*   ss. *)
  (* Qed. *)

  (* Lemma sint_sintz n *)
  (*       (RANGE_NAT: sint n) *)
  (*   : sintz (Z.of_nat n). *)
  (* Proof. *)
  (*   r. inv RANGE_NAT. *)
  (*   split. *)
  (*   { etransitivity. *)
  (*     2: {apply Nat2Z.is_nonneg. } *)
  (*     ss. } *)
  (*   apply Nat2Z.inj_le in RANGE. *)
  (*   rewrite Z2Nat.id in RANGE. *)
  (*   2: { clear. ss. } *)
  (*   ss. *)
  (* Qed. *)

  (* Lemma uint64_uintz64 n *)
  (*       (RANGE_NAT: uint64 n) *)
  (*   : uintz64 (Z.of_nat n). *)
  (* Proof. *)
  (*   r. inv RANGE_NAT. *)
  (*   split. *)
  (*   { apply Nat2Z.is_nonneg. } *)
  (*   apply Nat2Z.inj_le in RANGE. *)
  (*   rewrite Z2Nat.id in RANGE. *)
  (*   2: { clear. ss. } *)
  (*   ss. *)
  (* Qed. *)

  (* Lemma sint64_sintz64 n *)
  (*       (RANGE_NAT: sint64 n) *)
  (*   : sintz64 (Z.of_nat n). *)
  (* Proof. *)
  (*   r. inv RANGE_NAT. *)
  (*   split. *)
  (*   { etransitivity. *)
  (*     2: {apply Nat2Z.is_nonneg. } *)
  (*     ss. } *)
  (*   apply Nat2Z.inj_le in RANGE. *)
  (*   rewrite Z2Nat.id in RANGE. *)
  (*   2: { clear. ss. } *)
  (*   ss. *)
  (* Qed. *)

  (* Lemma uintz_uint z *)
  (*       (RANGE_Z: uintz z) *)
  (*   : uint (Z.to_nat z). *)
  (* Proof. *)
  (*   inv RANGE_Z. econs. nia. *)
  (* Qed. *)

  (* Lemma sintz_sint z *)
  (*       (RANGE_Z: sintz z) *)
  (*   : sint (Z.to_nat z). *)
  (* Proof. *)
  (*   inv RANGE_Z. econs. nia. *)
  (* Qed. *)

  (* Lemma uintz64_uint64 z *)
  (*       (RANGE_Z: uintz64 z) *)
  (*   : uint64 (Z.to_nat z). *)
  (* Proof. *)
  (*   inv RANGE_Z. econs. nia. *)
  (* Qed. *)

  (* Lemma sintz64_sint64 z *)
  (*       (RANGE_Z: sintz64 z) *)
  (*   : sint64 (Z.to_nat z). *)
  (* Proof. *)
  (*   inv RANGE_Z. econs. nia. *)
  (* Qed. *)

End IntRange.


Module IntNat.
  Definition of_nat (n: nat) : int := Int.repr (Z.of_nat n).
  Definition to_nat (i: int): nat := Z.to_nat (Int.unsigned i).

  Definition of_nat64 (n: nat) : int64 := Int64.repr (Z.of_nat n).
  Definition to_nat64 (i: int64): nat := Z.to_nat (Int64.unsigned i).

  Lemma int_nat_int (i: int)
    : of_nat (to_nat i) = i.
  Proof.
    unfold to_nat, of_nat.
    rewrite Z2Nat.id.
    2: { apply Int.unsigned_range. }
    rewrite Int.repr_unsigned. ss.
  Qed.

  Lemma nat_int_nat (n: nat)
        (RANGE_UINT: IntRange.uint n)
    : to_nat (of_nat n) = n.
  Proof.
    inv RANGE_UINT.
    unfold of_nat, to_nat.
    rewrite Int.unsigned_repr.
    2: {
      split.
      { nia. }
      { ss. }
      (* apply Nat2Z.inj_le in RANGE. *)
      (* rewrite Z2Nat.id in RANGE. *)
      (* 2: { clear. ss. } *)
      (* ss. *)
    }
    rewrite Nat2Z.id. ss.
  Qed.

  Lemma int_nat_int64 (i: int64)
    : of_nat64 (to_nat64 i) = i.
  Proof.
    unfold to_nat64, of_nat64.
    rewrite Z2Nat.id.
    2: { apply Int64.unsigned_range. }
    rewrite Int64.repr_unsigned. ss.
  Qed.

  Lemma nat_int_nat64 (n: nat)
        (RANGE_UINT: IntRange.uint64 n)
    : to_nat64 (of_nat64 n) = n.
  Proof.
    inv RANGE_UINT.
    unfold of_nat64, to_nat64.
    rewrite Int64.unsigned_repr.
    2: {
      split.
      { nia. }
      { ss. }
      (* apply Nat2Z.inj_le in RANGE. *)
      (* rewrite Z2Nat.id in RANGE. *)
      (* 2: { clear. ss. } *)
      (* ss. *)
    }
    rewrite Nat2Z.id. ss.
  Qed.

End IntNat.


(* Lemma IntRange_sint8_sint n *)
(*       (RANGE_SINT8: IntRange.sint8 n) *)
(*   : IntRange.sint n. *)
(* Proof. *)
(*   inv RANGE_SINT8. *)
(*   econs. *)
(*   etransitivity. *)
(*   { apply RANGE. } *)
(*   apply Nat.lt_le_incl. *)
(*   apply Z2Nat.inj_lt; ss. *)
(*   (* - apply Z.lt_le_incl. ss. *) *)
(*   (* - apply Z.lt_le_incl. ss. *) *)
(* Qed. *)

(* Lemma IntRange_sint_uint n *)
(*       (RANGE_SINT: IntRange.sint n) *)
(*   : IntRange.uint n. *)
(* Proof. *)
(*   inv RANGE_SINT. *)
(*   econs. *)
(*   etransitivity. *)
(*   { apply RANGE. } *)
(*   apply Nat.lt_le_incl. *)
(*   apply Z2Nat.inj_lt; ss. *)
(*   (* - apply Z.lt_le_incl. ss. *) *)
(*   (* - apply Z.lt_le_incl. ss. *) *)
(* Qed. *)

(* Lemma IntRange_sint8_uint8 n *)
(*       (RANGE_SINT8: IntRange.sint8 n) *)
(*   : IntRange.uint8 n. *)
(* Proof. *)
(*   inv RANGE_SINT8. *)
(*   econs. *)
(*   etransitivity. *)
(*   { apply RANGE. } *)
(*   apply Nat.lt_le_incl. *)
(*   apply Z2Nat.inj_lt; ss. *)
(*   (* - apply Z.lt_le_incl. ss. *) *)
(*   (* - apply Z.lt_le_incl. ss. *) *)
(* Qed. *)


Lemma int_consts_lts
  : (Ptrofs.min_signed = Int64.min_signed /\
     Int64.min_signed < Int.min_signed /\
     Int.min_signed < Byte.min_signed /\
     Byte.min_signed < 0 /\
     0 < Byte.max_signed < Byte.max_unsigned /\
     Byte.max_unsigned < Int.max_signed < Int.max_unsigned /\
     Int.max_unsigned < Int64.max_signed < Int64.max_unsigned /\
     Ptrofs.max_signed = Int64.max_signed /\
     Ptrofs.max_unsigned = Int64.max_unsigned)%Z.
Proof.
  splits; ss.
Qed.

Ltac unf_ranges :=
  unfold IntRange.sint8, IntRange.uint8,
  IntRange.sint, IntRange.uint,
  IntRange.sint64, IntRange.uint64 in *;
  unfold IntRange.sintz8, IntRange.uintz8,
  IntRange.sintz, IntRange.uintz,
  IntRange.sintz64, IntRange.uintz64 in *.

Ltac range_stac :=
  unf_ranges;
  let X := fresh in
  pose proof int_consts_lts as X; desH X; solve [nia|done].
