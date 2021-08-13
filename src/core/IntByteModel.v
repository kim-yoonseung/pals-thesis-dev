From compcert Require Import AST Memdata Values.
Require Import sflib Axioms IntegersExt StdlibExt.

Require Import List Basics ZArith Lia.
Import ListNotations.

Module Type IntByteModelSig.

  Parameter to_bytes: int -> list byte.
  Parameter of_bytes: list byte -> (* option *) int.

  Parameter to_bytes64: int64 -> list byte.
  Parameter of_bytes64: list byte -> (* option *) int64.

  Axiom to_bytes_length: forall i, length (to_bytes i) = 4.
  Axiom to_bytes_inv: forall i, of_bytes (to_bytes i) = (* Some *) i.
  Axiom of_bytes_inv: forall bs,
      length bs = 4 -> to_bytes (of_bytes bs) = bs.
  (* exists i, of_bytes bs = Some i /\ to_bytes i = bs. *)

  Axiom to_bytes_length64: forall i, length (to_bytes64 i) = 8.
  Axiom to_bytes_inv64: forall i, of_bytes64 (to_bytes64 i) = (* Some *) i.
  Axiom of_bytes_inv64: forall bs,
      length bs = 8 -> to_bytes64 (of_bytes64 bs) = bs.
  (* length bs = 8 -> exists i, of_bytes64 bs = Some i /\ to_bytes64 i = bs. *)

End IntByteModelSig.


(* Lemma lt_le_mone (a b: Z) *)
(*   : (a < b)%Z <-> (a <= b - 1)%Z. *)
(* Proof. nia. Qed. *)

Module IntByte <: IntByteModelSig.
  Definition to_bytes (i: int): list byte :=
    encode_int 4 (Int.unsigned i).

  (* Definition of_bytes (bl: list byte): int? := *)
  (*   if (Nat.eqb (length bl) 4)%nat then *)
  (*     Some (Int.repr (decode_int bl)) *)
  (*   else None. *)

  Definition of_bytes (bl: list byte): int :=
    Int.repr (decode_int bl).

  Definition to_bytes64 (i: int64): list byte :=
    encode_int 8 (Int64.unsigned i).

  Definition of_bytes64 (bl: list byte): int64 :=
    Int64.repr (decode_int bl).

  Lemma to_bytes_length: forall i, length (to_bytes i) = 4.
  Proof.
    i. unfold to_bytes.
    apply encode_int_length.
  Qed.

  Lemma to_bytes_inv: forall i, of_bytes (to_bytes i) = (* Some *) i.
  Proof.
    i. unfold of_bytes, to_bytes.
    rewrite decode_encode_int. ss.
    rewrite Zmod_small.
    - rewrite Int.repr_unsigned. ss.
    - apply Int.unsigned_range.
  Qed.

(*   Lemma encode_decode_int *)

(* decode_encode_int *)
(*      : forall (n : nat) (x : Z), decode_int (encode_int n x) = (x mod two_p (Z.of_nat n * 8))%Z *)

  Lemma int_of_bytes_inv bs l
        (LEN: length bs = l)
    : bytes_of_int l (int_of_bytes bs) = bs.
  Proof.
    depgen l.
    induction bs as [| h t IH]; i; ss.
    { subst. ss. }
    destruct l as [| l']; ss.

    hexploit (IH l').
    { inv LEN. ss. }

    clear IH. intros IH.
    f_equal.
    - match goal with
      | |- ?a = _ =>
        rewrite <- Byte.repr_unsigned with (i:=a)
      end.
      rewrite <- Byte.repr_unsigned with (i:=h) at 2.
      rewrite Byte.unsigned_repr_eq. f_equal.
      rewrite <- Zplus_mod_idemp_r.
      rewrite Z_mod_mult.
      rewrite Z.add_0_r.
      rewrite Zmod_small; ss.
      hexploit (Byte.unsigned_range_2 h).
      i. unfold Byte.max_unsigned in *.
      nia.
    - replace ((Byte.unsigned h + int_of_bytes t * 256) / 256)%Z
        with (int_of_bytes t).
      2: {
        rewrite Z_div_plus by ss.
        rewrite Z.div_small; ss.
        hexploit (Byte.unsigned_range_2 h). i.
        unfold Byte.max_unsigned in *.
        ss. nia.
      }
      ss.
  Qed.

  Lemma encode_decode bs l
        (LEN: length bs = l)
    : encode_int l (decode_int bs) = bs.
  Proof.
    unfold decode_int, encode_int.
    rewrite int_of_bytes_inv.
    - apply rev_if_be_involutive.
    - rewrite rev_if_be_length. ss.
  Qed.

  Lemma of_bytes_inv bs
        (LEN: length bs = 4)
    : to_bytes (of_bytes bs) = bs.
  Proof.
    i. unfold to_bytes, of_bytes.
    rewrite Int.unsigned_repr.
    2: {
      unfold decode_int.
      hexploit (int_of_bytes_range (rev_if_be bs)).
      intros [RANGE1 RANGE2].
      split; ss.
      rewrite rev_if_be_length in RANGE2.
      rewrite LEN in RANGE2. ss.
      assert (UNS_EQ: (Int.max_unsigned =
                       two_power_pos 32 - 1)%Z) by ss.
      nia.
    }
    apply encode_decode. ss.
  Qed.


  Lemma to_bytes_length64: forall i, length (to_bytes64 i) = 8.
  Proof.
    i. unfold to_bytes64.
    apply encode_int_length.
  Qed.

  Lemma to_bytes_inv64: forall i, of_bytes64 (to_bytes64 i) = (* Some *) i.
  Proof.
    i. unfold of_bytes64, to_bytes64.
    rewrite decode_encode_int. ss.
    rewrite Zmod_small.
    - rewrite Int64.repr_unsigned. ss.
    - apply Int64.unsigned_range.
  Qed.

  Lemma of_bytes_inv64 bs
        (LEN: length bs = 8)
    : to_bytes64 (of_bytes64 bs) = bs.
  Proof.
    i. unfold to_bytes64, of_bytes64.
    rewrite Int64.unsigned_repr.
    2: {
      unfold decode_int.
      hexploit (int_of_bytes_range (rev_if_be bs)).
      intros [RANGE1 RANGE2].
      split; ss.
      rewrite rev_if_be_length in RANGE2.
      rewrite LEN in RANGE2. ss.
      assert (UNS_EQ: (Int64.max_unsigned =
                       two_power_pos 64 - 1)%Z) by ss.
      rewrite UNS_EQ. nia.
    }
    apply encode_decode. ss.
  Qed.

End IntByte.
