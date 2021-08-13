(* From compcert Require Import Integers. *)
Require Import sflib.
Require Import StdlibExt IntegersExt.

Require Import ZArith.
Require Coq.Strings.String.


(* ips in nat representation (default) *)
Notation ip_t := nat (only parsing).
(* ips in string representation (xxx.xxx.xxx.xxx) *)
Notation ip_brep := (list byte) (only parsing).

(* Section A. *)
(*   Import String. *)
(*   Compute (String.length ("ss"))%string. *)
(* End A. *)

Module Type IPModelSig.
  Definition default_ip: ip_t := O. (* considered as invalid *)
  Definition max_byte_length: nat := 16.

  (* Conversion of IP representation (string -> option nat). *)
  Parameter convert_brep: ip_brep -> ip_t?.

  Parameter local_ip: ip_t -> bool. (* available to local nodes *)
  Parameter mcast_ip: ip_t -> bool. (* multicast addresses *)

  Axiom valid_ip_brep_spec:
    forall ip_b ip, convert_brep ip_b = Some ip ->
               List.Forall (fun b => b <> Byte.zero) ip_b /\
               length ip_b < max_byte_length /\
               (Z.of_nat ip <= Int.max_unsigned)%Z.

  Axiom normal_mcast_disjoint:
    forall ip, andb (local_ip ip) (mcast_ip ip) = false.

  Axiom default_ip_is_invalid:
    local_ip default_ip = false /\ mcast_ip default_ip = false.

End IPModelSig.

(* IPModSig could be instantiated, but it's not a contribution of our project. *)
Declare Module IP : IPModelSig.
