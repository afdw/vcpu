#[warnings="-notation-incompatible-prefix"]
From Vcpu Require Import Tools.
From Vcpu Require Import Circuit.
From Vcpu Require Import Plugin.

(* Eval hnf in (4 : nat). *)

(* Check (∀ x : _, _) _. *)

Check 5.

Print inl.
About sum.
About list.

(* Test. *)

(* Set Printing All. *)

Vcpu Derive Encoder for bool as bool.

Vcpu Derive Encoder for sum as sum.
Check sum_len.
Check sum_encode.

Vcpu Derive Encoder for (sum bool bool).

Vcpu Derive Encoder for option as option.

Check @option_map.

Definition I A (x : A) := x.

Vcpu Derive Compilation for (I) with (F T (F T T)).
(* Vcpu Derive Compilation for (@option_map) with (F T (F T (F (F T T) (F T T)))). *)
