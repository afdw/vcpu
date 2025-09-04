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

Vcpu Derive Encode for (sum bool bool).
