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
Check @pair.
Check @inl.

Definition identity A (x : A) := x.

(* Set Printing All. *)

(* Vcpu Derive Compilation for identity with (F T (F R T)). *)
(* Vcpu Derive Compilation for (@option_map) with (F T (F T (F (F T T) (F T T)))). *)
(* Vcpu Derive Compilation for (λ A : Type, true) with (F T T). *)
(* Vcpu Derive Compilation for @pair with (F T (F T (F T (F T T)))). *)
(* Vcpu Derive Compilation for (@inl bool) with (F T (F T T)). *)
Vcpu Derive Compilation for (@pair bool bool true) with (F T T).
