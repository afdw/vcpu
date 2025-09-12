#[warnings="-notation-incompatible-prefix"]
From Vcpu Require Import Tools.
From Vcpu Require Import Circuit.
From Vcpu Require Import Plugin.

Set Printing Width 120.

(* Eval hnf in (4 : nat). *)

(* Check (∀ x : _, _) _. *)

Check 5.

Print inl.
About sum.
About list.

(* Test. *)

(* Set Printing All. *)
Set Printing Implicit.

Print prod.

Vcpu Derive Encoder for prod as prod.
Print prod_encode.

Vcpu Derive Encoder for bool as bool.

Vcpu Derive Encoder for sum as sum.
Check sum_len.
Check sum_encode.

Vcpu Derive Encoder for (sum bool bool).

Vcpu Derive Encoder for option as option.

(* Vcpu Derive Encoder for vector. *)

Check @option_map.
Check @pair.
Check @inl.

Definition identity A (x : A) := x.

Check Nat.add_comm 2 3.

Definition swap A n m (v : vector A (n + m)) : vector A (m + n) :=
  rew [λ k, vector A k] (Nat.add_comm n m) in v.

Inductive vec' A (n : nat) := vec'_b (a : A).

Definition swap' A n m (v : vec' A (n + m)) : vec' A (m + n) :=
  rew [λ k, vec' A k] (Nat.add_comm n m) in v.

(* Set Printing All. *)

(* negb : bool → bool *)
(* ->   : ∀ in_len, circuit in_len 1 → circuit in_len 1 *)
(* ->   : ∀ in_len, bool * circuit in_len 1 → bool * circuit in_len 1 *)

(* @option_map A B : (A → B) → (option A → option B) *)
(* ->              : ∀ in_len, (circuit in_len A_len → circuit in_len B_len) → circuit in_len (1 + A_len) → circuit in_len (1 + B_len) *)

Compute swap'.

About eq_trans.

Print bool_encode.
Compute bool_encode true.
Compute [|true|] +||+ [||] +||+ [||].

Print xorb.

Definition exchange A B (p : A * B) : B * A :=
  match p with
  | (a, b) => (b, a)
  end.

Inductive many_things :=
  | MTA (_ : bool) (_ : bool) (_ : bool)
  | MTB (_ : bool)
  | MTC.

Definition many_things_transform (mt : many_things) : many_things :=
  match mt with
  | MTA b_1 b_2 b_3 => MTB (xorb b_1 (b_2 && b_3))
  | MTB b => MTC
  | MTC => MTA true false false
  end.

Vcpu Derive Encoder for many_things as many_things.

(* Vcpu Derive Compilation for identity with (F T (F R T)). *)
Vcpu Derive Compilation for @option_map with (F T (F T (F (F T T) (F T T)))).
(* Vcpu Derive Compilation for (λ A : Type, true) with (F T T). *)
(* Vcpu Derive Compilation for @pair with (F T (F T (F T (F T T)))). *)
(* Vcpu Derive Compilation for (@inl bool) with (F T (F T T)). *)
(* Vcpu Derive Compilation for (@pair bool bool true) with (F T T). *)
(* Vcpu Derive Compilation for swap' with (F T (F R (F R (F T T)))). *)
(* Vcpu Derive Compilation for (λ b : bool, if b then false else true) with (F R T). *)
(* Vcpu Derive Compilation for (λ b : bool, if b then false else true) with (F T T). *)
(* Vcpu Derive Compilation for @fst with (F T (F T (F T T))). *)
(* Vcpu Derive Compilation for @snd with (F T (F T (F T T))). *)
(* Vcpu Derive Compilation for xorb with (F T (F T T)). *)
(* Vcpu Derive Compilation for andb with (F T (F T T)). *)
(* Vcpu Derive Compilation for exchange with (F T (F T (F T T))). *)
(* Vcpu Derive Compilation for (λ p : bool * bool, let (b_1, b_2) := p in b_1 && b_2) with (F T T). *)
(* Vcpu Derive Compilation for many_things_transform with (F T T). *)
