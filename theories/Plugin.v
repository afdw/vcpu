Require Import Utils.
Require Import Vector.
Require Import Circuit.

Require Coq.Lists.List.
Import List.ListNotations.

Register le_S as num.nat.le_S.
Register length as core.list.length.

Lemma prove_nat_le :
  forall n m,
  PeanoNat.Nat.leb n m = true ->
  n <= m.
Proof.
  intros n m H. rewrite (Bool.reflect_iff _ _ (PeanoNat.Nat.leb_spec0 n m)). auto.
Qed.

Register prove_nat_le as num.nat.prove_le.

Fixpoint bitlist_to_nat (bl : list bool) : nat :=
  match bl with
  | [] => 0
  | b :: bl' => (if b then 1 else 0) + 2 * bitlist_to_nat bl'
  end.

Register bitlist_to_nat as vcpu.bitlist_to_nat.

Fixpoint bitlist_of_nat (n m : nat) : list bool :=
  match n with
  | 0 => []
  | S n' => (Nat.eqb (Nat.modulo m 2) 1) :: bitlist_of_nat n' (Nat.div m 2)
  end.

Declare ML Module "vcpu_plugin:vcpu-plugin.plugin".
