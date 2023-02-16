Require Import Utils.
Require Import Vector.
Require Import Circuit.
Require Import NativeCircuit.

Require Coq.Lists.List.
Import List.ListNotations.

Register le_S as num.nat.le_S.
Register length as core.list.length.

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

Lemma prove_eq :
  forall n m,
  PeanoNat.Nat.eqb n m = true ->
  n = m.
Proof.
  intros n m H. rewrite (Bool.reflect_iff _ _ (PeanoNat.Nat.eqb_spec n m)). auto.
Qed.

Register prove_eq as vcpu.prove_eq.

Lemma prove_le :
  forall n m,
  PeanoNat.Nat.leb n m = true ->
  n <= m.
Proof.
  intros n m H. rewrite (Bool.reflect_iff _ _ (PeanoNat.Nat.leb_spec0 n m)). auto.
Qed.

Register prove_le as vcpu.prove_le.

Lemma prove_le_fast :
  forall n m,
  n <= m.
Proof.
Admitted.

Register prove_le_fast as vcpu.prove_le_fast.

Register int as int.

Declare ML Module "vcpu_plugin:vcpu-plugin.plugin".
