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

Lemma prove_le :
  forall n m,
  PeanoNat.Nat.leb n m = true ->
  n <= m.
Proof.
  intros n m H. rewrite (Bool.reflect_iff _ _ (PeanoNat.Nat.leb_spec0 n m)). auto.
Qed.

Register prove_le as vcpu.prove_le.

Register int as int.

Declare ML Module "vcpu_plugin:vcpu-plugin.plugin".
