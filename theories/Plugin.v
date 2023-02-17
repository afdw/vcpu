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

Declare ML Module "vcpu_plugin:vcpu-plugin.plugin".
