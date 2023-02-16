Require Import Utils.

Require Import Lia.
Require Coq.Lists.List.
Import List.ListNotations.
Import Coq.NArith.BinNat.

Record vector {A n} := {
  vector_list : list A;
  vector_wf : N.of_nat (length vector_list) = n;
}.

Arguments vector : clear implicits.

Register vector as vcpu.vector.type.
Register Build_vector as vcpu.vector.constructor.
Register vector_list as vcpu.vector.list.
Register vector_wf as vcpu.vector.wf.

#[program] Definition vector_tail {A n} (v : vector A (N.succ n)) : vector A n := {|
  vector_list := List.tl (vector_list v);
|}.
Next Obligation.
  intros A n v. specialize (vector_wf v) as H. destruct (vector_list v).
  - simpl in H. apply N.neq_0_succ in H. destruct H.
  - simpl. simpl in H. lia.
Qed.

Notation bitvec := (vector bool).

Unset Program Cases.

#[program] Definition vector_map2 f {n} (bv1 bv2 : bitvec n) : bitvec n := {|
  vector_list := List.map (fun '(b1, b2) => f b1 b2) (List.combine (vector_list bv1) (vector_list bv2));
|}.
Next Obligation.
  intros f n bv1 bv2. rewrite List.map_length. rewrite List.combine_length.
  rewrite <- (Nnat.Nat2N.id (length (vector_list bv1))).
  rewrite <- (Nnat.Nat2N.id (length (vector_list bv2))).
  rewrite ? vector_wf. rewrite PeanoNat.Nat.min_id. lia.
Qed.

Set Program Cases.

Definition vector_and {n} (bv1 bv2 : bitvec n) : bitvec n := vector_map2 andb bv1 bv2.
