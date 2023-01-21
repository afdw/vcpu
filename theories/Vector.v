Require Import Utils.

Require Import Lia.

Require Coq.Lists.List.
Import List.ListNotations.

Record vector {A n} := {
  vector_list : list A;
  vector_wf : length vector_list = n;
}.

Arguments vector : clear implicits.

Register vector as vcpu.vector.type.
Register Build_vector as vcpu.vector.constructor.
Register vector_list as vcpu.vector.list.
Register vector_wf as vcpu.vector.wf.

#[program] Definition vector_tail {A n} (v : vector A (S n)) : vector A n := {|
  vector_list := List.tl (vector_list v);
|}.
Next Obligation.
  intros A n v. specialize (vector_wf v) as H. destruct (vector_list v).
  - simpl in H. congruence.
  - simpl. simpl in H. injection H as H. auto.
Qed.

Notation bitvec := (vector bool).

Unset Program Cases.

#[program] Definition vector_and {n} (bv1 bv2 : bitvec n) : bitvec n := {|
  vector_list := List.map (fun '(b1, b2) => b1 && b2) (List.combine (vector_list bv1) (vector_list bv2));
|}.
Next Obligation.
  intros n bv1 bv2. rewrite List.map_length. rewrite List.combine_length. rewrite ? vector_wf.
  apply PeanoNat.Nat.min_id.
Qed.

Set Program Cases.
