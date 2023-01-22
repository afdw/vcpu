Require Import Utils.
Require Import Circuit.
Require Import Vector.
Require Import Plugin.

Require Coq.Lists.List.
Import List.ListNotations.

Unset Program Cases.

#[program] Definition test1 (bv : bitvec 1) : bitvec 5 := let v := {|
  vector_list := match vector_list bv with [b] => [b; let e := b in e; false; true; negb b] | _ => [] end;
|} in v.
Next Obligation.
  intros bv. specialize (vector_wf bv) as H. destruct (vector_list bv) as [ | b l'].
  - simpl in H. congruence.
  - destruct l' as [ | b' l''].
    + auto.
    + simpl in H. congruence.
Qed.

Set Program Cases.

Compile test1.
Compute (circuit_wires test1_circuit).
Compute (circuit_outputs test1_circuit).
Compute (circuit_compute test1_circuit [false]). (* [false; false; false; true; true] *)
Compute (circuit_compute test1_circuit [true]). (* [true; true; false; true; false] *)

Definition test2 := @vector_and 4 {| vector_list := [true; false; true; false]; vector_wf := eq_refl |}.
Compile test2.
Compute (fun a b c d => circuit_compute test2_circuit [a; b; c; d]).
Compute circuit_compute test2_circuit [false; false; false; false]. (* [false; false; false; false] *)
Compute circuit_compute test2_circuit [true; true; true; true]. (* [true; false; true; false] *)
