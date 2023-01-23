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
Compute circuit_wires test1_circuit.
Compute circuit_outputs test1_circuit.
Compute circuit_compute test1_circuit [false]. (* [false; false; false; true; true] *)
Compute circuit_compute test1_circuit [true]. (* [true; true; false; true; false] *)

Definition test2 := @vector_and 4 {| vector_list := [true; false; true; false]; vector_wf := eq_refl |}.
Compile test2.
Compute fun a b c d => circuit_compute test2_circuit [a; b; c; d].
Compute circuit_compute test2_circuit [false; false; false; false]. (* [false; false; false; false] *)
Compute circuit_compute test2_circuit [true; true; true; true]. (* [true; false; true; false] *)

Definition test3 (_ : bitvec 0) : bitvec 2 := {|
  vector_list :=
    let p := (true, false) in
    let '(a, b) := p in
    [a; b];
  vector_wf := eq_refl;
|}.

Compile test3.
Compute circuit_compute test3_circuit [].

Definition add_one (b1 b2 c : bool) : bool * bool :=
  (b1 ^^ b2 ^^ c, b1 && b2 || c && (b1 ^^ b2)).

Fixpoint list_add_aux bl1 bl2 bl_r c : list bool :=
  match bl1, bl2 with
  | b1 :: bl1', b2 :: bl2' =>
    let '(b_r, c') := (let x := add_one b1 b2 c in x) in
    list_add_aux bl1' bl2' (bl_r ++ [b_r]) c'
  | _, _ => bl_r
  end.

Eval cbv beta delta iota in fun a1 a2 a3 a4 b1 b2 b3 b4 => list_add_aux [a1; a2; a3; a4] [b1; b2; b3; b4] [].
Compute list_add_aux [true; false; true; false] [false; true; false; false] [] false.
  (* [true; true; true; false] *)
Compute list_add_aux [true; false; true; false] [true; true; false; false] [] false.
  (* [false; false; false; true] *)

#[program] Definition vector_add {n} (bv1 bv2 : bitvec n) : bitvec n := {|
  vector_list := list_add_aux (vector_list bv1) (vector_list bv2) [] false;
|}.
Next Obligation.
Admitted.

Definition test4 := @vector_add 4 {| vector_list := [true; false; true; false]; vector_wf := eq_refl |}.

Eval cbv beta delta iota in test4.

Compile test4.
Compute circuit_wires test4_circuit.
Compute circuit_compute test4_circuit [false; true; false; false]. (* [true; true; true; false] *)
Compute circuit_compute test4_circuit [true; true; false; false]. (* [false; false; false; true] *)

#[program] Definition adder {n} (bv : bitvec (2 * n)) : bitvec n :=
  let bv1 : bitvec n := {| vector_list := list_select (vector_list bv) (List.seq 0 n) false |} in
  let bv2 : bitvec n := {| vector_list := list_select (vector_list bv) (List.seq n n) false |} in
  {|
    vector_list := list_add_aux (vector_list bv1) (vector_list bv2) [] false;
  |}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Definition test5 := @adder 8.

Compile test5.
Compute circuit_wires test5_circuit.
Compute circuit_compute test5_circuit [true; false; true; false; false; false; false; false;
  false; true; false; false; false; false; false; false].
  (* [true; true; true; false; false; false; false; false] *)
Compute circuit_compute test5_circuit [true; false; true; false; false; false; false; false;
  true; true; false; false; false; false; false; false].
  (* [false; false; false; true; false; false; false; false] *)
