Require Import Utils.
Require Import Circuit.
Require Import Vector.
Require Import Plugin.

Require Import Lia.
Require Coq.Lists.List.
Import List.ListNotations.
Import Coq.NArith.BinNat.

Test.

Unset Program Cases.

#[program] Definition test1 (bv : bitvec 1) : bitvec 5 := let v := {|
  vector_list := match vector_list bv with [b] => [b; let e := b in e; false; true; negb b] | _ => [] end;
|} in v.
Next Obligation.
  intros bv. specialize (vector_wf bv) as H. destruct (vector_list bv) as [ | b l'].
  - cbv in H. congruence.
  - destruct l' as [ | b' l''].
    + auto.
    + rewrite ? length_bin_cons in H. lia.
Qed.

Set Program Cases.

Compile test1.
Compute circuit_wires test1_circuit.
Compute circuit_outputs test1_circuit.
Compute circuit_compute test1_circuit [false]. (* [false; false; false; true; true] *)
Compute circuit_compute test1_circuit [true]. (* [true; true; false; true; false] *)

Definition test2 := @vector_and 4 [|true; false; true; false|].
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
Print test3_circuit.
Compute test3_circuit.
Compute circuit_compute test3_circuit [].

Definition add_one (b1 b2 c : bool) : bool * bool :=
  (b1 ^^ b2 ^^ c, b1 && b2 || c && (b1 ^^ b2)).

Fixpoint list_add_aux bl1 bl2 bl_r c :=
  match bl1, bl2 with
  | b1 :: bl1', b2 :: bl2' =>
    let '(b_r, c') := (let x := add_one b1 b2 c in x) in
    list_add_aux bl1' bl2' (bl_r ++ [b_r]) c'
  | _, _ => bl_r
  end.

Compute list_add_aux [true; false; true; false] [false; true; false; false] [] false.
  (* [true; true; true; false] *)
Compute list_add_aux [true; false; true; false] [true; true; false; false] [] false.
  (* [false; false; false; true] *)

Eval cbv beta delta iota in fun a1 a2 a3 a4 b1 b2 b3 b4 =>
  list_add_aux [a1; a2; a3; a4] [b1; b2; b3; b4] [].

#[program] Definition vector_add {n} (bv1 bv2 : bitvec n) : bitvec n := {|
  vector_list := list_add_aux (vector_list bv1) (vector_list bv2) [] false;
|}.
Next Obligation.
Admitted.

Definition test4 := @vector_add 4 [|true; false; true; false|].

Eval cbv beta delta iota in test4.

Compile test4.
Compute circuit_wires test4_circuit.
Compute circuit_compute test4_circuit [false; true; false; false]. (* [true; true; true; false] *)
Compute circuit_compute test4_circuit [true; true; false; false]. (* [false; false; false; true] *)

#[program] Definition adder {n} (bv : bitvec (2 * n)) : bitvec n :=
  let bv1 : bitvec n := {|
    vector_list := list_select_bin (vector_list bv) (list_seq_bin 0 n) false
  |} in
  let bv2 : bitvec n := {|
    vector_list := list_select_bin (vector_list bv) (list_seq_bin n n) false
  |} in
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
Compute test5_circuit.
Compute length (circuit_wires test5_circuit). (* 3075 *)
Compute circuit_compute test5_circuit [true; false; true; false; false; false; false; false;
  false; true; false; false; false; false; false; false].
  (* [true; true; true; false; false; false; false; false] *)
Compute circuit_compute test5_circuit [true; false; true; false; false; false; false; false;
  true; true; false; false; false; false; false; false].
  (* [false; false; false; true; false; false; false; false] *)

Definition test6 := @adder 4.

Compile test6.

Definition add4' a1 a2 a3 a4 b1 b2 b3 b4 :=
  let 'c := false in
  let '(r1, c) := add_one a1 b1 c in
  let '(r2, c) := add_one a2 b2 c in
  let '(r3, c) := add_one a3 b3 c in
  let '(r4, c) := add_one a4 b4 c in
  [r1; r2; r3; r4].

Eval cbv beta delta iota in add4'.

Definition add4 a1 a2 a3 a4 b1 b2 b3 b4 :=
  let 'c := false in
  let '(r1, c) := (let x := add_one a1 b1 c in x) in
  let '(r2, c) := (let x := add_one a2 b2 c in x) in
  let '(r3, c) := (let x := add_one a3 b3 c in x) in
  let '(r4, c) := (let x := add_one a4 b4 c in x) in
  [r1; r2; r3; r4].

Eval cbv beta delta iota in add4.

Definition add_one' (a b c_in : bool) : bool * bool :=
  let t := a ^^ b in
  (t ^^ c_in, c_in && t || a && b).

Unset Program Cases.

#[program] Definition test7 (bv : bitvec 3) : bitvec 2 := {|
  vector_list :=
    match vector_list bv with
    | [a; b; c] => let '(r, c') := add_one' a b c in [r; c']
    | _ => [] end;
|}.
Next Obligation.
  intros bv. specialize (vector_wf bv) as H. destruct (vector_list bv) as [ | b l'].
  - cbv in H. congruence.
  - destruct l' as [ | b' l''].
    + cbv in H. congruence.
    + simpl in H. destruct l'' as [ | b'' l'''].
      * cbv in H. congruence.
      * simpl in H. destruct l''' as [ | b''' l''''].
        -- auto.
        -- rewrite ? length_bin_cons in H. lia.
Qed.

Set Program Cases.

Compile test7.
Print test7_circuit.
Compute test7_circuit.

#[program] Definition add {n} (bv1 bv2 : bitvec n) : bitvec n := {|
  vector_list := list_add_aux (vector_list bv1) (vector_list bv2) [] false;
|}.
Next Obligation.
Admitted.

#[program] Definition shift_left_one {n} (bv : bitvec n) : bitvec n := {|
  vector_list := false :: list_select_bin (vector_list bv) (list_seq_bin 0 (N.pred n)) false;
|}.
Next Obligation.
Admitted.

Definition test8 := @shift_left_one 8.
Compile test8.
Compute test8_circuit.

#[program] Definition zero {n} : bitvec n := {|
  vector_list := list_init_bin (fun _ => false) n;
|}.
Next Obligation.
Admitted.

Definition mul {n} (bv1 bv2 : bitvec n) : bitvec n :=
  fst (
    List.fold_left (fun t (b : bool) =>
      let '(bv_r, bv2') := t in
      let x := if b then bv2' else zero in
      (add bv_r x, shift_left_one bv2')
    ) (vector_list bv1) (zero, bv2)
  ).

#[program] Definition muler {n} (bv : bitvec (2 * n)) : bitvec n :=
  let bv1 : bitvec n := {|
    vector_list := list_select_bin (vector_list bv) (list_seq_bin 0 n) false
  |} in
  let bv2 : bitvec n := {|
    vector_list := list_select_bin (vector_list bv) (list_seq_bin n n) false
  |} in
  mul bv1 bv2.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Compile zero of 8%N as zero_8.
Compile shift_left_one of 8%N as shift_left_one_8.
Compile add of 8%N as add_8.
Compile mul of 8%N as mul_8.

Compute mul
  {| vector_list := fixed_bitlist_of_nat 8 12; vector_wf := eq_refl |}
  {| vector_list := fixed_bitlist_of_nat 8 34; vector_wf := eq_refl |}.
Compute bitlist_to_nat (circuit_compute add_8_circuit (fixed_bitlist_of_nat 8 12 ++ fixed_bitlist_of_nat 8 34)).
Compute bitlist_to_nat (circuit_compute mul_8_circuit (fixed_bitlist_of_nat 8 11 ++ fixed_bitlist_of_nat 8 17)).

(*
Compile zero of 32%N as zero_32.
Compile shift_left_one of 32%N as shift_left_one_32.
Compile add of 32%N as add_32.
Compile mul of 32%N as mul_32.

Definition mul_32_circuit' := Eval vm_compute in mul_32_circuit.
Set NativeCompute Timing.
Definition mul_32_circuit'' := Eval native_compute in circuit_simplify mul_32_circuit'.
Unset NativeCompute Timing.

Set NativeCompute Timing.
Eval native_compute in bitlist_to_binnat (circuit_compute mul_32_circuit''
  (fixed_bitlist_of_binnat 32 3543 ++ fixed_bitlist_of_binnat 32 1231)).
Unset NativeCompute Timing.
*)

Serialize (bitvec 5) as serialize_bitvec_5.
Compute vector_list (serialize_bitvec_5 [|true; false; true; false; false|]).
Serialize comparison as serialize_comparison.
Serialize (bool * bool) as serialize_pair_bool_bool.
Compute vector_list (serialize_pair_bool_bool (true, false)).
Serialize (vector (option comparison) 2 * bool) as serialize_pair_vector_option_comparison_2_bool.
Serialize (bitvec 100) as serialize_bitvec_100.
