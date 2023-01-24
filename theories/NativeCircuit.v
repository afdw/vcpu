Require Import Utils.
Require Import Circuit.

Require Coq.Lists.List.
Import List.ListNotations.

Require Coq.Numbers.Cyclic.Int63.Uint63.
Require Coq.Array.PArray.

Definition int := Uint63.int.
Definition array := PArray.array.

Definition int_of_nat n := Uint63.of_Z (BinIntDef.Z.of_nat n).
Definition int_to_nat n := BinIntDef.Z.to_nat (Uint63.to_Z n).

Inductive native_binding :=
  | native_binding_Zero
  | native_binding_Input (i : int)
  | native_binding_Nand (i j : int).

Register native_binding as vcpu.native_binding.type.
Register native_binding_Zero as vcpu.native_binding.Zero.
Register native_binding_Input as vcpu.native_binding.Input.
Register native_binding_Nand as vcpu.native_binding.Nand.

Record native_circuit := {
  native_circuit_input_count : int;
  native_circuit_wires : array native_binding;
  native_circuit_outputs : array int;
}.

Register native_circuit as vcpu.native_circuit.type.
Register Build_native_circuit as vcpu.native_circuit.constructor.
Register native_circuit_input_count as vcpu.native_circuit.input_count.
Register native_circuit_wires as vcpu.native_circuit.wires.
Register native_circuit_outputs as vcpu.native_circuit.outputs.

(*
Fixpoint array_fold_left_aux {A B} (f : A -> B -> A) (a : array B) (x : A) (i : nat) : A :=
  match i with
  | 0 => x
  | S i' => array_fold_left_aux f a (f x (PArray.get a (int_of_nat (int_to_nat (PArray.length a) - i - 1)))) i'
  end.

Definition array_fold_left {A B} (f : A -> B -> A) (a : array B) (x : A) : A :=
  array_fold_left_aux f a x (int_to_nat (PArray.length a)).

Fixpoint array_init_aux {A} (f : nat -> A) (n : nat) (a : array A) (i : nat) : array A :=
  match i with
  | 0 => a
  | S i' => array_init_aux f n (PArray.set a (int_of_nat (n - i - 1)) (f (n - i - 1))) i'
  end.

Definition array_init {A} (f : nat -> A) (n : nat) : array A :=
  array_init_aux f n (PArray.make (int_of_nat n) (f 0)) n.

Definition array_concat {A} (a1 a2 : array A) : array A :=
  array_init (fun i =>

Definition native_circuit_compute_wires_aux start_wire_values wires inputs :=
  array_fold_left (fun wire_values b =>
    wire_values ++ [match b with
    | native_binding_Zero => false
    | native_binding_Input i => PArray.get inputs i
    | native_binding_Nand i j =>
      nandb
        (PArray.get (start_wire_values ++ wire_values) i)
        (PArray.get (start_wire_values ++ wire_values) j)
    end]
  ) wires [].

Definition circuit_compute_wires c inputs :=
  circuit_compute_wires_aux [] (circuit_wires c) inputs.
*)
