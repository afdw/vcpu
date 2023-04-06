Require Import Utils.
Require Import Vector.

Require Import Lia.
Require Coq.Lists.List.
Import List.ListNotations.
Import Coq.NArith.BinNat.

Inductive reference :=
  | reference_Zero
  | reference_One
  | reference_Input (i : binnat)
  | reference_Wire (i : binnat).

Register reference as vcpu.reference.type.
Register reference_Zero as vcpu.reference.Zero.
Register reference_One as vcpu.reference.One.
Register reference_Input as vcpu.reference.Input.
Register reference_Wire as vcpu.reference.Wire.

Inductive binding :=
  | binding_Immediate (r : reference)
  | binding_Not (r : reference)
  | binding_And (r1 r2 : reference)
  | binding_Or (r1 r2 : reference)
  | binding_Xor (r1 r2 : reference)
  | binding_If (r1 r2 r3 : reference).

Register binding as vcpu.binding.type.
Register binding_Immediate as vcpu.binding.Immediate.
Register binding_Not as vcpu.binding.Not.
Register binding_And as vcpu.binding.And.
Register binding_Or as vcpu.binding.Or.
Register binding_Xor as vcpu.binding.Xor.
Register binding_If as vcpu.binding.If.

Record circuit := {
  circuit_input_count : binnat;
  circuit_wire_count : binnat;
  circuit_wires : list binding;
  circuit_output_wires : list binnat;
}.

Register circuit as vcpu.circuit.type.
Register Build_circuit as vcpu.circuit.constructor.
Register circuit_input_count as vcpu.circuit.input_count.
Register circuit_wires as vcpu.circuit.wires.
Register circuit_output_wires as vcpu.circuit.output_wires.

Definition reference_wf input_count wire_count r :=
  match r with
  | reference_Zero => True
  | reference_One => True
  | reference_Input i => (i < input_count)%N
  | reference_Wire i => (i < wire_count)%N
  end.

Definition binding_wf input_count wire_count b :=
  match b with
  | binding_Immediate r => reference_wf input_count wire_count r
  | binding_Not r => reference_wf input_count wire_count r
  | binding_And r1 r2 =>
    reference_wf input_count wire_count r1 /\
    reference_wf input_count wire_count r2
  | binding_Or r1 r2 =>
    reference_wf input_count wire_count r1 /\
    reference_wf input_count wire_count r2
  | binding_Xor r1 r2 =>
    reference_wf input_count wire_count r1 /\
    reference_wf input_count wire_count r2
  | binding_If r1 r2 r3 =>
    reference_wf input_count wire_count r1 /\
    reference_wf input_count wire_count r2 /\
    reference_wf input_count wire_count r3
  end.

Register reference_wf as vcpu.reference.wf.
Register binding_wf as vcpu.binding.wf.

Definition reference_wf_b input_count wire_count r :=
  match r with
  | reference_Zero => true
  | reference_One => true
  | reference_Input i => (i <? input_count)%N
  | reference_Wire i => (i <? wire_count)%N
  end.

Lemma reference_wf_b_reflect :
  forall input_count wire_count r,
  Bool.reflect (reference_wf input_count wire_count r) (reference_wf_b input_count wire_count r).
Proof.
  intros input_count wire_count r. destruct r as [ | | j | j]; simpl;
  try apply true_reflect; apply N.ltb_spec0.
Qed.

Definition binding_wf_b input_count wire_count b :=
  match b with
  | binding_Immediate r => reference_wf_b input_count wire_count r
  | binding_Not r => reference_wf_b input_count wire_count r
  | binding_And r1 r2 =>
    reference_wf_b input_count wire_count r1 &&
    reference_wf_b input_count wire_count r2
  | binding_Or r1 r2 =>
    reference_wf_b input_count wire_count r1 &&
    reference_wf_b input_count wire_count r2
  | binding_Xor r1 r2 =>
    reference_wf_b input_count wire_count r1 &&
    reference_wf_b input_count wire_count r2
  | binding_If r1 r2 r3 =>
    reference_wf_b input_count wire_count r1 &&
    (reference_wf_b input_count wire_count r2 &&
    reference_wf_b input_count wire_count r3)
  end.

Lemma binding_wf_b_reflect :
  forall input_count wire_count b,
  Bool.reflect (binding_wf input_count wire_count b) (binding_wf_b input_count wire_count b).
Proof.
  intros input_count wire_count b. destruct b as [r | r | r1 r2 | r1 r2 | r1 r2 | r1 r2 r3]; simpl;
  try apply true_reflect; do 2 try apply andb_reflect; apply reference_wf_b_reflect.
Qed.

Definition circuit_wire_count_wf c :=
  length_bin (circuit_wires c) = circuit_wire_count c.

Definition circuit_wires_wf c :=
  list_forall_i_bin (binding_wf (circuit_input_count c)) (circuit_wires c).

Definition circuit_output_wires_wf c :=
  list_forall (fun i => (i < circuit_wire_count c)%N) (circuit_output_wires c).

Definition circuit_wf c :=
  circuit_wire_count_wf c /\ circuit_wires_wf c /\ circuit_output_wires_wf c.

Register circuit_wires_wf as vcpu.circuit.wires_wf.
Register circuit_output_wires_wf as vcpu.circuit.output_wires_wf.
Register circuit_wf as vcpu.circuit.wf.

Record circuit_with_wf := {
  circuit_with_wf_circuit : circuit;
  circuit_with_wf_circuit_wf : circuit_wf circuit_with_wf_circuit;
}.

Register circuit_with_wf as vcpu.circuit_with_wf.type.
Register Build_circuit_with_wf as vcpu.circuit_with_wf.constructor.
Register circuit_with_wf_circuit as vcpu.circuit_with_wf.circuit.
Register circuit_with_wf_circuit_wf as vcpu.circuit_with_wf.circuit_wf.

Lemma reference_wf_big_enough :
  forall input_count input_count' wire_count wire_count' r,
  reference_wf input_count wire_count r ->
  (input_count' >= input_count)%N ->
  (wire_count' >= wire_count)%N ->
  reference_wf input_count' wire_count' r.
Proof.
  intros input_count input_count' wire_count wire_count' r H1 H2 H3.
  destruct r as [ | | j | j]; simpl; simpl in H1; lia.
Qed.

Lemma binding_wf_big_enough :
  forall input_count input_count' wire_count wire_count' b,
  binding_wf input_count wire_count b ->
  (input_count' >= input_count)%N ->
  (wire_count' >= wire_count)%N ->
  binding_wf input_count' wire_count' b.
Proof.
  intros input_count input_count' wire_count wire_count' b H1 H2 H3.
  destruct b as [r | r | r1 r2 | r1 r2 | r1 r2 | r1 r2 r3]; simpl; simpl in H1;
  intuition apply (reference_wf_big_enough input_count input_count' wire_count wire_count'); auto.
Qed.

Record circuit_with_wf_and_spec := {
  circuit_with_wf_and_spec_circuit_with_wf : circuit_with_wf;
  circuit_with_wf_and_spec_spec_statement : Prop;
  circuit_with_wf_and_spec_spec : circuit_with_wf_and_spec_spec_statement;
}.

Register circuit_with_wf_and_spec as vcpu.circuit_with_wf_and_spec.type.
Register Build_circuit_with_wf_and_spec as vcpu.circuit_with_wf_and_spec.constructor.
Register circuit_with_wf_and_spec_circuit_with_wf as vcpu.circuit_with_wf_and_spec.circuit_with_wf.
Register circuit_with_wf_and_spec_spec_statement as vcpu.circuit_with_wf_and_spec.spec_statement.
Register circuit_with_wf_and_spec_spec as vcpu.circuit_with_wf_and_spec.spec.

Definition reference_compute inputs intermediates r :=
  match r with
  | reference_Zero => false
  | reference_One => true
  | reference_Input i => list_nth_bin i inputs false
  | reference_Wire i => list_nth_bin i intermediates false
  end.

Definition binding_compute inputs intermediates b :=
  match b with
  | binding_Immediate r => reference_compute inputs intermediates r
  | binding_Not r => negb (reference_compute inputs intermediates r)
  | binding_And r1 r2 =>
    reference_compute inputs intermediates r1 && reference_compute inputs intermediates r2
  | binding_Or r1 r2 =>
    reference_compute inputs intermediates r1 || reference_compute inputs intermediates r2
  | binding_Xor r1 r2 =>
    reference_compute inputs intermediates r1 ^^ reference_compute inputs intermediates r2
  | binding_If r1 r2 r3 =>
    if reference_compute inputs intermediates r1
    then reference_compute inputs intermediates r3
    else reference_compute inputs intermediates r2
  end.

Definition circuit_compute_wires_aux start_intermediates wires inputs :=
  List.fold_left (fun intermediates b =>
    intermediates ++ [binding_compute inputs (start_intermediates ++ intermediates) b]
  ) wires [].

Definition circuit_compute_wires c inputs :=
  circuit_compute_wires_aux [] (circuit_wires c) inputs.

Definition circuit_compute c inputs :=
  list_select_bin (circuit_compute_wires c inputs) (circuit_output_wires c) false.

Register reference_compute as vcpu.reference.compute.
Register binding_compute as vcpu.binding.compute.
Register circuit_compute_wires_aux as vcpu.circuit.compute_wires_aux.
Register circuit_compute_wires as vcpu.circuit.compute_wires.
Register circuit_compute as vcpu.circuit.compute.

Lemma reference_compute_big_enough :
  forall inputs_1 inputs_2 intermediates_1 intermediates_2 r,
  reference_wf (length_bin inputs_1) (length_bin intermediates_1) r ->
  reference_compute (inputs_1 ++ inputs_2) (intermediates_1 ++ intermediates_2) r =
    reference_compute inputs_1 intermediates_1 r.
Proof.
  intros inputs_1 inputs_2 intermediates_1 intermediates_2 r H. destruct r as [ | | i | i]; simpl; simpl in H.
  - auto.
  - auto.
  - apply list_app_bin_nth_1. auto.
  - apply list_app_bin_nth_1. auto.
Qed.

Lemma binding_compute_big_enough :
  forall inputs_1 inputs_2 intermediates_1 intermediates_2 b,
  binding_wf (length_bin inputs_1) (length_bin intermediates_1) b ->
  binding_compute (inputs_1 ++ inputs_2) (intermediates_1 ++ intermediates_2) b =
    binding_compute inputs_1 intermediates_1 b.
Proof.
  intros inputs_1 inputs_2 intermediates_1 intermediates_2 b H.
  destruct b as [r | r | r1 r2 | r1 r2 | r1 r2 | r1 r2 r3]; simpl; simpl in H;
  rewrite ? reference_compute_big_enough; intuition auto.
Qed.

Lemma circuit_compute_wires_aux_big_enough :
  forall start_intermediates wires inputs_1 inputs_2,
  list_forall_i_bin (binding_wf (length_bin inputs_1)) wires ->
  circuit_compute_wires_aux start_intermediates wires (inputs_1 ++ inputs_2) =
    circuit_compute_wires_aux start_intermediates wires inputs_1.
Proof.
  intros start_intermediates wires inputs_1 inputs_2. unfold circuit_compute_wires_aux.
  cut (
    forall l,
    list_forall_i_bin_aux (binding_wf (length_bin inputs_1)) (length_bin l) wires ->
    List.fold_left (fun intermediates b =>
      intermediates ++ [binding_compute (inputs_1 ++ inputs_2) (start_intermediates ++ intermediates) b]
    ) wires l =
    List.fold_left (fun intermediates b =>
      intermediates ++ [binding_compute inputs_1 (start_intermediates ++ intermediates) b]
    ) wires l
  ).
  - intros H. apply (H []).
  - induction wires as [ | b wires' IH]; intros l H.
    + auto.
    + simpl. rewrite (List.app_nil_end (start_intermediates ++ l)) at 1.
      destruct H as (H1 & H2). rewrite binding_compute_big_enough.
      * apply IH. rewrite length_bin_app. rewrite length_bin_cons, length_bin_nil. simpl.
        rewrite N.add_1_r. auto.
      * rewrite length_bin_app. apply (binding_wf_big_enough _ _ _ _ _ H1); lia.
Qed.

Lemma circuit_compute_wires_big_enough :
  forall c inputs_1 inputs_2,
  length_bin inputs_1 = circuit_input_count c ->
  circuit_wf c ->
  circuit_compute_wires c (inputs_1 ++ inputs_2) = circuit_compute_wires c inputs_1.
Proof.
  intros c inputs_1 inputs_2 H1 H2. unfold circuit_compute_wires. apply circuit_compute_wires_aux_big_enough.
  rewrite H1. apply (proj1 (proj2 H2)).
Qed.

Lemma circuit_compute_big_enough :
  forall c inputs_1 inputs_2,
  length_bin inputs_1 = circuit_input_count c ->
  circuit_wf c ->
  circuit_compute c (inputs_1 ++ inputs_2) = circuit_compute c inputs_1.
Proof.
  intros c inputs_1 inputs_2 H1 H2. unfold circuit_compute. f_equal.
  apply (circuit_compute_wires_big_enough _ _ _ H1 H2).
Qed.

Theorem length_bin_circuit_compute_wires_aux :
  forall start_intermediates wires inputs,
  length_bin (circuit_compute_wires_aux start_intermediates wires inputs) = length_bin wires.
Proof.
  intros start_intermediates wires inputs. unfold circuit_compute_wires_aux.
  cut (
    forall l,
    length_bin (List.fold_left (fun intermediates b =>
      intermediates ++ [binding_compute inputs (start_intermediates ++ intermediates) b]
    ) wires l) = (length_bin l + length_bin wires)%N
  ).
  - intros H. apply (H []).
  - induction wires as [ | b wires' IH]; intros l.
    + simpl. rewrite length_bin_nil. lia.
    + simpl. rewrite IH. rewrite length_bin_app, ? length_bin_cons, length_bin_nil. lia.
Qed.

Lemma circuit_compute_wires_aux_app :
  forall start_intermediates wires_1 wires_2 inputs,
  circuit_compute_wires_aux start_intermediates (wires_1 ++ wires_2) inputs =
    let intermediates_1 := circuit_compute_wires_aux start_intermediates wires_1 inputs in
    intermediates_1 ++ circuit_compute_wires_aux (start_intermediates ++ intermediates_1) wires_2 inputs.
Proof.
  intros start_intermediates wires_1 wires_2 inputs. simpl. unfold circuit_compute_wires_aux.
  rewrite List.fold_left_app. rewrite list_fold_left_app_shift. f_equal. apply list_fold_left_ext.
  intros intermediates b. rewrite List.app_assoc. auto.
Qed.

#[program] Definition circuit_with_wf_compute_wires_vec
  c_with_wf (inputs : bitvec (circuit_input_count (circuit_with_wf_circuit c_with_wf)))
  : bitvec (circuit_wire_count (circuit_with_wf_circuit c_with_wf)) :=
  mk_vector (circuit_compute_wires (circuit_with_wf_circuit c_with_wf) (vector_list inputs)) _.
Next Obligation.
  intros c_with_wf inputs. unfold circuit_compute_wires. rewrite length_bin_circuit_compute_wires_aux.
  apply (proj1 (circuit_with_wf_circuit_wf c_with_wf)).
Qed.

#[program] Definition circuit_with_wf_compute_vec
  c_with_wf (inputs : bitvec (circuit_input_count (circuit_with_wf_circuit c_with_wf)))
  : bitvec (length_bin (circuit_output_wires (circuit_with_wf_circuit c_with_wf))) :=
  mk_vector (circuit_compute (circuit_with_wf_circuit c_with_wf) (vector_list inputs)) _.
Next Obligation.
  intros c_with_wf inputs. unfold circuit_compute. apply length_bin_list_select_bin.
Qed.

Register circuit_with_wf_compute_wires_vec as vcpu.circuit_with_wf.compute_wires_vec.
Register circuit_with_wf_compute_vec as vcpu.circuit_with_wf.compute_vec.

Definition circuit_increase_input_count c additional_input_count := {|
  circuit_input_count := circuit_input_count c + additional_input_count;
  circuit_wire_count := circuit_wire_count c;
  circuit_wires := circuit_wires c;
  circuit_output_wires := circuit_output_wires c;
|}.

Lemma circuit_increase_input_count_wf :
  forall c additional_input_count,
  circuit_wf c ->
  circuit_wf (circuit_increase_input_count c additional_input_count).
Proof.
  intros c additional_input_count H1. repeat split.
  - apply (proj1 H1).
  - apply (list_forall_i_bin_incr _ _ _ (proj1 (proj2 H1))). intros i b H3. simpl.
    apply (binding_wf_big_enough _ _ _ _ _ H3); lia.
  - apply (proj2 (proj2 H1)).
Qed.

Lemma circuit_increase_input_count_spec_wires :
  forall c additional_input_count,
  circuit_wf c ->
  forall inputs_1 inputs_2,
  length_bin inputs_1 = circuit_input_count c ->
  length_bin inputs_2 = additional_input_count ->
  circuit_compute_wires (circuit_increase_input_count c additional_input_count) (inputs_1 ++ inputs_2) =
    circuit_compute_wires c inputs_1.
Proof.
  intros c additional_input_count H1 inputs_1 inputs_2 H2 H3. unfold circuit_compute_wires. simpl.
  apply circuit_compute_wires_aux_big_enough. rewrite H2. apply (proj1 (proj2 H1)).
Qed.

#[program] Definition circuit_increase_input_count_with_wf_and_spec c_with_wf additional_input_count
  : circuit_with_wf_and_spec :=
  let c := circuit_with_wf_circuit c_with_wf in
  let c_wf := circuit_with_wf_circuit_wf c_with_wf in
  let c_res_with_wf := {|
    circuit_with_wf_circuit := circuit_increase_input_count c additional_input_count;
    circuit_with_wf_circuit_wf := circuit_increase_input_count_wf c additional_input_count c_wf;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement :=
      forall (inputs_1 : bitvec (circuit_input_count c)) (inputs_2 : bitvec additional_input_count),
      circuit_with_wf_compute_wires_vec c_res_with_wf (inputs_1 ++ inputs_2) =
        circuit_with_wf_compute_wires_vec c_with_wf inputs_1;
  |}.
Next Obligation.
  intros c_with_wf additional_input_count c c_wf c_res_with_wf inputs_1 inputs_2.
  unfold circuit_with_wf_compute_wires_vec. apply mk_vector_ext_all.
  apply circuit_increase_input_count_spec_wires.
  - apply c_wf.
  - apply (vector_wf inputs_1).
  - apply (vector_wf inputs_2).
Qed.

Register circuit_increase_input_count_with_wf_and_spec as vcpu.circuit.increase_input_count_with_wf_and_spec.

Definition circuit_set_output_wires c output_wires := {|
  circuit_input_count := circuit_input_count c;
  circuit_wire_count := circuit_wire_count c;
  circuit_wires := circuit_wires c;
  circuit_output_wires := output_wires;
|}.

Lemma circuit_set_output_wires_wf :
  forall c output_wires,
  circuit_wf c ->
  list_forall (fun i => (i < circuit_wire_count c)%N) output_wires ->
  circuit_wf (circuit_set_output_wires c output_wires).
Proof.
  intros c output_wires H1 H2. repeat split.
  - apply (proj1 H1).
  - apply (proj1 (proj2 H1)).
  - apply H2.
Qed.

Lemma circuit_set_output_wires_spec_wires :
  forall c output_wires,
  circuit_wf c ->
  list_forall (fun i => (i < circuit_wire_count c)%N) output_wires ->
  forall inputs, length_bin inputs = circuit_input_count c ->
  circuit_compute_wires (circuit_set_output_wires c output_wires) inputs =
     circuit_compute_wires c inputs.
Proof.
  intros c output_wires H1 H2 inputs H3. unfold circuit_compute_wires. auto.
Qed.

Lemma circuit_set_output_wires_spec :
  forall c output_wires,
  circuit_wf c ->
  list_forall (fun i => (i < circuit_wire_count c)%N) output_wires ->
  forall inputs, length_bin inputs = circuit_input_count c ->
  circuit_compute (circuit_set_output_wires c output_wires) inputs =
    list_select_bin (circuit_compute_wires c inputs) output_wires false.
Proof.
  intros c output_wires H1 H2 inputs H3. unfold circuit_compute.
  rewrite (circuit_set_output_wires_spec_wires _ _ H1 H2 _ H3). auto.
Qed.

#[program] Definition circuit_set_output_wires_with_wf_and_spec
  c_with_wf output_count (output_wires : vector binnat output_count)
  (H :
    let n := circuit_wire_count (circuit_with_wf_circuit c_with_wf) in
    list_forall_b
      (fun i => (i <? n)%N)
      (vector_list output_wires) =
    true
  )
  : circuit_with_wf_and_spec :=
  let c := circuit_with_wf_circuit c_with_wf in
  let c_wf := circuit_with_wf_circuit_wf c_with_wf in
  let H' := proj2 (Bool.reflect_iff _ _ (list_forall_b_reflect _ _ _ (fun i => N.ltb_spec0 i _))) H in
  let c_res_with_wf := {|
    circuit_with_wf_circuit := circuit_set_output_wires c (vector_list output_wires);
    circuit_with_wf_circuit_wf := circuit_set_output_wires_wf c (vector_list output_wires) c_wf H';
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement :=
      forall (inputs : bitvec (circuit_input_count c)) (outputs : bitvec output_count),
      let intermediates := circuit_with_wf_compute_wires_vec c_with_wf inputs in
      outputs ~= circuit_with_wf_compute_vec c_res_with_wf inputs ->
      vector_select_bin intermediates output_wires false ~= outputs;
  |}.
Next Obligation.
  intros c_with_wf output_count output_wires H1 c c_wf H' c_res_with_wf inputs outputs intermediates H2.
  unfold circuit_with_wf_compute_vec, vector_select_bin. unfold vector_similar; simpl. rewrite H2.
  apply circuit_set_output_wires_spec.
  - apply (circuit_with_wf_circuit_wf c_with_wf).
  - auto.
  - apply (vector_wf inputs).
Qed.

Register circuit_set_output_wires_with_wf_and_spec as vcpu.circuit.set_output_wires_with_wf_and_spec.

Definition circuit_add_translate_reference parent_wire_count input_references r :=
  match r with
  | reference_Zero => reference_Zero
  | reference_One => reference_One
  | reference_Input i => list_nth_bin i input_references reference_Zero
  | reference_Wire i => reference_Wire (parent_wire_count + i)
  end.

Definition circuit_add_translate_binding parent_wire_count input_references b :=
  let translate_reference := circuit_add_translate_reference parent_wire_count input_references in
  match b with
  | binding_Immediate r => binding_Immediate (translate_reference r)
  | binding_Not r => binding_Not (translate_reference r)
  | binding_And r1 r2 => binding_And (translate_reference r1) (translate_reference r2)
  | binding_Or r1 r2 => binding_Or (translate_reference r1) (translate_reference r2)
  | binding_Xor r1 r2 => binding_Xor (translate_reference r1) (translate_reference r2)
  | binding_If r1 r2 r3 => binding_If (translate_reference r1) (translate_reference r2) (translate_reference r3)
  end.

Definition circuit_add c_parent c_child input_references := {|
  circuit_input_count := circuit_input_count c_parent;
  circuit_wire_count := circuit_wire_count c_parent + circuit_wire_count c_child;
  circuit_wires :=
    circuit_wires c_parent ++
    List.map
      (circuit_add_translate_binding (circuit_wire_count c_parent) input_references)
      (circuit_wires c_child);
  circuit_output_wires := circuit_output_wires c_parent;
|}.

Lemma circuit_add_translate_reference_wf :
  forall c_parent c_child input_references,
  circuit_wf c_parent ->
  circuit_wf c_child ->
  length_bin input_references = circuit_input_count c_child ->
  list_forall
    (reference_wf (circuit_input_count c_parent) (circuit_wire_count c_parent))
    input_references ->
  forall i r,
  reference_wf (circuit_input_count c_child) i r ->
  reference_wf
    (circuit_input_count c_parent)
    (circuit_wire_count c_parent + i)
    (circuit_add_translate_reference (circuit_wire_count c_parent) input_references r).
Proof.
  intros c_parent c_child input_references H1 H2 H3 H4 i r H5.
  destruct r as [ | | j | j]; simpl; simpl in H5.
  - auto.
  - auto.
  - apply list_forall_list_nth_bin.
    + apply (list_forall_incr _ _ _ H4). intros r H6. apply (reference_wf_big_enough _ _ _ _ _ H6); lia.
    + lia.
  - lia.
Qed.

Lemma circuit_add_translate_binding_wf :
  forall c_parent c_child input_references,
  circuit_wf c_parent ->
  circuit_wf c_child ->
  length_bin input_references = circuit_input_count c_child ->
  list_forall
    (reference_wf (circuit_input_count c_parent) (circuit_wire_count c_parent))
    input_references ->
  forall i b,
  binding_wf (circuit_input_count c_child) i b ->
  binding_wf
    (circuit_input_count c_parent)
    (circuit_wire_count c_parent + i)
    (circuit_add_translate_binding (circuit_wire_count c_parent) input_references b).
Proof.
  intros c_parent c_child input_references H1 H2 H3 H4 i b H5.
  destruct b as [r | r | r1 r2 | r1 r2 | r1 r2 | r1 r2 r3]; simpl; simpl in H5;
  intuition (apply (circuit_add_translate_reference_wf _ _ _ H1 H2 H3 H4); auto).
Qed.

Lemma circuit_add_wf :
  forall c_parent c_child input_references,
  circuit_wf c_parent ->
  circuit_wf c_child ->
  length_bin input_references = circuit_input_count c_child ->
  list_forall
    (reference_wf (circuit_input_count c_parent) (circuit_wire_count c_parent))
    input_references ->
  circuit_wf (circuit_add c_parent c_child input_references).
Proof.
  intros c_parent c_child input_references H1 H2 H3. repeat split.
  - unfold circuit_wire_count_wf. simpl. rewrite length_bin_app. rewrite length_bin_list_map.
    rewrite (proj1 H1), (proj1 H2). auto.
  - unfold circuit_wires_wf. simpl. rewrite list_forall_i_bin_app. rewrite (proj1 H1). split.
    + apply (proj1 (proj2 H1)).
    + rewrite list_forall_i_bin_aux_map. rewrite list_forall_i_bin_aux_to_simple.
      apply (list_forall_i_bin_incr _ _ _ (proj1 (proj2 H2))).
      apply circuit_add_translate_binding_wf; auto.
  - unfold circuit_output_wires_wf. apply (list_forall_incr _ _ _ (proj2 (proj2 H1))).
    simpl. lia.
Qed.

Lemma circuit_add_translate_reference_spec :
  forall c_parent c_child input_references,
  circuit_wf c_parent ->
  circuit_wf c_child ->
  length_bin input_references = circuit_input_count c_child ->
  list_forall
    (reference_wf (circuit_input_count c_parent) (circuit_wire_count c_parent))
    input_references ->
  forall inputs, length_bin inputs = circuit_input_count c_parent ->
  let parent_intermediates := circuit_compute_wires c_parent inputs in
  forall intermediates i r,
  reference_wf (circuit_input_count c_child) i r ->
  reference_compute inputs (parent_intermediates ++ intermediates)
    (circuit_add_translate_reference (circuit_wire_count c_parent) input_references r) =
  reference_compute (List.map (reference_compute inputs parent_intermediates) input_references) intermediates r.
Proof.
  intros c_parent c_child input_references H1 H2 H3 H4 inputs H5 parent_intermediates intermediates i r H6.
  assert (H7 : length_bin parent_intermediates = circuit_wire_count c_parent). {
    subst parent_intermediates. unfold circuit_compute_wires. rewrite length_bin_circuit_compute_wires_aux.
    rewrite (proj1 H1). auto.
  }
  destruct r as [ | | j | j]; simpl.
  - auto.
  - auto.
  - replace false with (reference_compute inputs parent_intermediates reference_Zero) by auto.
    rewrite list_nth_bin_list_map. rewrite List.app_nil_end at 1. apply reference_compute_big_enough.
    simpl in H6. rewrite <- H3 in H6. rewrite H5, H7.
    apply (list_forall_list_nth_bin _ _ _ reference_Zero H4 H6).
  - replace (circuit_wire_count c_parent) with (length_bin parent_intermediates). apply list_app_bin_nth_2_add.
Qed.

Lemma circuit_add_translate_binding_spec :
  forall c_parent c_child input_references,
  circuit_wf c_parent ->
  circuit_wf c_child ->
  length_bin input_references = circuit_input_count c_child ->
  list_forall
    (reference_wf (circuit_input_count c_parent) (circuit_wire_count c_parent))
    input_references ->
  forall inputs, length_bin inputs = circuit_input_count c_parent ->
  let parent_intermediates := circuit_compute_wires c_parent inputs in
  forall intermediates i b,
  binding_wf (circuit_input_count c_child) i b ->
  binding_compute inputs (parent_intermediates ++ intermediates)
    (circuit_add_translate_binding (circuit_wire_count c_parent) input_references b) =
  binding_compute (List.map (reference_compute inputs parent_intermediates) input_references) intermediates b.
Proof.
  intros c_parent c_child input_references H1 H2 H3 H4 inputs H5 parent_intermediates intermediates i b H6.
  destruct b as [r | r | r1 r2 | r1 r2 | r1 r2 | r1 r2 r3]; simpl; simpl in H6;
  rewrite ? (circuit_add_translate_reference_spec _ _ _ H1 H2 H3 H4 _ H5 _ i); intuition auto.
Qed.

Lemma circuit_add_spec_wires :
  forall c_parent c_child input_references,
  circuit_wf c_parent ->
  circuit_wf c_child ->
  length_bin input_references = circuit_input_count c_child ->
  list_forall
    (reference_wf (circuit_input_count c_parent) (circuit_wire_count c_parent))
    input_references ->
  forall inputs, length_bin inputs = circuit_input_count c_parent ->
  let parent_intermediates := circuit_compute_wires c_parent inputs in
  let child_inputs := List.map (reference_compute inputs parent_intermediates) input_references in
  circuit_compute_wires (circuit_add c_parent c_child input_references) inputs =
    parent_intermediates ++ circuit_compute_wires c_child child_inputs.
Proof.
  intros c_parent c_child input_references H1 H2 H3 H4 inputs H5 parent_intermediates child_inputs.
  unfold circuit_compute_wires, circuit_add. simpl. rewrite circuit_compute_wires_aux_app.
  replace (circuit_compute_wires_aux [] (circuit_wires c_parent) inputs) with parent_intermediates by auto.
  simpl. f_equal. subst child_inputs. unfold circuit_compute_wires_aux.
  rewrite list_fold_left_list_map. apply list_fold_left_ext_precise. intros intermediates.
  rewrite list_forall_list_forall_i_bin. apply (list_forall_i_bin_incr _ _ _ (proj1 (proj2 H2))).
  intros i b H6. do 2 f_equal. apply (circuit_add_translate_binding_spec _ _ _ H1 H2 H3 H4 _ H5 _ _ _ H6).
Qed.

#[program] Definition circuit_add_with_wf_and_spec {n m}
  c_parent_with_wf c_child_with_wf
  (e_inputs_sub : extractor (circuit_input_count (circuit_with_wf_circuit c_parent_with_wf)) n)
  (e_parent_intermediates_sub : extractor (circuit_wire_count (circuit_with_wf_circuit c_parent_with_wf)) m)
  (input_reference_indexes : list binnat)
  : circuit_with_wf_and_spec :=
  let c_parent := circuit_with_wf_circuit c_parent_with_wf in
  let c_parent_wf := circuit_with_wf_circuit_wf c_parent_with_wf in
  let c_child := circuit_with_wf_circuit c_child_with_wf in
  let c_child_wf := circuit_with_wf_circuit_wf c_child_with_wf in
  let input_references :=
    List.concat (
      list_select_bin (
        List.map (List.map reference_Input) (extractor_transitions_to_list e_inputs_sub) ++
        List.map (List.map reference_Wire) (extractor_transitions_to_list e_parent_intermediates_sub)
      )
      input_reference_indexes []
    ) in
  let c_res_with_wf := {|
    circuit_with_wf_circuit := circuit_add c_parent c_child input_references;
    circuit_with_wf_circuit_wf :=
      circuit_add_wf c_parent c_child input_references c_parent_wf c_child_wf _ _;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement :=
      forall
        (inputs : bitvec (circuit_input_count c_parent))
        inputs_sub_ideals
        parent_intermediates_sub_ideals
        (child_outputs_ideal : bitvec (length_bin (circuit_output_wires c_child))),
      extractor_spec e_inputs_sub inputs_sub_ideals inputs ->
      let parent_intermediates := circuit_with_wf_compute_wires_vec c_parent_with_wf inputs in
      extractor_spec e_parent_intermediates_sub parent_intermediates_sub_ideals parent_intermediates ->
      let child_inputs :=
        mk_vector (
          List.concat (
            list_select_bin (
              extractor_ideals_to_list e_inputs_sub inputs_sub_ideals ++
              extractor_ideals_to_list e_parent_intermediates_sub parent_intermediates_sub_ideals
            )
            input_reference_indexes []
          )
        ) _ in
      let child_outputs := circuit_with_wf_compute_vec c_child_with_wf child_inputs in
      child_outputs ~= child_outputs_ideal ->
      let res_intermediates := circuit_with_wf_compute_wires_vec c_res_with_wf inputs in
      extractor_spec
        (extractor_cons _ (vector_of_list (
          List.map (fun i => (circuit_wire_count c_parent + i)%N) (circuit_output_wires c_child)
        )) _ (extractor_increase_input_count e_parent_intermediates_sub (circuit_wire_count c_child)))
        (child_outputs_ideal, parent_intermediates_sub_ideals) res_intermediates;
  |}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
  intros. simpl. rewrite list_forall_list_map. apply (list_forall_incr _ _ _ (proj2 (proj2 c_child_wf))).
  subst c_parent c_child. lia.
Qed.
Next Obligation.
  intros. symmetry. apply length_bin_list_map.
Qed.
Next Obligation.
  intros. apply extractor_spec_structure_cons. split.
  - admit.
  - admit.
Admitted.

(*#[program] Definition circuit_add_with_wf_and_spec {n}
  c_parent_with_wf c_child_with_wf
  (e_parent_intermediates_sub : extractor (circuit_wire_count (circuit_with_wf_circuit c_parent_with_wf)) n)
  (e_input_references :
    extractor
    (
      circuit_input_count (circuit_with_wf_circuit c_parent_with_wf) +
      n
    )
    (circuit_input_count (circuit_with_wf_circuit c_child_with_wf))
  )
  : circuit_with_wf_and_spec :=
  let c_parent := circuit_with_wf_circuit c_parent_with_wf in
  let c_parent_wf := circuit_with_wf_circuit_wf c_parent_with_wf in
  let c_child := circuit_with_wf_circuit c_child_with_wf in
  let c_child_wf := circuit_with_wf_circuit_wf c_child_with_wf in
  let c_res_with_wf := _ in
  {|
    circuit_with_wf_and_spec_spec_statement :=
      forall
        (inputs : bitvec (circuit_input_count c_parent))
        parent_intermediates_sub_ideals
        child_inputs_ideals
        (child_outputs_ideal : bitvec (length_bin (circuit_output_wires c_child))),
      let parent_intermediates := circuit_with_wf_compute_wires_vec c_parent_with_wf inputs in
      extractor_spec e_parent_intermediates_sub parent_intermediates_sub_ideals parent_intermediates ->
      let parent_intermediates_sub :=
        extractor_flatten_ideals e_parent_intermediates_sub parent_intermediates_sub_ideals in
      extractor_spec e_input_references child_inputs_ideals (inputs ++ parent_intermediates_sub) ->
      let child_inputs := extractor_flatten_ideals e_input_references child_inputs_ideals in
      let child_outputs := circuit_with_wf_compute_vec c_child_with_wf child_inputs in
      child_outputs ~= child_outputs_ideal ->
      let res_intermediates := circuit_with_wf_compute_wires_vec c_res_with_wf inputs in
      extractor_spec
        (extractor_cons _ (vector_of_list (
          List.map (fun i => (circuit_wire_count c_parent + i)%N) (circuit_output_wires c_child)
        )) _ (extractor_increase_input_count e_parent_intermediates_sub (circuit_wire_count c_child)))
        (child_outputs_ideal, parent_intermediates_sub_ideals) res_intermediates;
  |}.
Next Obligation.
Admitted.
Next Obligation.
  intros. f_equal. apply (extractor_lengths_wf e_parent_intermediates_sub).
Qed.
Next Obligation.
  intros. apply (extractor_lengths_wf e_input_references).
Qed.
Next Obligation.
  intros. simpl. rewrite list_forall_list_map. apply (list_forall_incr _ _ _ (proj2 (proj2 c_child_wf))).
  subst c_parent c_child. lia.
Qed.
Next Obligation.
  intros. symmetry. apply length_bin_list_map.
Qed.
Next Obligation.
Admitted.
Next Obligation.
  intros. apply extractor_spec_structure_cons. split.
  - admit.
  - admit.
Admitted.*)

(*#[program] Definition circuit_add_with_wf_and_spec
  c_parent_with_wf c_child_with_wf
  (input_references : vector reference (circuit_input_count (circuit_with_wf_circuit c_child_with_wf)))
  (H :
    list_forall_b
      (
        reference_wf_b
          (circuit_input_count (circuit_with_wf_circuit c_parent_with_wf))
          (circuit_wire_count (circuit_with_wf_circuit c_parent_with_wf))
      )
      (vector_list input_references) =
    true
  )
  : circuit_with_wf_and_spec :=
  let c_parent := circuit_with_wf_circuit c_parent_with_wf in
  let c_parent_wf := circuit_with_wf_circuit_wf c_parent_with_wf in
  let c_child := circuit_with_wf_circuit c_child_with_wf in
  let c_child_wf := circuit_with_wf_circuit_wf c_child_with_wf in
  let H' := proj2 (Bool.reflect_iff _ _ (list_forall_b_reflect _ _ _ (reference_wf_b_reflect _ _))) H in
  let c_res_with_wf := {|
    circuit_with_wf_circuit := circuit_add c_parent c_child (vector_list input_references);
    circuit_with_wf_circuit_wf :=
      circuit_add_wf c_parent c_child (vector_list input_references) c_parent_wf c_child_wf
        (vector_wf input_references) H';
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement :=
      forall (inputs : bitvec (circuit_input_count c_parent)),
      let parent_intermediates := circuit_with_wf_compute_wires_vec c_parent_with_wf inputs in
      forall (child_inputs : bitvec (circuit_input_count c_child))
        (child_outputs : bitvec (length_bin (circuit_output_wires c_child))),
      child_inputs ~=
        vector_map
          (reference_compute (vector_list inputs) (vector_list parent_intermediates))
          input_references ->
      let res_intermediates := circuit_with_wf_compute_wires_vec c_res_with_wf inputs in
      child_outputs ~= circuit_with_wf_compute_vec c_child_with_wf child_inputs ->
      vector_select_bin res_intermediates
        (vector_seq_bin 0 (circuit_wire_count c_parent)) false ~= parent_intermediates /\
      vector_select_bin res_intermediates
        (vector_of_list (
          List.map (fun i => (circuit_wire_count c_parent + i)%N) (circuit_output_wires c_child)
        )) false ~= child_outputs;
  |}.
Next Obligation.
  intros c_parent_with_wf c_child_with_wf input_references H c_parent c_parent_wf c_child c_child_wf
    H' c_res_with_wf inputs parent_intermediates child_inputs child_outputs H1 res_intermediates H2.
  pose (child_intermediates := circuit_with_wf_compute_wires_vec c_child_with_wf child_inputs).
  cut (res_intermediates ~= parent_intermediates ++ child_intermediates).
  - intros H3. unfold vector_select_bin. rewrite H3. unfold vector_similar; simpl.
    simpl. split.
    + subst c_parent. rewrite <- (vector_wf parent_intermediates). apply list_select_bin_app_1_seq.
    + cut (
        vector_select_bin (
          vector_select_bin (parent_intermediates ++ child_intermediates)
            (vector_seq_bin (circuit_wire_count c_parent) (circuit_wire_count c_child)) false
        ) (vector_of_list (circuit_output_wires c_child)) false ~= child_outputs
      ).
      * intros H4. rewrite <- H4. simpl. rewrite <- list_select_bin_assoc. f_equal. unfold list_select_bin.
        apply list_map_ext_precise. apply (list_forall_incr _ _ _ (proj2 (proj2 c_child_wf))). intros i H5.
        symmetry. apply list_nth_bin_list_seq_bin. auto.
      * unfold vector_similar; simpl.
        subst c_parent. rewrite <- (vector_wf parent_intermediates).
        subst c_child. rewrite <- (vector_wf child_intermediates).
        rewrite list_select_bin_app_2_seq. auto.
  - unfold circuit_with_wf_compute_wires_vec, vector_similar in parent_intermediates, child_intermediates |- *;
      simpl in parent_intermediates, child_intermediates |- *.
    subst c_child. rewrite H1. apply circuit_add_spec_wires.
    + apply c_parent_wf.
    + apply c_child_wf.
    + apply (vector_wf input_references).
    + apply H'.
    + apply (vector_wf inputs).
Qed.*)

Register circuit_add_with_wf_and_spec as vcpu.circuit.add_with_wf_and_spec.

Definition circuit_empty input_count := {|
  circuit_input_count := input_count;
  circuit_wire_count := 0;
  circuit_wires := [];
  circuit_output_wires := [];
|}.

Theorem circuit_empty_wf :
  forall input_count,
  circuit_wf (circuit_empty input_count).
Proof.
  intros input_count. cbv. auto.
Qed.

Lemma circuit_empty_spec_wires :
  forall input_count,
  forall inputs, length_bin inputs = input_count ->
  circuit_compute_wires (circuit_empty input_count) inputs = [].
Proof.
  intros input_count inputs H. auto.
Qed.

#[program] Definition circuit_empty_with_wf_and_spec input_count : circuit_with_wf_and_spec :=
  let c_res_with_wf := {|
    circuit_with_wf_circuit := circuit_empty input_count;
    circuit_with_wf_circuit_wf := circuit_empty_wf input_count;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement :=
      forall (inputs : bitvec input_count),
      circuit_with_wf_compute_wires_vec c_res_with_wf inputs = [||];
  |}.
Next Obligation.
  intros input_count c_res_with_wf inputs. unfold circuit_with_wf_compute_wires_vec. simpl.
  rewrite <- (mk_vector_eq_refl []). apply mk_vector_ext.
Qed.

Register circuit_empty_with_wf_and_spec as vcpu.circuit.empty_with_wf_and_spec.

Definition circuit_id input_count := {|
  circuit_input_count := input_count;
  circuit_wire_count := input_count;
  circuit_wires := list_init_bin (fun i => binding_Immediate (reference_Input i)) input_count;
  circuit_output_wires := list_seq_bin 0 input_count;
|}.

Theorem circuit_id_wf :
  forall input_count,
  circuit_wf (circuit_id input_count).
Proof.
  intros input_count. repeat split.
  - unfold circuit_wire_count_wf. simpl. apply length_bin_list_init_bin.
  - unfold circuit_wires_wf. simpl. rewrite list_forall_i_bin_list_init_bin. simpl. auto.
  - unfold circuit_output_wires_wf. simpl. apply list_forall_list_seq_bin. auto.
Qed.

Lemma circuit_id_spec_wires :
  forall input_count,
  forall inputs, length_bin inputs = input_count ->
  circuit_compute_wires (circuit_id input_count) inputs = inputs.
Proof.
  intros input_count inputs H. unfold circuit_compute_wires, circuit_compute_wires_aux, circuit_id. simpl.
  rewrite list_fold_left_list_init_bin. rewrite <- H; clear input_count H.
  - induction inputs as [ | x inputs' IH].
    + auto.
    + simpl. rewrite length_bin_cons. rewrite list_seq_bin_succ. simpl. rewrite list_fold_left_app_shift. simpl.
      f_equal. rewrite (list_fold_left_list_seq_bin_shift _ 0 1). rewrite <- IH at 2. simpl.
      apply list_fold_left_ext. intros intermediates i. rewrite <- succ_to_add. rewrite list_nth_bin_succ_cons.
      auto.
Qed.

Lemma circuit_id_spec :
  forall input_count,
  forall inputs, length_bin inputs = input_count ->
  circuit_compute (circuit_id input_count) inputs = inputs.
Proof.
  intros input_count inputs H. unfold circuit_compute. rewrite (circuit_id_spec_wires _ _ H). simpl.
  rewrite <- H. apply list_select_bin_all.
Qed.

#[program] Definition circuit_id_with_wf_and_spec input_count : circuit_with_wf_and_spec :=
  let c_res_with_wf := {|
    circuit_with_wf_circuit := circuit_id input_count;
    circuit_with_wf_circuit_wf := circuit_id_wf input_count;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement :=
      forall (inputs : bitvec input_count),
      circuit_with_wf_compute_vec c_res_with_wf inputs ~= inputs;
  |}.
Next Obligation.
  intros input_count c_res_with_wf inputs. unfold circuit_with_wf_compute_vec. simpl.
  unfold vector_similar; simpl. apply circuit_id_spec. apply (vector_wf inputs).
Qed.

Register circuit_id_with_wf_and_spec as vcpu.circuit.id_with_wf_and_spec.

Definition circuit_switch data_size := {|
  circuit_input_count := 1 + 2 * data_size;
  circuit_wire_count := data_size;
  circuit_wires :=
    list_init_bin (fun i =>
      binding_If
        (reference_Input 0)
        (reference_Input (1 + i))
        (reference_Input (1 + data_size + i))
    ) data_size;
  circuit_output_wires := list_seq_bin 0 data_size;
|}.

Theorem circuit_switch_wf :
  forall data_size,
  circuit_wf (circuit_switch data_size).
Proof.
  intros data_size. repeat split.
  - unfold circuit_wire_count_wf. simpl. apply length_bin_list_init_bin.
  - unfold circuit_wires_wf. simpl. rewrite list_forall_i_bin_list_init_bin. simpl. lia.
  - unfold circuit_output_wires_wf. simpl. rewrite list_forall_list_seq_bin. auto.
Qed.

Lemma circuit_switch_spec_wires :
  forall data_size,
  forall b inputs_1 inputs_2,
  length_bin inputs_1 = data_size%N ->
  length_bin inputs_2 = data_size%N ->
  circuit_compute_wires (circuit_switch data_size) (b :: inputs_1 ++ inputs_2) =
    if b then inputs_2 else inputs_1.
Proof.
  intros data_size b inputs_1 inputs_2 H1 H2.
  unfold circuit_compute_wires, circuit_compute_wires_aux, circuit_switch. simpl.
  rewrite list_fold_left_list_init_bin. simpl. rewrite <- list_map_list_fold_left.
  rewrite list_nth_bin_zero_cons. destruct b.
  - rewrite <- (list_select_bin_all inputs_2 false) at 1. unfold list_select_bin. rewrite H2. apply List.map_ext.
    intros i. rewrite <- N.add_assoc, <- succ_to_add. rewrite list_nth_bin_succ_cons.
    rewrite <- H1. apply list_app_bin_nth_2_add.
  - rewrite <- (list_select_bin_all inputs_1 false) at 1. unfold list_select_bin. rewrite H1.
    apply list_map_ext_precise. apply list_forall_list_seq_bin. intros i H3. simpl.
    rewrite <- succ_to_add. rewrite list_nth_bin_succ_cons.
    apply list_app_bin_nth_1. lia.
Qed.

Lemma circuit_switch_spec :
  forall data_size,
  forall b inputs_1 inputs_2,
  length_bin inputs_1 = data_size%N ->
  length_bin inputs_2 = data_size%N ->
  circuit_compute (circuit_switch data_size) (b :: inputs_1 ++ inputs_2) =
    if b then inputs_2 else inputs_1.
Proof.
  intros data_size b inputs_1 inputs_2 H1 H2. unfold circuit_compute.
  rewrite (circuit_switch_spec_wires _ _ _ _ H1 H2). simpl. destruct b.
  - rewrite <- H2. apply list_select_bin_all.
  - rewrite <- H1. apply list_select_bin_all.
Qed.

#[program] Definition circuit_switch_with_wf_and_spec data_size : circuit_with_wf_and_spec :=
  let c_res_with_wf := {|
    circuit_with_wf_circuit := circuit_switch data_size;
    circuit_with_wf_circuit_wf := circuit_switch_wf data_size;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement :=
      forall inputs b (inputs_1 inputs_2 : bitvec data_size),
      inputs ~= [|b|] ++ inputs_1 ++ inputs_2 ->
      circuit_with_wf_compute_vec c_res_with_wf inputs ~=
        if b then inputs_2 else inputs_1;
  |}.
Next Obligation.
  intros data_size c_res_with_wf inputs b inputs_1 inputs_2 H. unfold circuit_with_wf_compute_vec.
  unfold vector_similar; simpl. destruct inputs as (inputs_list, inputs_wf). simpl.
  rewrite H. simpl. rewrite circuit_switch_spec.
  - destruct b; auto.
  - apply (vector_wf inputs_1).
  - apply (vector_wf inputs_2).
Qed.

Register circuit_switch_with_wf_and_spec as vcpu.circuit.switch_with_wf_and_spec.

Definition circuit_zero := {|
  circuit_input_count := 0;
  circuit_wire_count := 1;
  circuit_wires := [binding_Immediate reference_Zero];
  circuit_output_wires := [0%N];
|}.

Theorem circuit_zero_wf :
  circuit_wf circuit_zero.
Proof.
  cbv. auto.
Qed.

Lemma circuit_zero_spec :
  circuit_compute circuit_zero [] = [false].
Proof.
  auto.
Qed.

#[program] Definition circuit_zero_with_wf_and_spec : circuit_with_wf_and_spec :=
  let c_res_with_wf := {|
    circuit_with_wf_circuit := circuit_zero;
    circuit_with_wf_circuit_wf := circuit_zero_wf;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement :=
      circuit_with_wf_compute_vec c_res_with_wf [||] = [|false|];
  |}.
Next Obligation.
  intros c_res_with_wf. auto.
Qed.

Register circuit_zero_with_wf_and_spec as vcpu.circuit.zero_with_wf_and_spec.

Definition circuit_one := {|
  circuit_input_count := 0;
  circuit_wire_count := 1;
  circuit_wires := [binding_Immediate reference_One];
  circuit_output_wires := [0%N];
|}.

Theorem circuit_one_wf :
  circuit_wf circuit_one.
Proof.
  cbv. auto.
Qed.

Lemma circuit_one_spec :
  circuit_compute circuit_one [] = [true].
Proof.
  auto.
Qed.

#[program] Definition circuit_one_with_wf_and_spec : circuit_with_wf_and_spec :=
  let c_res_with_wf := {|
    circuit_with_wf_circuit := circuit_one;
    circuit_with_wf_circuit_wf := circuit_one_wf;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement :=
      circuit_with_wf_compute_vec c_res_with_wf [||] = [|true|];
  |}.
Next Obligation.
  intros c_res_with_wf. auto.
Qed.

Register circuit_one_with_wf_and_spec as vcpu.circuit.one_with_wf_and_spec.

Definition circuit_not := {|
  circuit_input_count := 1;
  circuit_wire_count := 1;
  circuit_wires := [binding_Not (reference_Input 0)];
  circuit_output_wires := [0%N];
|}.

Theorem circuit_not_wf :
  circuit_wf circuit_not.
Proof.
  cbv. auto.
Qed.

Lemma circuit_not_spec :
  forall b,
  circuit_compute circuit_not [b] = [negb b].
Proof.
  intros b. auto.
Qed.

#[program] Definition circuit_not_with_wf_and_spec : circuit_with_wf_and_spec :=
  let c_res_with_wf := {|
    circuit_with_wf_circuit := circuit_not;
    circuit_with_wf_circuit_wf := circuit_not_wf;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement :=
      forall b,
      circuit_with_wf_compute_vec c_res_with_wf [|b|] = [|negb b|];
  |}.
Next Obligation.
  intros c_res_with_wf. auto.
Qed.

Register circuit_not_with_wf_and_spec as vcpu.circuit.not_with_wf_and_spec.

Definition circuit_and := {|
  circuit_input_count := 2;
  circuit_wire_count := 1;
  circuit_wires := [binding_And (reference_Input 0) (reference_Input 1)];
  circuit_output_wires := [0%N];
|}.

Theorem circuit_and_wf :
  circuit_wf circuit_and.
Proof.
  cbv. auto.
Qed.

Lemma circuit_and_spec :
  forall b1 b2,
  circuit_compute circuit_and [b1; b2] = [b1 && b2].
Proof.
  intros inputs H. auto.
Qed.

#[program] Definition circuit_and_with_wf_and_spec : circuit_with_wf_and_spec :=
  let c_res_with_wf := {|
    circuit_with_wf_circuit := circuit_and;
    circuit_with_wf_circuit_wf := circuit_and_wf;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement :=
      forall b1 b2,
      circuit_with_wf_compute_vec c_res_with_wf [|b1; b2|] = [|b1 && b2|];
  |}.
Next Obligation.
  intros c_res_with_wf. auto.
Qed.

Register circuit_and_with_wf_and_spec as vcpu.circuit.and_with_wf_and_spec.

Definition circuit_or := {|
  circuit_input_count := 2;
  circuit_wire_count := 1;
  circuit_wires := [binding_Or (reference_Input 0) (reference_Input 1)];
  circuit_output_wires := [0%N];
|}.

Theorem circuit_or_wf :
  circuit_wf circuit_or.
Proof.
  cbv. auto.
Qed.

Lemma circuit_or_spec :
  forall b1 b2,
  circuit_compute circuit_or [b1; b2] = [b1 || b2].
Proof.
  intros inputs H. auto.
Qed.

#[program] Definition circuit_or_with_wf_and_spec : circuit_with_wf_and_spec :=
  let c_res_with_wf := {|
    circuit_with_wf_circuit := circuit_or;
    circuit_with_wf_circuit_wf := circuit_or_wf;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement :=
      forall b1 b2,
      circuit_with_wf_compute_vec c_res_with_wf [|b1; b2|] = [|b1 || b2|];
  |}.
Next Obligation.
  intros c_res_with_wf. auto.
Qed.

Register circuit_or_with_wf_and_spec as vcpu.circuit.or_with_wf_and_spec.

Definition circuit_xor := {|
  circuit_input_count := 2;
  circuit_wire_count := 1;
  circuit_wires := [binding_Xor (reference_Input 0) (reference_Input 1)];
  circuit_output_wires := [0%N];
|}.

Theorem circuit_xor_wf :
  circuit_wf circuit_xor.
Proof.
  cbv. auto.
Qed.

Lemma circuit_xor_spec :
  forall b1 b2,
  circuit_compute circuit_xor [b1; b2] = [b1 ^^ b2].
Proof.
  intros inputs H. auto.
Qed.

#[program] Definition circuit_xor_with_wf_and_spec : circuit_with_wf_and_spec :=
  let c_res_with_wf := {|
    circuit_with_wf_circuit := circuit_xor;
    circuit_with_wf_circuit_wf := circuit_xor_wf;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement :=
      forall b1 b2,
      circuit_with_wf_compute_vec c_res_with_wf [|b1; b2|] = [|b1 ^^ b2|];
  |}.
Next Obligation.
  intros c_res_with_wf. auto.
Qed.

Register circuit_xor_with_wf_and_spec as vcpu.circuit.xor_with_wf_and_spec.

Definition circuit_simplify_translate_reference mapping r :=
  match r with
  | reference_Zero => reference_Zero
  | reference_One => reference_One
  | reference_Input i => reference_Input i
  | reference_Wire i => reference_Wire (binnat_list_assoc i mapping 0%N)
  end.

Definition circuit_simplify_translate_binding mapping b :=
  let translate_reference := circuit_simplify_translate_reference mapping in
  match b with
  | binding_Immediate r => binding_Immediate (translate_reference r)
  | binding_Not r => binding_Not (translate_reference r)
  | binding_And r1 r2 => binding_And (translate_reference r1) (translate_reference r2)
  | binding_Or r1 r2 => binding_Or (translate_reference r1) (translate_reference r2)
  | binding_Xor r1 r2 => binding_Xor (translate_reference r1) (translate_reference r2)
  | binding_If r1 r2 r3 => binding_If (translate_reference r1) (translate_reference r2) (translate_reference r3)
  end.

Definition circuit_simplify c :=
  let '(_, wires, mapping) :=
    List.fold_left (fun '(i, wires, mapping) b =>
      match b with
      | binding_Immediate (reference_Wire j) =>
        (
          N.succ i,
          wires,
          mapping ++ [(i, binnat_list_assoc j mapping 0%N)]
        )
      | _ =>
        (
          N.succ i,
          wires ++ [circuit_simplify_translate_binding mapping b],
          mapping ++ [(i, length_bin wires)]
        )
      end
    ) (circuit_wires c) (0%N, [], []) in
  {|
    circuit_input_count := circuit_input_count c;
    circuit_wire_count := length_bin wires;
    circuit_wires := wires;
    circuit_output_wires := List.map (fun i => binnat_list_assoc i mapping 0%N) (circuit_output_wires c);
  |}.

Register circuit_simplify as vcpu.circuit.simplify.
