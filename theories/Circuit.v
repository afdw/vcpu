Require Import Utils.

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
  circuit_outputs : list binnat;
}.

Register circuit as vcpu.circuit.type.
Register Build_circuit as vcpu.circuit.constructor.
Register circuit_input_count as vcpu.circuit.input_count.
Register circuit_wires as vcpu.circuit.wires.
Register circuit_outputs as vcpu.circuit.outputs.

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

Definition circuit_outputs_wf c :=
  list_forall (fun i => (i < circuit_wire_count c)%N) (circuit_outputs c).

Definition circuit_wf c :=
  circuit_wire_count_wf c /\ circuit_wires_wf c /\ circuit_outputs_wf c.

Register circuit_wires_wf as vcpu.circuit.wires_wf.
Register circuit_outputs_wf as vcpu.circuit.outputs_wf.
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
  circuit_with_wf_and_spec_spec_statement : circuit_with_wf -> Prop;
  circuit_with_wf_and_spec_spec :
    circuit_with_wf_and_spec_spec_statement circuit_with_wf_and_spec_circuit_with_wf;
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
  list_select_bin (circuit_compute_wires c inputs) (circuit_outputs c) false.

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

Definition circuit_set_outputs c outputs := {|
  circuit_input_count := circuit_input_count c;
  circuit_wire_count := circuit_wire_count c;
  circuit_wires := circuit_wires c;
  circuit_outputs := outputs;
|}.

Lemma circuit_set_outputs_wf :
  forall c outputs,
  circuit_wf c ->
  list_forall (fun i => (i < circuit_wire_count c)%N) outputs ->
  circuit_wf (circuit_set_outputs c outputs).
Proof.
  intros c outputs H1 H2. repeat split.
  - apply (proj1 H1).
  - apply (proj1 (proj2 H1)).
  - apply H2.
Qed.

Lemma circuit_set_outputs_spec_wires :
  forall c outputs,
  circuit_wf c ->
  list_forall (fun i => (i < circuit_wire_count c)%N) outputs ->
  forall inputs, length_bin inputs = circuit_input_count c ->
  circuit_compute_wires (circuit_set_outputs c outputs) inputs = circuit_compute_wires c inputs.
Proof.
  intros c outputs H1 H2 inputs H3. unfold circuit_compute_wires. auto.
Qed.

Lemma circuit_set_outputs_spec :
  forall c outputs,
  circuit_wf c ->
  list_forall (fun i => (i < circuit_wire_count c)%N) outputs ->
  forall inputs, length_bin inputs = circuit_input_count c ->
  circuit_compute (circuit_set_outputs c outputs) inputs =
    list_select_bin (circuit_compute_wires c inputs) outputs false.
Proof.
  intros c outputs H1 H2 inputs H3. unfold circuit_compute.
  rewrite (circuit_set_outputs_spec_wires _ _ H1 H2 _ H3). auto.
Qed.

Definition circuit_set_outputs_with_wf_and_spec
  c_with_wf outputs
  (H :
    let n := circuit_wire_count (circuit_with_wf_circuit c_with_wf) in
    list_forall_b
      (fun i => (i <? n)%N)
      outputs =
    true
  )
  : circuit_with_wf_and_spec :=
  let c := circuit_with_wf_circuit c_with_wf in
  let c_wf := circuit_with_wf_circuit_wf c_with_wf in
  let H' := proj2 (Bool.reflect_iff _ _ (list_forall_b_reflect _ _ _ (fun i => N.ltb_spec0 i _))) H in
  let c_res_with_wf :=
  {|
    circuit_with_wf_circuit := circuit_set_outputs c outputs;
    circuit_with_wf_circuit_wf := circuit_set_outputs_wf c outputs c_wf H';
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement c_res :=
      forall inputs, length_bin inputs = circuit_input_count c ->
      circuit_compute (circuit_with_wf_circuit c_res) inputs =
        list_select_bin (circuit_compute_wires c inputs) outputs false;
    circuit_with_wf_and_spec_spec := circuit_set_outputs_spec c outputs c_wf H';
  |}.

Register circuit_set_outputs_with_wf_and_spec as vcpu.circuit.set_outputs_with_wf_and_spec.

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
  circuit_outputs := circuit_outputs c_parent;
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
  - unfold circuit_outputs_wf. apply (list_forall_incr _ _ _ (proj2 (proj2 H1))).
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
    rewrite list_nth_bin_list_map. remember (list_nth_bin j input_references reference_Zero) as r eqn:Heqr.
    destruct r as [ | | k | k]; simpl.
    + auto.
    + auto.
    + auto.
    + apply list_app_bin_nth_1. simpl in H6. rewrite <- H3 in H6.
      specialize (list_forall_list_nth_bin _ _ _ reference_Zero H4 H6) as H8. rewrite <- Heqr in H8. simpl in H8.
      lia.
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

Definition circuit_add_with_wf_and_spec
  c_parent_with_wf c_child_with_wf input_references
  (H1 : length_bin input_references = circuit_input_count (circuit_with_wf_circuit c_child_with_wf))
  (H2 :
    list_forall_b
      (
        reference_wf_b
          (circuit_input_count (circuit_with_wf_circuit c_parent_with_wf))
          (circuit_wire_count (circuit_with_wf_circuit c_parent_with_wf))
      )
      input_references =
    true
  )
  : circuit_with_wf_and_spec :=
  let c_parent := circuit_with_wf_circuit c_parent_with_wf in
  let c_parent_wf := circuit_with_wf_circuit_wf c_parent_with_wf in
  let c_child := circuit_with_wf_circuit c_child_with_wf in
  let c_child_wf := circuit_with_wf_circuit_wf c_child_with_wf in
  let H2' := proj2 (Bool.reflect_iff _ _ (list_forall_b_reflect _ _ _ (reference_wf_b_reflect _ _))) H2 in
  let c_res_with_wf := {|
    circuit_with_wf_circuit := circuit_add c_parent c_child input_references;
    circuit_with_wf_circuit_wf := circuit_add_wf c_parent c_child input_references c_parent_wf c_child_wf H1 H2';
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement c_res_with_wf :=
      forall inputs, length_bin inputs = circuit_input_count c_parent ->
      let parent_intermediates := circuit_compute_wires c_parent inputs in
      let child_inputs := List.map (reference_compute inputs parent_intermediates) input_references in
      circuit_compute_wires (circuit_with_wf_circuit c_res_with_wf) inputs =
        parent_intermediates ++ circuit_compute_wires c_child child_inputs;
    circuit_with_wf_and_spec_spec :=
      circuit_add_spec_wires c_parent c_child input_references c_parent_wf c_child_wf H1 H2';
  |}.

Register circuit_add_with_wf_and_spec as vcpu.circuit.add_with_wf_and_spec.

Definition circuit_empty input_count := {|
  circuit_input_count := input_count;
  circuit_wire_count := 0;
  circuit_wires := [];
  circuit_outputs := [];
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

Definition circuit_empty_with_wf_and_spec input_count : circuit_with_wf_and_spec :=
  let c_res_with_wf := {|
    circuit_with_wf_circuit := circuit_empty input_count;
    circuit_with_wf_circuit_wf := circuit_empty_wf input_count;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement c_res :=
      forall inputs, length_bin inputs = input_count ->
      circuit_compute_wires (circuit_with_wf_circuit c_res) inputs = [];
    circuit_with_wf_and_spec_spec := circuit_empty_spec_wires input_count;
  |}.

Register circuit_empty_with_wf_and_spec as vcpu.circuit.empty_with_wf_and_spec.

Definition circuit_id input_count := {|
  circuit_input_count := input_count;
  circuit_wire_count := input_count;
  circuit_wires := list_init_bin (fun i => binding_Immediate (reference_Input i)) input_count;
  circuit_outputs := list_seq_bin 0 input_count;
|}.

Theorem circuit_id_wf :
  forall input_count,
  circuit_wf (circuit_id input_count).
Proof.
  intros input_count. repeat split.
  - unfold circuit_wire_count_wf. simpl. apply length_bin_list_init_bin.
  - unfold circuit_wires_wf. simpl. rewrite list_forall_i_bin_list_init_bin. simpl. auto.
  - unfold circuit_outputs_wf. simpl. apply list_forall_list_seq_bin. auto.
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

Definition circuit_id_with_wf_and_spec input_count : circuit_with_wf_and_spec :=
  let c_res_with_wf := {|
    circuit_with_wf_circuit := circuit_id input_count;
    circuit_with_wf_circuit_wf := circuit_id_wf input_count;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement c_res :=
      forall inputs, length_bin inputs = input_count ->
      circuit_compute_wires (circuit_with_wf_circuit c_res) inputs = inputs;
    circuit_with_wf_and_spec_spec := circuit_id_spec_wires input_count;
  |}.

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
  circuit_outputs := list_seq_bin 0 data_size;
|}.

Theorem circuit_switch_wf :
  forall data_size,
  circuit_wf (circuit_switch data_size).
Proof.
  intros data_size. repeat split.
  - unfold circuit_wire_count_wf. simpl. apply length_bin_list_init_bin.
  - unfold circuit_wires_wf. simpl. rewrite list_forall_i_bin_list_init_bin. simpl. lia.
  - unfold circuit_outputs_wf. simpl. rewrite list_forall_list_seq_bin. auto.
Qed.

Lemma circuit_switch_spec_wires :
  forall data_size,
  forall inputs, length_bin inputs = (1 + 2 * data_size)%N ->
  circuit_compute_wires (circuit_switch data_size) inputs =
    if list_nth_bin 0 inputs false
    then list_select_bin inputs (list_seq_bin (1 + data_size) data_size) false
    else list_select_bin inputs (list_seq_bin 1 data_size) false.
Proof.
  intros data_size inputs H. unfold circuit_compute_wires, circuit_compute_wires_aux, circuit_switch. simpl.
  rewrite list_fold_left_list_init_bin. simpl. rewrite <- list_map_list_fold_left. unfold list_select_bin.
  destruct (list_nth_bin 0 inputs false).
  - rewrite (list_seq_bin_to_simple (1 + data_size)). rewrite List.map_map. auto.
  - rewrite (list_seq_bin_to_simple 1). rewrite List.map_map. auto.
Qed.

Lemma circuit_switch_spec :
  forall data_size,
  forall inputs, length_bin inputs = (1 + 2 * data_size)%N ->
  circuit_compute (circuit_switch data_size) inputs =
    if list_nth_bin 0 inputs false
    then list_select_bin inputs (list_seq_bin (1 + data_size) data_size) false
    else list_select_bin inputs (list_seq_bin 1 data_size) false.
Proof.
  intros data_size inputs H. unfold circuit_compute. rewrite (circuit_switch_spec_wires _ _ H). simpl.
  replace data_size with (length_bin (if list_nth_bin 0 inputs false
      then list_select_bin inputs (list_seq_bin (1 + data_size) data_size) false
      else list_select_bin inputs (list_seq_bin 1 data_size) false)) at 4.
  - apply list_select_bin_all.
  - destruct (list_nth_bin 0 inputs false).
    + rewrite length_bin_list_select_bin. apply length_list_seq_bin.
    + rewrite length_bin_list_select_bin. apply length_list_seq_bin.
Qed.

Definition circuit_switch_with_wf_and_spec data_size : circuit_with_wf_and_spec :=
  let c_res_with_wf := {|
    circuit_with_wf_circuit := circuit_switch data_size;
    circuit_with_wf_circuit_wf := circuit_switch_wf data_size;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c_res_with_wf;
    circuit_with_wf_and_spec_spec_statement c_res :=
      forall inputs, length_bin inputs = (1 + 2 * data_size)%N ->
      circuit_compute (circuit_with_wf_circuit c_res) inputs =
        if list_nth_bin 0 inputs false
        then list_select_bin inputs (list_seq_bin (1 + data_size) data_size) false
        else list_select_bin inputs (list_seq_bin 1 data_size) false;
    circuit_with_wf_and_spec_spec := circuit_switch_spec data_size;
  |}.

Register circuit_switch_with_wf_and_spec as vcpu.circuit.switch_with_wf_and_spec.

Definition circuit_zero := {|
  circuit_input_count := 0;
  circuit_wire_count := 1;
  circuit_wires := [binding_Immediate reference_Zero];
  circuit_outputs := [0%N];
|}.

Theorem circuit_zero_wf :
  circuit_wf circuit_zero.
Proof.
  cbv. auto.
Qed.

Lemma circuit_zero_spec :
  forall inputs, length_bin inputs = 0%N ->
  circuit_compute circuit_zero inputs = [false].
Proof.
  intros inputs H. auto.
Qed.

Definition circuit_zero_with_wf_and_spec : circuit_with_wf_and_spec :=
  let c := {|
    circuit_with_wf_circuit := circuit_zero;
    circuit_with_wf_circuit_wf := circuit_zero_wf;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c;
    circuit_with_wf_and_spec_spec_statement c :=
      forall inputs, length_bin inputs = 0%N ->
      circuit_compute (circuit_with_wf_circuit c) inputs = [false];
    circuit_with_wf_and_spec_spec := circuit_zero_spec;
  |}.

Register circuit_zero_with_wf_and_spec as vcpu.circuit.zero_with_wf_and_spec.

Definition circuit_one := {|
  circuit_input_count := 0;
  circuit_wire_count := 1;
  circuit_wires := [binding_Immediate reference_One];
  circuit_outputs := [0%N];
|}.

Theorem circuit_one_wf :
  circuit_wf circuit_one.
Proof.
  cbv. auto.
Qed.

Lemma circuit_one_spec :
  forall inputs, length_bin inputs = 0%N ->
  circuit_compute circuit_one inputs = [true].
Proof.
  intros inputs H. auto.
Qed.

Definition circuit_one_with_wf_and_spec : circuit_with_wf_and_spec :=
  let c := {|
    circuit_with_wf_circuit := circuit_one;
    circuit_with_wf_circuit_wf := circuit_one_wf;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c;
    circuit_with_wf_and_spec_spec_statement c :=
      forall inputs, length_bin inputs = 0%N ->
      circuit_compute (circuit_with_wf_circuit c) inputs = [true];
    circuit_with_wf_and_spec_spec := circuit_one_spec;
  |}.

Register circuit_one_with_wf_and_spec as vcpu.circuit.one_with_wf_and_spec.

Definition circuit_not := {|
  circuit_input_count := 1;
  circuit_wire_count := 1;
  circuit_wires := [binding_Not (reference_Input 0)];
  circuit_outputs := [0%N];
|}.

Theorem circuit_not_wf :
  circuit_wf circuit_not.
Proof.
  cbv. auto.
Qed.

Lemma circuit_not_spec :
  forall inputs, length_bin inputs = 1%N ->
  circuit_compute circuit_not inputs = [negb (List.nth 0 inputs false)].
Proof.
  intros inputs H. auto.
Qed.

Definition circuit_not_with_wf_and_spec : circuit_with_wf_and_spec :=
  let c := {|
    circuit_with_wf_circuit := circuit_not;
    circuit_with_wf_circuit_wf := circuit_not_wf;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c;
    circuit_with_wf_and_spec_spec_statement c :=
      forall inputs, length_bin inputs = 1%N ->
      circuit_compute (circuit_with_wf_circuit c) inputs = [negb (List.nth 0 inputs false)];
    circuit_with_wf_and_spec_spec := circuit_not_spec;
  |}.

Register circuit_not_with_wf_and_spec as vcpu.circuit.not_with_wf_and_spec.

Definition circuit_and := {|
  circuit_input_count := 2;
  circuit_wire_count := 1;
  circuit_wires := [binding_And (reference_Input 0) (reference_Input 1)];
  circuit_outputs := [0%N];
|}.

Theorem circuit_and_wf :
  circuit_wf circuit_and.
Proof.
  cbv. auto.
Qed.

Lemma circuit_and_spec :
  forall inputs, length_bin inputs = 2%N ->
  circuit_compute circuit_and inputs = [List.nth 0 inputs false && List.nth 1 inputs false].
Proof.
  intros inputs H. auto.
Qed.

Definition circuit_and_with_wf_and_spec : circuit_with_wf_and_spec :=
  let c := {|
    circuit_with_wf_circuit := circuit_and;
    circuit_with_wf_circuit_wf := circuit_and_wf;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c;
    circuit_with_wf_and_spec_spec_statement c :=
      forall inputs, length_bin inputs = 2%N ->
      circuit_compute (circuit_with_wf_circuit c) inputs = [List.nth 0 inputs false && List.nth 1 inputs false];
    circuit_with_wf_and_spec_spec := circuit_and_spec;
  |}.

Register circuit_and_with_wf_and_spec as vcpu.circuit.and_with_wf_and_spec.

Definition circuit_or := {|
  circuit_input_count := 2;
  circuit_wire_count := 1;
  circuit_wires := [binding_Or (reference_Input 0) (reference_Input 1)];
  circuit_outputs := [0%N];
|}.

Theorem circuit_or_wf :
  circuit_wf circuit_or.
Proof.
  cbv. auto.
Qed.

Lemma circuit_or_spec :
  forall inputs, length_bin inputs = 2%N ->
  circuit_compute circuit_or inputs = [List.nth 0 inputs false || List.nth 1 inputs false].
Proof.
  intros inputs H. auto.
Qed.

Definition circuit_or_with_wf_and_spec : circuit_with_wf_and_spec :=
  let c := {|
    circuit_with_wf_circuit := circuit_or;
    circuit_with_wf_circuit_wf := circuit_or_wf;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c;
    circuit_with_wf_and_spec_spec_statement c :=
      forall inputs, length_bin inputs = 2%N ->
      circuit_compute (circuit_with_wf_circuit c) inputs = [List.nth 0 inputs false || List.nth 1 inputs false];
    circuit_with_wf_and_spec_spec := circuit_or_spec;
  |}.

Register circuit_or_with_wf_and_spec as vcpu.circuit.or_with_wf_and_spec.

Definition circuit_xor := {|
  circuit_input_count := 2;
  circuit_wire_count := 1;
  circuit_wires := [binding_Xor (reference_Input 0) (reference_Input 1)];
  circuit_outputs := [0%N];
|}.

Theorem circuit_xor_wf :
  circuit_wf circuit_xor.
Proof.
  cbv. auto.
Qed.

Lemma circuit_xor_spec :
  forall inputs, length_bin inputs = 2%N ->
  circuit_compute circuit_xor inputs = [List.nth 0 inputs false ^^ List.nth 1 inputs false].
Proof.
  intros inputs H. auto.
Qed.

Definition circuit_xor_with_wf_and_spec : circuit_with_wf_and_spec :=
  let c := {|
    circuit_with_wf_circuit := circuit_xor;
    circuit_with_wf_circuit_wf := circuit_xor_wf;
  |} in
  {|
    circuit_with_wf_and_spec_circuit_with_wf := c;
    circuit_with_wf_and_spec_spec_statement c :=
      forall inputs, length_bin inputs = 2%N ->
      circuit_compute (circuit_with_wf_circuit c) inputs = [List.nth 0 inputs false ^^ List.nth 1 inputs false];
    circuit_with_wf_and_spec_spec := circuit_xor_spec;
  |}.

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
    circuit_outputs := List.map (fun i => binnat_list_assoc i mapping 0%N) (circuit_outputs c);
  |}.

Register circuit_simplify as vcpu.circuit.simplify.
