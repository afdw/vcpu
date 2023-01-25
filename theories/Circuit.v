Require Import Utils.

Require Import Lia.

Require Coq.Lists.List.
Import List.ListNotations.

Inductive reference :=
  | reference_Zero
  | reference_One
  | reference_Input (i : nat)
  | reference_Wire (i : nat).

Register reference as vcpu.reference.type.
Register reference_Zero as vcpu.reference.Zero.
Register reference_One as vcpu.reference.One.
Register reference_Input as vcpu.reference.Input.
Register reference_Wire as vcpu.reference.Wire.

Inductive binding :=
  | binding_Immidiate (r : reference)
  | binding_Not (r : reference)
  | binding_And (r1 r2 : reference)
  | binding_Or (r1 r2 : reference)
  | binding_Xor (r1 r2 : reference)
  | binding_If (r1 r2 r3 : reference).

Register binding as vcpu.binding.type.
Register binding_Immidiate as vcpu.binding.Immidiate.
Register binding_Not as vcpu.binding.Not.
Register binding_And as vcpu.binding.And.
Register binding_Or as vcpu.binding.Or.
Register binding_Xor as vcpu.binding.Xor.
Register binding_If as vcpu.binding.If.

Record circuit := {
  circuit_input_count : nat;
  circuit_wires : list binding;
  circuit_outputs : list nat;
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
  | reference_Input i => i < input_count
  | reference_Wire i => i < wire_count
  end.

Definition binding_wf input_count wire_count b :=
  match b with
  | binding_Immidiate r => reference_wf input_count wire_count r
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

Definition circuit_wires_wf c :=
  list_forall_i (binding_wf (circuit_input_count c)) (circuit_wires c).

Definition circuit_outputs_wf c :=
  list_forall (fun i => i < length (circuit_wires c)) (circuit_outputs c).

Definition circuit_wf c :=
  circuit_wires_wf c /\ circuit_outputs_wf c.

Definition reference_compute inputs intermediates r :=
  match r with
  | reference_Zero => false
  | reference_One => true
  | reference_Input i => List.nth i inputs false
  | reference_Wire i => List.nth i intermediates false
  end.

Definition binding_compute inputs intermediates b :=
  match b with
  | binding_Immidiate r => reference_compute inputs intermediates r
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
  list_select (circuit_compute_wires c inputs) (circuit_outputs c) false.

Definition circuit_set_outputs c outputs := {|
  circuit_input_count := circuit_input_count c;
  circuit_wires := circuit_wires c;
  circuit_outputs := outputs;
|}.

Register circuit_set_outputs as vcpu.circuit.set_outputs.

Definition circuit_add_translate_reference parent_wire_count input_references r :=
  match r with
  | reference_Zero => reference_Zero
  | reference_One => reference_One
  | reference_Input i => List.nth i input_references reference_Zero
  | reference_Wire i => reference_Wire (parent_wire_count + i)
  end.

Definition circuit_add_translate_binding parent_wire_count input_references b :=
  let translate_reference := circuit_add_translate_reference parent_wire_count input_references in
  match b with
  | binding_Immidiate r => binding_Immidiate (translate_reference r)
  | binding_Not r => binding_Not (translate_reference r)
  | binding_And r1 r2 => binding_And (translate_reference r1) (translate_reference r2)
  | binding_Or r1 r2 => binding_Or (translate_reference r1) (translate_reference r2)
  | binding_Xor r1 r2 => binding_Xor (translate_reference r1) (translate_reference r2)
  | binding_If r1 r2 r3 => binding_If (translate_reference r1) (translate_reference r2) (translate_reference r3)
  end.

Definition circuit_add c_parent c_child input_references := {|
  circuit_input_count := circuit_input_count c_parent;
  circuit_wires :=
    circuit_wires c_parent ++
    List.map
      (circuit_add_translate_binding (length (circuit_wires c_parent)) input_references)
      (circuit_wires c_child);
  circuit_outputs := circuit_outputs c_parent;
|}.

Register circuit_add as vcpu.circuit.add.

Definition circuit_empty input_count := {|
  circuit_input_count := input_count;
  circuit_wires := [];
  circuit_outputs := [];
|}.

Register circuit_empty as vcpu.circuit.empty.

Definition circuit_id input_count := {|
  circuit_input_count := input_count;
  circuit_wires := list_init (fun i => binding_Immidiate (reference_Input i)) input_count;
  circuit_outputs := List.seq 0 input_count;
|}.

Register circuit_id as vcpu.circuit.id.

Definition circuit_zero := {|
  circuit_input_count := 0;
  circuit_wires := [binding_Immidiate reference_Zero];
  circuit_outputs := [0];
|}.

Register circuit_zero as vcpu.circuit.zero.

Definition circuit_one := {|
  circuit_input_count := 0;
  circuit_wires := [binding_Immidiate reference_One];
  circuit_outputs := [0];
|}.

Register circuit_one as vcpu.circuit.one.

Definition circuit_not := {|
  circuit_input_count := 1;
  circuit_wires := [binding_Not (reference_Input 0)];
  circuit_outputs := [0];
|}.

Register circuit_not as vcpu.circuit.not.

Definition circuit_and := {|
  circuit_input_count := 2;
  circuit_wires := [binding_And (reference_Input 0) (reference_Input 1)];
  circuit_outputs := [0];
|}.

Register circuit_and as vcpu.circuit.and.

Definition circuit_or := {|
  circuit_input_count := 2;
  circuit_wires := [binding_Or (reference_Input 0) (reference_Input 1)];
  circuit_outputs := [0];
|}.

Register circuit_or as vcpu.circuit.or.

Definition circuit_xor := {|
  circuit_input_count := 2;
  circuit_wires := [binding_Xor (reference_Input 0) (reference_Input 1)];
  circuit_outputs := [0];
|}.

Register circuit_xor as vcpu.circuit.xor.

Definition circuit_switch data_size := {|
  circuit_input_count := 1 + 2 * data_size;
  circuit_wires :=
    list_init (fun i =>
      binding_If (reference_Input 0) (reference_Input (1 + i)) (reference_Input (1 + data_size + i))
    ) data_size;
  circuit_outputs := List.seq 0 data_size;
|}.

Register circuit_switch as vcpu.circuit.switch.

(*Inductive binding :=
  | binding_Zero
  | binding_Input (i : nat)
  | binding_Nand (i j : nat).

Register binding as vcpu.binding.type.
Register binding_Zero as vcpu.binding.Zero.
Register binding_Input as vcpu.binding.Input.
Register binding_Nand as vcpu.binding.Nand.

Record circuit := {
  circuit_input_count : nat;
  circuit_wires : list binding;
  circuit_outputs : list nat;
  circuit_wires_wf :
    list_forall_i (fun i b =>
      match b with
      | binding_Zero => True
      | binding_Input j => j < circuit_input_count
      | binding_Nand j k => j < i /\ k < i
      end
    ) circuit_wires;
  circuit_outputs_wf :
    list_forall (fun i => i < length circuit_wires) circuit_outputs;
}.

Register circuit as vcpu.circuit.type.
Register Build_circuit as vcpu.circuit.constructor.
Register circuit_input_count as vcpu.circuit.input_count.
Register circuit_wires as vcpu.circuit.wires.
Register circuit_outputs as vcpu.circuit.outputs.
Register circuit_wires_wf as vcpu.circuit.wires_wf.
Register circuit_outputs_wf as vcpu.circuit.outputs_wf.

Definition circuit_compute_wires_aux start_wire_values wires inputs :=
  List.fold_left (fun wire_values b =>
    wire_values ++ [match b with
    | binding_Zero => false
    | binding_Input i => List.nth i inputs false
    | binding_Nand i j =>
      nandb
        (List.nth i (start_wire_values ++ wire_values) false)
        (List.nth j (start_wire_values ++ wire_values) false)
    end]
  ) wires [].

Definition circuit_compute_wires c inputs :=
  circuit_compute_wires_aux [] (circuit_wires c) inputs.

Definition circuit_compute c inputs :=
  list_select (circuit_compute_wires c inputs) (circuit_outputs c) false.

Theorem length_circuit_compute_wires_aux :
  forall start_wire_values wires inputs,
  length (circuit_compute_wires_aux start_wire_values wires inputs) = length wires.
Proof.
  cut (forall start_wire_values wires inputs init_wire_values, length (List.fold_left (fun wire_values b =>
      wire_values ++ [match b with
      | binding_Zero => false
      | binding_Input i => List.nth i inputs false
      | binding_Nand i j =>
        nandb
          (List.nth i (start_wire_values ++ wire_values) false)
          (List.nth j (start_wire_values ++ wire_values) false)
      end]
    ) wires init_wire_values) = length init_wire_values + length wires).
  - intros H. intros start_wire_values wires inputs. apply (H _ _ _ []).
  - intros start_wire_values wires inputs. induction wires as [ | b wires' IH]; intros init_wire_values.
    + simpl. rewrite PeanoNat.Nat.add_0_r. auto.
    + simpl. rewrite IH. rewrite List.app_length. simpl. rewrite <- PeanoNat.Nat.add_assoc. auto.
Qed.

Theorem length_circuit_compute_wires :
  forall c inputs,
  length (circuit_compute_wires c inputs) = length (circuit_wires c).
Proof.
  intros c inputs. unfold circuit_compute_wires. apply length_circuit_compute_wires_aux.
Qed.

Theorem circuit_compute_wires_aux_app :
  forall start_wire_values wires_1 wires_2 inputs,
  circuit_compute_wires_aux start_wire_values (wires_1 ++ wires_2) inputs =
    let wire_values_1 := circuit_compute_wires_aux start_wire_values wires_1 inputs in
    wire_values_1 ++ circuit_compute_wires_aux (start_wire_values ++ wire_values_1) wires_2 inputs.
Proof.
  intros start_wire_values wires_1 wires_2 inputs. simpl. unfold circuit_compute_wires_aux.
  rewrite List.fold_left_app. rewrite list_fold_left_app_shift. f_equal. apply list_fold_left_ext.
  intros wire_values b. destruct b as [ | j | j k]; do 2 f_equal. f_equal.
  - f_equal. apply List.app_assoc.
  - f_equal. apply List.app_assoc.
Qed.

Definition circuit_set_outputs c outputs (H : list_forall (fun i => i < length (circuit_wires c)) outputs) := {|
  circuit_input_count := circuit_input_count c;
  circuit_wires := circuit_wires c;
  circuit_outputs := outputs;
  circuit_wires_wf := circuit_wires_wf c;
  circuit_outputs_wf := H;
|}.

Register circuit_set_outputs as vcpu.circuit.set_outputs.

#[program] Definition circuit_empty input_count := {|
  circuit_input_count := input_count;
  circuit_wires := list_init (fun i => binding_Input i) input_count;
  circuit_outputs := [];
|}.
Next Obligation.
  intros input_count. rewrite list_forall_i_list_init. auto.
Qed.
Next Obligation.
  simpl. auto.
Qed.

Register circuit_empty as vcpu.circuit.empty.

Lemma circuit_empty_spec_wires :
  forall input_count,
  forall inputs, length inputs = input_count ->
  circuit_compute_wires (circuit_empty input_count) inputs = inputs.
Proof.
  intros input_count inputs H. unfold circuit_compute_wires, circuit_compute_wires_aux, circuit_empty. simpl.
  rewrite list_fold_left_list_init. rewrite <- H; clear input_count H.
  cut (forall l,
    List.fold_left (fun y z => y ++ [List.nth z inputs false]) (List.seq 0 (length inputs)) l = l ++ inputs).
  - intros H. apply H.
  - induction inputs as [ | x inputs' IH]; intros l.
    + simpl. apply List.app_nil_end.
    + simpl. rewrite (list_fold_left_list_seq_shift _ 0 1). rewrite IH. rewrite List.app_assoc_reverse. auto.
Qed.

Lemma circuit_empty_spec :
  forall input_count,
  forall inputs, length inputs = input_count ->
  circuit_compute (circuit_empty input_count) inputs = [].
Proof.
  intros input_count inputs H. unfold circuit_compute, circuit_empty. auto.
Qed.

#[program] Definition circuit_zero := {|
  circuit_input_count := 0;
  circuit_wires := [binding_Zero];
  circuit_outputs := [0];
|}.
Next Obligation.
  unfold list_forall_i. simpl. lia.
Qed.
Next Obligation.
  simpl. lia.
Qed.

Register circuit_zero as vcpu.circuit.zero.

Lemma circuit_zero_spec_wires :
  circuit_compute_wires circuit_zero [] = [false].
Proof.
  auto.
Qed.

Lemma circuit_zero_spec :
  circuit_compute circuit_zero [] = [false].
Proof.
  auto.
Qed.

#[program] Definition circuit_one := {|
  circuit_input_count := 0;
  circuit_wires := [binding_Zero; binding_Nand 0 0];
  circuit_outputs := [1];
|}.
Next Obligation.
  unfold list_forall_i. simpl. lia.
Qed.
Next Obligation.
  simpl. lia.
Qed.

Register circuit_one as vcpu.circuit.one.

Lemma circuit_one_spec_wires :
  circuit_compute_wires circuit_one [] = [false; true].
Proof.
  auto.
Qed.

Lemma circuit_one_spec :
  circuit_compute circuit_one [] = [true].
Proof.
  auto.
Qed.

#[program] Definition circuit_nand := {|
  circuit_input_count := 2;
  circuit_wires := [binding_Input 0; binding_Input 1; binding_Nand 0 1];
  circuit_outputs := [2];
|}.
Next Obligation.
  unfold list_forall_i. simpl. lia.
Qed.
Next Obligation.
  simpl. lia.
Qed.

Lemma circuit_nand_spec_wires :
  forall i j,
  circuit_compute_wires circuit_nand [i; j] = [i; j; nandb i j].
Proof.
  auto.
Qed.

Lemma circuit_nand_spec :
  forall i j,
  circuit_compute circuit_nand [i; j] = [nandb i j].
Proof.
  auto.
Qed.

Unset Program Cases.

#[program] Definition circuit_add c_parent c_child input_wires
  (H1 : length input_wires = circuit_input_count c_child)
  (H2 : list_forall (fun i => i < length (circuit_wires c_parent)) input_wires) := {|
  circuit_input_count := circuit_input_count c_parent;
  circuit_wires :=
    circuit_wires c_parent ++
    List.map (fun i => binding_Nand i i) input_wires ++
    List.map (fun b =>
      match b with
      | binding_Zero => binding_Zero
      | binding_Input i =>
        binding_Nand (length (circuit_wires c_parent) + i) (length (circuit_wires c_parent) + i)
      | binding_Nand i j =>
        binding_Nand
          (length (circuit_wires c_parent) + circuit_input_count c_child + i)
          (length (circuit_wires c_parent) + circuit_input_count c_child + j)
      end
    ) (circuit_wires c_child);
  circuit_outputs := circuit_outputs c_parent;
|}.
Next Obligation.
  intros c_parent c_child input_wires H1 H2. rewrite list_forall_i_app; split.
  - apply (circuit_wires_wf c_parent).
  - rewrite list_forall_i_aux_app; split.
    + rewrite list_forall_i_aux_map. rewrite list_forall_i_aux_equiv.
      rewrite list_forall_list_forall_i in H2. apply (list_forall_i_incr _ _ _ H2). lia.
    + rewrite list_forall_i_aux_map. rewrite List.map_length.
      cut (
        list_forall_i_aux (fun i b =>
          match b with
          | binding_Zero => True
          | binding_Input j =>
            length (circuit_wires c_parent) + j < i /\ length (circuit_wires c_parent) + j < i
          | binding_Nand j k =>
            length (circuit_wires c_parent) + circuit_input_count c_child + j < i /\
            length (circuit_wires c_parent) + circuit_input_count c_child + k < i
          end
        ) (length (circuit_wires c_parent) + length input_wires) (circuit_wires c_child)
      ).
      * intros H. apply (list_forall_i_aux_incr _ _ _ _ H). intros i b. destruct b; auto.
      * rewrite list_forall_i_aux_equiv. apply (list_forall_i_incr _ _ _ (circuit_wires_wf c_child)).
        intros i b. destruct b; lia.
Qed.
Next Obligation.
  intros c_parent c_child input_wires H1 H2. apply (list_forall_incr _ _ _ (circuit_outputs_wf c_parent)).
  rewrite List.app_length. lia.
Qed.

Set Program Cases.

Register circuit_add as vcpu.circuit.add.

Lemma circuit_add_spec_wires :
  forall c_parent c_child input_wires
  (H1 : length input_wires = circuit_input_count c_child)
  (H2 : list_forall (fun i => i < length (circuit_wires c_parent)) input_wires),
  forall inputs, length inputs = circuit_input_count c_parent ->
  let c_parent_wire_values := circuit_compute_wires c_parent inputs in
  let c_child_inputs := list_select c_parent_wire_values input_wires false in
  circuit_compute_wires (circuit_add c_parent c_child input_wires H1 H2) inputs =
    c_parent_wire_values ++
    List.map negb c_child_inputs ++
    circuit_compute_wires c_child c_child_inputs.
Proof.
  intros c_parent c_child input_wires H1 H2. intros inputs H3. intros c_parent_wire_values c_child_inputs.
  unfold circuit_compute_wires, circuit_add. simpl. rewrite circuit_compute_wires_aux_app. simpl.
  replace (circuit_compute_wires_aux [] (circuit_wires c_parent) inputs) with c_parent_wire_values by auto.
  rewrite circuit_compute_wires_aux_app. simpl. f_equal.
  assert (HA : circuit_compute_wires_aux c_parent_wire_values
    (List.map (fun i => binding_Nand i i) input_wires) inputs = List.map negb c_child_inputs). {
    subst c_child_inputs. unfold circuit_compute_wires_aux, list_select. rewrite list_fold_left_list_map.
    rewrite List.map_map. rewrite (list_fold_left_ext_precise _ (fun wire_values i =>
      wire_values ++ [negb (List.nth i c_parent_wire_values false)])).
    - apply (eq_sym (list_map_list_fold_left _ _)).
    - intros y. apply (list_forall_incr _ _ _ H2). intros z H. rewrite nandb_negb. do 3 f_equal.
      apply List.app_nth1. subst c_parent_wire_values. rewrite length_circuit_compute_wires. auto.
  }
  f_equal.
  - auto.
  - rewrite HA; clear HA. unfold circuit_compute_wires_aux at 1. rewrite list_fold_left_list_map.
    rewrite (list_fold_left_ext _
      (fun wire_values b =>
       wire_values ++
       [match b with
        | binding_Zero => false
        | binding_Input i =>
          nandb
            (List.nth (length (circuit_wires c_parent) + i)
              ((c_parent_wire_values ++ List.map negb c_child_inputs) ++ wire_values) false)
            (List.nth (length (circuit_wires c_parent) + i)
              ((c_parent_wire_values ++ List.map negb c_child_inputs) ++ wire_values) false)
        | binding_Nand i j =>
          nandb
            (List.nth (length (circuit_wires c_parent) + circuit_input_count c_child + i)
              ((c_parent_wire_values ++ List.map negb c_child_inputs) ++ wire_values) false)
            (List.nth (length (circuit_wires c_parent) + circuit_input_count c_child + j)
              ((c_parent_wire_values ++ List.map negb c_child_inputs) ++ wire_values) false)
        end])
    ).
    + rewrite (list_fold_left_ext_precise _
      (fun wire_values b =>
         wire_values ++
         [match b with
          | binding_Zero => false
          | binding_Input i => negb (List.nth i (List.map negb c_child_inputs) false)
          | binding_Nand i j => nandb (List.nth i wire_values false) (List.nth j wire_values false)
          end])
      ).
      * unfold circuit_compute_wires_aux. apply list_fold_left_ext_precise.
        intros wire_values. rewrite list_forall_list_forall_i.
        apply (list_forall_i_incr _ _ _ (circuit_wires_wf c_child)). intros i b H.
        destruct b as [ | j | j k]; simpl; do 2 f_equal. rewrite <- Bool.negb_involutive. f_equal.
        rewrite <- (List.map_nth negb). apply List.nth_indep.
        rewrite List.map_length. subst c_child_inputs. rewrite length_list_select. lia.
      * intros wire_values. rewrite list_forall_list_forall_i.
        apply (list_forall_i_incr _ _ _ (circuit_wires_wf c_child)). intros i b H.
        destruct b as [ | j | j k]; simpl; do 2 f_equal.
        -- rewrite nandb_negb. f_equal. rewrite List.app_nth1.
           ++ rewrite List.app_nth2.
              ** f_equal. subst c_parent_wire_values. rewrite length_circuit_compute_wires. lia.
              ** subst c_parent_wire_values. rewrite length_circuit_compute_wires. lia.
           ++ rewrite List.app_length. subst c_parent_wire_values. rewrite length_circuit_compute_wires.
              rewrite List.map_length. subst c_child_inputs. rewrite length_list_select. lia.
        -- f_equal.
           ++ rewrite List.app_nth2.
              ** rewrite List.app_length. f_equal.
                 subst c_parent_wire_values. rewrite length_circuit_compute_wires.
                 rewrite List.map_length. subst c_child_inputs. rewrite length_list_select.
                 lia.
              ** rewrite List.app_length.
                 subst c_parent_wire_values. rewrite length_circuit_compute_wires.
                 rewrite List.map_length. subst c_child_inputs. rewrite length_list_select.
                 lia.
            ++ rewrite List.app_nth2.
              ** rewrite List.app_length. f_equal.
                 subst c_parent_wire_values. rewrite length_circuit_compute_wires.
                 rewrite List.map_length. subst c_child_inputs. rewrite length_list_select.
                 lia.
              ** rewrite List.app_length.
                 subst c_parent_wire_values. rewrite length_circuit_compute_wires.
                 rewrite List.map_length. subst c_child_inputs. rewrite length_list_select.
                 lia.
    + intros wire_values b. destruct b; auto.
Qed.

Definition circuit_add_parent_wires c_parent c_child input_wires
  (H1 : length input_wires = circuit_input_count c_child)
  (H2 : list_forall (fun i => i < length (circuit_wires c_parent)) input_wires) :=
  List.seq 0 (length (circuit_wires c_parent)).

Definition circuit_add_child_wires c_parent c_child input_wires
  (H1 : length input_wires = circuit_input_count c_child)
  (H2 : list_forall (fun i => i < length (circuit_wires c_parent)) input_wires) :=
  List.seq (length (circuit_wires c_parent) + circuit_input_count c_child) (length (circuit_wires c_child)).

Definition circuit_add_child_output_wires c_parent c_child input_wires
  (H1 : length input_wires = circuit_input_count c_child)
  (H2 : list_forall (fun i => i < length (circuit_wires c_parent)) input_wires) :=
  list_select (circuit_add_child_wires c_parent c_child input_wires H1 H2) (circuit_outputs c_child) 0.

Register circuit_add_child_output_wires as vcpu.circuit.add_child_output_wires.

Lemma circuit_add_spec_parent_wires :
  forall c_parent c_child input_wires
  (H1 : length input_wires = circuit_input_count c_child)
  (H2 : list_forall (fun i => i < length (circuit_wires c_parent)) input_wires),
  forall inputs, length inputs = circuit_input_count c_parent ->
  list_select (circuit_compute_wires (circuit_add c_parent c_child input_wires H1 H2) inputs)
    (circuit_add_parent_wires c_parent c_child input_wires H1 H2) false =
    circuit_compute_wires c_parent inputs.
Proof.
  intros c_parent c_child input_wires H1 H2. intros inputs H3. rewrite (circuit_add_spec_wires _ _ _ _ _ _ H3).
  unfold circuit_add_parent_wires.
  replace (List.seq 0 (length (circuit_wires c_parent)))
    with (List.seq 0 (length (circuit_compute_wires c_parent inputs))).
  - apply list_select_app_1_seq.
  - f_equal. apply length_circuit_compute_wires.
Qed.

Lemma circuit_add_spec_child_wires :
  forall c_parent c_child input_wires
  (H1 : length input_wires = circuit_input_count c_child)
  (H2 : list_forall (fun i => i < length (circuit_wires c_parent)) input_wires),
  forall inputs, length inputs = circuit_input_count c_parent ->
  list_select (circuit_compute_wires (circuit_add c_parent c_child input_wires H1 H2) inputs)
    (circuit_add_child_wires c_parent c_child input_wires H1 H2) false =
    circuit_compute_wires c_child (list_select (circuit_compute_wires c_parent inputs) input_wires false).
Proof.
  intros c_parent c_child input_wires H1 H2. intros inputs H3. rewrite (circuit_add_spec_wires _ _ _ _ _ _ H3).
  unfold circuit_add_child_wires. rewrite List.app_assoc.
  replace (List.seq (length (circuit_wires c_parent) + circuit_input_count c_child)
      (length (circuit_wires c_child)))
    with (List.seq (length (circuit_compute_wires c_parent inputs ++
      List.map negb (list_select (circuit_compute_wires c_parent inputs) input_wires false)))
      (length (circuit_compute_wires c_child (list_select (circuit_compute_wires c_parent inputs)
      input_wires false)))).
  - apply list_select_app_2_seq.
  - f_equal.
    + rewrite List.app_length. f_equal.
      * apply length_circuit_compute_wires.
      * rewrite List.map_length. rewrite length_list_select. auto.
    + apply length_circuit_compute_wires.
Qed.

Lemma circuit_add_spec_child_output_wires :
  forall c_parent c_child input_wires
  (H1 : length input_wires = circuit_input_count c_child)
  (H2 : list_forall (fun i => i < length (circuit_wires c_parent)) input_wires),
  forall inputs, length inputs = circuit_input_count c_parent ->
  list_select (circuit_compute_wires (circuit_add c_parent c_child input_wires H1 H2) inputs)
    (circuit_add_child_output_wires c_parent c_child input_wires H1 H2) false =
    circuit_compute c_child (list_select (circuit_compute_wires c_parent inputs) input_wires false).
Proof.
  intros c_parent c_child input_wires H1 H2. intros inputs H3.
  unfold circuit_compute. rewrite <- (circuit_add_spec_child_wires _ _ _ H1 H2 _ H3).
  unfold circuit_add_child_output_wires. apply list_select_com.
  apply (list_forall_incr _ _ _ (circuit_outputs_wf c_child)). intros i H4.
  unfold circuit_add_child_wires. rewrite List.seq_length. auto.
Qed.

#[program] Definition circuit_add_fast c_parent c_child input_wires
  (H1 : length input_wires = circuit_input_count c_child)
  (H2 : list_forall (fun i => i < length (circuit_wires c_parent)) input_wires) := {|
  circuit_input_count := circuit_input_count c_parent;
  circuit_wires :=
    circuit_wires c_parent ++
    List.map (fun b =>
      match b with
      | binding_Zero => binding_Zero
      | binding_Input i =>
        List.nth (List.nth i input_wires 0) (circuit_wires c_parent) binding_Zero
      | binding_Nand i j =>
        binding_Nand (length (circuit_wires c_parent) + i) (length (circuit_wires c_parent) + j)
      end
    ) (circuit_wires c_child);
  circuit_outputs := circuit_outputs c_parent;
|}.
Next Obligation.
  intros c_parent c_child input_wires H1 H2. rewrite list_forall_i_app; split.
  - apply (circuit_wires_wf c_parent).
  - rewrite list_forall_i_aux_map. rewrite list_forall_i_aux_equiv.
Admitted.
Next Obligation.
Admitted.

Register circuit_add_fast as vcpu.circuit.add_fast.

#[program] Definition circuit_switch data_size := {|
  circuit_input_count := 1 + 2 * data_size;
  circuit_wires :=
    list_init (fun i => binding_Input i) (1 + 2 * data_size) ++
    binding_Nand 0 0 ::
    list_init (fun i => binding_Nand (1 + 2 * data_size) (1 + i)) data_size ++
    list_init (fun i => binding_Nand 0 (1 + data_size + i)) data_size ++
    list_init (fun i => binding_Nand (2 + 2 * data_size + i) (2 + 3 * data_size + i)) data_size;
  circuit_outputs := List.seq (2 + 4 * data_size) data_size;
|}.
Next Obligation.
  intros data_size. rewrite list_forall_i_app; split.
  - rewrite list_forall_i_list_init. auto.
  - simpl; split.
    + lia.
    + rewrite list_forall_i_aux_app; split.
      * rewrite list_forall_i_aux_equiv. rewrite list_forall_i_list_init.
        intros i H. rewrite length_list_init_aux. lia.
      * rewrite list_forall_i_aux_app; split.
        -- rewrite list_forall_i_aux_equiv. rewrite list_forall_i_list_init.
           intros i H. rewrite length_list_init_aux. lia.
        -- rewrite list_forall_i_aux_equiv. rewrite list_forall_i_list_init.
           intros i H. rewrite length_list_init_aux, ? length_list_init. lia.
Qed.
Next Obligation.
  intros data_size. rewrite list_forall_list_seq. rewrite List.app_length. simpl.
  rewrite ? List.app_length. rewrite length_list_init_aux, ? length_list_init. lia.
Qed.

Register circuit_switch as vcpu.circuit.switch.

Lemma circuit_switch_spec_wires :
  forall data_size,
  forall inputs, length inputs = 1 + 2 * data_size ->
  circuit_compute_wires (circuit_switch data_size) inputs =
    inputs ++
    negb (List.nth 0 inputs false) ::
    List.map (fun b => nandb (negb (List.nth 0 inputs false)) b)
      (list_select inputs (List.seq 1 data_size) false) ++
    List.map (fun b => nandb (List.nth 0 inputs false) b)
      (list_select inputs (List.seq (1 + data_size) data_size) false) ++
    if List.nth 0 inputs false
    then list_select inputs (List.seq (1 + data_size) data_size) false
    else list_select inputs (List.seq 1 data_size) false.
Proof.
  intros data_size. intros inputs H1. unfold circuit_compute_wires, circuit_switch. cbv [circuit_wires].
  rewrite circuit_compute_wires_aux_app. simpl. f_equal.
  - apply (circuit_empty_spec_wires (1 + 2 * data_size) inputs H1).
  - specialize (circuit_empty_spec_wires (1 + 2 * data_size) inputs H1) as H2.
    unfold circuit_compute_wires, circuit_empty in H2. simpl in H2. rewrite H2. clear H2.
    rewrite <- list_cons_app. rewrite circuit_compute_wires_aux_app.
    assert (A1 : circuit_compute_wires_aux inputs [binding_Nand 0 0] inputs =
        [negb (List.nth 0 inputs false)]). {
      cbn. rewrite nandb_negb. rewrite List.app_nil_r. auto.
    }
    rewrite A1. simpl. f_equal. destruct inputs as [ | b inputs'].
    + simpl in H1. congruence.
    + simpl in H1. injection H1 as H1. simpl. rewrite circuit_compute_wires_aux_app. simpl.
      assert (A2 : circuit_compute_wires_aux (b :: inputs' ++ [negb b])
          (list_init (fun i => binding_Nand (S (data_size + (data_size + 0))) (S i)) data_size) 
          (b :: inputs') =
          List.map (fun b' => nandb (negb b) b') (list_select (b :: inputs') (List.seq 1 data_size) false)). {
        unfold circuit_compute_wires_aux. rewrite list_fold_left_list_init.
        rewrite list_fold_left_ext_precise with (f2 := fun wire_values i =>
          wire_values ++ [nandb (negb b) (List.nth i inputs' false)]).
        - rewrite <- list_fold_left_list_init. rewrite list_init_list_map_list_seq.
          rewrite <- (List.map_map _ (fun x => [x])). rewrite list_fold_left_app_list_map_singleton.
          unfold list_select. rewrite List.map_map. rewrite <- List.seq_shift. rewrite List.map_map.
          simpl. auto.
        - intros wire_values. rewrite list_forall_list_seq. intros i H2. do 3 f_equal.
           + rewrite List.app_nth1.
              * simpl. rewrite List.app_nth2.
                -- rewrite H1. rewrite PeanoNat.Nat.sub_diag. auto.
                -- lia.
              * simpl. rewrite List.app_length. simpl. lia.
           + simpl. rewrite <- List.app_assoc. apply List.app_nth1. lia.
      }
      rewrite ? A2. f_equal. rewrite ? List.app_comm_cons. rewrite circuit_compute_wires_aux_app. simpl.
      assert (A3 : circuit_compute_wires_aux
          (b :: (inputs' ++ [negb b]) ++
             List.map (fun b' => nandb (negb b) b') (list_select (b :: inputs') (List.seq 1 data_size) false))
          (list_init (fun i : nat => binding_Nand 0 (S (data_size + i))) data_size) (b :: inputs') =
          List.map (fun b' => nandb b b') (list_select (b :: inputs')
            (List.seq (S data_size) data_size) false)). {
        admit.
      }
      rewrite ? A3. f_equal. destruct b.
      * unfold nandb. simpl. unfold circuit_compute_wires_aux. rewrite list_fold_left_list_init.
        simpl. admit.
      * admit.
Admitted.

Lemma circuit_switch_spec :
  forall data_size,
  forall inputs, length inputs = 1 + 2 * data_size ->
  circuit_compute (circuit_switch data_size) inputs =
    if List.nth 0 inputs false
    then list_select inputs (List.seq (1 + data_size) data_size) false
    else list_select inputs (List.seq 1 data_size) false.
Proof.
  intros data_size. intros inputs H1. unfold circuit_compute. rewrite (circuit_switch_spec_wires _ _ H1).
  rewrite <- list_cons_app. rewrite ? List.app_assoc. simpl.
  assert (A1 : List.length (((inputs ++ [negb (List.nth 0 inputs false)]) ++
      List.map (fun b : bool => nandb (negb (List.nth 0 inputs false)) b)
        (list_select inputs (List.seq 1 data_size) false)) ++
      List.map (fun b : bool => nandb (List.nth 0 inputs false) b)
        (list_select inputs (List.seq (S data_size) data_size) false)) =
        S (S (data_size + (data_size + (data_size + (data_size + 0)))))). {
    rewrite ? List.app_length. rewrite H1. rewrite ? List.map_length. rewrite ? length_list_select.
    rewrite ? List.seq_length. simpl. lia.
  }
  assert (A2 : List.length (if List.nth 0 inputs false
      then list_select inputs (List.seq (S data_size) data_size) false
      else list_select inputs (List.seq 1 data_size) false) =
      data_size). {
    destruct (List.nth 0 inputs false); rewrite length_list_select; apply List.seq_length.
  }
  rewrite <- A2 at 11. rewrite <- A1. apply list_select_app_2_seq.
Qed.
*)
