Require Import Utils.

Require Import Lia.

Require Coq.Lists.List.
Import List.ListNotations.

Inductive binding :=
  | binding_Zero
  | binding_Input (i : nat)
  | binding_Nand (i j : nat).

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

#[program] Definition circuit_empty input_count := {|
  circuit_input_count := input_count;
  circuit_wires := list_init (fun i => binding_Input i) input_count;
  circuit_outputs := [];
|}.
Next Obligation.
  intros input_count. unfold list_forall_i, list_init.
  cut (
    forall s, list_forall_i_aux (fun i b =>
      match b with
      | binding_Zero => True
      | binding_Input j => j < s + input_count
      | binding_Nand j k => j < i /\ k < i
      end
    ) s (list_init_aux (fun i => binding_Input i) s input_count)
  ).
  - intros H. apply (H 0).
  - induction input_count as [ | input_count IH]; intros s.
    + simpl. auto.
    + simpl. split.
      * lia.
      * rewrite <- PeanoNat.Nat.add_succ_comm. apply (IH (S s)).
Qed.
Next Obligation.
  simpl. auto.
Qed.

Lemma circuit_empty_spec :
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

Lemma circuit_zero_spec :
  circuit_compute_wires circuit_zero [] = [false].
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

Lemma circuit_nand_spec :
  forall i j,
  circuit_compute_wires circuit_nand [i; j] = [i; j; nandb i j].
Proof.
  auto.
Qed.

Unset Program Cases.

#[program] Definition circuit_add c_parent c_child input_wires
  (H1 : length input_wires = circuit_input_count c_child)
  (H2 : list_forall (fun i => i < length (circuit_wires c_parent)) input_wires) := {|
  circuit_input_count := circuit_input_count c_parent;
  circuit_wires :=
    circuit_wires c_parent ++ List.map (fun i => binding_Nand i i) input_wires ++ List.map (fun b =>
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

Lemma circuit_add_spec :
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
