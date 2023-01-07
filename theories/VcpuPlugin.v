Inductive vector {A : Type} : nat -> Type :=
  | vector_Nil : @vector A 0
  | vector_Cons {n} : A -> @vector A n -> @vector A (S n).

Arguments vector : clear implicits.

Notation "[| |]" := vector_Nil (format "[| |]").
Notation "x :||: v" := (vector_Cons x v) (at level 60, right associativity).
Notation "[| x |]" := (vector_Cons x vector_Nil).
Notation "[| x ; y ; .. ; z |]" := (vector_Cons x (vector_Cons y .. (vector_Cons z vector_Nil) ..)).

Register vector as vcpu.vector.type.

Definition vector_tail {A n} (v : vector A (S n)) : vector A n :=
  let '(_ :||: v') in (vector _ (S n)) := v return _ in
  v'.

Notation bitvec := (vector bool).

Inductive binding :=
  | binding_Zero
  | binding_Input (i : nat)
  | binding_Nand (i j : nat).

Require Coq.Lists.List.
Import List.ListNotations.
Open Scope list_scope.

Fixpoint list_forall {A} f (l : list A) :=
  match l with
  | [] => True
  | x :: l' => f x /\ list_forall f l'
  end.

Lemma list_forall_ext :
  forall {A} f1 f2 (l : list A),
  (forall x, f1 x <-> f2 x) ->
  list_forall f1 l <-> list_forall f2 l.
Proof.
  intros A f1 f2 l H. induction l as [ | x l' IH].
  - intuition auto.
  - specialize (H x). simpl. intuition auto.
Qed.

Lemma list_forall_incr :
  forall {A} (f1 f2 : _ -> Prop) (l : list A),
  list_forall f1 l ->
  (forall x, f1 x -> f2 x) ->
  list_forall f2 l.
Proof.
  intros A f1 f2 l H1 H2. induction l as [ | x l' IH].
  - intuition auto.
  - specialize (H2 x). simpl. simpl in H1. intuition auto.
Qed.

Lemma list_forall_coarse :
  forall {A} (f : _ -> Prop) (l : list A),
  (forall x, f x) ->
  list_forall f l.
Proof.
  intros A f l H. induction l as [ | x l' IH].
  - simpl. auto.
  - specialize (H x). simpl. auto.
Qed.

Fixpoint list_forall_i_aux {A} f i (l : list A) :=
  match l with
  | [] => True
  | x :: l' => f i x /\ list_forall_i_aux f (S i) l'
  end.

Definition list_forall_i {A} f (l : list A) := list_forall_i_aux f 0 l.

Lemma list_forall_i_aux_ext :
  forall {A} f1 f2 s (l : list A),
  (forall i x, f1 i x <-> f2 i x) ->
  list_forall_i_aux f1 s l <-> list_forall_i_aux f2 s l.
Proof.
  intros A f1 f2 s l H. generalize dependent s. induction l as [ | x l' IH]; intros s.
  - simpl. intuition auto.
  - specialize (IH (S s)). simpl. rewrite H. intuition auto.
Qed.

Lemma list_forall_i_ext :
  forall {A} f1 f2 (l : list A),
  (forall i x, f1 i x <-> f2 i x) ->
  list_forall_i f1 l <-> list_forall_i f2 l.
Proof.
  unfold list_forall_i. intros A f1 f2 l. apply (list_forall_i_aux_ext f1 f2 0 l).
Qed.

Lemma list_forall_i_aux_incr :
  forall {A} (f1 f2 : _ -> _ -> Prop) s (l : list A),
  list_forall_i_aux f1 s l ->
  (forall i x, f1 i x -> f2 i x) ->
  list_forall_i_aux f2 s l.
Proof.
  intros A f1 f2 s l H1 H2. generalize dependent s. induction l as [ | x l' IH]; intros s.
  - simpl. intuition auto.
  - specialize (IH (S s)). simpl. intuition auto.
Qed.

Lemma list_forall_i_incr :
  forall {A} (f1 f2 : _ -> _ -> Prop) (l : list A),
  list_forall_i f1 l ->
  (forall i x, f1 i x -> f2 i x) ->
  list_forall_i f2 l.
Proof.
  unfold list_forall_i. intros A f1 f2 l H1 H2. apply (list_forall_i_aux_incr f1 f2 0 l H1 H2).
Qed.

Lemma list_forall_i_aux_shift :
  forall {A} f s t (l : list A),
  list_forall_i_aux f (t + s) l <-> list_forall_i_aux (fun i x => f (t + i) x) s l.
Proof.
  intros A f s е l. generalize dependent s. induction l as [ | x l' IH]; intros s.
  - simpl. intuition auto.
  - specialize (IH (S s)). simpl. rewrite <- PeanoNat.Nat.add_succ_comm in IH. intuition auto.
Qed.

Lemma list_forall_i_aux_equiv :
  forall {A} f s (l : list A),
  list_forall_i_aux f s l <-> list_forall_i (fun i x => f (s + i) x) l.
Proof.
  intros A f s l. unfold list_forall_i. generalize dependent s. induction l as [ | x l' IH]; intros s.
  - simpl. intuition auto.
  - specialize (IH (S s)). simpl. rewrite (list_forall_i_aux_shift _ 0 1).
    simpl. rewrite PeanoNat.Nat.add_0_r. rewrite IH. apply and_iff_compat_l.
    apply list_forall_i_ext. intros i y. rewrite PeanoNat.Nat.add_succ_comm. intuition auto.
Qed.

Lemma list_forall_i_aux_app :
  forall {A} f s (l1 l2 : list A),
  list_forall_i_aux f s (l1 ++ l2) <-> list_forall_i_aux f s l1 /\ list_forall_i_aux f (s + length l1) l2.
Proof.
  intros A f s l1 l2. generalize dependent s. induction l1 as [ | x l1' IH]; intros s.
  - rewrite PeanoNat.Nat.add_comm. simpl. intuition auto.
  - specialize (IH (S s)). simpl. rewrite <- PeanoNat.Nat.add_succ_comm. intuition auto.
Qed.

Lemma list_forall_list_forall_i :
  forall {A} f (l : list A),
  list_forall f l <-> list_forall_i (fun _ => f) l.
Proof.
  intros A f l. unfold list_forall_i. induction l as [ | x l' IH].
  - intuition auto.
  - simpl. rewrite (list_forall_i_aux_shift _ 0 1). intuition auto.
Qed.

Lemma list_forall_i_app :
  forall {A} f (l1 l2 : list A),
  list_forall_i f (l1 ++ l2) <-> list_forall_i f l1 /\ list_forall_i_aux f (length l1) l2.
Proof.
  unfold list_forall_i. intros A f l1 l2. apply (list_forall_i_aux_app f 0 l1 l2).
Qed.

Lemma list_forall_i_aux_map :
  forall {A B} f s (g : A -> B) (l : list A),
  list_forall_i_aux f s (List.map g l) <-> list_forall_i_aux (fun i x => f i (g x)) s l.
Proof.
  intros A B f s g l. generalize dependent s. induction l as [ | x l' IH]; intros s.
  - simpl. intuition auto.
  - specialize (IH (S s)). simpl. intuition auto.
Qed.

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

Open Scope bool_scope.

Definition nandb b1 b2 := negb (b1 && b2).

Require Import Btauto.

Theorem nandb_negb : forall b, nandb b b = negb b.
Proof.
  intros b. unfold nandb. btauto.
Qed.

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

Lemma list_fold_left_ext_precise :
  forall {A B} f1 f2 (l : list B) (x : A),
  (forall y, list_forall (fun z => f1 y z = f2 y z) l) ->
  List.fold_left f1 l x = List.fold_left f2 l x.
Proof.
  intros A B f1 f2 l x H. generalize dependent x. induction l as [ | z l' IH]; intros x.
  - auto.
  - simpl in H. simpl. rewrite (proj1 (H x)). apply IH. intros y. specialize (H y). intuition auto.
Qed.

Lemma list_fold_left_ext :
  forall {A B} f1 f2 (l : list B) (x : A),
  (forall y z, f1 y z = f2 y z) ->
  List.fold_left f1 l x = List.fold_left f2 l x.
Proof.
  intros A B f1 f2 l x H. apply list_fold_left_ext_precise. intros y. apply list_forall_coarse. auto.
Qed.

Lemma list_fold_left_morph :
  forall {A B C} f (g : A -> C) (l : list B) (x : A),
  g (List.fold_left (fun y z => f (g y) z) l x) = List.fold_left (fun y z => g (f y z)) l (g x).
Proof.
  intros A B C f g l. induction l as [ | y l' IH]; intros x.
  - auto.
  - simpl. apply IH.
Qed.

Lemma list_fold_left_app_shift :
  forall {A B} f (l1 : list B) (l2 : list A),
  List.fold_left (fun l y => l ++ [f l y]) l1 l2 =
  l2 ++ List.fold_left (fun l y => l ++ [f (l2 ++ l) y]) l1 [].
Proof.
  intros A B f l1. induction l1 as [ | x l1' IH]; intros l2.
  - simpl. apply List.app_nil_end.
  - simpl. rewrite List.app_nil_r. specialize (IH (l2 ++ [f l2 x])). rewrite IH; clear IH.
    rewrite <- List.app_assoc. f_equal. simpl.
    rewrite (list_fold_left_ext _ (fun y z => List.tl ((f l2 x :: y) ++ [f (l2 ++ f l2 x :: y) z]))).
    + rewrite (list_fold_left_morph (fun l3 z => List.tl (l3 ++ [f (l2 ++ l3) z])) (cons (f l2 x))).
      cut (forall e,
        List.fold_left (fun l3 z => f l2 x :: List.tl (l3 ++ [f (l2 ++ l3) z])) l1' (f l2 x :: e) =
        List.fold_left (fun l3 z => l3 ++ [f (l2 ++ l3) z]) l1' (f l2 x :: e)).
      * intros H. apply (H []).
      * induction l1' as [ | z l1'' IH]; intros e.
        -- auto.
        -- simpl. apply IH.
    + intros l3 z. simpl. rewrite <- List.app_assoc. auto.
Qed.

Lemma list_map_list_fold_left :
  forall {A B} (f : A -> B) l,
  List.map f l = List.fold_left (fun y z => y ++ [f z]) l [].
Proof.
  intros A B f l. cut (forall s, s ++ List.map f l = List.fold_left (fun y z => y ++ [f z]) l s).
  - intros H. apply (H []).
  - induction l as [ | x l' IH]; intros s.
    + simpl. apply List.app_nil_r.
    + simpl. rewrite <- IH. rewrite <- List.app_assoc. auto.
Qed.

Theorem circuit_compute_wires_aux_app :
  forall start_wire_values wires_1 wires_2 inputs,
  circuit_compute_wires_aux start_wire_values (wires_1 ++ wires_2) inputs =
    let wire_values_1 := circuit_compute_wires_aux start_wire_values wires_1 inputs in
    wire_values_1 ++ circuit_compute_wires_aux (start_wire_values ++ wire_values_1) wires_2 inputs.
Proof.
  intros start_wire_values wires_1 wires_2 inputs. simpl.
unfold circuit_compute_wires_aux.
  rewrite List.fold_left_app. rewrite list_fold_left_app_shift. f_equal. apply list_fold_left_ext.
  intros wire_values b. destruct b as [ | j | j k]; do 2 f_equal. f_equal.
  - f_equal. apply List.app_assoc.
  - f_equal. apply List.app_assoc.
Qed.

Obligation Tactic := idtac.

Require Import Lia.

Fixpoint list_init_aux {A} f s n : list A :=
  match n with
  | 0 => []
  | S n' => f s :: list_init_aux f (S s) n'
  end.

Definition list_init {A} f n : list A := list_init_aux f 0 n.

Lemma list_fold_left_list_init_aux :
  forall {A B} f (g : _ -> B) s n (x : A),
  List.fold_left f (list_init_aux g s n) x = List.fold_left (fun y z => f y (g z)) (List.seq s n) x.
Proof.
  intros A B f g s n x. generalize dependent x. generalize dependent s. induction n as [ | n' IH]; intros s x.
  - auto.
  - apply IH.
Qed.

Lemma list_fold_left_list_init :
  forall {A B} f (g : _ -> B) n (x : A),
  List.fold_left f (list_init g n) x = List.fold_left (fun y z => f y (g z)) (List.seq 0 n) x.
Proof.
  intros A B f g n x. apply list_fold_left_list_init_aux.
Qed.

Lemma list_fold_left_list_seq_shift :
  forall {A} f s t n (x : A),
  List.fold_left f (List.seq (s + t) n) x = List.fold_left (fun y z => f y (t + z)) (List.seq s n) x.
Proof.
  intros A f s t n. generalize dependent s. induction n as [ | n' IH]; intros s x.
  - auto.
  - specialize (IH (S s) (f x (s + t))). simpl. rewrite (PeanoNat.Nat.add_comm t s). simpl in IH. apply IH.
Qed.

Lemma list_fold_left_list_map :
  forall {A B C} f (g : B -> C) l (x : A),
  List.fold_left f (List.map g l) x = List.fold_left (fun y z => f y (g z)) l x.
Proof.
  intros A B C f g l. induction l; intros x.
  - auto.
  - simpl. auto.
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

Definition list_select {A} values indices (default : A) :=
  List.map (fun i => List.nth i values default) indices.

Lemma length_list_select :
  forall {A} values indices (default : A),
  length (list_select values indices default) = length indices.
Proof.
  intros A values indices default. unfold list_select. apply List.map_length.
Qed.

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

Declare ML Module "vcpu_plugin:vcpu-plugin.plugin".
