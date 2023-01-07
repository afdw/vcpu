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
      | binding_Input j => j < circuit_input_count
      | binding_Nand j k => j < i /\ k < i
      end
    ) circuit_wires;
  circuit_outputs_wf :
    list_forall (fun i => i < length circuit_wires) circuit_outputs;
}.

Obligation Tactic := idtac.

Require Import Lia.

Fixpoint list_init_aux {A} f n i : list A :=
  match n with
  | 0 => []
  | S n' => f i :: list_init_aux f n' (S i)
  end.

Definition list_init {A} f n : list A := list_init_aux f n 0.

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
      | binding_Input j => j < s + input_count
      | binding_Nand j k => j < i /\ k < i
      end
    ) s (list_init_aux (fun i => binding_Input i) input_count s)
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

#[program] Definition circuit_add c_parent c_child input_wires
  (H1 : length input_wires = circuit_input_count c_child)
  (H2 : list_forall (fun i => i < length (circuit_wires c_parent)) input_wires) := {|
  circuit_input_count := circuit_input_count c_parent;
  circuit_wires :=
    circuit_wires c_parent ++ List.map (fun i => binding_Nand i i) input_wires ++ List.map (fun b =>
      match b with
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

Declare ML Module "vcpu_plugin:vcpu-plugin.plugin".
