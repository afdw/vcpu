From Ltac2 Require Export Ltac2.
From Stdlib Require Export Unicode.Utf8.
From Stdlib Require Export Logic.Eqdep_dec.
From Stdlib Require Arith.Arith.
From Stdlib Require Export ZArith.ZArith.
From Stdlib Require Export micromega.Lia.
Export Corelib.Init.Logic.EqNotations.
From Stdlib Require Lists.List.
Export Stdlib.Lists.List.ListNotations.
From Corelib Require Export Program.Basics.
(* From Corelib Require Export Program.Utils. *)
From Stdlib Require Export Classes.EquivDec.

#[global] Obligation Tactic := ().
#[global] Unset Program Cases.
#[global] Unset Program Generalized Coercion.
#[global] Unset Implicit Arguments.

(* #[global] Set Typeclasses Iterative Deepening. *)
#[global] Set Typeclasses Depth 20.

Ltac2 Notation "lia" := ltac1:(lia).

Open Scope program_scope.
Open Scope equiv_scope.
Open Scope bool_scope.
Open Scope list_scope.
Open Scope nat_scope.

Disable Notation "_ ≤ _".
Disable Notation "_ ≥ _".
(* Disable Notation "{ ( _ , _ ) : _ | _ }". *)

Notation "x ≤ y" := (le x y) : nat_scope.
Notation "x ≥ y" := (ge x y) : nat_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) : nat_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) : nat_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) : nat_scope.

Notation "x ≤ y" := (N.le x y) : N_scope.
Notation "x ≥ y" := (N.ge x y) : N_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%N : N_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%N : N_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z)%N : N_scope.

Notation "x ≤ y" := (Z.le x y) : Z_scope.
Notation "x ≥ y" := (Z.ge x y) : Z_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%Z : Z_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%Z : Z_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z)%Z : Z_scope.

(* Notation " ! " := (False_rect _ _) : program_scope. (* copied from Corelib.Program.Utils *) *)

Notation " ` t " := (proj1_sig t) (at level 10, t at next level) : program_scope. (* copied from Corelib.Program.Utils *)

Fixpoint list_prefix {A} n (l : list A) default : list A :=
  match n with
  | 0 => []
  | S n' => List.hd default l :: list_prefix n' (List.tl l) default
  end.

Lemma list_length_list_prefix {A} :
  ∀ n (l : list A) default,
  List.length (list_prefix n l default) = n.
Proof.
  intros n l default. revert l; induction n as [| n' IH]; intros l; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Defined.

Lemma list_prefix_list_app {A} :
  ∀ (l_1 l_2 : list A) default,
  list_prefix (List.length l_1) (l_1 ++ l_2) default = l_1.
Proof.
  intros l_1 l_2 default. induction l_1 as [| x l_1' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Definition list_suffix {A} n (l : list A) default : list A :=
  List.rev (list_prefix n (List.rev l) default).

Lemma list_length_list_suffix {A} :
  ∀ n (l : list A) default,
  List.length (list_suffix n l default) = n.
Proof.
  intros n l default. unfold list_suffix. rewrite List.length_rev, list_length_list_prefix. reflexivity.
Defined.

Lemma list_suffix_list_app {A} :
  ∀ (l_1 l_2 : list A) default,
  list_suffix (List.length l_2) (l_1 ++ l_2) default = l_2.
Proof.
  intros l_1 l_2 default. unfold list_suffix. ltac1:(replace (List.length l_2) with (List.length (List.rev l_2)) by (rewrite List.length_rev; reflexivity)).
  rewrite List.rev_app_distr, list_prefix_list_app, List.rev_involutive. reflexivity.
Qed.

Definition list_sub {A} n m (l : list A) default : list A :=
  List.map (λ i, List.nth i l default) (List.seq n m).

Lemma list_length_list_sub {A} :
  ∀ n m (l : list A) default,
  List.length (list_sub n m l default) = m.
Proof.
  intros n m l default. unfold list_sub. rewrite List.length_map, List.length_seq. reflexivity.
Defined.

Lemma list_rev_list_sub {A} :
  ∀ n m (l : list A) default,
  n + m ≤ List.length l →
  List.rev (list_sub n m l default) = list_sub (List.length l - n - m) m (List.rev l) default.
Proof.
  intros n m l default H_n_m. unfold list_sub. rewrite <- List.map_rev.
  apply eq_trans with (List.map (λ i, List.nth (List.length l - S i) l default) (List.seq (List.length l - n - m) m)).
  - change (λ i, List.nth (List.length l - S i) l default) with (λ i, (λ i, List.nth i l default) ((λ i, List.length l - S i) i)). rewrite <- List.map_map.
    f_equal. revert n H_n_m; induction m as [| m' IH]; intros n H_n_m; simpl.
    + reflexivity.
    + specialize (IH n ltac2:(lia)). ltac1:(replace (S (List.length l - n - S m')) with (List.length l - n - m') by lia). rewrite <- IH.
      ltac1:(replace (List.length l - (List.length l - n - m')) with (n + m') by lia).
      change (List.rev (List.seq (S n) m') ++ List.rev [n] = List.rev [n + m'] ++ List.rev (List.seq n m')). rewrite <- ? List.rev_app_distr. f_equal. simpl. rewrite List.cons_seq, List.seq_S. reflexivity.
  - apply List.map_ext_in. intros i H_i. rewrite List.in_seq in H_i. rewrite List.rev_nth by lia. reflexivity.
Qed.

Lemma list_prefix_eq_list_sub {A} :
  ∀ n (l : list A) default,
  n ≤ List.length l →
  list_prefix n l default = list_sub 0 n l default.
Proof.
  intros n l default H_n. unfold list_sub. revert l H_n; induction n as [| n' IH]; intros l H_n; simpl.
  - reflexivity.
  - destruct l as [| x l']; simpl in H_n |- *.
    + lia.
    + rewrite IH by lia. rewrite <- List.seq_shift. rewrite List.map_map. reflexivity.
Qed.

Lemma list_suffix_eq_list_sub {A} :
  ∀ n (l : list A) default,
  n ≤ List.length l →
  list_suffix n l default = list_sub (List.length l - n) n l default.
Proof.
  intros n l default H_n. unfold list_suffix. apply List.rev_inj. rewrite List.rev_involutive.
  rewrite list_rev_list_sub by lia. ltac1:(replace (List.length l - (List.length l - n) - n) with 0 by lia).
  rewrite list_prefix_eq_list_sub by (rewrite List.length_rev; auto). reflexivity.
Qed.

Record vector A n := {
  vector_l : list A;
  vector_wf_l : length vector_l = n;
}.
Arguments vector_l {A n}.
Arguments vector_wf_l {A n}.

Declare Scope vector_scope.
Delimit Scope vector_scope with vector.
Bind Scope vector_scope with vector.
Open Scope vector_scope.

Notation "[||]" := {| vector_l := []; vector_wf_l := eq_refl |} (at level 1) : vector_scope.
#[warnings="-notation-incompatible-prefix"] (* Does not silence warnings when this files is Required… *)
Notation "[ | x | ]" := {| vector_l := [x]; vector_wf_l := eq_refl |} (at level 1, format "[ | x | ]") : vector_scope.
Notation "[ | x ; y ; .. ; z | ]" := {| vector_l := cons x (cons y .. [z] ..); vector_wf_l := eq_refl |} (at level 1, format "[ | x ;  y ;  .. ;  z | ]") : vector_scope.

Register vector as vcpu.vector.type.
Register Build_vector as vcpu.vector.constructor.
Register vector_l as vcpu.vector.l.
Register vector_wf_l as vcpu.vector.wf_l.

Lemma irrelevant_vector {A n} :
  ∀ u v : vector A n,
  vector_l u = vector_l v →
  u = v.
Proof.
  intros u v H_l. destruct u as [u_l u_wf_l], v as [v_l v_wf_l]; simpl in H_l.
  destruct H_l. f_equal. remember (length u_l) as m eqn:H_m; clear u_l H_m.
  destruct v_wf_l. apply UIP_refl_nat.
Defined.

Definition vector_repeat {A} (x : A) n : vector A n := {|
  vector_l := List.repeat x n;
  vector_wf_l := List.repeat_length _ _;
|}.

Register vector_repeat as vcpu.vector.repeat.

#[program]
Definition vector_app {A n m} (u : vector A n) (v : vector A m) : vector A (n + m) := {|
  vector_l := vector_l u ++ vector_l v;
|}.
Next Obligation.
  intros A n m u v. rewrite List.length_app. rewrite ? vector_wf_l. reflexivity.
Defined.

Notation "u  +||+  v" := (vector_app u v) (at level 60, right associativity) : vector_scope.

Register vector_app as vcpu.vector.app.

Definition vector_prefix {A n} m (u : vector A n) default : vector A m := {|
  vector_l := list_prefix m (vector_l u) default;
  vector_wf_l := list_length_list_prefix _ _ _;
|}.

Lemma vector_prefix_vector_app {A n m} :
  ∀ (u : vector A n) (v : vector A m) default,
  vector_prefix n (u +||+ v) default = u.
Proof.
  intros u v default. unfold vector_prefix. apply irrelevant_vector. simpl.
  rewrite <- (vector_wf_l u) at 1. rewrite list_prefix_list_app. reflexivity.
Qed.

Definition vector_suffix {A n} m (u : vector A n) default : vector A m := {|
  vector_l := list_suffix m (vector_l u) default;
  vector_wf_l := list_length_list_suffix _ _ _;
|}.

Lemma vector_suffix_vector_app {A n m} :
  ∀ (u : vector A n) (v : vector A m) default,
  vector_suffix m (u +||+ v) default = v.
Proof.
  intros u v default. unfold vector_suffix. apply irrelevant_vector. simpl.
  rewrite <- (vector_wf_l v) at 1. rewrite list_suffix_list_app. reflexivity.
Qed.

Definition vector_sub {A n} m k (u : vector A n) default : vector A k := {|
  vector_l := list_sub m k (vector_l u) default;
  vector_wf_l := list_length_list_sub _ _ _ _;
|}.
