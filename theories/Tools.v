From Ltac2 Require Export Ltac2.
From Equations Require Export Equations.
From Equations Require Export TransparentEquations.
From Stdlib Require Export Unicode.Utf8.
From Stdlib Require Export Logic.Classical.
From Stdlib Require Export Logic.FunctionalExtensionality.
From Stdlib Require Export Logic.PropExtensionality.
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

#[global] Obligation Tactic := try (solve [ltac1:(Equations.CoreTactics.equations_simpl)]).
#[global] Unset Program Cases.
#[global] Unset Program Generalized Coercion.
#[global] Unset Implicit Arguments.

(* #[global] Set Typeclasses Iterative Deepening. *)
#[global] Set Typeclasses Depth 20.

#[global] Set Equations With UIP.
#[global] Set Equations Transparent.

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
  list_prefix (length l_1) (l_1 ++ l_2) default = l_1.
Proof.
  intros l_1 l_2 default. induction l_1 as [| x l_1' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma list_nth_list_prefix {A} :
  ∀ i n (l : list A) default,
  i < n →
  List.nth i (list_prefix n l default) default = List.nth i l default.
Proof.
  intros i n l default H_i.
Admitted.

Definition list_sub {A} n m (l : list A) default : list A :=
  List.map (λ i, List.nth i l default) (List.seq n m).

Lemma list_length_list_sub {A} :
  ∀ n m (l : list A) default,
  List.length (list_sub n m l default) = m.
Proof.
  intros n m l default. unfold list_sub. rewrite List.length_map, List.length_seq. reflexivity.
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

Lemma irrelevant_vector {A n} :
  ∀ u v : vector A n,
  vector_l u = vector_l v →
  u = v.
Proof.
  intros u v H_l. destruct u as [u_l u_wf_l], v as [v_l v_wf_l]; simpl in H_l.
  destruct H_l. f_equal. remember (length u_l) as m eqn:H_m; clear u_l H_m.
  destruct v_wf_l. apply UIP_refl_nat.
Defined.

#[program]
Definition vector_app {A n m} (u : vector A n) (v : vector A m) : vector A (n + m) := {|
  vector_l := vector_l u ++ vector_l v;
|}.
Next Obligation.
  intros A n m u v. rewrite List.length_app. rewrite ? vector_wf_l. reflexivity.
Defined.

Notation "u  +||+  v" := (vector_app u v) (at level 60, right associativity) : vector_scope.

Register vector_app as vcpu.vector.app.

#[program]
Definition vector_sub {A n} m k (u : vector A n) default : vector A k := {|
  vector_l := list_sub m k (vector_l u) default;
  vector_wf_l := list_length_list_sub _ _ _ _;
|}.
