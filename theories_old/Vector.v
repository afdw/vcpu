Require Import Utils.

Require Import Lia.
Require Coq.Lists.List.
Import List.ListNotations.
Import Coq.NArith.BinNat.
Import EqNotations.

Record vector {A n} := {
  vector_list : list A;
  vector_wf : length_bin vector_list = n;
}.

Arguments vector : clear implicits.

Notation bitvec := (vector bool).

Declare Scope vector_scope.
Delimit Scope vector_scope with vector.
Bind Scope vector_scope with vector.
Notation "[| |]" := {| vector_list := []; vector_wf := eq_refl |} (format "[| |]").
Notation "[| x |]" := {| vector_list := [x]; vector_wf := eq_refl |}.
Notation "[| x ; y ; .. ; z |]" := {| vector_list := cons x (cons y .. [z] ..); vector_wf := eq_refl |}.

Register vector as vcpu.vector.type.
Register Build_vector as vcpu.vector.constructor.
Register vector_list as vcpu.vector.list.
Register vector_wf as vcpu.vector.wf.

Definition mk_vector {A n} v_list v_wf : vector A n := {|
  vector_list := v_list;
  vector_wf := normalize_eq_binnat _ _ v_wf;
|}.

Lemma mk_vector_ext :
  forall {A n} (v_list : list A) (v_wf_1 v_wf_2 : length_bin v_list = n),
  mk_vector v_list v_wf_1 = mk_vector v_list v_wf_2.
Proof.
  intros A n v_list v_wf_1 v_wf_2. unfold mk_vector. f_equal. apply normalize_eq_binnat_ext.
Qed.

Lemma mk_vector_ext_all :
  forall {A n} (v_list_1 v_list_2 : list A)
  (v_wf_1 : length_bin v_list_1 = n) (v_wf_2 : length_bin v_list_2 = n),
  v_list_1 = v_list_2 ->
  mk_vector v_list_1 v_wf_1 = mk_vector v_list_2 v_wf_2.
Proof.
  intros A n v_list_1 v_list_2 v_wf_1 v_wf_2 H. subst v_list_2. apply mk_vector_ext.
Qed.

Lemma mk_vector_eq_refl :
  forall {A} (l : list A),
  mk_vector l eq_refl = {| vector_list := l; vector_wf := eq_refl |}.
Proof.
  intros A l. unfold mk_vector. f_equal. apply normalize_eq_binnat_eq_refl.
Qed.

Definition vector_normalize {A n} (v : vector A n) : vector A n := mk_vector (vector_list v) (vector_wf v).

Definition vector_similar {A n1 n2} (v1 : vector A n1) (v2 : vector A n2) := vector_list v1 = vector_list v2.

Infix "~=" := vector_similar (at level 70) : type_scope.

Register vector_similar as vcpu.vector.similar.

Lemma vector_similar_ext :
  forall {A n} (v1 : vector A n) (v2 : vector A n),
  v1 = v2 ->
  v1 ~= v2.
Proof.
  intros A n v1 v2 H. rewrite H. reflexivity.
Qed.

Register vector_similar_ext as vcpu.vector.similar_ext.

#[program] Definition vector_head {A n} (v : vector A (N.succ n)) : A :=
  match vector_list v with
  | x :: _ => x
  | [] => _
  end.
Next Obligation.
  intros A n v. specialize (vector_wf v) as H. destruct (vector_list v).
  - simpl in H. apply N.neq_0_succ in H. destruct H.
  - simpl. auto.
Qed.

#[program] Definition vector_tail {A n} (v : vector A (N.succ n)) : vector A n := {|
  vector_list := List.tl (vector_list v);
|}.
Next Obligation.
  intros A n v. specialize (vector_wf v) as H. destruct (vector_list v).
  - simpl in H. apply N.neq_0_succ in H. destruct H.
  - simpl. rewrite length_bin_cons in H. apply N.succ_inj in H. auto.
Qed.

Definition vector_dest {A n} (v : vector A (N.succ n)) : A * vector A n :=
  (vector_head v, vector_tail v).

Register vector_dest as vcpu.vector.dest.

(* Recursion Schema  *)

(* Definition vector_case {A n} (v : vector A n) :  *)

Definition vector_of_list {A} (l : list A) : vector A (length_bin l) := mk_vector l eq_refl.

#[program] Definition vector_app {A n1 n2} (v1 : vector A n1) (v2 : vector A n2) : vector A (n1 + n2) :=
  mk_vector (vector_list v1 ++ vector_list v2) _.
Next Obligation.
  intros A n1 n2 v1 v2. rewrite length_bin_app. rewrite ? vector_wf. auto.
Qed.

Infix "++" := vector_app : vector_scope.

Register vector_app as vcpu.vector.app.

Lemma vector_app_mk_vector :
  forall A n1 n2 (v_list_1 v_list_2 : list A)
    (v_wf_1 : length_bin v_list_1 = n1) (v_wf_2 : length_bin v_list_2 = n2),
  ((mk_vector v_list_1 v_wf_1) ++ (mk_vector v_list_2 v_wf_2))%vector =
    mk_vector (v_list_1 ++ v_list_2)
      (vector_app_obligation_1 _ _ _(mk_vector v_list_1 v_wf_1) (mk_vector v_list_2 v_wf_2)).
Proof.
  intros A n1 n2 v_list_1 v_list_2 v_wf_1 v_wf_2. unfold vector_app. apply mk_vector_ext.
Qed.

Definition vector_seq_bin s n : vector binnat n :=
  mk_vector (list_seq_bin s n) (length_bin_list_seq_bin s n).

Definition vector_select_bin {A n m} (values : vector A n) (indices : vector binnat m) default : vector A m :=
  mk_vector
    (list_select_bin (vector_list values) (vector_list indices) default)
    (rew vector_wf indices in length_bin_list_select_bin _ _ _).

Register vector_select_bin as vcpu.vector.select_bin.

#[program] Definition vector_map {A B n} f (v : vector A n) : vector B n :=
  mk_vector (List.map f (vector_list v)) _.
Next Obligation.
  intros A B n f v. rewrite length_bin_list_map. apply (vector_wf v).
Qed.

Unset Program Cases.

#[program] Definition vector_map2 f {n} (bv1 bv2 : bitvec n) : bitvec n := {|
  vector_list := List.map (fun '(b1, b2) => f b1 b2) (List.combine (vector_list bv1) (vector_list bv2));
|}.
Next Obligation.
  intros f n bv1 bv2. rewrite length_bin_list_map. rewrite length_bin_list_combine.
  rewrite ? vector_wf. apply N.min_id.
Qed.

Set Program Cases.

Definition vector_and {n} (bv1 bv2 : bitvec n) : bitvec n := vector_map2 andb bv1 bv2.

Fixpoint extractor_transitions_wf_aux {n} e_lengths
  (e_transitions : htype (List.map (vector binnat : _ -> Type) e_lengths))
  : Prop :=
  match e_lengths, e_transitions with
  | [], tt => True
  | e_length :: e_lengths', (e_transition, e_transitions') =>
    list_forall (fun i => (i < n)%N) (vector_list e_transition) /\
      extractor_transitions_wf_aux (n := n) e_lengths' e_transitions'
  end.

Record extractor {n m} := {
  extractor_lengths : list binnat;
  extractor_transitions : htype (List.map (vector binnat : _ -> Type) extractor_lengths);
  extractor_lengths_wf : sum extractor_lengths = m;
  extractor_transitions_wf :
    extractor_transitions_wf_aux (n := n) extractor_lengths extractor_transitions;
}.

Arguments extractor : clear implicits.

Fixpoint extractor_offsets_concat_aux e_lengths
  (e_transitions : htype (List.map (vector binnat : _ -> Type) e_lengths))
  : vector binnat (sum e_lengths) :=
  match e_lengths, e_transitions with
  | [], tt => [||]
  | e_length :: e_lengths', (e_transition, e_transitions') =>
    (e_transition ++ extractor_offsets_concat_aux e_lengths' e_transitions')%vector
  end.

Definition extractor_offsets_concat {n m} (e : extractor n m) :=
  extractor_offsets_concat_aux (extractor_lengths e) (extractor_transitions e).

Definition extractor_apply {n m} (s : extractor n m) (v : bitvec n) :=
  vector_select_bin v (extractor_offsets_concat s) false.

Fixpoint extractor_spec_aux {n} e_lengths
  (e_transitions : htype (List.map (vector binnat : _ -> Type) e_lengths))
  (ideals : htype (List.map (bitvec : _ -> Type) e_lengths))
  (v : bitvec n)
  : Prop :=
  match e_lengths, e_transitions, ideals with
  | [], tt, tt => True
  | e_length :: e_lengths', (e_transition, e_stransisions'), (ideal, ideals') =>
    vector_select_bin v e_transition false ~= ideal /\
      extractor_spec_aux e_lengths' e_stransisions' ideals' v
  end.

Definition extractor_spec {n m} (e : extractor n m) ideals (v : bitvec n) :=
  extractor_spec_aux (extractor_lengths e) (extractor_transitions e) ideals v.

Fixpoint extractor_flatten_aux {A} e_lengths
  (fragments : htype (List.map (vector A) e_lengths))
  : vector A (sum e_lengths) :=
  match e_lengths, fragments with
  | [], tt => [||]
  | e_length :: e_lengths', (fragment, fragments') =>
    (fragment ++ extractor_flatten_aux e_lengths' fragments')%vector
  end.

Definition extractor_flatten_transitions {n m} (e : extractor n m) :=
  extractor_flatten_aux (extractor_lengths e) (extractor_transitions e).

Definition extractor_flatten_ideals {n m} (e : extractor n m) ideals :=
  extractor_flatten_aux (A := bool) (extractor_lengths e) ideals.

Fixpoint extractor_to_list_aux e_lengths {A} (fragments : htype (List.map (vector A) e_lengths)) :=
  match e_lengths, fragments with
  | [], tt => []
  | e_length :: e_lengths', (fragment, fragments') =>
    vector_list fragment :: extractor_to_list_aux e_lengths' fragments'
  end.

Definition extractor_transitions_to_list {n m} (e : extractor n m) :=
  extractor_to_list_aux (extractor_lengths e) (extractor_transitions e).

Definition extractor_ideals_to_list {n m} (e : extractor n m) ideals :=
  extractor_to_list_aux (A := bool) (extractor_lengths e) ideals.

#[program] Definition extractor_increase_input_count {n m} (e : extractor n m)
  additional_input_count : extractor (n + additional_input_count) m := {|
  extractor_lengths := extractor_lengths e;
  extractor_transitions := extractor_transitions e;
  extractor_lengths_wf := extractor_lengths_wf e;
|}.
Next Obligation.
  intros n m e additional_input_count. destruct e as (e_lengths, e_transitions, H1, H2). simpl. clear H1.
  induction e_lengths as [ | e_length e_lengths' IH].
  - auto.
  - simpl. simpl in H2. destruct e_transitions as (e_transition, e_transitions'). destruct H2 as (H1 & H2). split.
    + apply (list_forall_incr _ _ _ H1). lia.
    + apply IH. auto.
Qed.

Definition extractor_cons {n m} e_length
  (e_transition : vector binnat e_length)
  (e_transition_wf : list_forall (fun i => (i < n)%N) (vector_list e_transition)) (e : extractor n m)
  : extractor n (e_length + m) := {|
  extractor_lengths := e_length :: extractor_lengths e;
  extractor_transitions := (e_transition, extractor_transitions e);
  extractor_lengths_wf := f_equal_2_plus_bin _ _ _ _ eq_refl (extractor_lengths_wf e);
  extractor_transitions_wf := conj e_transition_wf (extractor_transitions_wf e);
|}.

Lemma extractor_spec_structure_cons :
  forall {n m} e_length e_transition e_transition_wf (e : extractor n m) ideal ideals' (v : bitvec n),
  extractor_spec (extractor_cons e_length e_transition e_transition_wf e) (ideal, ideals') v <->
    vector_select_bin v e_transition false ~= ideal /\ extractor_spec e ideals' v.
Proof.
  intros n m e_length e_transition e_transition_wf e ideal ideals' v.
  unfold extractor_cons, extractor_spec. simpl. intuition auto.
Qed.
