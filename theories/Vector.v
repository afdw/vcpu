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
