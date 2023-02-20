Require Import Utils.

Require Import Lia.
Require Coq.Lists.List.
Import List.ListNotations.
Import Coq.NArith.BinNat.

Record vector {A n} := {
  vector_list : list A;
  vector_wf : length_bin vector_list = n;
}.

Arguments vector : clear implicits.

Notation bitvec := (vector bool).

Notation "[| |]" := {| vector_list := []; vector_wf := eq_refl |} (format "[| |]").
Notation "[| x |]" := {| vector_list := [x]; vector_wf := eq_refl |}.
Notation "[| x ; y ; .. ; z |]" := {| vector_list := cons x (cons y .. [z] ..); vector_wf := eq_refl |}.

Register vector as vcpu.vector.type.
Register Build_vector as vcpu.vector.constructor.
Register vector_list as vcpu.vector.list.
Register vector_wf as vcpu.vector.wf.

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

#[program] Definition vector_app {A n1 n2} (v1 : vector A n1) (v2 : vector A n2) : vector A (n1 + n2) := {|
  vector_list := vector_list v1 ++ vector_list v2;
|}.
Next Obligation.
  intros A n1 n2 v1 v2. rewrite length_bin_app. rewrite ? vector_wf. auto.
Qed.

Register vector_app as vcpu.vector.app.

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
