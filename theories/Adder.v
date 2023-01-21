Require Import Utils.
Require Import Vector.
Require Import Plugin.

Require Coq.Lists.List.
Import List.ListNotations.

Unset Program Cases.

#[program] Definition test1 (bv : bitvec 1) : bitvec 2 := {|
  vector_list := match vector_list bv with [b] => [b; b] | _ => [] end;
|}.
Next Obligation.
  intros bv. specialize (vector_wf bv) as H. destruct (vector_list bv) as [ | b l'].
  - simpl in H. congruence.
  - destruct l' as [ | b' l''].
    + auto.
    + simpl in H. congruence.
Qed.

Set Program Cases.

Compile test1.
