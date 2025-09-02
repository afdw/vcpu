Require Import Utils.
Require Import Vector.

Require Import Utf8.
Import List.ListNotations.
Import Coq.NArith.BinNat.

Record shape := {
  shape_params_type : Type;
  shape_args_type : shape_params_type → Type;
  shape_type : shape_params_type → Type;
  shape_build : ∀ (params : shape_params_type) (args : shape_args_type params), shape_type params;
  shape_dest : ∀ (params : shape_params_type) (v : shape_type params), option (shape_args_type params);
}.

Definition shape_nat := {|
  shape_params_type := nat;
  shape_args_type := λ _, unit;
  shape_type := λ _, nat;
  shape_build := λ n 'tt, n;
  shape_dest := λ n _, Some tt;
|}.

Definition shape_list A := {|
  shape_params_type := binnat;
  shape_args_type := λ n, vector A n;
  shape_type := λ _, list A;
  shape_build := λ n v, vector_list v;
  shape_dest := λ n l,
    match N.eq_dec (length_bin l) n with
    | left H => Some (mk_vector l H)
    | right _ => None
    end;
|}.

(*
[] = shape_build 0 [||]
x :: shape_build n v = shape_build (S n) (x :||: v)
*)

Definition shape_vector A := {|
  shape_params_type := binnat;
  shape_args_type := λ n, vector A n;
  shape_type := λ n, vector A n;
  shape_build := λ _ v, v;
  shape_dest := λ _ v, Some v;
|}.

Definition invert_list :=
  fix f (l : list bool) : list bool :=
    match l with
    | [] => []
    | x :: l' => negb x :: f l'
    end.

Compute invert_list [true; false; true; true].

Print ex_intro.

Definition option_dest {A} (o : option A) {H : ∃ x, o = Some x} : A :=
  match o, H with
  | Some x, H => x
  | None, H =>
    False_rect _ (
      match H with
      | ex_intro _ x H' =>
        match H' with
        end
      end
    )
  end.

Print option_dest.

Check well_founded.

Definition list_nord {A : Type} (l_1 l_2 : list A) : Prop :=
  match l_2 with
  | [] => False
  | _ :: l_2' => l_2' = l_1
  end.

Lemma list_nord_wf {A : Type} :
  well_founded (@list_nord A).
Proof.
  unfold well_founded. intros l. induction l.
  - exists. simpl. intuition.
  - exists. simpl. intros _ <-. auto.
Qed.

Print Wf.
Check well_founded_induction_type (list_nord_wf) (λ _, list bool).
Check well_founded.
Print well_founded.
Compute well_founded_induction_type.
Print Acc.
About Acc_intro.

#[program]
Definition invert_list_wf :=
  fix f (l : list bool) (a : Acc list_nord l) {struct a} : list bool :=
    let '(Acc_intro _ g) := a in
    match l with
    | [] => []
    | x :: l' => negb x :: f l' (g l' (_ : list_nord l' l))
    end.
Next Obligation.
  intros. subst l. simpl in *. auto.
Qed.

Print invert_list_wf.
Eval simpl in (fix f (l : bitlist) (a : Acc list_nord l) {struct a} : bitlist :=
let program_branch_0 :=
λ (g : ∀ y : bitlist, list_nord y l → Acc list_nord y) (Heq_a : Acc_intro l g = a),
let program_branch_0 := λ _ : [] = l, [] in
let program_branch_1 :=
λ (x : bool) (l' : bitlist) (Heq_l : x :: l' = l),
negb x
:: f l'
(g l'
((λ (_ : ∀ l0 : bitlist, Acc list_nord l0 → bitlist) (l0 : bitlist) (a0 : Acc list_nord l0) (g0 : ∀ y : bitlist,
list_nord y l0
→ Acc list_nord y) (Heq_a0 : Acc_intro
l0
g0 =
a0) (x0 : bool) (l'0 : bitlist) (Heq_l0 : x0
:: l'0 =
l0),
invert_list_wf_obligation_1 l0 a0 g0 Heq_a0 x0 l'0 Heq_l0) f l a g Heq_a x l' Heq_l
:
list_nord l' l)) in
match l as l' return (l' = l → bitlist) with
| [] => program_branch_0
| x :: l' => program_branch_1 x l'
end eq_refl in
(let 'Acc_intro _ g as a' := a return (a' = a → bitlist) in program_branch_0 g) eq_refl).

(*
= fix f (l : bitlist) (a : Acc list_nord l) {struct a} : bitlist :=
(let
'Acc_intro _ g as a' := a return (a' = a → bitlist) in
λ Heq_a : Acc_intro l g = a,
match l as l' return (l' = l → bitlist) with
| [] => λ _ : [] = l, []
| x :: l' => λ Heq_l : x :: l' = l, negb x :: f l' (g l' (invert_list_wf_obligation_1 l a g Heq_a x l' Heq_l))
end eq_refl) eq_refl      : ∀ l : bitlist, Acc list_nord l → bitlist
*)

Definition invert_list_wf' :=
  fix f (l : list bool) (a : Acc list_nord l) {struct a} : list bool :=
    let '(Acc_intro _ g) := a in
    match l with
    | [] => fun _ => []
    | x :: l' => fun (g : ∀ y : bitlist, list_nord y (x :: l') → Acc list_nord y) => negb x :: f l' (g l' (eq_refl : list_nord l' (x :: l')))
    end g.

Print invert_list_wf'.

#[program]
Definition invert_list_wf'' :=
  fix f (l : list bool) (a : Acc list_nord l) {struct a} : list bool :=
    let '(Acc_intro _ g) := a in
    match l return forall (g : ∀ y : bitlist, list_nord y l → Acc list_nord y), _ with
    | [] => fun _ => []
    | x :: l' => fun (g : ∀ y : bitlist, list_nord y (x :: l') → Acc list_nord y) => negb x :: f l' (g l' (_ : list_nord l' (x :: l')))
    end g.
Next Obligation.
  reflexivity.
Qed.


Print Wf.

Axiom vector_cons : ∀ {A n} (x : A) (v : vector A n), vector A (N.succ n).

Definition id {A : Type} (x : A) : A := x.

Check id I : True : Prop.
Check Type : Type : Type : Type : Type.

Search well_founded.

Require Stdlib.Program.Wf.

#[program]
Fixpoint invert_vector (n : binnat) (v : vector bool n) {wf N.lt n} : vector bool n :=
    match vector_list v with
    | [] => [||]
    | x :: l' => vector_cons (negb x) (invert_vector (N.pred n) (@option_dest _ (shape_dest (shape_list bool) (N.pred n) l') _))
    end.

(* #[program] Definition invert_vector :=
  fix f (n : binnat) (v : vector bool n) : vector bool n :=
    match vector_list v with
    | [] => [||]
    | x :: l' => vector_cons (negb x) (f (N.pred n) (option_dest (shape_dest (shape_list bool) (N.pred n) l')))
    end. *)
