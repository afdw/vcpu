Require Import Utils.

Require Coq.Strings.String.
Import String.StringSyntax.

Definition id := String.string.
Definition path := String.string.

Inductive sort :=
  | Sort_prop
  | Sort_set
  | Sort_type.

Inductive term :=
  | Term_rel (i : nat)
  | Term_var (i : id)
  | Term_set (s : sort)
  | Term_prod (type : term) (body : term)
  | Term_lambda (type : term) (body : term)
  | Term_let_in (value : term) (body : term)
  | Term_app (fn : term) (arg : term)
  | Term_const (p : path)
  | Term_ind (p : path)
  | Term_construct (p : path)
  | Term_case (ind : path) (params : list term) (scrutinee : term) (return_ : term) (branches : list term)
  | Term_fix (defs : nat * term * term) (i : nat).

Inductive declaration :=
  | Declaration_assum (type : term)
  | Declaration_def (type : term) (value : term).

Record env := {
  env_rel_context : list declaration;
  env_var_context : list (id * declaration);
}.
