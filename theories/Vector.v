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
