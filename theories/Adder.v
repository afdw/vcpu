Require Import VcpuPlugin.

Open Scope bool_scope.

Fixpoint bitvec_and {n} (bv1 bv2 : bitvec n) : bitvec n :=
  match n, bv1, bv2 with
  | 0, _, _ => [||]
  | S n', bv1, bv2 =>
    (
      let '(b1 :||: bv1') in (vector _ (S n1')) := bv1 return _ in
      let '(b2 :||: bv2') in (vector _ (S n2')) := bv2 return _ in
      fun cast_1 cast_2 =>
        (b1 && b2) :||: @bitvec_and n' (cast_1 bv1') (cast_2 bv2')
    ) (@id _) (@id _)
  end.
