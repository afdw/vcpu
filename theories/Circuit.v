#[warnings="-notation-incompatible-prefix"]
From Vcpu Require Import Tools.

Inductive wire :=
  | wire_True : wire
  | wire_False : wire
  | wire_Id : nat → wire
  | wire_Not : nat → wire
  | wire_And : nat → nat → wire
  | wire_Or : nat → nat → wire
  | wire_Eq : nat → nat → wire
  | wire_If : nat → nat → nat → wire.

Register wire as vcpu.wire.type.
Register wire_True as vcpu.wire.True.
Register wire_False as vcpu.wire.False.
Register wire_Id as vcpu.wire.Id.
Register wire_Not as vcpu.wire.Not.
Register wire_And as vcpu.wire.And.
Register wire_Or as vcpu.wire.Or.
Register wire_Eq as vcpu.wire.Eq.
Register wire_If as vcpu.wire.If.

Definition wire_map f (w : wire) : wire :=
  match w with
  | wire_True => wire_True
  | wire_False => wire_False
  | wire_Id w_1 => wire_Id (f w_1)
  | wire_Not w_1 => wire_Not (f w_1)
  | wire_And w_1 w_2 => wire_And (f w_1) (f w_2)
  | wire_Or w_1 w_2 => wire_Or (f w_1) (f w_2)
  | wire_Eq w_1 w_2 => wire_Eq (f w_1) (f w_2)
  | wire_If w_1 w_2 w_3 => wire_If (f w_1) (f w_2) (f w_3)
  end.

Record circuit (n m : nat) := {
  circuit_wires : list wire;
}.
Arguments circuit_wires {n m}.

Register circuit as vcpu.circuit.type.
Register Build_circuit as vcpu.circuit.constructor.
Register circuit_wires as vcpu.circuit.wires.

Definition wire_wf n (w : wire) :=
  match w with
  | wire_True => True
  | wire_False => True
  | wire_Id w_1 => w_1 < n
  | wire_Not w_1 => w_1 < n
  | wire_And w_1 w_2 => w_1 < n ∧ w_2 < n
  | wire_Or w_1 w_2 => w_1 < n ∧ w_2 < n
  | wire_Eq w_1 w_2 => w_1 < n ∧ w_2 < n
  | wire_If w_1 w_2 w_3 => w_1 < n ∧ w_2 < n ∧ w_3 < n
  end.

Definition circuit_wf_wires n (c_wires : list wire) :=
  List.fold_right (λ w '(i, H), (S i, wire_wf (i + n) w ∧ H)) (0, True) c_wires.

Definition circuit_wf {n m} (c : circuit n m) :=
  let '(k, H) := circuit_wf_wires n (circuit_wires c) in
  k ≥ m ∧ H.

Register circuit_wf as vcpu.circuit.wf.

Definition wire_eval (w : wire) (intermediates : list bool) : bool :=
  match w with
  | wire_True => true
  | wire_False => false
  | wire_Id w_1 => List.nth w_1 intermediates false
  | wire_Not w_1 => negb (List.nth w_1 intermediates false)
  | wire_And w_1 w_2 => List.nth w_1 intermediates false && List.nth w_2 intermediates false
  | wire_Or w_1 w_2 => List.nth w_1 intermediates false || List.nth w_2 intermediates false
  | wire_Eq w_1 w_2 => Bool.eqb (List.nth w_1 intermediates false) (List.nth w_2 intermediates false)
  | wire_If w_1 w_2 w_3 => if List.nth w_1 intermediates false then List.nth w_2 intermediates false else List.nth w_3 intermediates false
  end.

Definition circuit_eval_wires (c_wires : list wire) (inputs : list bool) : list bool :=
  List.fold_right (λ w intermediates, wire_eval w intermediates :: intermediates) inputs c_wires.

Definition circuit_eval {n m} (c : circuit n m) (inputs : vector bool n) : vector bool m := {|
  vector_l := list_prefix m (circuit_eval_wires (circuit_wires c) (vector_l inputs)) false;
  vector_wf_l := list_length_list_prefix _ _ _;
|}.

Register circuit_eval as vcpu.circuit.eval.

Definition circuit_const {n} m (u : vector bool n) : circuit m n := {|
  circuit_wires :=
    List.map (λ b : bool, if b then wire_True else wire_False) (vector_l u);
|}.

Lemma circuit_wf_circuit_const {n} :
  ∀ m (u : vector bool n),
  circuit_wf (circuit_const m u).
Proof.
  intros m u. unfold circuit_wf, circuit_const. destruct u as [u_l u_wf_l]. simpl.
  subst n. induction u_l as [| b u_l' IH]; simpl.
  - auto.
  - destruct (circuit_wf_wires m (List.map (λ b : bool, if b then wire_True else wire_False) u_l')) as (k & H). destruct b; simpl; ltac1:(intuition lia).
Qed.

Lemma circuit_eval_circuit_const {n} :
  ∀ m (u : vector bool n) inputs,
  circuit_eval (circuit_const m u) inputs = u.
Proof.
  intros m u inputs. unfold circuit_eval, circuit_const, list_sub. apply irrelevant_vector. destruct u as [u_l u_wf_l]. simpl.
  subst n. induction u_l as [| b u_l' IH]; simpl.
  - reflexivity.
  - f_equal.
    + destruct b; simpl; reflexivity.
    + rewrite IH. reflexivity.
Qed.

Register circuit_const as vcpu.circuit.const.
Register circuit_wf_circuit_const as vcpu.circuit.wf_const.
Register circuit_eval_circuit_const as vcpu.circuit.eval_const.

Definition circuit_sub n m k : circuit n k := {|
  circuit_wires := List.repeat (wire_Id (Nat.pred (k + m))) k;
|}.

Lemma circuit_wf_circuit_sub :
  ∀ n m k,
  m + k ≤ n →
  circuit_wf (circuit_sub n m k).
Proof.
  intros n m k H_m_k. unfold circuit_wf, circuit_sub. simpl. revert m H_m_k; induction k as [| k' IH]; intros m H_m_k; simpl.
  - auto.
  - specialize (IH (S m)). rewrite Nat.add_succ_r in IH. simpl in IH.
    destruct (circuit_wf_wires n (ListDef.repeat (wire_Id (k' + m)) k')) as (l & H).
    specialize (IH ltac2:(lia)). ltac1:(intuition lia).
Qed.

Lemma circuit_eval_circuit_sub :
  ∀ n m k inputs,
  circuit_eval (circuit_sub n m k) inputs = vector_sub m k inputs false.
Proof.
  intros n m k inputs. unfold circuit_eval, circuit_sub, vector_sub, list_sub. apply irrelevant_vector. destruct inputs as [inputs_l inputs_wf_l]. simpl.
  clear inputs_wf_l.
  ltac1:(replace (circuit_eval_wires (List.repeat (wire_Id (Nat.pred (k + m))) k) inputs_l) with (List.map (λ i, List.nth i inputs_l false) (List.seq m k) ++ inputs_l); revgoals). {
    symmetry. revert m; induction k as [| k' IH]; intros m; simpl.
    - reflexivity.
    - specialize (IH (S m)). rewrite Nat.add_succ_r in IH. simpl in IH. rewrite IH.
      ltac1:(replace k' with (List.length (List.map (λ i, List.nth i inputs_l false) (List.seq (S m) k'))) at 1; revgoals). {
        rewrite List.length_map, List.length_seq. reflexivity.
      }
      rewrite List.app_nth2_plus. reflexivity.
  }
  ltac1:(replace k with (List.length (List.map (λ i, ListDef.nth i inputs_l false) (List.seq m k))) at 1; revgoals). {
    rewrite List.length_map, List.length_seq. reflexivity.
  }
  rewrite list_prefix_list_app. reflexivity.
Qed.

Definition circuit_prefix n m : circuit (n + m) n :=
  circuit_sub (n + m) 0 n.

Lemma circuit_wf_circuit_prefix :
  ∀ n m,
  circuit_wf (circuit_prefix n m).
Proof.
  intros n m. unfold circuit_prefix. apply circuit_wf_circuit_sub; lia.
Qed.

Lemma circuit_eval_circuit_prefix :
  ∀ n m inputs,
  circuit_eval (circuit_prefix n m) inputs = vector_prefix n inputs false.
Proof.
  intros n m inputs. unfold circuit_prefix. rewrite circuit_eval_circuit_sub.
  unfold vector_sub, vector_prefix. apply irrelevant_vector. destruct inputs as [inputs_l inputs_wf_l]. simpl.
  rewrite list_prefix_eq_list_sub by lia. reflexivity.
Qed.

Definition circuit_suffix n m : circuit (n + m) m :=
  circuit_sub (n + m) n m.

Lemma circuit_wf_circuit_suffix :
  ∀ n m,
  circuit_wf (circuit_suffix n m).
Proof.
  intros n m. unfold circuit_suffix. apply circuit_wf_circuit_sub; lia.
Qed.

Lemma circuit_eval_circuit_suffix :
  ∀ n m inputs,
  circuit_eval (circuit_suffix n m) inputs = vector_suffix m inputs false.
Proof.
  intros n m inputs. unfold circuit_suffix. rewrite circuit_eval_circuit_sub.
  unfold vector_sub, vector_prefix. apply irrelevant_vector. destruct inputs as [inputs_l inputs_wf_l]. simpl.
  rewrite list_suffix_eq_list_sub by lia. ltac1:(replace (List.length inputs_l - m) with n by lia). reflexivity.
Qed.

Definition circuit_select n : circuit (1 + (n + n)) n := {|
  circuit_wires :=
    List.map
      (λ i, wire_If i (Nat.pred (n + 1)) (Nat.pred (n + (1 + n))))
      (List.seq 0 n);
|}.

Lemma circuit_wf_circuit_select :
  ∀ n,
  circuit_wf (circuit_select n).
Proof.
  intros n.
  specialize (circuit_wf_circuit_sub (1 + (n + n)) 1 n ltac:(lia)) as H_1.
  specialize (circuit_wf_circuit_sub (1 + (n + n)) (1 + n) n ltac:(lia)) as H_2.
  unfold circuit_wf, circuit_sub, circuit_select in H_1, H_2 |- *. simpl in H_1, H_2 |- *.
  unfold circuit_wf_wires.
Admitted.

(* Lemma circuit_eval_circuit_select :
  ∀ n inputs,
  circuit_eval (circuit_select n) inputs =  *)

Definition circuit_comp {n m k} (c_2 : circuit m k) (c_1 : circuit n m) : circuit n k := {|
  circuit_wires := circuit_wires c_2 ++ circuit_wires c_1;
|}.

Lemma circuit_wf_circuit_comp {n m k} :
  ∀ (c_2 : circuit m k) (c_1 : circuit n m),
  circuit_wf c_2 →
  circuit_wf c_1 →
  circuit_wf (circuit_comp c_2 c_1).
Proof.
  intros c_2 c_1 wf_c_2 wf_c_1. unfold circuit_wf in wf_c_2, wf_c_1 |- *. destruct c_2 as [c_2_wires], c_1 as [c_1_wires]. simpl in wf_c_2, wf_c_1 |- *.
  (* destruct (circuit_wf_wires m c_2_wires) as (k_c_2 & H_c_2). *)
  induction c_2_wires as [| w c_2_wires IH]; simpl in wf_c_2 |- *.
  - destruct (circuit_wf_wires n c_1_wires) as (k_c_1 & H_c_1). ltac1:(intuition lia).
  - destruct (circuit_wf_wires m c_2_wires) as (k_c_2 & H_c_2).
    (* specialize (IH ltac2:(ltac1:(intuition (auto; lia)))). *)
  (* destruct (circuit_wf_wires n c_1_wires) as (k_c_1 & H_c_1). *)
Admitted.

Lemma circuit_eval_circuit_comp {n m k} :
  ∀ (c_2 : circuit m k) (c_1 : circuit n m) inputs,
  circuit_eval (circuit_comp c_2 c_1) inputs = circuit_eval c_2 (circuit_eval c_1 inputs).
Proof.
Admitted.

Definition wire_lift n m (w : wire) : wire :=
  wire_map (λ i, if i <? n then i else i + m) w.

Definition circuit_lift_wires n (c_wires : list wire) : list wire :=
  snd (List.fold_right (λ w '(i, l), (S i, wire_lift i n w :: l)) (0, []) c_wires).

Definition circuit_combine {n m k} (c_1 : circuit n m) (c_2 : circuit n k) : circuit n (m + k) := {|
  circuit_wires :=
    List.repeat (wire_Id (Nat.pred (m + List.length (circuit_wires c_2)))) m ++
    circuit_lift_wires (List.length (circuit_wires c_1)) (circuit_wires c_2) ++
    circuit_wires c_1;
|}.

Lemma circuit_wf_circuit_combine {n m k} :
  ∀ (c_1 : circuit n m) (c_2 : circuit n k),
  circuit_wf c_1 →
  circuit_wf c_2 →
  circuit_wf (circuit_combine c_1 c_2).
Proof.
  intros c_1 c_2 wf_c_1 wf_c_2. unfold circuit_wf in wf_c_1, wf_c_2 |- *. destruct c_1 as [c_1_wires], c_2 as [c_2_wires]. simpl in wf_c_1, wf_c_2 |- *.
Admitted.

Lemma circuit_eval_circuit_combine {n m k} :
  ∀ (c_1 : circuit n m) (c_2 : circuit n k) inputs,
  circuit_eval (circuit_combine c_1 c_2) inputs = circuit_eval c_1 inputs +||+ circuit_eval c_2 inputs.
Proof.
Admitted.

(* Compute circuit_combine (@Build_circuit 5 2 [wire_Id 0; wire_Id 1]) (@Build_circuit 5 2 [wire_Id 3; wire_Id 4]). *)
(* Compute circuit_eval (circuit_sub 10 3 5) [|?[a]; ?[b]; ?[c]; ?[d]; ?[e]; ?[f]; ?[g]; ?[h]; ?[i]; ?[j]|].
Compute circuit_eval_wires (circuit_wires (circuit_sub 10 3 5)) [?[a]; ?[b]; ?[c]; ?[d]; ?[e]; ?[f]; ?[g]; ?[h]; ?[i]; ?[j]]. *)
