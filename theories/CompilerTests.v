#[warnings="-notation-incompatible-prefix"]
From Vcpu Require Import Tools.
From Vcpu Require Import Circuit.
From Vcpu Require Import Plugin.

Set Printing Width 120.
Set Printing Depth 10000.

(* Set Printing All. *)
(* Set Printing Implicit. *)

Vcpu Derive Encoder for unit as unit.
Vcpu Derive Encoder for prod as prod.
Vcpu Derive Encoder for bool as bool.
Vcpu Derive Encoder for sum as sum.
Vcpu Derive Encoder for option as option.

Vcpu Derive Encoder for (sum bool bool).

Definition identity A (x : A) := x.

Definition swap A n m (v : vector A (n + m)) : vector A (m + n) :=
  rew [λ k, vector A k] (Nat.add_comm n m) in v.

Inductive vec' A (n : nat) := vec'_b (a : A).

Definition swap' A n m (v : vec' A (n + m)) : vec' A (m + n) :=
  rew [λ k, vec' A k] (Nat.add_comm n m) in v.

Definition exchange A B (p : A * B) : B * A :=
  match p with
  | (a, b) => (b, a)
  end.

Inductive many_things :=
  | MTA (_ : bool) (_ : bool) (_ : bool)
  | MTB (_ : bool)
  | MTC.

Definition many_things_transform (mt : many_things) : many_things :=
  match mt with
  | MTA b_1 b_2 b_3 => MTB (xorb b_1 (b_2 && b_3))
  | MTB b => MTC
  | MTC => MTA true false false
  end.

Vcpu Derive Encoder for many_things as many_things.

Fixpoint flip (b : bool) n :=
  match n with
  | 0 => b
  | S n' => negb (flip b n')
  end.

Fixpoint flip_s (b : bool) n (s : bool) :=
  match n with
  | 0 => b
  | S n' => xorb s (flip_s b n' s)
  end.

Fixpoint vec A n : Type :=
  match n with
  | 0 => unit
  | S n' => A * vec A n'
  end.

Fixpoint vec_len A A_len (A_encode : A → vector bool A_len) n : nat :=
  match n with
  | 0 =>
    unit_len
  | S n' =>
    prod_len A A_len A_encode (vec A n') (vec_len A A_len A_encode n') (λ _, vector_repeat false _)
  end.

Fixpoint vec_encode A A_len (A_encode : A → vector bool A_len) n : vec A n → vector bool (vec_len A A_len A_encode n) :=
  match n return vec A n → vector bool (vec_len A A_len A_encode n) with
  | 0 => λ v,
    unit_encode v
  | S n' => λ v,
    prod_encode A A_len A_encode (vec A n') (vec_len A A_len A_encode n') (vec_encode A A_len A_encode n') v
  end.

Register vec as vcpu.vec.type.
Register vec_len as vcpu.vec.len.
Register vec_encode as vcpu.vec.encode.

Vcpu Derive Encoder for (vec bool ?[n]).

Fixpoint bv_not n : vec bool n → vec bool n :=
  match n return vec bool n → vec bool n with
  | 0 => λ '(tt),
    tt
  | S n' => λ '(b, bv'),
    let not_bv' := bv_not n' bv' in
    (negb b, not_bv')
  end.

Fixpoint bv_add n : vec bool n → vec bool n → bool * vec bool n :=
  match n return vec bool n → vec bool n → bool * vec bool n with
  | 0 => λ bv_1 bv_2,
    let 'tt := bv_1 in
    let 'tt := bv_2 in
    (false, tt)
  | S n' => λ bv_1 bv_2,
    let '(b_1, bv_1') := bv_1 in
    let '(b_2, bv_2') := bv_2 in
    let carry_in_add_bv_1'_bv_2' := bv_add n' bv_1' bv_2' in
    let '(carry_in, add_bv_1'_bv_2') := carry_in_add_bv_1'_bv_2' in
    let b_res := xorb (xorb b_1 b_2) carry_in in
    let carry_out := (b_1 && b_2) || (carry_in && (b_1 || b_2)) in
    (carry_out, (b_res, add_bv_1'_bv_2'))
  end.

Compute bv_add 4 (false, (true, (false, (true, tt)))) (false, (true, (true, (false, tt)))).

(* Check λ input_len input_encode,
. *)

Vcpu Derive Compilation for identity with (F T (F R T)) as identity.
Vcpu Derive Compilation for @option_map with (F T (F T (F (F T T) (F T T)))) as option_map.
Vcpu Derive Compilation for (λ A : Type, true) with (F T T).
Vcpu Derive Compilation for @pair with (F T (F T (F T (F T T)))).
Vcpu Derive Compilation for (@inl bool) with (F T (F T T)).
Vcpu Derive Compilation for (@pair bool bool true) with (F T T).
(* Vcpu Derive Compilation for swap' with (F T (F R (F R (F T T)))). *)
Vcpu Derive Compilation for (λ b : bool, if b then false else true) with (F R T).
Vcpu Derive Compilation for (λ b : bool, if b then false else true) with (F T T).
Vcpu Derive Compilation for @fst with (F T (F T (F T T))).
Vcpu Derive Compilation for @snd with (F T (F T (F T T))).
Vcpu Derive Compilation for negb with (F T T) as negb.
Vcpu Derive Compilation for andb with (F T (F T T)) as andb.
Vcpu Derive Compilation for orb with (F T (F T T)) as orb.
Vcpu Derive Compilation for xorb with (F T (F T T)) as xorb.
Vcpu Derive Compilation for exchange with (F T (F T (F T T))) as exchange.
Vcpu Derive Compilation for (λ p : bool * bool, let (b_1, b_2) := p in b_1 && b_2) with (F T T).
Vcpu Derive Compilation for many_things_transform with (F T T) as many_things_transform.
Vcpu Derive Compilation for (λ b : bool, let b' := negb b in (b', xorb b' b)) with (F T T).
Vcpu Derive Compilation for flip with (F T (F R T)) as flip.
Vcpu Derive Compilation for flip_s with (F T (F R (F T T))) as flip_s.
Vcpu Derive Compilation for bv_not with (F R (F T T)) as bv_not.
(* Vcpu Derive Compilation for bv_add with (F R (F T (F T T))) as bv_add. *)

Print negb_orig.
Print negb_circuit.
Print negb_wf_circuit.
Print negb_eval_circuit.

Print flip_circuit.
Check flip_eval_circuit.

(* Print bv_add_orig.
Print bv_add_circuit.
About bv_add_eval_circuit.
About bv_add_wf_circuit. *)

Definition bv_add_orig :=
  (fix bv_add (n : nat) : vec bool n → vec bool n → bool * vec bool n :=
    match n as n0 return (vec bool n0 → vec bool n0 → bool * vec bool n0) with
    | 0 => λ bv_1 bv_2 : unit, let 'tt := bv_1 in let 'tt := bv_2 in (false, tt)
    | S n' =>
        λ bv_1 bv_2 : bool * vec bool n',
          let
          '(b_1, bv_1') := bv_1 in
          let
          '(b_2, bv_2') := bv_2 in
            let
            '(carry_in, add_bv_1'_bv_2') := bv_add n' bv_1' bv_2' in
            (orb_orig (andb_orig b_1 b_2) (andb_orig carry_in (orb_orig b_1 b_2)),
              (xorb_orig (xorb_orig b_1 b_2) carry_in, add_bv_1'_bv_2'))
    end)
     : ∀ n : nat, vec bool n → vec bool n → bool * vec bool n.

Definition bv_add_circuit :=
  (λ input_len : nat,
    fix bv_add_circuit (n : nat) :
        circuit input_len (vec_len bool bool_len bool_encode n)
        → circuit input_len (vec_len bool bool_len bool_encode n)
          → circuit input_len (bool_len + (vec_len bool bool_len bool_encode n + 0)) :=
      match
        n as n0
        return
          (circuit input_len (vec_len bool bool_len bool_encode n0)
          → circuit input_len (vec_len bool bool_len bool_encode n0)
            → circuit input_len (bool_len + (vec_len bool bool_len bool_encode n0 + 0)))
      with
      | 0 =>
          λ _ _ : circuit input_len unit_len,
            circuit_const input_len
              ((λ H : bool * unit, let (H0, H1) := H in bool_encode H0 +||+ unit_encode H1 +||+ [||]) (false, tt))
      | S n' =>
          λ bv_1_circuit bv_2_circuit : circuit input_len (bool_len + (vec_len bool bool_len bool_encode n' + 0)),
            circuit_comp
              (circuit_comp
                (circuit_comp
                    (circuit_combine
                      (circuit_suffix (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0)) + bool_len)
                          bool_len)
                      (circuit_combine
                          (circuit_combine
                            (circuit_comp
                                (circuit_suffix (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0)))
                                  bool_len)
                                (circuit_prefix
                                  (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0)) + bool_len)
                                  bool_len))
                            (circuit_combine
                                (circuit_comp
                                  (circuit_comp
                                      (circuit_comp_prefix (vec_len bool bool_len bool_encode n') 0
                                        (circuit_comp_suffix bool_len (vec_len bool bool_len bool_encode n' + 0)
                                            (circuit_suffix input_len
                                              (bool_len + (vec_len bool bool_len bool_encode n' + 0)))))
                                      (circuit_prefix
                                        (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0))) bool_len))
                                  (circuit_prefix
                                      (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0)) + bool_len)
                                      bool_len))
                                (circuit_const
                                  (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0)) + bool_len +
                                    bool_len)
                                  [||])))
                          (circuit_const
                            (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0)) + bool_len + bool_len)
                            [||])))
                    (circuit_combine
                      (circuit_suffix 0
                          (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0)) + bool_len))
                      (orb_circuit (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0)) + bool_len)
                          (andb_circuit
                            (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0)) + bool_len)
                            (circuit_comp
                                (circuit_comp
                                  (circuit_comp_prefix bool_len (vec_len bool bool_len bool_encode n' + 0)
                                      bv_1_circuit)
                                  (circuit_prefix input_len (bool_len + (vec_len bool bool_len bool_encode n' + 0))))
                                (circuit_prefix (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0)))
                                  bool_len))
                            (circuit_comp
                                (circuit_comp
                                  (circuit_comp_prefix bool_len (vec_len bool bool_len bool_encode n' + 0)
                                      bv_2_circuit)
                                  (circuit_prefix input_len (bool_len + (vec_len bool bool_len bool_encode n' + 0))))
                                (circuit_prefix (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0)))
                                  bool_len)))
                          (andb_circuit
                            (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0)) + bool_len)
                            (circuit_comp
                                (circuit_comp_prefix bool_len (vec_len bool bool_len bool_encode n' + 0)
                                  (circuit_suffix input_len (bool_len + (vec_len bool bool_len bool_encode n' + 0))))
                                (circuit_prefix (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0)))
                                  bool_len))
                            (orb_circuit
                                (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0)) + bool_len)
                                (circuit_comp
                                  (circuit_comp
                                      (circuit_comp_prefix bool_len (vec_len bool bool_len bool_encode n' + 0)
                                        bv_1_circuit)
                                      (circuit_prefix input_len (bool_len + (vec_len bool bool_len bool_encode n' + 0))))
                                  (circuit_prefix
                                      (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0))) bool_len))
                                (circuit_comp
                                  (circuit_comp
                                      (circuit_comp_prefix bool_len (vec_len bool bool_len bool_encode n' + 0)
                                        bv_2_circuit)
                                      (circuit_prefix input_len (bool_len + (vec_len bool bool_len bool_encode n' + 0))))
                                  (circuit_prefix
                                      (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0))) bool_len)))))))
                (circuit_combine
                    (circuit_suffix 0 (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0))))
                    (xorb_circuit (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0)))
                      (xorb_circuit (input_len + (bool_len + (vec_len bool bool_len bool_encode n' + 0)))
                          (circuit_comp
                            (circuit_comp_prefix bool_len (vec_len bool bool_len bool_encode n' + 0) bv_1_circuit)
                            (circuit_prefix input_len (bool_len + (vec_len bool bool_len bool_encode n' + 0))))
                          (circuit_comp
                            (circuit_comp_prefix bool_len (vec_len bool bool_len bool_encode n' + 0) bv_2_circuit)
                            (circuit_prefix input_len (bool_len + (vec_len bool bool_len bool_encode n' + 0)))))
                      (circuit_comp_prefix bool_len (vec_len bool bool_len bool_encode n' + 0)
                          (circuit_suffix input_len (bool_len + (vec_len bool bool_len bool_encode n' + 0)))))))
              (circuit_combine (circuit_suffix 0 input_len)
                (bv_add_circuit n'
                    (circuit_comp_prefix (vec_len bool bool_len bool_encode n') 0
                      (circuit_comp_suffix bool_len (vec_len bool bool_len bool_encode n' + 0) bv_1_circuit))
                    (circuit_comp_prefix (vec_len bool bool_len bool_encode n') 0
                      (circuit_comp_suffix bool_len (vec_len bool bool_len bool_encode n' + 0) bv_2_circuit))))
      end)
      : ∀ input_len n : nat,
          circuit input_len (vec_len bool bool_len bool_encode n)
          → circuit input_len (vec_len bool bool_len bool_encode n)
            → circuit input_len (bool_len + (vec_len bool bool_len bool_encode n + 0)).

Axiom bv_add_eval_circuit
      : ∀ (input_len : nat) (input_encode : vector bool input_len) (n : nat)
          (H : vec bool n) (H0 : circuit input_len (vec_len bool bool_len bool_encode n)),
        circuit_wf H0
        → circuit_eval H0 input_encode = vec_encode bool bool_len bool_encode n H
          → ∀ (H1 : vec bool n) (H2 : circuit input_len (vec_len bool bool_len bool_encode n)),
              circuit_wf H2
              → circuit_eval H2 input_encode = vec_encode bool bool_len bool_encode n H1
                → circuit_eval (bv_add_circuit input_len n H0 H2) input_encode =
                  (λ H3 : bool * vec bool n,
                    let (H4, H5) := H3 in bool_encode H4 +||+ vec_encode bool bool_len bool_encode n H5 +||+ [||])
                    (bv_add_orig n H H1).

Axiom bv_add_wf_circuit
  : ∀ (input_len n : nat) (H : circuit input_len (vec_len bool bool_len bool_encode n)),
      circuit_wf H
      → ∀ H0 : circuit input_len (vec_len bool bool_len bool_encode n),
          circuit_wf H0 → circuit_wf (bv_add_circuit input_len n H H0).

Lemma transparent_eq_nat :
  ∀ {n m : nat},
  n = m →
  n = m.
Proof.
  intros n m H_n_m. destruct (Nat.eq_dec n m) as [H | H].
  - apply H.
  - exfalso. apply H, H_n_m.
Defined.

Lemma bool_len_def :
  ∀ n,
  vec_len bool bool_len bool_encode n = n.
Proof.
  intros n. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. unfold prod_len, bool_len. lia.
Defined.

Definition final_bv_add_circuit n : circuit (n + n) (1 + n) :=
  rew <- [fun m => circuit (n + n) (bool_len + m)] transparent_eq_nat (plus_n_O n) in
  rew [fun m => circuit (n + n) (bool_len + (m + 0))] transparent_eq_nat (bool_len_def n) in
    bv_add_circuit (n + n) n
      (rew <- [fun m => circuit (n + n) m] transparent_eq_nat (bool_len_def n) in circuit_prefix n n)
      (rew <- [fun m => circuit (n + n) m] transparent_eq_nat (bool_len_def n) in circuit_suffix n n).

Compute (circuit_wires (final_bv_add_circuit 2)).
Compute circuit_eval (final_bv_add_circuit 4) [|false; true; false; true; false; true; true; false|].

(* From Equations Require Export Equations.
From Equations Require Export TransparentEquations. *)

Lemma circuit_wf_final_bv_add_circuit :
  ∀ n,
  circuit_wf (final_bv_add_circuit n).
Proof.
  intros n. unfold final_bv_add_circuit.
  remember (transparent_eq_nat (plus_n_O n)) as e.
  destruct (Nat.eq_dec n (n + 0)).
Abort.

Definition final_bv_add_circuit' n : circuit (vec_len bool bool_len bool_encode n + vec_len bool bool_len bool_encode n) (bool_len + (vec_len bool bool_len bool_encode n + 0)) :=
  bv_add_circuit (vec_len bool bool_len bool_encode n + vec_len bool bool_len bool_encode n) n (circuit_prefix (vec_len bool bool_len bool_encode n) (vec_len bool bool_len bool_encode n))(circuit_suffix (vec_len bool bool_len bool_encode n) (vec_len bool bool_len bool_encode n)).

Lemma circuit_wf_final_bv_add_circuit' :
  ∀ n,
  circuit_wf (final_bv_add_circuit' n).
Proof.
  intros n. unfold final_bv_add_circuit'. apply bv_add_wf_circuit.
  - apply circuit_wf_circuit_prefix.
  - apply circuit_wf_circuit_suffix.
Qed.

Fixpoint vec_to_vector {A n} : vec A n → vector A n :=
  match n with
  | 0 => λ '(tt), [||]
  | S n' => λ '(x, v'), x :||: vec_to_vector v'
  end.

Lemma circuit_eval_final_bv_add_circuit' :
  ∀ n (bv_1 bv_2 : vec bool (vec_len bool bool_len bool_encode n)),
  let '(carry, bv_res) := bv_add (vec_len bool bool_len bool_encode n) bv_1 bv_2 in
  circuit_eval (final_bv_add_circuit' n) (vec_to_vector bv_1 +||+ vec_to_vector bv_2) =
  [|carry|] +||+ (vec_to_vector bv_res +||+ [||]).
Proof.
  intros n bv_1 bv_2. remember ((bv_add (vec_len bool bool_len bool_encode n) bv_1 bv_2)) as bv_res eqn:H_bv_res. destruct bv_res as [carry add_bv_1_bv_2].
  unfold final_bv_add_circuit'.
  pose (bv_1' := rew [λ m, vec bool m] transparent_eq_nat (bool_len_def n) in bv_1); pose (bv_2' := rew [λ m, vec bool m] transparent_eq_nat (bool_len_def n) in bv_2).
  assert (H_1 :
    circuit_eval
      (circuit_prefix (vec_len bool bool_len bool_encode n) (vec_len bool bool_len bool_encode n))
      (vec_to_vector bv_1 +||+ vec_to_vector bv_2) =
    vec_encode bool bool_len bool_encode n bv_1'
  ). {
    rewrite circuit_eval_circuit_prefix. rewrite vector_prefix_vector_app. subst bv_1'.
    clear - n bv_1. revert bv_1; induction n as [| n' IH]; intros bv_1; admit.
  }
  assert (H_2 :
    circuit_eval
      (circuit_suffix (vec_len bool bool_len bool_encode n) (vec_len bool bool_len bool_encode n))
      (vec_to_vector bv_1 +||+ vec_to_vector bv_2) =
    vec_encode bool bool_len bool_encode n bv_2'
  ). {
    rewrite circuit_eval_circuit_suffix. rewrite vector_suffix_vector_app. subst bv_2'.
    clear - n bv_2. revert bv_2; induction n as [| n' IH]; intros bv_2; admit.
  }
  specialize (bv_add_eval_circuit (vec_len bool bool_len bool_encode n + vec_len bool bool_len bool_encode n) (vec_to_vector bv_1 +||+ vec_to_vector bv_2) n bv_1' (circuit_prefix _ _) (circuit_wf_circuit_prefix _ _) H_1 bv_2' (circuit_suffix _ _) (circuit_wf_circuit_suffix _ _) H_2) as H.
  rewrite H. destruct (bv_add_orig n bv_1' bv_2') as [carry' add_bv_1'_bv_2'].
  f_equal > [| f_equal].
  - admit.
  - admit.
Admitted.

Fixpoint bv_to_nat (n : nat) (m : nat) : vec bool n → nat :=
  match n with
  | 0 => λ tt, m
  | S n' => λ '(b, bv'), bv_to_nat n' (m * 2 + (if b then 1 else 0)) bv'
  end.

Compute bv_to_nat 4 0 (false, (true, (false, (true, tt)))).

Lemma bv_to_nat_add :
  ∀ n m_1 m_2 m_3 m_4 (bv_1 bv_2 : vec bool n),
  m_1 + m_2 = m_3 + m_4 →
  bv_to_nat n m_1 bv_1 + bv_to_nat n m_2 bv_2 = bv_to_nat n m_3 bv_1 + bv_to_nat n m_4 bv_2.
Proof.
  intros n m_1 m_2 m_3 m_4 bv_1 bv_2 H_m. revert m_1 m_2 m_3 m_4 H_m; induction n as [| n' IH]; intros m_1 m_2 m_3 m_4 H_m.
  - destruct bv_1 as [], bv_2 as []. simpl. lia.
  - destruct bv_1 as [b_1 bv_1'], bv_2 as [b_2 bv_2']. simpl.
    apply IH. lia.
Qed.

Lemma bv_add_spec :
  ∀ n m (bv_1 bv_2 : vec bool n),
  let '(carry, bv_res) := bv_add n bv_1 bv_2 in
  bv_to_nat n (m * 2 + (if carry then 1 else 0)) bv_res = bv_to_nat n m bv_1 + bv_to_nat n m bv_2.
Proof.
  intros n m bv_1 bv_2. revert m; induction n as [| n' IH]; intros m.
  - destruct bv_1 as [], bv_2 as []. simpl. lia.
  - destruct bv_1 as [b_1 bv_1'], bv_2 as [b_2 bv_2']. simpl.
    specialize (IH bv_1' bv_2'). destruct (bv_add n' bv_1' bv_2') as (carry', bv_res').
    destruct b_1 as [|], b_2 as [|], carry' as [|]; simpl.
    + rewrite IH. reflexivity.
    + rewrite IH. reflexivity.
    + specialize (IH (m * 2)) as IH.
      specialize (bv_to_nat_add n' ((m * 2 * 2 + 1) + 1) (m * 2) (m * 2 * 2 + 1) (m * 2 + 1) bv_res' bv_1' ltac:(lia)) as H.
      ltac1:(replace ((m * 2 + 1) * 2 + 0) with (m * 2 * 2 + 1 + 1) by lia). ltac1:(replace (m * 2 + 0) with (m * 2) by lia). lia.
    + specialize (IH (m * 2)) as IH.
      specialize (bv_to_nat_add n' (m * 2 * 2 + 1) (m * 2) (m * 2 * 2) (m * 2 + 1) bv_res' bv_1' ltac:(lia)) as H.
      ltac1:(replace ((m * 2 + 0) * 2 + 1) with (m * 2 * 2 + 1) by lia). ltac1:(replace (m * 2 + 0) with (m * 2) by lia). ltac1:(replace (m * 2 * 2 + 0) with (m * 2 * 2) in IH by lia). lia.
    + specialize (IH (m * 2)) as IH.
      specialize (bv_to_nat_add n' (m * 2 * 2 + 1 + 1) (m * 2) (m * 2 * 2 + 1) (m * 2 + 1) bv_res' bv_2' ltac:(lia)) as H.
      ltac1:(replace ((m * 2 + 1) * 2 + 0) with (m * 2 * 2 + 1 + 1) by lia). ltac1:(replace (m * 2 + 0) with (m * 2) by lia). lia.
    + specialize (IH (m * 2)) as IH.
      specialize (bv_to_nat_add n' (m * 2 * 2 + 1) (m * 2) (m * 2 * 2) (m * 2 + 1) bv_res' bv_2' ltac:(lia)) as H.
      ltac1:(replace ((m * 2 + 0) * 2 + 1) with (m * 2 * 2 + 1) by lia). ltac1:(replace (m * 2 + 0) with (m * 2) by lia). ltac1:(replace (m * 2 * 2 + 0) with (m * 2 * 2) in IH by lia). lia.
    + rewrite IH. reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma final_bv_add_circuit'_spec :
  ∀ n (bv_1 bv_2 : vec bool (vec_len bool bool_len bool_encode n)),
  let '(carry, bv_res) := bv_add _ bv_1 bv_2 in
  circuit_eval (final_bv_add_circuit' n) (vec_to_vector bv_1 +||+ vec_to_vector bv_2) =
  [|carry|] +||+ (vec_to_vector bv_res +||+ [||]) ∧
  bv_to_nat _ (if carry then 1 else 0) bv_res = bv_to_nat _ 0 bv_1 + bv_to_nat _ 0 bv_2.
Proof.
  intros n bv_1 bv_2.
  specialize (circuit_eval_final_bv_add_circuit' _ bv_1 bv_2) as H_1.
  specialize (bv_add_spec _ 0 bv_1 bv_2) as H_2.
  remember ((bv_add (vec_len bool bool_len bool_encode n) bv_1 bv_2)) as bv_res eqn:H_bv_res. destruct bv_res as [carry add_bv_1_bv_2]. split.
  - auto.
  - auto.
Qed.

