Require Import Btauto.
Require Import Lia.

#[global] Obligation Tactic := idtac.

Require Coq.Lists.List.
Import List.ListNotations.

Open Scope list_scope.
Open Scope bool_scope.

Infix "^^" := xorb (at level 40, left associativity) : bool_scope.

Definition nandb b1 b2 := negb (b1 && b2).

Lemma nandb_negb : forall b, nandb b b = negb b.
Proof.
  intros b. unfold nandb. btauto.
Qed.

Lemma list_cons_app :
  forall {A} (x : A) l,
  [x] ++ l = x :: l.
Proof.
  auto.
Qed.

Fixpoint list_forall {A} f (l : list A) :=
  match l with
  | [] => True
  | x :: l' => f x /\ list_forall f l'
  end.

Lemma list_forall_ext :
  forall {A} f1 f2 (l : list A),
  (forall x, f1 x <-> f2 x) ->
  list_forall f1 l <-> list_forall f2 l.
Proof.
  intros A f1 f2 l H. induction l as [ | x l' IH].
  - intuition auto.
  - specialize (H x). simpl. intuition auto.
Qed.

Lemma list_forall_incr :
  forall {A} (f1 f2 : _ -> Prop) (l : list A),
  list_forall f1 l ->
  (forall x, f1 x -> f2 x) ->
  list_forall f2 l.
Proof.
  intros A f1 f2 l H1 H2. induction l as [ | x l' IH].
  - intuition auto.
  - specialize (H2 x). simpl. simpl in H1. intuition auto.
Qed.

Lemma list_forall_coarse :
  forall {A} (f : _ -> Prop) (l : list A),
  (forall x, f x) ->
  list_forall f l.
Proof.
  intros A f l H. induction l as [ | x l' IH].
  - simpl. auto.
  - specialize (H x). simpl. auto.
Qed.

Lemma list_forall_list_seq :
  forall f s n,
  list_forall f (List.seq s n) <-> forall i, i < n -> f (s + i).
Proof.
  intros f s n. generalize dependent s. induction n as [ | n' IH]; intros s.
  - simpl. intuition lia.
  - simpl. rewrite IH. split.
    + intros (H1 & H2). intros i H3. destruct i as [ | i'].
      * rewrite PeanoNat.Nat.add_0_r. auto.
      * rewrite PeanoNat.Nat.add_succ_r. apply H2. lia.
    + intros H1. split.
      * specialize (H1 0 ltac:(lia)). rewrite PeanoNat.Nat.add_0_r in H1. auto.
      * intros i H2. specialize (H1 (S i) ltac:(lia)). rewrite PeanoNat.Nat.add_succ_r in H1. auto.
Qed.

Fixpoint list_forall_i_aux {A} f i (l : list A) :=
  match l with
  | [] => True
  | x :: l' => f i x /\ list_forall_i_aux f (S i) l'
  end.

Definition list_forall_i {A} f (l : list A) := list_forall_i_aux f 0 l.

Lemma list_forall_i_aux_ext :
  forall {A} f1 f2 s (l : list A),
  (forall i x, f1 i x <-> f2 i x) ->
  list_forall_i_aux f1 s l <-> list_forall_i_aux f2 s l.
Proof.
  intros A f1 f2 s l H. generalize dependent s. induction l as [ | x l' IH]; intros s.
  - simpl. intuition auto.
  - specialize (IH (S s)). simpl. rewrite H. intuition auto.
Qed.

Lemma list_forall_i_ext :
  forall {A} f1 f2 (l : list A),
  (forall i x, f1 i x <-> f2 i x) ->
  list_forall_i f1 l <-> list_forall_i f2 l.
Proof.
  unfold list_forall_i. intros A f1 f2 l. apply (list_forall_i_aux_ext f1 f2 0 l).
Qed.

Lemma list_forall_i_aux_incr :
  forall {A} (f1 f2 : _ -> _ -> Prop) s (l : list A),
  list_forall_i_aux f1 s l ->
  (forall i x, f1 i x -> f2 i x) ->
  list_forall_i_aux f2 s l.
Proof.
  intros A f1 f2 s l H1 H2. generalize dependent s. induction l as [ | x l' IH]; intros s.
  - simpl. intuition auto.
  - specialize (IH (S s)). simpl. intuition auto.
Qed.

Lemma list_forall_i_incr :
  forall {A} (f1 f2 : _ -> _ -> Prop) (l : list A),
  list_forall_i f1 l ->
  (forall i x, f1 i x -> f2 i x) ->
  list_forall_i f2 l.
Proof.
  unfold list_forall_i. intros A f1 f2 l H1 H2. apply (list_forall_i_aux_incr f1 f2 0 l H1 H2).
Qed.

Lemma list_forall_i_aux_shift :
  forall {A} f s t (l : list A),
  list_forall_i_aux f (t + s) l <-> list_forall_i_aux (fun i x => f (t + i) x) s l.
Proof.
  intros A f s t l. generalize dependent s. induction l as [ | x l' IH]; intros s.
  - simpl. intuition auto.
  - specialize (IH (S s)). simpl. rewrite <- PeanoNat.Nat.add_succ_comm in IH. intuition auto.
Qed.

Lemma list_forall_list_forall_i :
  forall {A} f (l : list A),
  list_forall f l <-> list_forall_i (fun _ => f) l.
Proof.
  intros A f l. unfold list_forall_i. induction l as [ | x l' IH].
  - intuition auto.
  - simpl. rewrite (list_forall_i_aux_shift _ 0 1). intuition auto.
Qed.

Lemma list_forall_i_aux_equiv :
  forall {A} f s (l : list A),
  list_forall_i_aux f s l <-> list_forall_i (fun i x => f (s + i) x) l.
Proof.
  intros A f s l. unfold list_forall_i. generalize dependent s. induction l as [ | x l' IH]; intros s.
  - simpl. intuition auto.
  - specialize (IH (S s)). simpl. rewrite (list_forall_i_aux_shift _ 0 1).
    simpl. rewrite PeanoNat.Nat.add_0_r. rewrite IH. apply and_iff_compat_l.
    apply list_forall_i_ext. intros i y. rewrite PeanoNat.Nat.add_succ_comm. intuition auto.
Qed.

Lemma list_forall_i_aux_app :
  forall {A} f s (l1 l2 : list A),
  list_forall_i_aux f s (l1 ++ l2) <-> list_forall_i_aux f s l1 /\ list_forall_i_aux f (s + length l1) l2.
Proof.
  intros A f s l1 l2. generalize dependent s. induction l1 as [ | x l1' IH]; intros s.
  - rewrite PeanoNat.Nat.add_comm. simpl. intuition auto.
  - specialize (IH (S s)). simpl. rewrite <- PeanoNat.Nat.add_succ_comm. intuition auto.
Qed.

Lemma list_forall_i_app :
  forall {A} f (l1 l2 : list A),
  list_forall_i f (l1 ++ l2) <-> list_forall_i f l1 /\ list_forall_i_aux f (length l1) l2.
Proof.
  unfold list_forall_i. intros A f l1 l2. apply (list_forall_i_aux_app f 0 l1 l2).
Qed.

Lemma list_forall_i_aux_map :
  forall {A B} f s (g : A -> B) (l : list A),
  list_forall_i_aux f s (List.map g l) <-> list_forall_i_aux (fun i x => f i (g x)) s l.
Proof.
  intros A B f s g l. generalize dependent s. induction l as [ | x l' IH]; intros s.
  - simpl. intuition auto.
  - specialize (IH (S s)). simpl. intuition auto.
Qed.

Fixpoint list_forallb_i_aux {A} f i (l : list A) :=
  match l with
  | [] => true
  | x :: l' => f i x && list_forallb_i_aux f (S i) l'
  end.

Definition list_forallb_i {A} f (l : list A) := list_forallb_i_aux f 0 l.

Lemma list_forallb_i_aux_reflect :
  forall {A} f g i (l : list A),
  (forall j x, Bool.reflect (f j x) (g j x)) ->
  Bool.reflect (list_forall_i_aux f i l) (list_forallb_i_aux g i l).
Proof.
  intros A f g i l H. generalize dependent i. induction l as [ | x l' IH]; intros i.
  - simpl. apply Bool.ReflectT. auto.
  - simpl. specialize (IH (S i)). specialize (H i x).
    apply Bool.reflect_iff in IH. apply Bool.reflect_iff in H. apply Bool.iff_reflect. intuition auto.
Qed.

Lemma list_forallb_i_reflect :
  forall {A} f g (l : list A),
  (forall j x, Bool.reflect (f j x) (g j x)) ->
  Bool.reflect (list_forall_i f l) (list_forallb_i g l).
Proof.
  intros A f g l H. apply (list_forallb_i_aux_reflect _ _ _ _ H).
Qed.

Lemma list_fold_left_ext_precise :
  forall {A B} f1 f2 (l : list B) (x : A),
  (forall y, list_forall (fun z => f1 y z = f2 y z) l) ->
  List.fold_left f1 l x = List.fold_left f2 l x.
Proof.
  intros A B f1 f2 l x H. generalize dependent x. induction l as [ | z l' IH]; intros x.
  - auto.
  - simpl in H. simpl. rewrite (proj1 (H x)). apply IH. intros y. specialize (H y). intuition auto.
Qed.

Lemma list_fold_left_ext :
  forall {A B} f1 f2 (l : list B) (x : A),
  (forall y z, f1 y z = f2 y z) ->
  List.fold_left f1 l x = List.fold_left f2 l x.
Proof.
  intros A B f1 f2 l x H. apply list_fold_left_ext_precise. intros y. apply list_forall_coarse. auto.
Qed.

Lemma list_fold_left_morph :
  forall {A B C} f (g : A -> C) (l : list B) (x : A),
  g (List.fold_left (fun y z => f (g y) z) l x) = List.fold_left (fun y z => g (f y z)) l (g x).
Proof.
  intros A B C f g l. induction l as [ | y l' IH]; intros x.
  - auto.
  - simpl. apply IH.
Qed.

Lemma list_fold_left_app_shift :
  forall {A B} f (l1 : list B) (l2 : list A),
  List.fold_left (fun l y => l ++ [f l y]) l1 l2 =
  l2 ++ List.fold_left (fun l y => l ++ [f (l2 ++ l) y]) l1 [].
Proof.
  intros A B f l1. induction l1 as [ | x l1' IH]; intros l2.
  - simpl. apply List.app_nil_end.
  - simpl. rewrite List.app_nil_r. specialize (IH (l2 ++ [f l2 x])). rewrite IH; clear IH.
    rewrite <- List.app_assoc. f_equal. simpl.
    rewrite (list_fold_left_ext _ (fun y z => List.tl ((f l2 x :: y) ++ [f (l2 ++ f l2 x :: y) z]))).
    + rewrite (list_fold_left_morph (fun l3 z => List.tl (l3 ++ [f (l2 ++ l3) z])) (cons (f l2 x))).
      cut (forall e,
        List.fold_left (fun l3 z => f l2 x :: List.tl (l3 ++ [f (l2 ++ l3) z])) l1' (f l2 x :: e) =
        List.fold_left (fun l3 z => l3 ++ [f (l2 ++ l3) z]) l1' (f l2 x :: e)).
      * intros H. apply (H []).
      * induction l1' as [ | z l1'' IH]; intros e.
        -- auto.
        -- simpl. apply IH.
    + intros l3 z. simpl. rewrite <- List.app_assoc. auto.
Qed.

Lemma list_map_list_fold_left :
  forall {A B} (f : A -> B) l,
  List.map f l = List.fold_left (fun y z => y ++ [f z]) l [].
Proof.
  intros A B f l. cut (forall s, s ++ List.map f l = List.fold_left (fun y z => y ++ [f z]) l s).
  - intros H. apply (H []).
  - induction l as [ | x l' IH]; intros s.
    + simpl. apply List.app_nil_r.
    + simpl. rewrite <- IH. rewrite <- List.app_assoc. auto.
Qed.

Lemma list_fold_left_list_seq_shift :
  forall {A} f s t n (x : A),
  List.fold_left f (List.seq (s + t) n) x = List.fold_left (fun y z => f y (t + z)) (List.seq s n) x.
Proof.
  intros A f s t n. generalize dependent s. induction n as [ | n' IH]; intros s x.
  - auto.
  - specialize (IH (S s) (f x (s + t))). simpl. rewrite (PeanoNat.Nat.add_comm t s). simpl in IH. apply IH.
Qed.

Lemma list_fold_left_list_map :
  forall {A B C} f (g : B -> C) l (x : A),
  List.fold_left f (List.map g l) x = List.fold_left (fun y z => f y (g z)) l x.
Proof.
  intros A B C f g l. induction l; intros x.
  - auto.
  - simpl. auto.
Qed.

Lemma list_fold_left_app_list_map_singleton :
  forall {A} (l : list A),
  List.fold_left (@app A) (List.map (fun x => [x]) l) [] = l.
Proof.
  intros A l. cut (forall init, List.fold_left (@app A) (List.map (fun x => [x]) l) init = init ++ l).
  - intros H. apply H.
  - induction l as [ | x l' IH]; intros init.
    + simpl. apply List.app_nil_end.
    + simpl. rewrite IH. apply List.app_assoc_reverse.
Qed.

Lemma list_map_ext_precise :
  forall {A B} (f1 f2 : _ -> B) (l : list A),
  list_forall (fun x => f1 x = f2 x) l ->
  List.map f1 l = List.map f2 l.
Proof.
  intros A B f1 f2 l H. induction l as [ | z l' IH].
  - auto.
  - simpl in H. simpl. rewrite (proj1 H). f_equal. apply IH. intuition auto.
Qed.

Fixpoint list_init_aux {A} f s n : list A :=
  match n with
  | 0 => []
  | S n' => f s :: list_init_aux f (S s) n'
  end.

Definition list_init {A} f n : list A := list_init_aux f 0 n.

Lemma length_list_init_aux :
  forall {A} (f : _ -> A) s n,
  length (list_init_aux f s n) = n.
Proof.
  intros A f s n. generalize dependent s. induction n as [ | n' IH]; intros s.
  - auto.
  - simpl. f_equal. apply IH.
Qed.

Lemma length_list_init :
  forall {A} (f : _ -> A) n,
  length (list_init f n) = n.
Proof.
  intros A f n. apply (length_list_init_aux _ 0 _).
Qed.

Lemma list_init_aux_list_map_list_seq :
  forall {A} (f : _ -> A) s n,
  list_init_aux f s n = List.map f (List.seq s n).
Proof.
  intros A f s n. generalize dependent s. induction n as [ | n' IH]; intros s.
  - auto.
  - simpl. f_equal. apply IH.
Qed.

Lemma list_init_list_map_list_seq :
  forall {A} (f : _ -> A) n,
  list_init f n = List.map f (List.seq 0 n).
Proof.
  intros A f n. apply list_init_aux_list_map_list_seq.
Qed.

Lemma list_forall_i_aux_i_list_init_aux :
  forall {A} f s (g : _ -> A) n,
  list_forall_i_aux f s (list_init_aux g s n) <-> forall i, i < n -> f (s + i) (g (s + i)).
Proof.
  intros A f s g n. generalize dependent s. induction n as [ | n' IH]; intros s.
  - simpl. intuition lia.
  - simpl. specialize (IH (S s)). rewrite IH. split.
    + intros (H1 & H2). intros i H3. destruct i as [ | i'].
      * rewrite ? PeanoNat.Nat.add_0_r. auto.
      * rewrite ? PeanoNat.Nat.add_succ_r. apply H2. lia.
    + intros H1. split.
      * specialize (H1 0 ltac:(lia)). rewrite ? PeanoNat.Nat.add_0_r in H1. auto.
      * intros i H2. specialize (H1 (S i) ltac:(lia)). rewrite ? PeanoNat.Nat.add_succ_r in H1. auto.
Qed.

Lemma list_forall_i_list_init :
  forall {A} f (g : _ -> A) n,
  list_forall_i f (list_init g n) <-> forall i, i < n -> f i (g i).
Proof.
  intros A f g n. apply (list_forall_i_aux_i_list_init_aux _ 0 _ _).
Qed.

Lemma list_fold_left_list_init_aux :
  forall {A B} f (g : _ -> B) s n (x : A),
  List.fold_left f (list_init_aux g s n) x = List.fold_left (fun y z => f y (g z)) (List.seq s n) x.
Proof.
  intros A B f g s n x. generalize dependent x. generalize dependent s. induction n as [ | n' IH]; intros s x.
  - auto.
  - apply IH.
Qed.

Lemma list_fold_left_list_init :
  forall {A B} f (g : _ -> B) n (x : A),
  List.fold_left f (list_init g n) x = List.fold_left (fun y z => f y (g z)) (List.seq 0 n) x.
Proof.
  intros A B f g n x. apply list_fold_left_list_init_aux.
Qed.

Definition list_select {A} values indices (default : A) :=
  List.map (fun i => List.nth i values default) indices.

Lemma length_list_select :
  forall {A} values indices (default : A),
  length (list_select values indices default) = length indices.
Proof.
  intros A values indices default. unfold list_select. apply List.map_length.
Qed.

Lemma list_select_app_1_seq :
  forall {A} values_1 values_2 (default : A),
  list_select (values_1 ++ values_2) (List.seq 0 (length values_1)) default = values_1.
Proof.
  intros A values_1 values_2 default. unfold list_select. induction values_1 as [ | x values_1' IH].
  - auto.
  - simpl. rewrite <- List.seq_shift. rewrite List.map_map. rewrite IH. auto.
Qed.

Lemma list_select_app_2_seq :
  forall {A} values_1 values_2 (default : A),
  list_select (values_1 ++ values_2) (List.seq (length values_1) (length values_2)) default = values_2.
Proof.
  intros A values_1 values_2 default. unfold list_select. induction values_1 as [ | x values_1' IH].
  - simpl. rewrite <- (list_select_app_1_seq values_2 [] default) at 2. rewrite List.app_nil_r. auto.
  - simpl. rewrite <- List.seq_shift. rewrite List.map_map. rewrite IH. auto.
Qed.

Lemma list_select_com :
  forall {A} l1 l2 l3 (default : A),
  list_forall (fun i => i < length l2) l3 ->
  list_select l1 (list_select l2 l3 0) default =
  list_select (list_select l1 l2 default) l3 default.
Proof.
  intros A l1 l2 l3 default H. unfold list_select. rewrite List.map_map. apply list_map_ext_precise.
  apply (list_forall_incr _ _ _ H). intros i H1. apply List.nth_nth_nth_map. auto.
Qed.

Fixpoint list_fold_left2 {A B C} (f : A -> B -> C -> A) (l1 : list B) (l2 : list C) (x : A) : A :=
  match l1, l2 with
  | y :: l1', z :: l2' => list_fold_left2 f l1' l2' (f x y z)
  | _, _ => x
  end.

Fixpoint list_fold_right2 {A B C} (f : B -> C -> A -> A) (x : A) (l1 : list B) (l2 : list C) : A :=
  match l1, l2 with
  | y :: l1', z :: l2' => f y z (list_fold_right2 f x l1' l2')
  | _, _ => x
  end.

Fixpoint nat_list_assoc {A} n l (default : A) :=
  match l with
  | [] => default
  | (m, x) :: l' => if Nat.eqb m n then x else nat_list_assoc n l' default
  end.

Fixpoint nat_list_mem n l :=
  match l with
  | [] => false
  | m :: l' => Nat.eqb m n || nat_list_mem n l'
  end.
