Import /Logic.
Import /Induction.
Import /Eq.

Axiom set_from_func_unfold: ∀ A: U, ∀ f: A -> U, ∀ a: A, a ∈ (set_from_func A f) -> f a.
Axiom set_from_func_fold: ∀ A: U, ∀ f: A -> U, ∀ a: A, f a -> a ∈ (set_from_func A f).
Suggest hyp default apply set_from_func_unfold in $n; a ∈ {b | f b} => f a.
Suggest goal default apply set_from_func_fold; a ∈ {b | f b} => f a.

Theorem empty_intro: ∀ A: U, ∀ a: A, a ∈ {} -> False.
Proof. intros. auto_set. Qed.
Suggest hyp default chain (apply empty_intro in $n) (apply (False_ind $n ?)); Contradiction.
Todo eq_set_empty: ∀ A: U, ∀ S: set A, S = {} -> ∀ a: A, ~ a ∈ S.
Todo empty_set_eq: ∀ A: U, ∀ S: set A, (∀ x: A, ~ x ∈ S) -> S = {}.
Suggest goal default apply empty_set_eq; Trivial.

Theorem singleton_unfold: ∀ A: U, ∀ a b: A, b ∈ {a} -> a = b.
Proof. intros. auto_set. Qed.
Theorem singleton_fold: ∀ A: U, ∀ a b: A, a = b -> b ∈ {a}. 
Proof. intros. auto_set. Qed.
Suggest hyp default apply singleton_unfold in $n; a ∈ {b} => a = b.
Suggest goal default apply singleton_fold; a ∈ {b} => a = b.

Theorem union_unfold: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∪ y -> a ∈ x ∨ a ∈ y.
Proof. intros. auto_set. Qed.
Theorem union_fold: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∨ a ∈ y -> a ∈ x ∪ y.
Proof. intros. auto_set. Qed.
Suggest hyp default apply union_unfold in $n; a ∈ x ∪ y => a ∈ x ∨ a ∈ y.
Suggest goal default apply union_fold; a ∈ x ∪ y => a ∈ x ∨ a ∈ y.

Theorem intersection_unfold: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∩ y -> a ∈ x ∧ a ∈ y.
Proof. intros. auto_set. Qed.
Theorem intersection_fold: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∧ a ∈ y -> a ∈ x ∩ y.
Proof. intros. auto_set. Qed.
Suggest hyp default apply intersection_unfold in $n; a ∈ x ∩ y => a ∈ x ∧ a ∈ y.
Suggest goal default apply intersection_fold; a ∈ x ∩ y => a ∈ x ∧ a ∈ y.
Theorem intersection_intro: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∩ y ↔ a ∈ x ∧ a ∈ y.
Proof. intros. auto_set. Qed.

Theorem setminus_unfold: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∖ y -> a ∈ x ∧ (a ∈ y -> False).
Proof. intros. auto_set. Qed.
Theorem setminus_fold: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∧ (a ∈ y -> False) -> a ∈ x ∖ y.
Proof. intros. auto_set. Qed.
Suggest hyp default apply setminus_unfold in $n; a ∈ x ∖ y => a ∈ x ∧ ~ a ∈ y.
Suggest goal default apply setminus_fold; a ∈ x ∖ y => a ∈ x ∧ ~ a ∈ y.

Theorem included_unfold: ∀ A: U, ∀ x y: set A, x ⊆ y -> (∀ a: A, a ∈ x -> a ∈ y).
Proof. intros. auto_set. Qed.
Axiom included_fold: ∀ A: U, ∀ x y: set A, (∀ a: A, a ∈ x -> a ∈ y) -> x ⊆ y.
Suggest hyp default apply included_unfold in $n; a ⊆ b => ∀ x: T, x ∈ a -> x ∈ b.
Suggest goal default apply included_fold; a ⊆ b => ∀ x: T, x ∈ a -> x ∈ b.
Todo included_trans: ∀ A: U, ∀ x y z: set A, x ⊆ y -> y ⊆ z -> x ⊆ z.

Theorem set_equality: ∀ A: U, ∀ x y: set A, x ⊆ y -> y ⊆ x -> x = y.
Proof. intros. auto_set. Qed.
Suggest goal default apply set_equality; A = B => A ⊆ B ∧ B ⊆ A.

Theorem set_equality_forall: ∀ A: U, ∀ x y: set A, (∀ a: A, a ∈ x ↔ a ∈ y) -> x = y.
Proof.
    intros.
    apply set_equality.
    apply included_fold.
    intros.
    add_hyp H_ex := (H (a)).
    assumption.
    apply included_fold.
    intros.
    add_hyp H_ex := (H (a)).
    assumption.
Qed.

Axiom set_equality_unfold: ∀ A: U, ∀ x y: set A, x = y -> x ⊆ y ∧ y ⊆ x.

Theorem minus_of_subset: ∀ A: U, ∀ x y: set A, x ⊆ y -> x ∪ y ∖ x = y.
Proof. intros. auto_set. Qed.

Theorem non_empty_has_member: ∀ A: U, ∀ S: set A, ~ S = {} -> ∃ x: A, x ∈ S.
Proof.
    intros.
    apply NNPP.
    intros.
    apply not_exists_imply_forall in H0.
    apply H.
    apply set_equality.
    auto_set.
    apply included_fold.
    intros.
    apply H0 in H1.
    assumption.
Qed.
Suggest hyp apply non_empty_has_member in $n; ~ S = {} => ∃ x, x ∈ S.

Theorem empty_finite : ∀ A: U, finite (set_empty A).
Proof. intros. auto_set. Qed.
Theorem finite_add : ∀ A: U, ∀ x: set A, finite x -> ∀ a: A, (a ∈ x -> False) -> finite (x ∪ {a}).
Proof. intros. auto_set. Qed.

Theorem finite_included : ∀ A: U, ∀ x y: set A, finite y -> x ⊆ y -> finite x.
Proof. intros. auto_set. Qed.

Theorem empty_len: ∀ A: U, |set_empty A| = 0.
Proof. intros. lia. Qed.
Axiom empty_len_unique: ∀ A: U, ∀ S: set A, |S| = 0 -> S = {}.
Suggest hyp apply empty_len_unique in $n; |S| = 0 => S = {}.
Axiom finite_add_len: ∀ A: U, ∀ S: set A, finite S -> ∀ a: A, ~ a ∈ S -> |S ∪ {a}| = |S| + 1.
Axiom finite_len_ge_0: ∀ A: U, ∀ S: set A, finite S -> 0 ≤ |S|.
Axiom infinite_len_const: ∀ A: U, ∀ S: set A, ~ finite S -> |S| = -1.

Todo len_ge_0_finite: ∀ A: U, ∀ S: set A, 0 ≤ |S| -> finite S.

Theorem set_induction : ∀ A: U, ∀ P: set A -> U, P {} -> (∀ x: set A, finite x -> P x -> ∀ a: A, (a ∈ x -> False) -> P (x ∪ {a})) -> ∀ e: set A, finite e -> P e.
Proof.
    intros.
    add_hyp (∃ k, k = |e|).
    apply (ex_intro ? ? (|e|)).
    auto_list.
    destruct H2 with (ex_ind ? ?) to (k k_property).
    add_hyp (0 ≤ k).
    rewrite k_property.
    apply finite_len_ge_0.
    assumption.
    revert k_property.
    revert H1.
    revert e.
    revert H2.
    revert k.
    apply z_induction_simple.
    intros.
    Switch 1.
    intros.
    add_hyp (e={}).
    apply empty_len_unique.
    auto_set.
    rewrite H2.
    apply H.
    add_hyp (~ e = {}).
    intros.
    add_hyp (|e|=0).
    rewrite H3.
    apply empty_len.
    lia.
    apply non_empty_has_member in H3.
    destruct H3 with (ex_ind ? ?) to (x x_property).
    add_hyp H2_ex := (H2 (e ∖ {x})).
    add_hyp (⁨finite (e ∖ {x})⁩).
    remove_hyp H2_ex.
    Switch 1.
    add_hyp H2_ex_o := (H2_ex H3).
    remove_hyp H3.
    remove_hyp H2_ex.
    Switch 1.
    auto_set.
    add_hyp (⁨n = |e ∖ {x}|⁩).
    remove_hyp H2_ex_o.
    Switch 1.
    add_hyp H2_ex_o_o := (H2_ex_o H3).
    remove_hyp H3.
    remove_hyp H2_ex_o.
    apply H0 in H2_ex_o_o.
    auto_set.
    add_hyp H2_ex_o_o_ex := (H2_ex_o_o (x)).
    add_hyp (⁨~ x ∈ e ∖ {x}⁩).
    remove_hyp H2_ex_o_o_ex.
    Switch 1.
    add_hyp H2_ex_o_o_ex_o := (H2_ex_o_o_ex H3).
    remove_hyp H3.
    remove_hyp H2_ex_o_o_ex.
    replace #1 ((e ∖ {x} ∪ {x})) with (e) in H2_ex_o_o_ex_o.
    auto_set.
    assumption.
    auto_set.
    add_from_lib finite_add_len.
    add_hyp (~ x ∈ (e ∖ {x})).
    auto_set.
    apply finite_add_len in H3.
    auto_set.
    replace #1 (e ∖ {x} ∪ {x}) with (e) in H3.
    auto_set.
    lia.
Qed.

Axiom singleton_len: ∀ A: U, ∀ x: A, |{x}| = 1.
Suggest goal auto apply singleton_len; Trivial.

Axiom len_eq_eq: ∀ T: U, ∀ A B: set T, A = B -> |A| = |B|.
Axiom set_from_func_eq: ∀ A: U, ∀ f: A -> U, ∀ g: A -> U, (∀ x: A, f x ↔ g x) -> set_from_func A f = set_from_func A g.
Todo len_gt_0_not_empty_set: ∀ T: U, ∀ S: set T, |S| > 0 → ∃ t: T, t ∈ S.