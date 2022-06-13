Import /Logic.

Axiom set_from_func_unfold: ∀ A: U, ∀ f: A -> U, ∀ a: A, a ∈ (set_from_func A f) -> f a.
Axiom set_from_func_fold: ∀ A: U, ∀ f: A -> U, ∀ a: A, f a -> a ∈ (set_from_func A f).
Suggest hyp default apply set_from_func_unfold in $n; a ∈ {b | f b} => f a.
Suggest goal default apply set_from_func_fold; a ∈ {b | f b} => f a.

Theorem empty_intro: ∀ A: U, ∀ a: A, a ∈ {} -> False.
Proof. intros. auto_set. Qed.
Suggest hyp default chain (apply empty_intro in $n) (apply (False_ind $n ?)); Contradiction.

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
Suggest goal default apply union_fold; a ∈ x ∪ y => a ∈ x ∨ a ∈ y.

Theorem intersection_intro: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∩ y ↔ a ∈ x ∧ a ∈ y.
Proof. intros. auto_set. Qed.
Theorem setminus_intro: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∖ y ↔ a ∈ x ∧ (a ∈ y -> False).
Proof. intros. auto_set. Qed.
Theorem included_unfold: ∀ A: U, ∀ x y: set A, x ⊆ y -> (∀ a: A, a ∈ x -> a ∈ y).
Proof. intros. auto_set. Qed.
Axiom included_fold: ∀ A: U, ∀ x y: set A, (∀ a: A, a ∈ x -> a ∈ y) -> x ⊆ y.
Suggest hyp default apply included_unfold in $n; a ⊆ b => ∀ x: T, x ∈ a -> x ∈ b.
Suggest goal default apply included_fold; a ⊆ b => ∀ x: T, x ∈ a -> x ∈ b.

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

Theorem minus_of_subset: ∀ A: U, ∀ x y: set A, x ⊆ y -> x ∪ y ∖ x = y.
Proof. intros. auto_set. Qed.

Axiom finite: ∀ A: U, (set A) -> U.
Axiom empty_finite : ∀ A: U, finite (set_empty A).
Axiom finite_add : ∀ A: U, ∀ x: set A, finite x -> ∀ a: A, (a ∈ x -> False) -> finite (x ∪ {a}).

Axiom finite_included : ∀ A: U, ∀ x y: set A, finite y -> x ⊆ y -> finite x.

Axiom set_induction : ∀ A: U, ∀ P: set A -> U, P {} -> (∀ x: set A, finite x -> P x -> ∀ a: A, (a ∈ x -> False) -> P (x ∪ {a})) -> ∀ e: set A, finite e -> P e.
