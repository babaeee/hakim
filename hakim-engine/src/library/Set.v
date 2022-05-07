Axiom set_from_func_unfold: ∀ A: U, ∀ f: A -> U, ∀ a: A, a ∈ (set_from_func A f) -> f a.
Axiom set_from_func_fold: ∀ A: U, ∀ f: A -> U, ∀ a: A, f a -> a ∈ (set_from_func A f).
Suggest hyp default apply set_from_func_unfold in $n; a ∈ {b | f b} => f a.
Suggest goal default apply set_from_func_fold; a ∈ {b | f b} => f a.
Axiom empty_intro: ∀ A: U, ∀ a: A, a ∈ {} -> False.
Suggest hyp default chain (apply empty_intro in $n) (apply (False_ind $n ?)); Contradiction.
Axiom singleton_unfold: ∀ A: U, ∀ a b: A, b ∈ {a} -> a = b.
Axiom singleton_fold: ∀ A: U, ∀ a b: A, a = b -> b ∈ {a}. 
Suggest hyp default apply singleton_unfold in $n; a ∈ {b} => a = b.
Suggest goal default apply singleton_fold; a ∈ {b} => a = b.
Axiom union_unfold: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∪ y -> a ∈ x ∨ a ∈ y.
Axiom union_fold: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∨ a ∈ y -> a ∈ x ∪ y.
Suggest goal default apply union_fold; a ∈ x ∪ y => a ∈ x ∨ a ∈ y.
Axiom intersection_intro: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∩ y ↔ a ∈ x ∧ a ∈ y.
Axiom setminus_intro: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∖ y ↔ a ∈ x ∨ (a ∈ y -> False).
Axiom included_unfold: ∀ A: U, ∀ x y: set A, x ⊆ y -> (∀ a: A, a ∈ x -> a ∈ y).
Axiom included_fold: ∀ A: U, ∀ x y: set A, (∀ a: A, a ∈ x -> a ∈ y) -> x ⊆ y.
Suggest hyp default apply included_unfold in $n; a ⊆ b => ∀ x: T, x ∈ a -> x ∈ b.
Suggest goal default apply included_fold; a ⊆ b => ∀ x: T, x ∈ a -> x ∈ b.
Axiom set_equality: ∀ A: U, ∀ x y: set A, x ⊆ y -> y ⊆ x -> x = y.
Suggest goal default apply set_equality; A = B => A ⊆ B ∧ B ⊆ A.
Axiom set_equality_forall: ∀ A: U, ∀ x y: set A, (∀ a: A, a ∈ x ↔ a ∈ y) -> x = y.
Axiom minus_of_subset: ∀ A: U, ∀ x y: set A, x ⊆ y -> x ∪ y ∖ x = y.

Axiom finite: ∀ A: U, (set A) -> U.
Axiom empty_finite : ∀ A: U, finite A (set_empty A).
Axiom finite_add : ∀ A: U, ∀ x: set A, finite A x -> ∀ a: A, (a ∈ x -> False) -> finite A (x ∪ {a}).

Axiom finite_included : ∀ A: U, ∀ x y: set A, finite A y -> x ⊆ y -> finite A x.

Axiom set_induction : ∀ A: U, ∀ P: set A -> U, P {} -> (∀ x: set A, finite A x -> P x -> ∀ a: A, (a ∈ x -> False) -> P (x ∪ {a})) -> ∀ e: set A, finite A e -> P e.
