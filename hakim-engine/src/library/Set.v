Axiom set_from_func_fold: ∀ A: U, ∀ f: A -> U, ∀ a: A, f a -> a ∈ (set_from_func A f).
Axiom set_from_func_unfold: ∀ A: U, ∀ f: A -> U, ∀ a: A, a ∈ (set_from_func A f) -> f a.
Axiom empty_intro: ∀ A: U, ∀ a: A, a ∈ {} -> False.
Axiom singleton_unfold: ∀ A: U, ∀ a b: A, b ∈ {a} -> a = b. 
Axiom singleton_fold: ∀ A: U, ∀ a b: A, a = b -> b ∈ {a}. 
Axiom union_unfold: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∪ y -> a ∈ x ∨ a ∈ y.
Axiom union_fold: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∨ a ∈ y -> a ∈ x ∪ y.
Axiom intersection_intro: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∩ y ↔ a ∈ x ∧ a ∈ y.
Axiom setminus_intro: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∖ y ↔ a ∈ x ∨ (a ∈ y -> False).
Axiom included_fold: ∀ A: U, ∀ x y: set A, (∀ a: A, a ∈ x -> a ∈ y) -> x ⊆ y.
Axiom included_unfold: ∀ A: U, ∀ x y: set A, x ⊆ y -> (∀ a: A, a ∈ x -> a ∈ y).
Axiom set_equality: ∀ A: U, ∀ x y: set A, x ⊆ y -> y ⊆ x -> x = y.
Axiom set_equality_forall: ∀ A: U, ∀ x y: set A, (∀ a: A, a ∈ x ↔ a ∈ y) -> x = y.
Axiom minus_of_subset: ∀ A: U, ∀ x y: set A, x ⊆ y -> x ∪ y ∖ x = y.

Axiom finite: ∀ A: U, (set A) -> U.
Axiom empty_finite : ∀ A: U, finite A (set_empty A).
Axiom finite_add : ∀ A: U, ∀ x: set A, finite A x -> ∀ a: A, (a ∈ x -> False) -> finite A (x ∪ {a}).

Axiom finite_included : ∀ A: U, ∀ x y: set A, finite A y -> x ⊆ y -> finite A x.

Axiom set_induction : ∀ A: U, ∀ P: set A -> U, P {} -> (∀ x: set A, finite A x -> P x -> ∀ a: A, (a ∈ x -> False) -> P (x ∪ {a})) -> ∀ e: set A, finite A e -> P e.
