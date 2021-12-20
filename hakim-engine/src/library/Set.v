Axiom set_from_func_intro: ∀ A: U, ∀ f: A -> U, ∀ a: A, (f a) -> a ∈ (set_from_func A f).
Axiom empty_intro: ∀ A: U, ∀ a: A, a ∈ {} -> False.
Axiom singleton_unfold: ∀ A: U, ∀ a b: A, b ∈ {a} -> a = b. 
Axiom singleton_fold: ∀ A: U, ∀ a b: A, a = b -> b ∈ {a}. 
Axiom unino_intro: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∪ y ↔ a ∈ x ∨ a ∈ y.
Axiom intersection_intro: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∩ y ↔ a ∈ x ∧ a ∈ y.
Axiom setminus_intro: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∖ y ↔ a ∈ x ∨ (a ∈ y -> False).
Axiom included_fold: ∀ A: U, ∀ x y: set A, (∀ a: A, a ∈ x -> a ∈ y) -> x ⊆ y.
Axiom included_unfold: ∀ A: U, ∀ x y: set A, x ⊆ y -> (∀ a: A, a ∈ x -> a ∈ y).
Axiom set_equality: ∀ A: U, ∀ x y: set A, x ⊆ y -> y ⊆ x -> x = y.
Axiom minus_of_subset: ∀ A: U, ∀ x y: set A, x ⊆ y -> x ∪ y ∖ x = y.
