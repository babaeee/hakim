Axiom set_from_func_intro: ∀ A: U, ∀ f: A -> U, ∀ a: A, (f a) -> a ∈ (set_from_func A f).
Axiom empty: ∀ A: U, set A.
Axiom empty_intro: ∀ A: U, ∀ a: A, a ∈ (empty A) -> False.
Axiom singleton: ∀ A: U, ∀ a: A, set A.
Axiom singleton_intro: ∀ A: U, ∀ a b: A, b ∈ (singleton A a)-> eq A a b. 
Axiom unino_intro: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∪ y ↔ a ∈ x ∨ a ∈ y.
Axiom intersection_intro: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∩ y ↔ a ∈ x ∧ a ∈ y.
Axiom setminus_intro: ∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∖ y ↔ a ∈ x ∨ (a ∈ y -> False).
Axiom included_intro: ∀ A: U, ∀ x y: set A, ∀ a: A, x ⊆ y ↔ (a ∈ x -> a ∈ y).