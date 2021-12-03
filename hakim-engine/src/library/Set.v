Axiom In: ∀ A: U, set A -> A -> U.
Axiom set_from_func_intro: ∀ A: U, ∀ f: A -> U, ∀ a: A, (f a) -> (In A (set_from_func A f) a).
Axiom empty: ∀ A: U, set A.
Axiom empty_intro: ∀ A: U, ∀ a: A, In A (empty A) a -> False.
Axiom singleton: ∀ A: U, ∀ a: A, set A.
Axiom singleton_intro: ∀ A: U, ∀ a b: A, In A (singleton A a) b -> eq A a b.
Axiom included: ∀ A: U, set A -> set A -> U. 
Axiom union: ∀ A: U, set A -> set A -> set A.
Axiom intersection: ∀ A: U, set A -> set A -> set A.
Axiom minus: ∀ A: U, set A -> set A -> set A. 
Axiom included_intro: ∀ A: U, ∀ x y: set A, included A x y ↔ ∀ a: A, In A x a -> In A y a.
Axiom unino_intro: ∀ A: U, ∀ x y: set A, ∀ a: A, In A (union A x y) a ↔ In A x a ∨ In A y a.