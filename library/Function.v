Import /Logic.

Axiom exist_function: ∀ A B: U, ∀ P: A -> B -> U, (∀ x: A, ∃ y: B, P x y) -> ∃ f: A -> B, ∀ x: A, P x (f x).
