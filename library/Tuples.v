Axiom pair_eq: ∀ A B: U, ∀ x y: A, ∀ p q: B, (x, p) = (y, q) -> x = y ∧ p = q;
Suggest goal default apply pair_eq with label (x, p) = (y, q) => x = y ∧ p = q;
