Axiom simple_induction: ∀ k: ℤ, ∀ P: ℤ -> U, P k -> (∀ n: ℤ, P n -> P (n+1)) -> (∀ n: ℤ, P n).
