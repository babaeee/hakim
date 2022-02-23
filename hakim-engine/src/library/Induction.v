Axiom simple_induction: ∀ k: ℤ, ∀ P: ℤ -> U, P k -> (∀ n: ℤ, k < n + 1 -> P n -> P (n+1)) -> (∀ n: ℤ, k < n + 1 -> P n).
