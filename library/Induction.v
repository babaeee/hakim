Import /Function.

Axiom simple_induction: ∀ k: ℤ, ∀ P: ℤ -> U, P k -> (∀ n: ℤ, k ≤ n -> P n -> P (n+1)) -> (∀ n: ℤ, k ≤ n -> P n).

Todo simple_induction_combinator_dependent: ∀ k: ℤ, ∀ B: U, ∀ a: B, ∀ b: B -> B, ∃ f: ℤ -> B, f k = a ∧ ∀ n: ℤ, k ≤ n -> f (n+1) = b (f n).
