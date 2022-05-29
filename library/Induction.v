Import /Function.

Axiom z_simple_induction: ∀ k: ℤ, ∀ P: ℤ -> U, P k -> (∀ n: ℤ, k ≤ n -> P n -> P (n+1)) -> (∀ n: ℤ, k ≤ n -> P n).

Todo z_simple_recursion: ∀ k: ℤ, ∀ B: U, ∀ a: B, ∀ b: B -> B, ∃ f: ℤ -> B, f k = a ∧ ∀ n: ℤ, k ≤ n -> f (n+1) = b (f n).
