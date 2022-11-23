Import /NumberTheory;

Axiom sqrt: ℝ -> ℝ;

Axiom sqrt_def: ∀ x: ℝ, 0. ≤ x -> sqrt x * sqrt x = x;

Axiom is_q: ℝ -> U;

Axiom is_q_unfold: ∀ x: ℝ, is_q x -> ∃ a b: ℤ, a / b = x ∧ gcd a b = 1 ∧ b > 0;

Suggest hyp default apply is_q_unfold in $n with label is_q x => ∃ a b: ℤ, a / b = x ∧ gcd a b = 1 ∧ b > 0;
