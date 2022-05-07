Import Logic.
Import Eq.

Axiom zero_lt_mult: ∀ a b: ℤ, 0 < a -> 0 < b -> 0 < a * b.
Axiom lt_plus_r: ∀ a b c: ℤ, a < b -> a + c < b + c.
Axiom lt_plus_l: ∀ a b c: ℤ, a < b -> c + a < c + b.
Axiom lt_trans: ∀ n m p : ℤ, n < m -> m < p -> n < p.
Axiom lt_divide_positive: ∀ a b c: ℤ, 0 < c -> c * a < c * b -> a < b.
Axiom lt_divide_negative: ∀ a b c: ℤ, c < 0 -> c * a < c * b -> b < a.
Axiom lt_multiply_positive: ∀ a b c: ℤ, 0 < c -> a < b -> c * a < c * b.
Axiom lt_multiply_negative: ∀ a b c: ℤ, c < 0 -> a < b -> c * b < c * a.

Axiom le_intro_l: ∀ a b: ℤ, a ≤ b -> a < b ∨ a = b.
Axiom le_intro_r: ∀ a b: ℤ, a < b ∨ a = b -> a ≤ b.
Axiom le_refl: ∀ a: ℤ, a ≤ a. 
Axiom zero_le_mult: ∀ a b: ℤ, 0 ≤ a -> 0 ≤ b -> 0 ≤ a * b.
Axiom le_plus_r: ∀ a b c: ℤ, a ≤ b -> a + c ≤ b + c.
Axiom le_plus_l: ∀ a b c: ℤ, a ≤ b -> c + a ≤ c + b.
Axiom le_trans: ∀ n m p : ℤ, n ≤ m -> m ≤ p -> n ≤ p.
Axiom le_divide_positive: ∀ a b c: ℤ, 0 < c -> c * a ≤ c * b -> a ≤ b.
Axiom le_divide_negative: ∀ a b c: ℤ, c < 0 -> c * a ≤ c * b -> b ≤ a.
Axiom le_multiply_positive: ∀ a b c: ℤ, 0 < c -> a ≤ b -> c * a ≤ c * b.
Axiom le_multiply_negative: ∀ a b c: ℤ, c < 0 -> a ≤ b -> c * b ≤ c * a.

Theorem lt_0_1: 0 < 1.
Proof.
    lia.
Qed.
