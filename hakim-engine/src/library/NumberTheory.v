Axiom divide_unfold: ∀ a b: ℤ, a | b -> ∃ c: ℤ, a * c = b.
Axiom divide_fold: ∀ a b: ℤ, (∃ c: ℤ, a * c = b) -> a | b.
Todo divide_refl: ∀ a: ℤ, a | a.
Todo divide_trans: ∀ a b c: ℤ, a | b -> b | c -> a | c.
Todo divide_0: ∀ a: ℤ, a | 0 -> a = 0.
Todo divide_1_positive: ∀ a: ℤ, 0 < a -> a | 1 -> a = 1.
Todo divide_factor: ∀ a b c: ℤ, a | b -> a | b * c.
Todo divide_plus: ∀ a b c: ℤ, a | b -> a | c -> a | b + c.
Todo divide_minus: ∀ a b c: ℤ, a | b -> a | b + c -> a | c.
Todo divide_le: ∀ a b: ℤ, 0 < b -> a | b -> a ≤ b.
Todo divide_linear_combination: ∀ a b c: ℤ, a | b -> a | c -> (∀ k l: ℤ, a | k * b + l * c).

Axiom prime: ℤ -> U.
Axiom prime_intro_l: ∀ x: ℤ, prime x -> 0 < x ∧ (∀ y: ℤ, 0 < y -> y | x -> y = 1 ∨ y = x).
Axiom prime_intro_r: ∀ x: ℤ, 0 < x ∧ (∀ y: ℤ, 0 < y -> y | x -> y = 1 ∨ y = x) -> prime x.
Todo prime_gt_2: ∀ x: ℤ, prime x -> 2 < x.
Todo prime_is_positive: ∀ x: ℤ, prime x -> 0 < x.
Todo prime_divisor_for_positive: ∀ x: ℤ, 0 < x -> (x = 1 -> False) -> ∃ p: ℤ, prime p ∧ p | x.

Import ProductOperator.
Axiom divide_multi:   ∀ A: set ℤ, ∀ a : ℤ, a ∈ A -> a | multi A.
