Axiom divide_introl: ∀ a b: ℤ, a | b -> ∃ c: ℤ, a * c = b.
Axiom divide_intror: ∀ a b: ℤ, (∃ c: ℤ, a * c = b) -> a | b.
Axiom divide_refl: ∀ a: ℤ, a | a.
Axiom divide_trans: ∀ a b c: ℤ, a | b -> b | c -> a | c.
Axiom divide_0: ∀ a: ℤ, a | 0 -> a = 0.
Axiom divide_1_positive: ∀ a: ℤ, 0 < a -> a | 1 -> a = 1.
Axiom divide_factor: ∀ a b c: ℤ, a | b -> a | b * c.
Axiom divide_plus: ∀ a b c: ℤ, a | b -> a | c -> a | b + c.
Axiom divide_minus: ∀ a b c: ℤ, a | b -> a | b + c -> a | c.
Axiom divide_linear_combination: ∀ a b c: ℤ, a | b -> a | c -> (∀ k l: ℤ, a | k * b + l * c).

Axiom prime: ℤ -> U.
Axiom prime_intro_l: ∀ x: ℤ, prime x -> 0 < x ∧ (∀ y: ℤ, 0 < y -> y | x -> y = 0 ∨ y = x).
Axiom prime_intro_r: ∀ x: ℤ, 0 < x ∧ (∀ y: ℤ, 0 < y -> y | x -> y = 0 ∨ y = x) -> prime x.
Axiom prime_gt_2: ∀ x: ℤ, prime x -> 2 < x.

Axiom prime_divisor: ∀ x: ℤ, (x = 0 -> False) -> ∃ p: ℤ, prime p ∧ p | x.