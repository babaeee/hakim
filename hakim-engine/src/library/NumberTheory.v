Axiom divide_intro: ∀ a b: ℤ, a | b -> ∃ c: ℤ, a * c = b.
Axiom divide_refl: ∀ a: ℤ, a | a.
Axiom divide_trans: ∀ a b c: ℤ, a | b -> b | c -> a | c.
Axiom divide_factor: ∀ a b c: ℤ, a | b -> a | b * c.
Axiom divide_plus: ∀ a b c: ℤ, a | b -> a | c -> a | b + c.
Axiom divide_linear_combination: ∀ a b c: ℤ, a | b -> a | c -> (∀ k l: ℤ, a | k * b + l * c).

Axiom prime: ℤ -> U.
Axiom prime_intro: ∀ x: ℤ, prime x -> 0 < x ∧ (∀ y: ℤ, 0 < y -> y | x -> y = 0 ∨ y = x).
Axiom prime_gt_2: ∀ x: ℤ, prime x -> 2 < x.

Axiom prime_divisor: ∀ x: ℤ, (x = 0 -> False) -> ∃ p: ℤ, p | x.