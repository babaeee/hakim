Import /Arith.

Axiom divide_unfold: ∀ a b: ℤ, a | b -> ∃ c: ℤ, a * c = b.
Axiom divide_fold: ∀ a b: ℤ, (∃ c: ℤ, a * c = b) -> a | b.
Suggest hyp default apply divide_unfold in $n; a | b => ∃ c, a * c = b.
Suggest goal default apply divide_fold; a | b => ∃ c, a * c = b.

Todo divide_refl: ∀ a: ℤ, a | a.
Todo divide_trans: ∀ a b c: ℤ, a | b -> b | c -> a | c.
Todo divide_0: ∀ a: ℤ, a | 0 -> a = 0.
Theorem divide_1_positive: ∀ a: ℤ, 0 < a -> a | 1 -> a = 1.
Proof.
    intros.
    apply divide_unfold in H0.
    destruct H0 with (ex_ind ? ?) to (c c_property).
    add_hyp (1 < a -> False).
    Switch 1.
    lia.
    intros.
    add_hyp (0 < c).
    apply NNPP.
    intros.
    add_hyp (0 = c ∨ c < 0).
    lia.
    destruct H2 with (or_ind ? ?).
    add_hyp (a * c < 0).
    replace #1 (a * c) with (c * a).
    ring.
    replace #1 (0) with (c * 0).
    ring.
    apply lt_multiply_negative.
    assumption.
    assumption.
    lia.
    replace #1 (c) with (0) in c_property.
    auto_set.
    lia.
    add_hyp (c * 1 < c * a).
    apply lt_multiply_positive.
    assumption.
    assumption.
    replace #1 (c * a) with (1) in H2.
    lia.
    lia.
Qed.
Todo divide_factor: ∀ a b c: ℤ, a | b -> a | b * c.
Todo divide_plus: ∀ a b c: ℤ, a | b -> a | c -> a | b + c.
Todo divide_minus: ∀ a b c: ℤ, a | b -> a | b + c -> a | c.
Todo divide_le: ∀ a b: ℤ, 0 < b -> a | b -> a ≤ b.
Theorem divide_linear_combination: ∀ a b c: ℤ, a | b -> a | c -> (∀ k l: ℤ, a | k * b + l * c).
Proof.
    intros.
    apply divide_plus.
    replace #1 (l * c) with (c * l).
    ring.
    apply divide_factor.
    assumption.
    replace #1 (k * b) with (b * k).
    ring.
    apply divide_factor.
    assumption.
Qed.

Axiom prime: ℤ -> U.
Axiom prime_intro_l: ∀ x: ℤ, prime x -> 0 < x ∧ (∀ y: ℤ, 0 < y -> y | x -> y = 1 ∨ y = x).
Axiom prime_intro_r: ∀ x: ℤ, 0 < x ∧ (∀ y: ℤ, 0 < y -> y | x -> y = 1 ∨ y = x) -> prime x.
Todo prime_gt_2: ∀ x: ℤ, prime x -> 2 < x.
Todo prime_is_positive: ∀ x: ℤ, prime x -> 0 < x.
Todo prime_divisor_for_positive: ∀ x: ℤ, 0 < x -> (x = 1 -> False) -> ∃ p: ℤ, prime p ∧ p | x.

Import /ProductOperator.
Axiom divide_multi:   ∀ A: set ℤ, ∀ a : ℤ, a ∈ A -> a | multi A.
