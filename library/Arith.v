Import /Logic.
Import /Eq.
Import /Induction.

Todo zero_lt_mult: ∀ a b: ℤ, 0 < a -> 0 < b -> 0 < a * b.
Todo lt_plus_r: ∀ a b c: ℤ, a < b -> a + c < b + c.
Todo lt_plus_l: ∀ a b c: ℤ, a < b -> c + a < c + b.
Todo lt_trans: ∀ n m p : ℤ, n < m -> m < p -> n < p.
Todo lt_divide_positive: ∀ a b c: ℤ, 0 < c -> c * a < c * b -> a < b.
Todo lt_divide_negative: ∀ a b c: ℤ, c < 0 -> c * a < c * b -> b < a.
Todo lt_multiply_positive: ∀ a b c: ℤ, 0 < c -> a < b -> c * a < c * b.
Todo lt_multiply_negative: ∀ a b c: ℤ, c < 0 -> a < b -> c * b < c * a.

Todo eq_plus_r: ∀ a b c: ℤ, a + c = b + c -> a = b.
Todo eq_plus_l: ∀ a b c: ℤ, c + a = c + b -> a = b.
Todo eq_mult_r: ∀ a b c: ℤ, ~ c = 0 -> a * c = b * c -> a = b.
Todo eq_mult_l: ∀ a b c: ℤ, ~ c = 0 -> c * a = c * b -> a = b.

Todo le_refl: ∀ a: ℤ, a ≤ a. 
Todo zero_le_mult: ∀ a b: ℤ, 0 ≤ a -> 0 ≤ b -> 0 ≤ a * b.
Todo le_plus_r: ∀ a b c: ℤ, a ≤ b -> a + c ≤ b + c.
Todo le_plus_l: ∀ a b c: ℤ, a ≤ b -> c + a ≤ c + b.
Todo le_trans: ∀ n m p : ℤ, n ≤ m -> m ≤ p -> n ≤ p.
Todo le_divide_positive: ∀ a b c: ℤ, 0 < c -> c * a ≤ c * b -> a ≤ b.
Todo le_divide_negative: ∀ a b c: ℤ, c < 0 -> c * a ≤ c * b -> b ≤ a.
Todo le_multiply_positive: ∀ a b c: ℤ, 0 < c -> a ≤ b -> c * a ≤ c * b.
Todo le_multiply_negative: ∀ a b c: ℤ, c < 0 -> a ≤ b -> c * b ≤ c * a.

Theorem lt_0_1: 0 < 1.
Proof.
    lia.
Qed.

Axiom pow_unfold_l: ∀ a n: ℤ, 0 ≤ n -> a ^ (n + 1) = a * a ^ n.
Theorem pow_unfold_r: ∀ a n: ℤ, 0 ≤ n -> a ^ (n + 1) = a ^ n * a.
Proof.
    intros.
    replace (a ^ n * a) with (a * a ^ n).
    lia.
    apply pow_unfold_l.
Qed.
Suggest goal apply pow_unfold_l;  a ^ (n + 1) = a * a ^ n => 0 ≤ n.
Suggest goal apply pow_unfold_r;  a ^ (n + 1) = a ^ n * a => 0 ≤ n.

Theorem pow_pos: ∀ a n: ℤ, 0 ≤ n -> 0 < a -> 0 < a ^ n.
Proof.
    intros a.
    apply simple_induction.
    intros.
    add_hyp (0 < a).
    Switch 1.
    add_hyp H0_o := (H0 H2).
    remove_hyp H2.
    remove_hyp H0.
    replace #1 (a ^ (n + 1)) with (a * a ^ n).
    apply pow_unfold_l.
    assumption.
    apply zero_lt_mult.
    assumption.
    assumption.
    assumption.
    lia.
Qed.

Todo pow_lt_l: ∀ a b c: ℤ, 0 < a -> a < b -> 0 < c -> a ^ c < b ^ c.
Todo pow_lt_r: ∀ a b c: ℤ, 0 < a -> a < b -> 1 < c -> c ^ a < c ^ b.


Axiom abs_pos: ∀ a: ℤ, 0 ≤ |a|.
Axiom abs_eq: ∀ a: ℤ, |a| = a ∨ |a| = -a.
