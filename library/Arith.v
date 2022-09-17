Import /Logic.
Import /Eq.
Import /Induction.

Todo lt_le: ∀ k a: ℤ, k < a -> k + 1 ≤ a.
Theorem zero_lt_mult_pos: ∀ a b: ℤ, 0 < a -> 0 < b -> 0 < a * b.
Proof.
    intros.
    add_hyp (1 ≤ b).
    lia.
    remove_hyp H0.
    revert H1.
    revert b.
    apply z_induction_simple.
    intros.
    lia.
    lia.
Qed.

Theorem zero_lt_mult_neg: ∀ a b: ℤ, a < 0 -> b < 0 -> 0 < a * b.
Proof.
    intros.
    replace #1 (a * b) with ((-a) * (-b)).
    lia.
    apply zero_lt_mult_pos.
    lia.
    lia.
Qed.
Suggest goal apply zero_lt_mult_pos; 0 < a * b => 0 < a ∧ 0 < b.
Suggest goal apply zero_lt_mult_neg; 0 < a * b => a < 0 ∧ b < 0.
Theorem zero_le_mult_pos: ∀ a b: ℤ, 0 ≤ a -> 0 ≤ b -> 0 ≤ a * b.
Proof.
    intros.
    revert H0.
    revert b.
    apply z_induction_simple.
    intros.
    lia.
    lia.
Qed.
Theorem zero_le_mult_neg: ∀ a b: ℤ, a ≤ 0 -> b ≤ 0 -> 0 ≤ a * b.
Proof.
    intros.
    destruct H0 with (or_ind ? ?).
    rewrite H0.
    lia.
    destruct H with (or_ind ? ?).
    rewrite H.
    lia.
    apply or_introl.
    apply zero_lt_mult_neg.
    assumption.
    assumption.
Qed.
Suggest goal apply zero_le_mult_pos; 0 ≤ a * b => 0 ≤ a ∧ 0 ≤ b.
Suggest goal apply zero_le_mult_neg; 0 ≤ a * b => a ≤ 0 ∧ b ≤ 0.

Theorem not_lt: ∀ a b: ℤ, ~ a < b -> b ≤ a.
Proof. intros. lia. Qed.
Theorem not_le: ∀ a b: ℤ, ~ a ≤ b -> b < a.
Proof. intros. lia. Qed.
Suggest hyp default apply not_lt in $n; ~ a < b => b ≤ a.
Suggest hyp default apply not_le in $n; ~ a ≤ b => b < a.

Theorem lt_plus_r: ∀ a b c: ℤ, a < b -> a + c < b + c.
Proof. intros. lia. Qed.
Theorem lt_plus_l: ∀ a b c: ℤ, a < b -> c + a < c + b.
Proof. intros. lia. Qed.
Theorem plus_lt_r: ∀ a b c: ℤ, a + c < b + c -> a < b.
Proof. intros. lia. Qed.
Theorem plus_lt_l: ∀ a b c: ℤ, c + a < c + b -> a < b.
Proof. intros. lia. Qed.
Theorem lt_trans: ∀ n m p : ℤ, n < m -> m < p -> n < p.
Proof. intros. lia. Qed.
Theorem multiply_lt_positive: ∀ a b c: ℤ, 0 < c -> c * a < c * b -> a < b.
Proof.
intros.
add_hyp (1 ≤ c).
lia.
revert H0.
revert H.
revert H1.
revert c.
apply z_induction_simple.
intros.
lia.
lia.
Qed.
Theorem multiply_lt_negative: ∀ a b c: ℤ, c < 0 -> c * a < c * b -> b < a.
Proof.
    intros.
    add_hyp (∃ d: ℤ, d = -c).
    apply (ex_intro ? ? (-c)).
    auto_list.
    destruct H1 with (ex_ind ? ?) to (d d_property).
    add_hyp (d * a > d * b).
    rewrite d_property.
    lia.
    apply (⁨multiply_lt_positive ?0 ?2 d ?6 ?8⁩).
    assumption.
    lia.
Qed.
Theorem lt_multiply_positive: ∀ a b c: ℤ, 0 < c -> a < b -> c * a < c * b.
Proof.
    intros.
    add_hyp (1 ≤ c).
    lia.
    revert H.
    revert H1.
    revert c.
    apply z_induction_simple.
    intros.
    lia.
    lia.
Qed.
Theorem lt_multiply_negative: ∀ a b c: ℤ, c < 0 -> a < b -> c * b < c * a.
Proof.
    intros.
    add_hyp (-c * a < -c * b).
    apply lt_multiply_positive.
    assumption.
    lia.
    lia.
Qed.
Axiom eq_cansel_plus_r: ∀ a b c: ℤ, a = b -> a + c = b + c.
Axiom eq_cansel_plus_l: ∀ a b c: ℤ, a = b -> c + a = c + b.
Theorem eq_plus_r: ∀ a b c: ℤ, a + c = b + c -> a = b.
Proof. intros. lia. Qed.
Theorem eq_plus_l: ∀ a b c: ℤ, c + a = c + b -> a = b.
Proof. intros. lia. Qed.
Todo eq_mult_r: ∀ a b c: ℤ, ~ c = 0 -> a * c = b * c -> a = b.
Todo eq_mult_l: ∀ a b c: ℤ, ~ c = 0 -> c * a = c * b -> a = b.
Theorem eq_subtract_positive_lt: ∀ a b c: ℤ, 0 < b -> a + b = c -> a < c.
Proof. intros. lia. Qed.

Theorem le_refl: ∀ a: ℤ, a ≤ a. 
Proof. intros. lia. Qed.
Theorem le_plus_r: ∀ a b c: ℤ, a ≤ b -> a + c ≤ b + c.
Proof. intros. lia. Qed.
Theorem le_plus_l: ∀ a b c: ℤ, a ≤ b -> c + a ≤ c + b.
Proof. intros. lia. Qed.
Theorem le_trans: ∀ n m p : ℤ, n ≤ m -> m ≤ p -> n ≤ p.
Proof. intros. lia. Qed.
Todo le_divide_positive: ∀ a b c: ℤ, 0 < c -> c * a ≤ c * b -> a ≤ b.
Todo le_divide_negative: ∀ a b c: ℤ, c < 0 -> c * a ≤ c * b -> b ≤ a.
Theorem le_multiply_positive: ∀ a b c: ℤ, 0 ≤ c -> a ≤ b -> c * a ≤ c * b.
Proof.
    intros a b.
    apply z_induction_simple.
    intros.
    lia.
    lia.
Qed.
Theorem le_multiply_negative: ∀ a b c: ℤ, c ≤ 0 -> a ≤ b -> c * b ≤ c * a.
Proof.
    intros.
    add_hyp (-c * a ≤ -c * b).
    apply le_multiply_positive.
    assumption.
    lia.
    lia.
Qed.

Theorem lt_0_1: 0 < 1.
Proof. lia. Qed.

Axiom pow_unfold_l: ∀ a n: ℤ, 0 ≤ n -> a ^ (n + 1) = a * a ^ n.
Theorem pow_unfold_r: ∀ a n: ℤ, 0 ≤ n -> a ^ (n + 1) = a ^ n * a.
Proof.
    intros.
    replace (a ^ n * a) with (a * a ^ n).
    lia.
    apply pow_unfold_l.
    assumption.
Qed.
Suggest goal apply pow_unfold_l;  a ^ (n + 1) = a * a ^ n => 0 ≤ n.
Suggest goal apply pow_unfold_r;  a ^ (n + 1) = a ^ n * a => 0 ≤ n.

Theorem pow_pos: ∀ a n: ℤ, 0 ≤ n -> 0 < a -> 0 < a ^ n.
Proof.
    intros a.
    apply z_induction_simple.
    intros.
    add_hyp (0 < a).
    Switch 1.
    add_hyp H0_o := (H0 H2).
    remove_hyp H2.
    remove_hyp H0.
    replace #1 (a ^ (n + 1)) with (a * a ^ n).
    apply pow_unfold_l.
    assumption.
    apply zero_lt_mult_pos.
    assumption.
    assumption.
    assumption.
    lia.
Qed.

Todo pow_lt_l: ∀ a b c: ℤ, 0 < a -> a < b -> 0 < c -> a ^ c < b ^ c.
Todo pow_lt_r: ∀ a b c: ℤ, 0 < a -> a < b -> 1 < c -> c ^ a < c ^ b.


Axiom abs_pos: ∀ a: ℤ, 0 ≤ |a|.
Axiom abs_eq: ∀ a: ℤ, |a| = a ∨ |a| = -a.
