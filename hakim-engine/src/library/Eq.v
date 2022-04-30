Axiom eq_refl: ∀ A: U, ∀ x: A, eq A x x.
Theorem eq_sym: ∀ A: U, ∀ x y: A, x = y -> y = x.
Proof.
    intros.
    rewrite H.
    apply eq_refl.
Qed.

Axiom eq_subtract_positive_lt: ∀ a b c: ℤ, 0 < b -> a + b = c -> a < c.