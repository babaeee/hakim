Axiom eq_refl: ∀ A: U, ∀ x: A, eq A x x.
Theorem eq_sym: ∀ A: U, ∀ x y: A, x = y -> y = x.
Proof.
    intros.
    rewrite H.
    apply eq_refl.
Qed.
