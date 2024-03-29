Suggest hyp default rewrite $n with label Rewrite;

Axiom eq_refl: ∀ A: U, ∀ x: A, eq A x x;
Theorem eq_sym: ∀ A: U, ∀ x y: A, x = y -> y = x;
Proof;
    intros;
    rewrite H;
    apply eq_refl;
Qed;
Suggest hyp apply eq_sym in $n with label a = b => b = a;
Suggest goal apply eq_sym with label a = b => b = a;
