Import /Logic;

Theorem exist_function: ∀ A B: U, ∀ P: A -> B -> U, (∀ x: A, ∃ y: B, P x y) -> ∃ f: A -> B, ∀ x: A, P x (f x);
Proof;
    intros;
    apply (ex_intro ? ? (λ x, ex_value ? ? (H x)));
    intros;
    apply (ex_proof B (P x) ?1);
Qed;

Axiom compos_eq: ∀ X Y Z: U, ∀ f: Y -> Z, ∀ g: X -> Y, ∀ x: X, (f ∘ g) x = f (g x);
Suggest goal default apply compact_eq with label Trivial;