Import /Logic.

Theorem exist_function: ∀ A B: U, ∀ P: A -> B -> U, (∀ x: A, ∃ y: B, P x y) -> ∃ f: A -> B, ∀ x: A, P x (f x).
Proof.
    intros.
    apply (ex_intro ? ? (λ x, ex_value ? ? (H x))).
    intros.
    apply (ex_proof B (P x) ?1).
Qed.

