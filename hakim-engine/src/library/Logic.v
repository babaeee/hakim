Axiom ex_intro: ∀ A: U, ∀ P: A → U, ∀ x: A, P x -> ∃ y: A, P y.
Axiom ex_ind: ∀ A: U, ∀ P: A → U, (∃ y: A, P y) -> ∀ Q: U, (∀ x: A, P x -> Q) -> Q.
Axiom False_ind: False -> ∀ A: U, A.
Axiom imply_refl: ∀ A: U, A -> A.
Axiom imply_trans: ∀ A B C: U, (A -> B) -> (B -> C) -> (A -> C).
