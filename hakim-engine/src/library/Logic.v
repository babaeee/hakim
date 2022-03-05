Axiom ex_intro: ∀ A: U, ∀ P: A → U, ∀ x: A, P x -> ∃ y: A, P y.
Axiom ex_ind: ∀ A: U, ∀ P: A → U, (∃ y: A, P y) -> ∀ Q: U, (∀ x: A, P x -> Q) -> Q.
Axiom False_ind: False -> ∀ A: U, A.
Axiom True_proof: True.
Axiom True_proof_unique: ∀ p: True, p = True_proof.
Todo imply_refl: ∀ A: U, A -> A.
Todo imply_trans: ∀ A B C: U, (A -> B) -> (B -> C) -> (A -> C).
Axiom and_intro: ∀ A B: U, A -> B -> A ∧ B. 
Axiom and_ind: ∀ A B: U, A ∧ B -> ∀ Q: U, (A -> B -> Q) -> Q.
Axiom or_introl: ∀ A B: U, A -> A ∨ B.
Axiom or_intror: ∀ A B: U, B -> A ∨ B.
Axiom or_ind: ∀ A B: U, A ∨ B -> ∀ Q: U, (A -> Q) -> (B -> Q) -> Q.
Axiom p_or_not_p: ∀ A: U, A ∨ (A → False).
Todo NNPP: ∀ A: U, ((A -> False) -> False) -> A.
Todo or_not_intro: ∀ A B: U, ((B -> False) -> A) -> A ∨ B.
