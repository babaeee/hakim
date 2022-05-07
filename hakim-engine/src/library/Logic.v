Axiom ex_intro: ∀ A: U, ∀ P: A → U, ∀ x: A, P x -> ∃ y: A, P y.
Axiom ex_ind: ∀ A: U, ∀ P: A → U, (∃ y: A, P y) -> ∀ Q: U, (∀ x: A, P x -> Q) -> Q.
Suggest hyp default destruct $n with (ex_ind ? ?) to ($n_value $n_proof); Destruct.

Axiom False_ind: False -> ∀ A: U, A.
Suggest hyp default apply (False_ind $n ?); Contradiction.
Axiom True_proof: True.
Axiom True_proof_unique: ∀ p: True, p = True_proof.
Todo imply_refl: ∀ A: U, A -> A.
Todo imply_trans: ∀ A B C: U, (A -> B) -> (B -> C) -> (A -> C).

Axiom and_intro: ∀ A B: U, A -> B -> A ∧ B. 
Axiom and_ind: ∀ A B: U, A ∧ B -> ∀ Q: U, (A -> B -> Q) -> Q.
Suggest hyp default destruct $n with (and_ind ? ?) to ($n_l $n_r); Destruct.
Suggest goal default apply and_intro; Destruct.

Axiom or_introl: ∀ A B: U, A -> A ∨ B.
Axiom or_intror: ∀ A B: U, B -> A ∨ B.
Suggest goal apply or_introl; A ∨ B => A.
Suggest goal apply or_intror; A ∨ B => B.
Axiom or_sym: ∀ A B: U, B ∨ A -> A ∨ B.
Axiom or_ind: ∀ A B: U, A ∨ B -> ∀ Q: U, (A -> Q) -> (B -> Q) -> Q.
Axiom or_to_imply: ∀ A B: U, ((B -> False) -> A) -> A ∨ B.
Suggest hyp default destruct $n with (or_ind ? ?); Destruct.
Suggest goal default chain (apply or_to_imply) (intros); A ∨ B => ~ B → A.
Suggest goal chain (apply or_sym) (apply or_to_imply) (intros); A ∨ B => ~ A → B.

Axiom p_or_not_p: ∀ A: U, A ∨ (A → False).
Todo NNPP: ∀ A: U, ((A -> False) -> False) -> A.
Todo or_not_intro: ∀ A B: U, ((B -> False) -> A) -> A ∨ B.
