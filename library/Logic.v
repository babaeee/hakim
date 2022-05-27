Axiom ex_intro: ∀ A: U, ∀ P: A → U, ∀ x: A, P x -> ∃ y: A, P y.
Axiom ex_ind: ∀ A: U, ∀ P: A → U, (∃ y: A, P y) -> ∀ Q: U, (∀ x: A, P x -> Q) -> Q.
Suggest hyp default destruct $n with (ex_ind ? ?) to ($n_value $n_proof); Destruct.

Theorem False_ind: False -> ∀ A: U, A.
Proof. intros. assumption. Qed.

Suggest hyp default apply (False_ind $n ?); Contradiction.
Theorem True_proof: True.
Proof. intros. assumption. Qed.

Axiom True_proof_unique: ∀ p: True, p = True_proof.
Theorem imply_refl: ∀ A: U, A -> A.
Proof. intros. assumption. Qed.
Theorem imply_trans: ∀ A B C: U, (A -> B) -> (B -> C) -> (A -> C).
Proof. intros. assumption. Qed.

Theorem and_intro: ∀ A B: U, A -> B -> A ∧ B. 
Proof. intros. assumption. Qed.
Theorem and_ind: ∀ A B: U, A ∧ B -> ∀ Q: U, (A -> B -> Q) -> Q.
Proof. intros. assumption. Qed.
Suggest hyp default destruct $n with (and_ind ? ?) to ($n_l $n_r); Destruct.
Suggest goal default apply and_intro; Destruct.

Theorem or_introl: ∀ A B: U, A -> A ∨ B.
Proof. intros. assumption. Qed.
Theorem or_intror: ∀ A B: U, B -> A ∨ B.
Proof. intros. assumption. Qed.
Suggest goal apply or_introl; A ∨ B => A.
Suggest goal apply or_intror; A ∨ B => B.
Theorem or_sym: ∀ A B: U, B ∨ A -> A ∨ B.
Proof. intros. assumption. Qed.
Theorem or_ind: ∀ A B: U, A ∨ B -> ∀ Q: U, (A -> Q) -> (B -> Q) -> Q.
Proof. intros. assumption. Qed.
Theorem or_to_imply: ∀ A B: U, ((B -> False) -> A) -> A ∨ B.
Proof. intros. assumption. Qed.
Suggest hyp default destruct $n with (or_ind ? ?); Destruct.
Suggest goal default chain (apply or_to_imply) (intros); A ∨ B => ~ B → A.
Suggest goal chain (apply or_sym) (apply or_to_imply) (intros); A ∨ B => ~ A → B.

Theorem p_or_not_p: ∀ A: U, A ∨ (A → False).
Proof. intros. assumption. Qed.
Theorem NNPP: ∀ A: U, ((A -> False) -> False) -> A.
Proof. intros. assumption. Qed.
