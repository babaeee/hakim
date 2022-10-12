Axiom ex_intro: ∀ A: U, ∀ P: A → U, ∀ x: A, P x -> ∃ y: A, P y.
Axiom ex_value: ∀ A: U, ∀ P: A → U, (∃ y: A, P y) -> A.
Axiom ex_proof: ∀ A: U, ∀ P: A → U, ∀ e: (∃ y: A, P y), P (ex_value ? ? e).
Theorem ex_ind: ∀ A: U, ∀ P: A → U, (∃ y: A, P y) -> ∀ Q: U, (∀ x: A, P x -> Q) -> Q.
Proof.
    intros.
    apply (H0 (ex_value A P H) ?1).
    apply (ex_proof A P ?1).
Qed.
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
Theorem contpos: ∀ P Q: U, (~ P -> ~ Q) -> Q -> P.
Proof. intros. assumption. Qed.

Theorem not_exists_imply_forall: ∀ A: U, ∀ P: A -> U, (~ ∃ x: A, P x) -> ∀ x: A, ~ P x.
Proof.
    intros.
    apply H.
    apply (ex_intro ? ? (x)).
    assumption.
Qed.
Suggest hyp default apply not_exists_imply_forall in $n; ~ ∃ x: A, P x => ∀ x: A, ~ P x.
Theorem not_forall_imply_exists: ∀ A: U, ∀ P: A -> U, (~ ∀ x: A, P x) -> ∃ x: A, ~ P x.
Proof.
    intros.
    apply NNPP.
    intros.
    apply not_exists_imply_forall in H0.
    apply H.
    intros.
    apply NNPP.
    apply H0.
Qed.
Suggest hyp default apply not_forall_imply_exists in $n; ~ ∀ x: A, P x => ∃ x: A, ~ P x.

Axiom #1 if_f: ∀ A: U, U -> A -> A -> A.
Axiom if_true: ∀ A P: U, ∀ x y: A, P -> if_f P x y = x.
Axiom if_false: ∀ A P: U, ∀ x y: A, ~ P -> if_f P x y = y.
Suggest goal auto apply if_true; (if P then x else y) = x => P.
Suggest goal auto apply if_false; (if P then x else y) = y  => ~ P.
Theorem if_possible_values: ∀ A P: U, ∀ x y: A, if_f P x y = x ∨ if_f P x y = y.
Proof.
    intros.
    add_hyp (P ∨ ~P).
    assumption.
    destruct H with (or_ind ? ?).
    apply or_intror.
    apply if_false.
    assumption.
    apply or_introl.
    apply if_true.
    assumption.
Qed.
Axiom empty_or_Inhabits: ∀ T: U, (∀ x: T, False) ∨ ∃ x: T, True.

Todo iff_imp_l: ∀ A B: U, (A <-> B) -> B -> A.
Todo iff_imp_r: ∀ A B: U, (A <-> B) -> A -> B.