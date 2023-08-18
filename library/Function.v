Import /Logic;

Theorem exist_function: ∀ A B: U, ∀ P: A -> B -> U, (∀ x: A, ∃ y: B, P x y) -> ∃ f: A -> B, ∀ x: A, P x (f x);
Proof;
    intros;
    apply (ex_intro ? ? (λ x, ex_value ? ? (H x)));
    intros;
    apply (ex_proof B (P x) ?1);
Qed;
Theorem exist_function_not_total: ∀ A B: U, B → ∀ S: set A, ∀ P: A → B → U, 
        (∀ x: A, x ∈ S → ∃ y: B, P x y) 
        → ∃ f: A → B, ∀ x: A, x ∈ S → P x (f x);
Proof;
    intros;
    apply (⁨exist_function ?0 ?2 (λ x: A, λ y: B, x ∈ S → P x y) ?6⁩);
    intros;
    add_hyp (~ x ∈ S ∨ x ∈ S);
    assumption;
    destruct H1 with (or_ind ? ?);
    add_hyp H0_ex := (H0 (x));
    Seq (add_hyp (⁨x ∈ S⁩)) (remove_hyp H0_ex) (Switch 1) (add_hyp H0_ex_o := (H0_ex H2)) (remove_hyp H2) (remove_hyp H0_ex);
    destruct H0_ex_o with (ex_ind ? ?) to (y y_property);
    apply (ex_intro ? ? (y));
    assumption;
    assumption;
    apply (ex_intro ? ? (H));
    assumption;
Qed;

Axiom compos_eq: ∀ X Y Z: U, ∀ f: Y -> Z, ∀ g: X -> Y, ∀ x: X, (f ∘ g) x = f (g x);
Suggest goal default apply compact_eq with label Trivial;