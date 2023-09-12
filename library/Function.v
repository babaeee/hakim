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

Definition #2 injective := λ A B: U, λ f: A -> B, λ S: set A, ∀ x y: A, x ∈ S -> y ∈ S -> f x = f y -> x = y;
Theorem injective_unfold: ∀ A B: U, ∀ f: A -> B, ∀ S: set A, injective f S -> (∀ x y: A, x ∈ S -> y ∈ S -> f x = f y -> x = y);
Proof; unfold injective; intros A B f S H; assumption; Qed;
Theorem injective_fold: ∀ A B: U, ∀ f: A -> B, ∀ S: set A, (∀ x y: A, x ∈ S -> y ∈ S -> f x = f y -> x = y) -> injective f S;
Proof; unfold injective; intros; assumption; Qed;
Suggest hyp default apply injective_unfold in $n with label Destruct;
Suggest goal default apply injective_fold with label Destruct;

Todo injective_included: ∀ A B: U, ∀ f: A -> B, ∀ x y: set A, x ⊆ y -> injective f y -> injective f x;

Definition #2 projection := λ A B: U, λ S: set A, λ f: A -> B, { y: B | ∃ x: A, x ∈ S ∧ y = f x };
Axiom projection_in_intro_l: ∀ A B: U, ∀ f: A -> B, ∀ S: set A, ∀ y: B, y ∈ projection S f -> ∃ x: A, x ∈ S ∧ y = f x;
Axiom projection_in_intro_r: ∀ A B: U, ∀ f: A -> B, ∀ S: set A, ∀ y: B, (∃ x: A, x ∈ S ∧ y = f x) -> y ∈ projection S f;
Suggest hyp default apply projection_in_intro_l in $n with label Destruct;
Suggest goal default apply projection_in_intro_r with label Destruct;

Definition #2 bijective := λ A B: U, λ f: A -> B, λ a: set A, λ b: set B, injective f a ∧ projection a f = b;
Axiom bijective_unfold: ∀ A B: U, ∀ f: A → B, ∀ a: set A, ∀ b: set B, bijective f a b -> injective f a ∧ projection a f = b;
Axiom bijective_fold: ∀ A B: U, ∀ f: A → B, ∀ a: set A, ∀ b: set B, injective f a -> projection a f = b -> bijective f a b;
Suggest hyp default apply bijective_unfold in $n with label Destruct;
Suggest goal default apply bijective_fold with label Destruct;

Todo #8 bicompos: ∀ A B C: U, ∀ a: set A, ∀ b: set B, ∀ c: set C, ∀ f: A -> B, ∀ g: B -> C, ∀ gH: bijective g b c, ∀ fH: bijective f a b, bijective (g ∘ f) a c;
