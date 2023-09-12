Import /EnumerativeCombinatorics;
Import /Function;

Axiom species: (U → U) → U;

Axiom #2 Fun: ∀ A: U, ∀ X: U → U, ∀ x: species X, set A → set (X A);
Axiom #6 Is: ∀ A B: U, ∀ a: set A, ∀ b: set B, ∀ f: A → B, ∀ X: U → U, ∀ x: species X, ∀ H: bijective f a b, (X A) -> (X B);
Axiom specise_compos: ∀ X: U → U, ∀ x: species X,
    ∀ A B C: U, ∀ n: ℤ, 0 < n → ∀ a: set A, |a| = n → ∀ b: set B, ∀ c: set C, 
        ∀ f: A → B, ∀ H: bijective f a b, ∀ g: B → C, ∀ H0: bijective g b c,
            ∀ s: X A, s ∈ Fun x a → Is x (bicompos H0 H) s = Is x H0 (Is x H s);
Axiom specise_id: ∀ X: U → U, ∀ x: species X,
    ∀ A: U, ∀ n: ℤ, 0 < n → ∀ a: set A, |a| = n 
        → ∀ f: A → A, ∀ H: bijective f a a, 
            (∀ s: X A, s ∈ Fun x a -> Is x H s = s);

Axiom #1 Fun_eq: ∀ X: U → U, ∀ x: species X, ∀ F: ∀ A: U, set A → set (X A), Universe;
Axiom Fun_eq_unfold: ∀ X: U → U, ∀ x: species X, ∀ F: ∀ A: U, set A → set (X A), 
    Fun_eq x F -> ∀ A: U, ∀ a: set A, finite a -> Fun x a = F A a;
Suggest hyp default apply Fun_eq_unfold in $n with label Destruct;
Axiom #1 Is_eq: ∀ X: U → U, ∀ x: species X, ∀ is: ∀ A B: U, ∀ a: set A, ∀ b: set B, ∀ f: A → B, X A → X B, Universe;
Axiom Is_eq_unfold: ∀ X: U → U, ∀ x: species X, 
    ∀ is: ∀ A B: U, ∀ a: set A, ∀ b: set B, ∀ f: A → B, X A → X B, Is_eq x is
        -> ∀ A B: U, ∀ a: set A, finite a -> ∀ b: set B, ∀ f: A → B, ∀ H: bijective f a b, 
            Is x H = is A B a b f;
Suggest hyp default apply Is_eq_unfold in $n with label Destruct;

Axiom specise_intro: ∀ X: U → U,
    ∀ F: ∀ A: U, set A → set (X A),      
    ∀ is: ∀ A B: U, ∀ a: set A, ∀ b: set B, ∀ f: A → B, X A → X B,
        (∀ A B C: U, ∀ n: ℤ, 0 < n → ∀ a: set A, |a| = n → ∀ b: set B, ∀ c: set C, 
            (∀ f: A → B, bijective f a b → ∀ g: B → C, bijective g b c 
                → ∀ s: X A, s ∈ F A a → is A C a c (g ∘ f) s = is B C b c g (is A B a b f s))
            ∧ (∀ f: (A → A), bijective f a a → ∀ s: X A, s ∈ F A a → is A A a a f s = s) )
                -> ∃ x: species X, Fun_eq x F ∧ Is_eq x is;
Suggest hyp default apply specise_compos in $n with label Destruct;
Suggest goal default apply specise_intro with label Destruct;

Import /Set;

Definition projection_Is := λ x: species (λ A: Universe, set A), ∀ A B: Universe, ∀ a: set A, ∀ b: set B, ∀ f: A → B, ∀ H: bijective f a b, ∀ s: set A, Is x H s = projection s f;
Axiom projection_Is_unfold: ∀ x: species (λ A: U, set A), projection_Is x → ∀ A B: U, ∀ a: set A, ∀ b: set B, ∀ f: A → B, ∀ H: bijective f a b, ∀ s: set A, Is x H s = projection s f;
Suggest hyp default apply projection_Is_unfold in $n with label Destruct;

Axiom spX: species (λ A: U, set A);
Axiom FspX: ∀ A: U, ∀ a: set A, Fun spX a = if_f (|a| = 1) {a} {};
Axiom IsspX: projection_Is spX;

Axiom sp1: species (λ A: U, set A);
Axiom Fsp1: ∀ A: U, ∀ a: set A, Fun sp1 a = if_f (|a| = 0) {{}} {};
Axiom Issp1: projection_Is sp1;

Axiom sp0: ∀ X: U → U, species X;
Axiom Fsp0: ∀ X: U → U, ∀ A: U, ∀ a: set A, Fun (sp0 X) a = {};

Axiom #2 naturality: ∀ X Y: U → U, ∀ x: species X, ∀ y: species Y, ∀ tr: ∀ A: U, X A → Y A, Universe;
Axiom naturality_fold: ∀ X Y: U → U, ∀ x: species X, ∀ y: species Y, ∀ tr: ∀ A: U, X A → Y A, 
    (∀ A B: U, ∀ a: set A, ∀ b: set B, ∀ f: A → B, finite a -> ∀ H: bijective f a b, 
        ∀ s: X A, s ∈ Fun x a -> Is y H (tr A s ) = tr B (Is x H s))
        -> naturality x y tr;
Suggest goal default apply naturality_fold with label Destruct;

Axiom #2 eq_sp: ∀ X Y: U → U, ∀ x: species X, ∀ y: species Y, Universe;
Axiom eq_sp_intro: ∀ X: U → U, ∀ Y: U → U, ∀ x: species X, ∀ y: species Y, ∀ tr: ∀ A, X A → Y A, 
    (∀ A: U, ∀ a: set A, finite a → bijective (tr A) (Fun x a) (Fun y a)) 
    -> naturality x y tr -> eq_sp x y;
Suggest goal default apply eq_sp_intro with label Destruct;

Axiom Fplus: ∀ X: U → U, ∀ x y: species X, ∀ A: U, ∀ a: set A, finite a → Fun (x + y) a = Fun x a ∪ Fun y a; 
Axiom Isplus: ∀ X: U → U, ∀ x y: species X, 
    ∀ A B: U, ∀ a: set A, ∀ b: set B, ∀ f: A → B, finite a -> ∀ H: bijective f a b,
        ∀ s: X A, s ∈ Fun (x + y) a -> Is (x + y) H s = if_f (s ∈ Fun x a) (Is x H s) (Is y H s);

Axiom #1 sumable: ∀ X: U → U, ∀ x y: species X, Universe;
Axiom sumable_fold: ∀ X: U → U, ∀ x y: species X, 
    (∀ A: U, ∀ a: set A, ∀ n: ℤ, 0 ≤ n → |a| = n → Fun x a ∩ Fun y a = {})
        -> sumable x y;
Axiom sumable_unfold: ∀ X: U → U, ∀ x y: species X, sumable x y
    -> (∀ A: U, ∀ a: set A, ∀ n: ℤ, 0 ≤ n → |a| = n → Fun x a ∩ Fun y a = {});
Suggest hyp default apply sumable_unfold in $n with label Destruct;
Suggest goal default apply sumable_fold with label Destruct;

Theorem plus_sp_comm: ∀ X: U → U, ∀ x y: species X, sumable x y -> eq_sp (x + y) (y + x);
Proof;
    intros;
    apply (⁨eq_sp_intro ?0 ?2 ?4 ?6 (λ A: Universe, λ a: X A, a) ?10 ?12⁩);
    apply naturality_fold;
    intros;
    replace #1 (Is (y + x) H1 s) with (if_f (s ∈ Fun y a) (Is y H1 s) (Is x H1 s));
    apply Isplus;
    replace #1 (Fun (x + y) a) with (Fun x a ∪ Fun (y) a) in H2;
    apply Fplus;
    assumption;
    replace #1 (Fun (y + x) a) with (Fun y a ∪ Fun  x a);
    apply Fplus;
    assumption;
    auto_set;
    assumption;
    replace #1 (Is (x + y) H1 s) with (if_f (s ∈ Fun x a) (Is x H1 s) (Is y H1 s));
    apply Isplus;
    assumption;
    assumption;
    add_hyp (s ∈ Fun (x) a ∨ ~ s ∈ Fun (x) a);
    assumption;
    destruct H3 with (or_ind ? ?);
    add_hyp (s ∈ Fun (y) a);
    replace #1 (Fun (x + y) a) with (Fun x a ∪ Fun ( y) a) in H2;
    apply Fplus;
    assumption;
    auto_set;
    replace #1 (if_f (s ∈ Fun y a) (Is y H1 s) (Is x H1 s)) with ( (Is y H1 s) );
    apply if_true;
    assumption;
    replace #1 (if_f (s ∈ Fun x a) (Is x H1 s) (Is y H1 s)) with ( (Is y H1 s));
    apply if_false;
    assumption;
    auto_list;
    apply sumable_unfold in H ;
    add_hyp H_ex := (H (A));
    add_hyp H_ex_ex := (H_ex (a));
    add_hyp (~ s ∈ Fun y a);
    add_hyp H_ex_ex_ex := (H_ex_ex (|a|));
    Seq (add_hyp (⁨0 ≤ |a|⁩)) (remove_hyp H_ex_ex_ex) (Switch 1) (add_hyp H_ex_ex_ex_o := (H_ex_ex_ex H4)) (remove_hyp H4) (remove_hyp H_ex_ex_ex) ;
    z3;
    apply finite_len_ge_0;
    assumption;
    z3;
    intros;
    apply bijective_fold ;
    replace #1 (projection (Fun (x + y) a) (λ a0: (X A), a0)) with ((Fun (x + y) a));
    unfold projection;
    apply eq_sym ;
    apply set_equality ;
    apply included_fold ;
    intros;
    apply set_from_func_unfold in H1 ;
    destruct H1 with (ex_ind ? ?) to (x0 x0_property);
    auto_set;
    apply included_fold ;
    intros;
    apply set_from_func_fold ;
    apply (ex_intro ? ? (a0));
    z3;
    replace #1 (Fun (x + y) a) with (Fun x a ∪ Fun y a);
    apply Fplus;
    assumption;
    replace #1 (Fun (y + x) a) with (Fun y a ∪  Fun x a);
    apply Fplus;
    assumption;
    auto_set;
    apply injective_fold ;
    intros;
    assumption;
Qed; 

Axiom #1 sp_nth: ∀ X: U → U, species X -> ℤ -> species X;
Axiom Fsp_nth: ∀ X: U → U, ∀ x: species X, ∀ n: ℤ, ∀ A: U, ∀ a: set A, Fun (sp_nth x n) a = if_f (|a| = n) (Fun x a) ({});
Axiom Issp_nth: ∀ X: U → U, ∀ x: species X, ∀ n: ℤ, 
    ∀ A B: U, ∀ a: set A, finite a -> ∀ b: set B, ∀ f: A → B, ∀ H: bijective f a b, 
        Is x H = Is (sp_nth x n) H;

