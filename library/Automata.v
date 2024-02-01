Import /List;
Import /Set;
Import /EnumerativeCombinatorics;

Axiom IsWord: list char → list char → U;
Axiom IsWord_unfold: ∀ sigma s: list char, IsWord sigma s → member_set s ⊆ member_set sigma;
Axiom IsWord_fold: ∀ sigma s: list char, member_set s ⊆ member_set sigma → IsWord sigma s;
Suggest goal default apply IsWord_fold with label IsWord sigma s => member_set s ⊆ member_set sigma;
Suggest hyp default apply IsWord_unfold in $n with label IsWord sigma s => member_set s ⊆ member_set sigma;

Axiom words: list char → set (list char);
Axiom in_words_unfold: ∀ sigma s: list char, s ∈ words sigma -> IsWord sigma s;
Axiom in_words_fold: ∀ sigma s: list char, IsWord sigma s -> s ∈ words sigma;
Suggest goal default apply in_words_fold with label s ∈ words sigma => IsWord sigma s;
Suggest hyp default apply in_words_unfold in $n with label s ∈ words sigma => IsWord sigma s;

Axiom rep: list char → ℤ → list char;
Axiom rep_0: ∀ s, rep s 0 = "";
Axiom rep_unfold: ∀ s, ∀ n, n ≥ 0 → rep s (n + 1) = s + rep s n;
Suggest goal default apply rep_0 with label Trivial;

Todo rep_len: ∀ s: list char, ∀ n: ℤ, 0 ≤ n → |rep s n| = n * |s|;
Suggest goal default apply rep_len with label Trivial;
Todo rep_add_1: ∀ s, ∀ n, n ≥ 0 → rep s (n + 1) = rep s n + s;

Todo rep_nth: ∀ d: char, ∀ s, ∀ k, k > 0 -> ∀ i, 0 ≤ i ∧ i < k * |s| -> nth d (rep s k) i = nth d s (i mod |s|);
Todo rep_append: ∀ s, ∀ n m, 0 ≤ n → 0 ≤ m → rep s (n + m) = rep s n + rep s m;
Todo valid_paren_n: ∀ n: ℤ, 0 ≤ n → valid_paren (rep "(" n + rep ")" n);
Todo rep_to_repeat: ∀ c: char, ∀ n: ℤ, 0 ≤ n → rep ([c]) n = repeat n c;

Axiom in_Lmult_unfold: ∀ L1 L2: set (list char), ∀ s: list char, s ∈ L1 * L2 → ∃ a b: list char, s = a + b ∧ a ∈ L1 ∧ b ∈ L2;
Axiom in_Lmult_fold: ∀ L1 L2: set (list char), ∀ a b: list char, a ∈ L1 -> b ∈ L2 -> a + b ∈ L1 * L2;
Suggest goal default apply in_Lmult_fold with label Trivial;
Suggest hyp default apply in_Lmult_unfold in $n with label Trivial;

Axiom lpow: set (list char) → ℤ → set (list char);
Axiom lpow_0: ∀ L, lpow L 0 = {""};
Axiom lpow_unfold: ∀ L, ∀ n, 0 ≤ n ->  lpow L (n + 1) = L * (lpow L n);

Todo lpow_1: ∀ L, lpow L 1 = L;
Todo rep_in_lpow: ∀ s, ∀ L, s ∈ L → ∀ k, 0 ≤ k → rep s k ∈ lpow L k;

Axiom star: set (list char) → set (list char);
Axiom star_unfold: ∀ L, ∀ s, s ∈ star L → ∃ n: ℤ, 0 ≤ n ∧ s ∈ lpow L n;
Axiom star_fold: ∀ L, ∀ s, ∀ n, 0 ≤ n → s ∈ lpow L n → s ∈ star L;
Suggest hyp default apply star_unfold in $n with label s ∈ star L => ∃ n, s ∈ lpow L n;

Theorem star_append: ∀ a b, ∀ L, a ∈ star L -> b ∈ star L -> a + b ∈ star L;
Proof;
    intros;
    apply star_unfold in H ;
    destruct H with (ex_ind ? ?) to (n n_property);
    apply star_unfold in H0 ;
    destruct H0 with (ex_ind ? ?) to (m m_property);
    destruct n_property with (and_ind ? ?) to (n_property_l n_property_r) ;
    revert n_property_r;
    revert a;
    revert n_property_l;
    revert n;
    apply z_induction_simple;
    intros;
    replace #1 (lpow L (n + 1)) with (L * lpow L (n )) in n_property_r;
    apply lpow_unfold;
    assumption;
    apply in_Lmult_unfold in n_property_r ;
    destruct n_property_r with (ex_ind ? ?) to (x x_property);
    destruct x_property with (ex_ind ? ?) to (y y_property);
    add_hyp H0_ex := (H0 (y));
    destruct y_property with (and_ind ? ?) to (y_property_l y_property_r) ;
    Seq (add_hyp (⁨y ∈ lpow L n⁩)) (remove_hyp H0_ex) (Switch 1) (add_hyp H0_ex_o := (H0_ex H1)) (remove_hyp H1) (remove_hyp H0_ex) ;
    apply star_unfold in H0_ex_o ;
    destruct H0_ex_o with (ex_ind ? ?) to (k k_property);
    apply (⁨star_fold ?0 ?2 (k + 1) ?6 ?8⁩);
    rewrite y_property_l ;
    replace #1 (x + y + b) with (x +( y + b));
    auto_list;
    replace #1 (lpow L (k + 1)) with (L * lpow L (k ));
    apply lpow_unfold;
    assumption;
    apply in_Lmult_fold ;
    assumption;
    assumption;
    lia;
    assumption;
    intros;
    replace #1 (lpow L 0) with ({""}) in n_property_r;
    apply lpow_0;
    apply singleton_unfold in n_property_r ;
    apply (⁨star_fold ?0 ?2 m ?6 ?8⁩);
    z3;
    assumption;
Qed;
Suggest goal default apply star_append with label a + b ∈ star L =>  a ∈ star L and b ∈ star L;

Todo star_incl_sigma: ∀ sigma, ∀ L, L ⊆ words sigma → star L ⊆ words sigma;

Axiom DFA: list char -> U;
Axiom construct_DFA: ∀ sigma, ℤ → list (char → ℤ) → ℤ → set ℤ → DFA sigma;
Axiom #1 edges_of_DFA: ∀ sigma, DFA sigma -> list (char → ℤ);
Axiom #1 accept_nodes_of_DFA: ∀ sigma, DFA sigma -> set ℤ;
Axiom #1 start_of_DFA: ∀ sigma, DFA sigma -> ℤ;

Axiom n_DFA_pos: ∀ sigma, ∀ A: DFA sigma, |A| > 0;
Axiom #1 run_dfa: ∀ sigma, (DFA sigma) → ℤ → (list char) → ℤ;
Axiom run_dfa_nil: ∀ sigma, ∀ A: DFA sigma, ∀ u, run_dfa A u "" = u;
Axiom run_dfa_cons: ∀ sigma, ∀ A: DFA sigma, ∀ u, ∀ s, ∀ c, ∀ f: char → ℤ, f = nth (λ a: char, - 1) (edges_of_DFA A) u → ∀ v, v = f c → run_dfa A u (c :: s) = run_dfa A v s;

Todo run_dfa_append: ∀ sigma: list char, ∀ A: DFA sigma, ∀ u, ∀ a b, run_dfa A u (a + b) = run_dfa A (run_dfa A u a) b;

Axiom #1 Ldfa: ∀ sigma, DFA sigma → set (list char);
Axiom Ldfa_unfold: ∀ sigma, ∀ A: DFA sigma, ∀ s, s ∈ Ldfa A -> IsWord sigma s ∧ run_dfa A (start_of_DFA A) s ∈ accept_nodes_of_DFA A;
Axiom Ldfa_fold: ∀ sigma, ∀ A: DFA sigma, ∀ s, IsWord sigma s ∧ run_dfa A (start_of_DFA A) s ∈ accept_nodes_of_DFA A -> s ∈ Ldfa A;
Suggest goal default apply Ldfa_fold with label Destruct;
Suggest hyp default apply Ldfa_unfold in $n with label Destruct;

Todo pumping_lemma: ∀ sigma, ∀ A: DFA sigma, 
    ∀ s, IsWord sigma s → |s| ≥ |A| → ∀ start, 0 ≤ start ∧ start < |A| →
    ∃ x y z, s = x + y + z ∧ |y| > 0 ∧ |x| + |y| ≤ |A| ∧ ∀ i, i ≥ 0 → run_dfa A start (x + rep y i + z) = run_dfa A start s;
Todo pumping_lemma_Ldfa: ∀ sigma, ∀ A: DFA sigma, 
    ∀ s, s ∈ Ldfa A → |s| ≥ |A| →
    ∃ x y z, s = x + y + z ∧ |y| > 0 ∧ |x| + |y| ≤ |A| ∧ ∀ i, i ≥ 0 → x + rep y i + z ∈ Ldfa A;
Todo pumping_lemma_mid_big: ∀ sigma, ∀ A: DFA sigma, 
    ∀ s, IsWord sigma s → |s| ≥ |A| → ∀ start, 0 ≤ start ∧ start < |A| →
    ∃ x y z, s = x + y + z ∧ |y| > 0 ∧ |x| + |z| ≤ |A| ∧ ∀ i, i ≥ 0 → run_dfa A start (x + rep y i + z) = run_dfa A start s;

Axiom TM: U;
Axiom turing_accept: TM -> list char -> U;
Axiom turing_reject: TM -> list char -> U;
Axiom turing_halt: TM -> list char -> U;
Axiom halt_unfold: ∀ t: TM, ∀ s, turing_halt t s -> turing_accept t s ∨ turing_reject t s;
Axiom halt_fold: ∀ t: TM, ∀ s, turing_accept t s ∨ turing_reject t s -> turing_halt t s;
Suggest goal default apply halt_fold with label Destruct;
Suggest hyp default apply halt_unfold in $n with label Destruct;

Axiom turing_accept_not_reject: ∀ t: TM, ∀ s, turing_accept t s -> ~ turing_reject t s;
Axiom turing_reject_not_accept: ∀ t: TM, ∀ s, turing_reject t s -> ~ turing_accept t s;

Axiom accept_everything: TM;
Axiom accept_everything_def: ∀ s, turing_accept accept_everything s;
Suggest goal auto apply accept_everything_def with label Trivial;
Axiom reject_everything: TM;
Axiom reject_everything_def: ∀ s, turing_reject reject_everything s;
Suggest goal auto apply reject_everything_def with label Trivial;
Axiom loop_on_everything: TM;
Axiom loop_on_everything_def: ∀ s, ~ turing_halt loop_on_everything s;
Suggest goal auto apply loop_on_everything with label Trivial;

Axiom decider: TM -> U;
Axiom decider_fold: ∀ t: TM, (∀ s, turing_halt t s) -> decider t;
Axiom decider_unfold: ∀ t: TM, decider t -> (∀ s, turing_halt t s);
Suggest goal default apply decider_fold with label Destruct;
Suggest hyp default apply decider_unfold in $n with label Destruct;

Axiom turing_to_str: TM -> list char;
Axiom turing_to_str_unique: ∀ t t0: TM, ∀ a a0: list char, turing_to_str t + "*" + a = turing_to_str t0 + "*" + a0 -> t = t0 ∧ a = a0;
Axiom turing_to_str_not_have_star: ∀ t: TM, ~ '*' in (turing_to_str t); 
Axiom universal_turing_machine: TM;

Axiom utm_accept_unfold: ∀ t: TM, ∀ s, turing_accept universal_turing_machine (turing_to_str t + "*" + s) -> turing_accept t s;
Axiom utm_accept_fold: ∀ t: TM, ∀ s, turing_accept t s -> turing_accept universal_turing_machine (turing_to_str t + "*" + s);
Suggest goal default apply utm_accept_fold with label Destruct;
Suggest hyp default apply utm_accept_unfold in $n with label Destruct;

Axiom utm_reject_unfold: ∀ t: TM, ∀ s, turing_reject universal_turing_machine (turing_to_str t + "*" + s) -> turing_reject t s;
Axiom utm_reject_fold: ∀ t: TM, ∀ s, turing_reject t s -> turing_reject universal_turing_machine (turing_to_str t + "*" + s);
Suggest goal default apply utm_reject_fold with label Destruct;
Suggest hyp default apply utm_reject_unfold in $n with label Destruct;

Axiom utm_halt_unfold: ∀ t: TM, ∀ s, turing_halt universal_turing_machine (turing_to_str t + "*" + s) -> turing_halt t s;
Axiom utm_halt_fold: ∀ t: TM, ∀ s, turing_halt t s -> turing_halt universal_turing_machine (turing_to_str t + "*" + s);
Suggest goal default apply utm_halt_fold with label Destruct;
Suggest hyp default apply utm_halt_unfold in $n with label Destruct;

Axiom utm_reject_invalid_format: ∀ s: list char, (~ ∃ t: TM, ∃ a: list char, s = turing_to_str t + "*" + a) → turing_reject universal_turing_machine s;

Axiom select_tm: list char -> TM;
Axiom select_tm_fold: ∀ s, turing_accept (select_tm s) s;
Axiom select_tm_unfold: ∀ s1 s2, turing_accept (select_tm s1) s2 -> s1 = s2;
Axiom select_tm_decider: ∀ s, decider (select_tm s);

Axiom conditional_tm: TM -> TM -> TM -> TM;
Axiom conditional_tm_accept_unfold: ∀ cond then else: TM, ∀ s, turing_accept (conditional_tm cond then else) s
    -> turing_accept cond s ∧ turing_accept then s ∨ turing_reject cond s ∧ turing_accept else s;
Axiom conditional_tm_accept_fold: ∀ cond then else: TM, ∀ s,
    turing_accept cond s ∧ turing_accept then s ∨ turing_reject cond s ∧ turing_accept else s
    -> turing_accept (conditional_tm cond then else) s;
Axiom conditional_tm_reject_unfold: ∀ cond then else: TM, ∀ s, turing_reject (conditional_tm cond then else) s
    -> turing_accept cond s ∧ turing_reject then s ∨ turing_reject cond s ∧ turing_reject else s;
Axiom conditional_tm_reject_fold: ∀ cond then else: TM, ∀ s,
    turing_accept cond s ∧ turing_reject then s ∨ turing_reject cond s ∧ turing_reject else s
    -> turing_reject (conditional_tm cond then else) s;

Axiom is_decidable: set (list char) -> U;
Axiom is_decidable_fold: ∀ lang, (∃ t, decider t ∧ ∀ s, s ∈ lang ↔ turing_accept t s) -> is_decidable lang;
Axiom is_decidable_unfold: ∀ lang, is_decidable lang -> 
    (∃ t, decider t ∧ (∀ s, s ∈ lang <-> turing_accept t s) ∧ (∀ s, ~ s ∈ lang <-> turing_reject t s));
Suggest goal default apply is_decidable_fold with label Destruct;
Suggest hyp default apply is_decidable_unfold in $n with label Destruct;

Axiom #2 computable: ∀ X Y: U, (X → Y) → U;
Axiom computable_concat: computable (plus (list char));
Axiom computable_const: ∀ X Y: U, ∀ a: Y, computable (λ x: X, a);
Suggest goal default apply computable_const with label Trivial;

Axiom computable_partials_first: ∀ X Y Z: U, ∀ f: (X → Y → Z), ∀ g: (X → Y), 
    computable f -> computable g -> computable  (λ x, f x (g x));
Axiom computable_partials_second: ∀ X Y Z: U, ∀ f: (X → Y → Z), ∀ g: (Y → X), 
    computable f -> computable g -> computable  (λ y, f (g y) y);
Axiom computable_compos: ∀ X Y Z: U, ∀ f: (Y → Z), ∀ g: (X → Y), computable f -> computable g
    -> computable (λ x, f (g x));
Axiom computable_eq_if_f: ∀ X Y Z: U, ∀ left: (X → Z), ∀ right: (X → Z), ∀ then: (X → Y), ∀ else: (X → Y),
    computable left -> computable right -> computable then -> computable else
        -> computable (λ x, if_f (left x = right x) (then x) (else x));

Axiom decider_to_computable: ∀ t, decider t -> ∃ f: list char → ℤ, computable f ∧
    (∀ s, turing_accept t s <-> f s = 1) ∧ (∀ s, turing_reject t s <-> f s = 0);

Axiom computable_function_to_turing: ∀ f: list char  → ℤ, computable f
    -> ∃ t: TM, (∀ s, f s > 0 -> turing_accept t s) ∧ (∀ s, f s = 0 -> turing_reject t s)
    ∧ (∀ s, f s < 0 -> ~ turing_halt t s);
    
