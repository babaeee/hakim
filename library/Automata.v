Import /List;
Import /Set;

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

Todo rep_nth: ∀ d: char, ∀ s, ∀ k, k > 0 -> ∀ i, 0 ≤ i ∧ i < k * |s| -> nth d (rep s k) i = nth d s (i mod |s|);

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

Axiom NFA: ℤ → list char → list (char → ℤ) → ℤ → set ℤ → U;
Axiom NFA_fold: ∀ n, 0 < n → ∀ sigma: list char, 0 < |sigma| 
    → ∀ edges: list (char → ℤ), |edges| = n → ∀ start, 0 ≤ start ∧ start < n 
    → ∀ F, F ⊆ { x: ℤ | 0 ≤ x ∧ x < n } → NFA n sigma edges start F;
Suggest goal default apply NFA_fold with label Destruct;

Axiom #5 run_nfa: ∀ n, ∀ sigma, ∀ edges, ∀ start, ∀ F, (NFA n sigma edges start F) → ℤ → (list char) → ℤ;
Axiom run_nfa_nil: ∀ n, ∀ sigma, ∀ edges, ∀ start, ∀ F, ∀ A: NFA n sigma edges start F, ∀ u, run_nfa A u "" = u;
Axiom run_nfa_cons: ∀ n, ∀ sigma, ∀ edges, ∀ start, ∀ F, ∀ A: NFA n sigma edges start F, ∀ u, ∀ s, ∀ c, ∀ f: char → ℤ, f = nth (λ a: char, - 1) edges u → ∀ v, v = f c → run_nfa A u (c :: s) = run_nfa A v s;

Axiom #5 Lnfa: ∀ n, ∀ sigma, ∀ edges, ∀ start, ∀ F, (NFA n sigma edges start F) → set (list char);
Axiom Lnfa_unfold: ∀ n, ∀ sigma, ∀ edges, ∀ start, ∀ F, ∀ A: NFA n sigma edges start F, ∀ s, s ∈ Lnfa A -> IsWord sigma s ∧ run_nfa A start s ∈ F;
Axiom Lnfa_fold: ∀ n, ∀ sigma, ∀ edges, ∀ start, ∀ F, ∀ A: NFA n sigma edges start F, ∀ s, IsWord sigma s ∧ run_nfa A start s ∈ F -> s ∈ Lnfa A;
Suggest goal default apply Lnfa_fold with label Destruct;
Suggest hyp default apply NFA_unfold in $n with label Destruct;

