Import /List.
Import /NumberTheory.
Import /Sigma.

Definition injective := λ A B: U, λ f: A -> B, λ S: set A, ∀ x y: A, x ∈ S -> y ∈ S -> f x = f y -> x = y.
Theorem injective_unfold: ∀ A B: U, ∀ f: A -> B, ∀ S: set A, injective A B f S -> (∀ x y: A, x ∈ S -> y ∈ S -> f x = f y -> x = y).
Proof. unfold injective. intros A B f S H. assumption. Qed.
Theorem injective_fold: ∀ A B: U, ∀ f: A -> B, ∀ S: set A, (∀ x y: A, x ∈ S -> y ∈ S -> f x = f y -> x = y) -> injective A B f S.
Proof. unfold injective. intros. assumption. Qed.
Suggest hyp default apply injective_unfold in $n; Destruct.
Suggest goal default apply injective_fold; Destruct.

Definition #1 projection := λ A B: U, λ S: set A, λ f: A -> B, { y: B | ∃ x: A, x ∈ S ∧ y = f x }.
Axiom projection_in_intro_l: ∀ A B: U, ∀ f: A -> B, ∀ S: set A, ∀ y: B, y ∈ projection B S f -> ∃ x: A, x ∈ S ∧ y = f x.
Axiom projection_in_intro_r: ∀ A B: U, ∀ f: A -> B, ∀ S: set A, ∀ y: B, (∃ x: A, x ∈ S ∧ y = f x) -> y ∈ projection B S f.
Suggest hyp default apply projection_in_intro_l in $n; Destruct.
Suggest goal default apply projection_in_intro_r; Destruct.

Axiom projection_empty: ∀ A B: U, ∀ f: A -> B, projection B {} f = {}.
Axiom projection_empty_unique:  ∀ A B: U, ∀ f: A -> B, ∀ S: set A, projection B S f = {} -> S = {}.
Axiom rule_of_bijectionR: ∀ A B: U, ∀ f: A -> B, ∀ S: set A, finite S -> injective A B f S -> |S| = |projection B S f|.
Axiom projection_finiteR: ∀ A B: Universe, ∀ f: A → B, ∀ S: set A, finite S → finite (projection B S f).

Import /set.
Import /Arith.
Import /Logic.
Import /Eq.
Import /Combinatorics.

Todo asl_zarb2: ∀ X: U, ∀ C: set X, ∀ n m: ℤ, n > 0 -> m > 0 -> ∀ Y: U, ∀ f: X -> Y, |projection Y C f| = n -> (∀ y: Y, y ∈ (projection Y C f) -> |{ x: X | x ∈ C ∧ f x = y }| = m) -> ∀ c: ℤ, c = n * m -> |C| = c.

Axiom cm: ℤ -> ℤ -> ℤ.
Axiom cm0: ∀ r, 0 ≤ r -> cm r 0 = 1.
Axiom cmeq: ∀ r, 0 ≤ r -> cm r r = 1.
Axiom cmdefr: ∀ a b, 0 < a -> 0 < b -> b < a -> cm a b = cm (a - 1) b + cm (a - 1) (b - 1).
Axiom cm2: ∀ r, 2 * cm r 2 = r * (r - 1).

Theorem sigma_0_n: ∀ n, (Σ i in [0, n) i) = cm n 2.
Proof.
    add_hyp (∀ n0: ℤ, 0 ≤ n0 → (Σ i in [0, n0) i) = cm n0 2).
    apply z_induction_simple.
    intros.
    add_from_lib cm2.
    add_hyp cm2_ex := (cm2 (n)).
    add_hyp cm2_ex0 := (cm2 (n+1)).
    lia.
    add_from_lib cm2.
    add_hyp cm2_ex := (cm2 (0)).
    lia.
    intros.
    add_hyp (n < 0 ∨ n ≥ 0).
    lia.
    destruct H0 with (or_ind ? ?).
    apply H.
    assumption.
    add_hyp (∀ x, 0 ≤ x -> (Σ i in [0, - x) i) = cm (- x) 2).
    apply z_induction_simple.
    intros.
    add_from_lib cm2.
    add_hyp cm2_ex := (cm2 (-n0)).
    add_hyp cm2_ex0 := (cm2 (-(n0+1))).
    lia.
    add_from_lib cm2.
    add_hyp cm2_ex := (cm2 (-0)).
    lia.
    add_hyp (∃ k, k = - n).
    apply (ex_intro ? ? (-n)).
    auto_list.
    destruct H2 with (ex_ind ? ?) to (k k_property).
    add_hyp (n = -k).
    lia.
    rewrite H2.
    apply H1.
    lia.
Qed.

Theorem binomial_coefficients: ∀ n, 0 ≤ n -> ∀ a b, (a+b) ^ n = (Σ i in [0, n + 1) cm n i * a ^ i * b ^ (n - i)).
Proof.
    apply z_induction_simple.
    Switch 1.
    intros.
    replace #1 (Σ i in [0, 0 + 1) cm 0 i * a ^ i * b ^ - i) with (Σ i in [0, 0 + 1) 1).
    apply sigma_f_equal.
    intros.
    add_hyp (i=0).
    lia.
    rewrite H1.
    replace #1 (- 0) with (0).
    lia.
    replace #1 (cm 0 0) with (1).
    apply cm0.
    auto_list.
    lia.
    lia.
    lia.
    intros.
    add_hyp H0_ex := (H0 (a)).
    add_hyp H0_ex_ex := (H0_ex (b)).
    add_hyp ((a + b) * (a + b) ^ n = a * (Σ i in [0, n + 1) cm n i * a ^ i * b ^ (n - i)) + b * Σ i0 in [0, n + 1) cm n i0 * a ^ i0 * b ^ (n - i0)).
    replace #1 (a * (Σ i in [0, n + 1) cm n i * a ^ i * b ^ (n - i)) + b * Σ i0 in [0, n + 1) cm n i0 * a ^ i0 * b ^ (n - i0)) with ((a+b) * (Σ i in [0, n + 1) cm n i * a ^ i * b ^ (n - i))).
    lia.
    rewrite H0_ex_ex.
    auto_list.
    replace #1 ((a + b) ^ (n + 1)) with ((a+b)*(a + b) ^ n).
    apply pow_unfold_l.
    assumption.
    rewrite H1.
    replace #1 (a * (Σ i in [0, n + 1) cm n i * a ^ i * b ^ (n - i))) with ( (Σ i in [0, n + 1) a * cm n i * a ^ i * b ^ (n - i))).
    replace #1 (Σ i in [0, n + 1) a * cm n i * a ^ i * b ^ (n - i)) with (Σ i in [0, n + 1) a * (cm n i * a ^ i * b ^ (n - i))).
    apply sigma_f_equal.
    intros.
    lia.
    lia.
    apply sigma_factor.
    replace #1 (b * (Σ i0 in [0, n + 1) cm n i0 * a ^ i0 * b ^ (n - i0))) with ((Σ i0 in [0, n + 1) cm n i0 * a ^ i0 * b ^ (n - i0 + 1))).
    replace #1 (Σ i0 in [0, n + 1) cm n i0 * a ^ i0 * b ^ (n - i0 + 1)) with (Σ i0 in [0, n + 1) b * (cm n i0 * a ^ i0 * b ^ (n - i0))).
    apply sigma_f_equal.
    intros.
    replace #1 (b ^ (n - i + 1)) with (b * b ^ (n - i)).
    apply pow_unfold_l.
    lia.
    lia.
    lia.
    apply sigma_factor.
    replace #1 ((Σ i in [0, n + 1) a * cm n i * a ^ i * b ^ (n - i))) with ((Σ i in [0, n + 1) cm n i * a ^ (i+1) * b ^ (n - (i+1) + 1))).
    apply sigma_f_equal.
    intros.
    replace #1 (a ^ (i + 1)) with (a * a ^ i).
    apply pow_unfold_l.
    assumption.
    lia.
    lia.
    replace #1 ((Σ i in [0, n + 1) cm n i * a ^ (i + 1) * b ^ (n - (i + 1) + 1))) with ((Σ i in [0+1, n + 1 +1) cm n (i-1) * a ^ i * b ^ (n - i + 1))).
    apply sigma_shift.
    replace #1 ((Σ i in [0 + 1, n + 1 + 1) cm n (i - 1) * a ^ i * b ^ (n - i + 1))) with ((Σ i in [0 + 1, n + 1) cm n (i - 1) * a ^ i * b ^ (n - i + 1)) + cm n n * a ^ (n+1) * b ^ (n - (n+1) + 1)).
    lia.
    replace #1 (cm n n * a ^ (n + 1) * b ^ (n - (n + 1) + 1)) with (a ^ (n + 1)).
    add_from_lib cmeq.
    add_hyp cmeq_ex := (cmeq (n)).
    replace #1 ((n - (n + 1) + 1)) with (0).
    lia.
    add_hyp (⁨0 ≤ n⁩).
    remove_hyp cmeq_ex.
    Switch 1.
    add_hyp cmeq_ex_o := (cmeq_ex H2).
    remove_hyp H2.
    remove_hyp cmeq_ex.
    rewrite cmeq_ex_o.
    lia.
    assumption.
    replace #1 ((Σ i0 in [0, n + 1) cm n i0 * a ^ i0 * b ^ (n - i0 + 1))) with ((Σ i0 in [1, n + 1) cm n i0 * a ^ i0 * b ^ (n - i0 + 1)) + cm n 0 * a ^ 0 * b ^ (n - 0 + 1)).
    lia.
    replace #1 (cm n 0 * a ^ 0 * b ^ (n - 0 + 1)) with (b ^ (n - 0 + 1)).
    add_from_lib cm0.
    add_hyp cm0_ex := (cm0 (n)).
    add_hyp (⁨0 ≤ n⁩).
    remove_hyp cm0_ex.
    Switch 1.
    add_hyp cm0_ex_o := (cm0_ex H2).
    remove_hyp H2.
    remove_hyp cm0_ex.
    rewrite cm0_ex_o.
    lia.
    assumption.
    replace #1 ((Σ i in [0 + 1, n + 1) cm n (i - 1) * a ^ i * b ^ (n - i + 1)) + a ^ (n + 1) + ((Σ i0 in [1, n + 1) cm n i0 * a ^ i0 * b ^ (n - i0 + 1)) + b ^ (n - 0 + 1))) with ((Σ i in [1, n + 1) cm n (i - 1) * a ^ i * b ^ (n - i + 1)) + ((Σ i0 in [1, n + 1) cm n i0 * a ^ i0 * b ^ (n - i0 + 1)) + a ^ (n + 1) + b ^ (n - 0 + 1))).
    lia.
    replace #1 ((Σ i in [1, n + 1) cm n (i - 1) * a ^ i * b ^ (n - i + 1)) + ((Σ i0 in [1, n + 1) cm n i0 * a ^ i0 * b ^ (n - i0 + 1)) + a ^ (n + 1) + b ^ (n - 0 + 1))) with ((Σ i in [1, n + 1) cm n (i - 1) * a ^ i * b ^ (n - i + 1)) + (Σ i0 in [1, n + 1) cm n i0 * a ^ i0 * b ^ (n - i0 + 1)) + a ^ (n + 1) + b ^ (n - 0 + 1)).
    lia.
    replace #1 ((Σ i in [1, n + 1) cm n (i - 1) * a ^ i * b ^ (n - i + 1)) + (Σ i0 in [1, n + 1) cm n i0 * a ^ i0 * b ^ (n - i0 + 1))) with ((Σ i in [1, n + 1) cm n (i - 1) * a ^ i * b ^ (n - i + 1) + cm n i * a ^ i * b ^ (n - i + 1))).
    apply sigma_plus2.
    replace #1 ((Σ i in [1, n + 1) cm n (i - 1) * a ^ i * b ^ (n - i + 1) + cm n i * a ^ i * b ^ (n - i + 1))) with ((Σ i in [1, n + 1) (cm n (i - 1) + cm n i) * a ^ i * b ^ (n - i + 1))).
    apply sigma_f_equal.
    intros.
    lia.
    lia.
    replace #1 ((Σ i in [1, n + 1) (cm n (i - 1) + cm n i) * a ^ i * b ^ (n - i + 1))) with ((Σ i in [1, n + 1) (cm (n+1) i) * a ^ i * b ^ (n - i + 1))).
    apply sigma_f_equal.
    intros.
    add_from_lib cmdefr.
    add_hyp cmdefr_ex := (cmdefr (n+1)).
    add_hyp cmdefr_ex_ex := (cmdefr_ex (i)).
    add_hyp (⁨0 < n + 1⁩).
    remove_hyp cmdefr_ex_ex.
    Switch 1.
    add_hyp cmdefr_ex_ex_o := (cmdefr_ex_ex H4).
    remove_hyp H4.
    remove_hyp cmdefr_ex_ex.
    add_hyp (⁨0 < i⁩).
    remove_hyp cmdefr_ex_ex_o.
    Switch 1.
    add_hyp cmdefr_ex_ex_o_o := (cmdefr_ex_ex_o H4).
    remove_hyp H4.
    remove_hyp cmdefr_ex_ex_o.
    add_hyp (⁨i < n + 1⁩).
    remove_hyp cmdefr_ex_ex_o_o.
    Switch 1.
    add_hyp cmdefr_ex_ex_o_o_o := (cmdefr_ex_ex_o_o H4).
    remove_hyp H4.
    remove_hyp cmdefr_ex_ex_o_o.
    replace #1 ((n + 1 - 1)) with (n) in cmdefr_ex_ex_o_o_o.
    lia.
    replace #1 ((n + 1 - 1)) with (n) in cmdefr_ex_ex_o_o_o.
    lia.
    apply eq_sym in cmdefr_ex_ex_o_o_o.
    rewrite cmdefr_ex_ex_o_o_o.
    apply eq_sym in cmdefr_ex_ex_o_o_o.
    rewrite cmdefr_ex_ex_o_o_o.
    lia.
    assumption.
    lia.
    lia.
    lia.
    replace #1 (n - 0 + 1) with (n+1).
    lia.
    replace #1 (Σ i in [0, n + 1 + 1) cm (n + 1) i * a ^ i * b ^ (n + 1 - i)) with (cm (n + 1) 0 * a ^ 0 * b ^ (n + 1 - 0) + Σ i in [1, n + 1 + 1) cm (n + 1) i * a ^ i * b ^ (n + 1 - i)).
    lia.
    replace #1 (Σ i in [1, n + 1 + 1) cm (n + 1) i * a ^ i * b ^ (n + 1 - i)) with (cm (n + 1) (n + 1) * a ^ (n + 1) * b ^ (n + 1 - (n + 1)) + Σ i in [1, n + 1) cm (n + 1) i * a ^ i * b ^ (n + 1 - i)).
    lia.
    replace #1 (cm (n + 1) 0 * a ^ 0 * b ^ (n + 1 - 0)) with (b^(n+1)).
    Switch 1.
    replace #1 (cm (n + 1) (n + 1) * a ^ (n + 1) * b ^ (n + 1 - (n + 1))) with (a^(n+1)).
    Switch 1.
    replace #1 (Σ i in [1, n + 1) cm (n + 1) i * a ^ i * b ^ (n + 1 - i)) with (Σ i in [1, n + 1) cm (n + 1) i * a ^ i * b ^ (n - i + 1)).
    Switch 1.
    lia.
    apply sigma_f_equal.
    intros.
    lia.
    lia.
    add_from_lib cmeq.
    add_hyp cmeq_ex := (cmeq (n+1)).
    add_hyp (⁨0 ≤ n + 1⁩).
    remove_hyp cmeq_ex.
    Switch 1.
    add_hyp cmeq_ex_o := (cmeq_ex H2).
    remove_hyp H2.
    remove_hyp cmeq_ex.
    rewrite cmeq_ex_o.
    replace #1 ((n + 1 - (n + 1))) with (0).
    lia.
    lia.
    lia.
    add_from_lib cm0.
    add_hyp cm0_ex := (cm0 (n+1)).
    add_hyp (⁨0 ≤ n + 1⁩).
    remove_hyp cm0_ex.
    Switch 1.
    add_hyp cm0_ex_o := (cm0_ex H2).
    remove_hyp H2.
    remove_hyp cm0_ex.
    rewrite cm0_ex_o.
    lia.
    lia.
Qed.

Theorem sigma_cm_n: ∀ n, 0 ≤ n -> (Σ i in [0, n + 1) cm n i) = 2 ^ n.
Proof.
    intros.
    add_from_lib binomial_coefficients.
    add_hyp binomial_coefficients_ex := (binomial_coefficients (n)).
    Seq (add_hyp (0 ≤ n)) (remove_hyp binomial_coefficients_ex) (Switch 1) (add_hyp binomial_coefficients_ex_o := (binomial_coefficients_ex H0)) (remove_hyp H0) (remove_hyp binomial_coefficients_ex).
    add_hyp binomial_coefficients_ex_o_ex := (binomial_coefficients_ex_o (1)).
    add_hyp binomial_coefficients_ex_o_ex_ex := (binomial_coefficients_ex_o_ex (1)).
    lia.
    assumption.
Qed.

Todo count_of_paths: ∀ r, 0 ≤ r -> ∀ u, 0 ≤ u -> |{ l: list char | cnt 'r' l = r ∧ cnt 'u' l = u ∧ |l| = r + u }| = cm (r+u) u.

Axiom valid_paren: list char -> Universe.
Axiom valid_paren_unfold: ∀ l, valid_paren l -> l = "" ∨ ∃ x y, valid_paren x ∧ valid_paren y ∧ l = "(" ++ x ++ ")" ++ y.
Suggest hyp default apply valid_paren_unfold in $n; Destruct.
Axiom valid_paren_fold: ∀ l, (∃ x y, valid_paren x ∧ valid_paren y ∧ l = "(" ++ x ++ ")" ++ y) -> valid_paren l.
Axiom valid_paren_empty: valid_paren "".
Theorem valid_paren_wrap: ∀ l, valid_paren l -> valid_paren ("(" ++ l ++ ")").
Proof.
    intros.
    apply valid_paren_fold.
    apply (ex_intro ? ? (l)).
    apply (ex_intro ? ? ("")).
    apply and_intro.
    apply and_intro.
    auto_list.
    Switch 1.
    assumption.
    apply valid_paren_empty.
Qed.
Theorem valid_paren_concat: ∀ a b, valid_paren a -> valid_paren b -> valid_paren (a ++ b).
Proof.
    apply list_induction_len.
    intros.
    apply valid_paren_unfold in H0.
    destruct H0 with (or_ind ? ?).
    destruct H0 with (ex_ind ? ?) to (x x_property).
    destruct x_property with (ex_ind ? ?) to (y y_property).
    destruct y_property with (and_ind ? ?) to (y_property_l y_property_r).
    destruct y_property_r with (and_ind ? ?) to (y_property_r_l y_property_r_r).
    rewrite y_property_r_r.
    apply valid_paren_fold.
    apply (ex_intro ? ? (x)).
    apply (ex_intro ? ? (y++b0)).
    apply and_intro.
    apply and_intro.
    auto_list.
    apply H.
    assumption.
    assumption.
    rewrite y_property_r_r.
    apply list_len_concat_lt.
    auto_list.
    assumption.
    rewrite H0.
    replace #1 (("" ++ b0)) with (b0).
    auto_list.
    assumption.
Qed.
Suggest goal default apply valid_paren_wrap; valid_paren ("(" ++ l ++ ")") => valid_paren l.
Suggest goal default apply valid_paren_concat; valid_paren (a ++ b) => valid_paren a ∧ valid_paren b.
Theorem valid_paren_len_even: ∀ a, valid_paren a -> 2 | |a|.
Proof.
    apply list_induction_len.
    intros.
    apply valid_paren_unfold in H0.
    destruct H0 with (or_ind ? ?).
    destruct H0 with (ex_ind ? ?) to (x x_property).
    destruct x_property with (ex_ind ? ?) to (y y_property).
    destruct y_property with (and_ind ? ?) to (y_property_l y_property_r).
    destruct y_property_r with (and_ind ? ?) to (y_property_r_l y_property_r_r).
    replace #1 (b) with ("(" ++ x ++ ")" ++ y) in H.
    assumption.
    apply H in y_property_r_l.
    lia.
    apply H in y_property_l.
    lia.
    replace #1 (|b|) with (|x|+|y|+2).
    rewrite y_property_r_r.
    lia.
    apply divide_plus.
    apply divide_fold.
    apply (ex_intro ? ? (1)).
    lia.
    apply divide_plus.
    assumption.
    assumption.
    rewrite H0.
    apply divide_fold.
    apply (ex_intro ? ? (0)).
    lia.
Qed.
Theorem valid_paren_single: valid_paren "()".
Proof.
    replace #1 ("()") with ("("++""++")").
    auto_list.
    apply valid_paren_wrap.
    apply valid_paren_empty.
Qed.
Theorem valid_paren_cnt_left: ∀ a, valid_paren a -> ∀ k, 2 * k = |a| -> cnt '(' a = k.
Proof.
    apply list_induction_len.
    intros.
    apply valid_paren_unfold in H0.
    destruct H0 with (or_ind ? ?).
    destruct H0 with (ex_ind ? ?) to (x x_property).
    destruct x_property with (ex_ind ? ?) to (y y_property).
    destruct y_property with (and_ind ? ?) to (y_property_l y_property_r).
    destruct y_property_r with (and_ind ? ?) to (y_property_r_l y_property_r_r).
    replace #1 (b) with ("(" ++ x ++ ")" ++ y) in H.
    assumption.
    add_from_lib valid_paren_len_even.
    add_hyp valid_paren_len_even_ex := (valid_paren_len_even (x)).
    add_hyp valid_paren_len_even_ex0 := (valid_paren_len_even (y)).
    add_hyp (⁨valid_paren x⁩).
    remove_hyp valid_paren_len_even_ex.
    Switch 1.
    add_hyp valid_paren_len_even_ex_o := (valid_paren_len_even_ex H0).
    remove_hyp H0.
    remove_hyp valid_paren_len_even_ex.
    add_hyp (⁨valid_paren y⁩).
    remove_hyp valid_paren_len_even_ex0.
    Switch 1.
    add_hyp valid_paren_len_even_ex0_o := (valid_paren_len_even_ex0 H0).
    remove_hyp H0.
    remove_hyp valid_paren_len_even_ex0.
    apply divide_unfold in valid_paren_len_even_ex_o.
    apply divide_unfold in valid_paren_len_even_ex0_o.
    destruct valid_paren_len_even_ex_o with (ex_ind ? ?) to (cx cx_property).
    destruct valid_paren_len_even_ex0_o with (ex_ind ? ?) to (cy cy_property).
    add_hyp H_ex := (H (x)).
    add_hyp H_ex0 := (H (y)).
    add_hyp (⁨|x| < |"(" ++ x ++ ")" ++ y|⁩).
    remove_hyp H_ex.
    Switch 1.
    add_hyp H_ex_o := (H_ex H0).
    remove_hyp H0.
    remove_hyp H_ex.
    add_hyp (⁨|y| < |"(" ++ x ++ ")" ++ y|⁩).
    remove_hyp H_ex0.
    Switch 1.
    add_hyp H_ex0_o := (H_ex0 H0).
    remove_hyp H0.
    remove_hyp H_ex0.
    add_hyp (⁨valid_paren x⁩).
    remove_hyp H_ex_o.
    Switch 1.
    add_hyp H_ex_o_o := (H_ex_o H0).
    remove_hyp H0.
    remove_hyp H_ex_o.
    add_hyp (⁨valid_paren y⁩).
    remove_hyp H_ex0_o.
    Switch 1.
    add_hyp H_ex0_o_o := (H_ex0_o H0).
    remove_hyp H0.
    remove_hyp H_ex0_o.
    add_hyp H_ex_o_o_ex := (H_ex_o_o (cx)).
    add_hyp H_ex0_o_o_ex := (H_ex0_o_o (cy)).
    add_hyp (⁨2 * cx = |x|⁩).
    remove_hyp H_ex_o_o_ex.
    Switch 1.
    add_hyp H_ex_o_o_ex_o := (H_ex_o_o_ex H0).
    remove_hyp H0.
    remove_hyp H_ex_o_o_ex.
    add_hyp (⁨2 * cy = |y|⁩).
    remove_hyp H_ex0_o_o_ex.
    Switch 1.
    add_hyp H_ex0_o_o_ex_o := (H_ex0_o_o_ex H0).
    remove_hyp H0.
    remove_hyp H_ex0_o_o_ex.
    rewrite y_property_r_r.
    replace #1 (k) with (cx+cy+1).
    Switch 1.
    lia.
    add_hyp (2*k=2*cx+2*cy+2).
    rewrite H1.
    rewrite cx_property.
    rewrite cy_property.
    rewrite y_property_r_r.
    lia.
    lia.
    assumption.
    assumption.
    assumption.
    assumption.
    lia.
    lia.
    assumption.
    assumption.
    replace #1 (|b|) with (0) in H1.
    rewrite H0.
    lia.
    replace #1 (k) with (0).
    lia.
    rewrite H0.
    lia.
Qed.