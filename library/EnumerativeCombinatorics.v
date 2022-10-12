Import /set.
Import /List.
Import /NumberTheory.
Import /Sigma.

Theorem add_len: ∀ T: U, ∀ S: set T, ∀ n: ℤ, n ≥ 0 → |S| = n → ∀ a: T, ~ a ∈ S → |S ∪ {a}| = n + 1.
Proof.
    intros.
    replace #1 (n) with (|S|).
    auto_set.
    apply finite_add_len.
    assumption.
    apply len_ge_0_finite.
    lia.
Qed.

Todo subset_len: ∀ T: U, ∀ S: set T, ∀ n: ℤ, n ≥ 0 → |S| = n + 1 -> ∀ a: T, a ∈ S -> |S ∖ {a}| = n.

Import /Combinatorics.

Theorem asle_jame: ∀ T: U, ∀ A B: set T, ∀ n m: ℤ, n ≥ 0 -> m ≥ 0 -> |A| = n -> |B| = m -> A ∩ B = {} -> |A ∪ B| = n + m.
Proof.
    intros T A B n m Hn.
    revert A.
    revert B.
    revert m.
    revert Hn.
    revert n.
    apply z_induction_simple.
    Switch 1.
    intros.
    apply empty_len_unique in H0.
    replace #1 (A ∪ B) with (B).
    rewrite H0.
    auto_set.
    lia.
    intros.
    add_hyp (∃ x: T, x ∈ A).
    apply len_gt_0_not_empty_set.
    lia.
    destruct H5 with (ex_ind ? ?) to (x x_property).
    replace #1 (A ∪ B) with (((A ∖ {x}) ∪ B) ∪ {x}).
    auto_set.
    replace #1 (n + 1 + m) with (n + m + 1).
    lia.
    apply add_len.
    intros.
    apply union_unfold in H5.
    destruct H5 with (or_ind ? ?).
    add_hyp (x ∈ A ∩ B).
    auto_set.
    replace #1 (A ∩ B) with ({}) in H6.
    assumption.
    auto_set.
    auto_set.
    Switch 1.
    lia.
    apply H0.
    apply empty_set_eq.
    intros.
    apply eq_set_empty in H4.
    add_hyp H4_ex := (H4 (x0)).
    auto_set.
    assumption.
    replace #1 (A) with ((A ∖ {x}) ∪ {x}) in H2.
    auto_set.
    replace #1 (|A ∖ {x} ∪ {x}|) with (|A ∖ {x}| + |{x}|) in H2.
    replace #1 (|{x}|) with (1).
    apply singleton_len.
    apply add_len.
    auto_set.
    auto_list.
    apply finite_len_ge_0.
    apply (⁨finite_included ?0 ?2 A ?6 ?8⁩).
    auto_set.
    apply len_ge_0_finite.
    replace #1 (A ∖ {x} ∪ {x}) with (A) in H2.
    auto_set.
    lia.
    replace #1 (|{x}|) with (1) in H2.
    apply singleton_len.
    lia.
    assumption.
Qed.
Theorem rule_of_minus2: ∀ T: U, ∀ U A: set T, ∀ n m a: ℤ, n ≥ 0 -> m ≥ 0 -> |U| = n -> |U ∖ A| = m -> A ⊆ U -> a = n - m -> |A| = a.
Proof.
    intros.
    replace #1 (A) with (U0 ∖ (U0 ∖ A)).
    auto_set.
    rewrite H4.
    apply eq_sym in H1.
    rewrite H1.
    apply eq_sym in H2.
    rewrite H2.
    apply rule_of_minus.
    auto_set.
    apply len_ge_0_finite.
    lia.
Qed.

Definition #2 injective := λ A B: U, λ f: A -> B, λ S: set A, ∀ x y: A, x ∈ S -> y ∈ S -> f x = f y -> x = y.
Theorem injective_unfold: ∀ A B: U, ∀ f: A -> B, ∀ S: set A, injective f S -> (∀ x y: A, x ∈ S -> y ∈ S -> f x = f y -> x = y).
Proof. unfold injective. intros A B f S H. assumption. Qed.
Theorem injective_fold: ∀ A B: U, ∀ f: A -> B, ∀ S: set A, (∀ x y: A, x ∈ S -> y ∈ S -> f x = f y -> x = y) -> injective f S.
Proof. unfold injective. intros. assumption. Qed.
Suggest hyp default apply injective_unfold in $n; Destruct.
Suggest goal default apply injective_fold; Destruct.
Todo injective_included: ∀ A B: U, ∀ f: A -> B, ∀ x y: set A, x ⊆ y -> injective f y -> injective f x.

Definition #2 projection := λ A B: U, λ S: set A, λ f: A -> B, { y: B | ∃ x: A, x ∈ S ∧ y = f x }.
Axiom projection_in_intro_l: ∀ A B: U, ∀ f: A -> B, ∀ S: set A, ∀ y: B, y ∈ projection S f -> ∃ x: A, x ∈ S ∧ y = f x.
Axiom projection_in_intro_r: ∀ A B: U, ∀ f: A -> B, ∀ S: set A, ∀ y: B, (∃ x: A, x ∈ S ∧ y = f x) -> y ∈ projection S f.
Suggest hyp default apply projection_in_intro_l in $n; Destruct.
Suggest goal default apply projection_in_intro_r; Destruct.

Axiom projection_empty: ∀ A B: U, ∀ f: A -> B, projection {} f = {}.
Axiom projection_empty_unique:  ∀ A B: U, ∀ f: A -> B, ∀ S: set A, projection S f = {} -> S = {}.
Todo projection_singleton: ∀ A B: U, ∀ f: A -> B, ∀ a: A, projection {a} f = {f a}.
Todo projection_union: ∀ A B: U, ∀ f: A -> B, ∀ x y: set A, projection (x ∪ y) f = projection x f ∪ projection y f.

Theorem rule_of_bijectionR: ∀ A B: U, ∀ f: A -> B, ∀ S: set A, injective f S -> ∀ n: ℤ, n ≥ 0 -> |projection S f| = n -> |S| = n.
Proof.
    intros.
    revert H1.
    revert H.
    revert S.
    revert f.
    revert H0.
    revert n.
    apply z_induction_simple.
    Switch 1.
    intros.
    apply empty_len_unique in H1.
    apply projection_empty_unique in H1.
    rewrite H1.
    lia.
    intros.
    add_hyp (∃ y: B, y ∈ projection S f).
    apply len_gt_0_not_empty_set.
    lia.
    destruct H2 with (ex_ind ? ?) to (y y_property).
    apply projection_in_intro_l in y_property.
    destruct y_property with (ex_ind ? ?) to (x x_property).
    replace #1 (S) with ((S ∖ {x}) ∪ {x}).
    auto_set.
    apply asle_jame.
    auto_set.
    apply singleton_len.
    apply (⁨H0 f ?2 ?4 ?6⁩).
    replace #1 (projection (S ∖ {x}) f) with (projection (S) f ∖ {y}).
    apply set_equality.
    apply included_fold.
    intros.
    apply setminus_unfold in H2.
    destruct H2 with (and_ind ? ?) to (H2_l H2_r).
    apply projection_in_intro_l in H2_l.
    destruct H2_l with (ex_ind ? ?) to (xp xp_property).
    apply projection_in_intro_r.
    apply (ex_intro ? ? (xp)).
    apply and_intro.
    assumption.
    apply setminus_fold.
    apply and_intro.
    intros.
    apply singleton_unfold in H2.
    destruct xp_property with (and_ind ? ?) to (xp_property_l xp_property_r).
    add_hyp (a = y).
    Seq (add_hyp (⁨a ∈ {y}⁩)) (remove_hyp H2_r) (Switch 1) (add_hyp H2_r_o := (H2_r H3)) (remove_hyp H3) (remove_hyp H2_r).
    assumption.
    apply singleton_fold.
    destruct x_property with (and_ind ? ?) to (x_property_l x_property_r).
    replace #1 (xp) with (x) in xp_property_r.
    auto_set.
    auto_set.
    auto_set.
    assumption.
    apply included_fold.
    intros.
    apply projection_in_intro_l in H2.
    apply setminus_fold.
    apply and_intro.
    intros.
    apply singleton_unfold in H3.
    destruct H2 with (ex_ind ? ?) to (xp xp_property).
    destruct xp_property with (and_ind ? ?) to (xp_property_l xp_property_r).
    add_hyp (x = xp).
    apply injective_unfold in H1.
    apply H1.
    auto_set.
    auto_set.
    assumption.
    auto_set.
    destruct H2 with (ex_ind ? ?) to (xp xp_property).
    apply projection_in_intro_r.
    apply (ex_intro ? ? (xp)).
    auto_set.
    apply subset_len.
    apply projection_in_intro_r.
    apply (ex_intro ? ? (x)).
    assumption.
    assumption.
    assumption.
    apply (⁨injective_included ?0 ?2 ?4 ?6 S ?10 ?12⁩).
    assumption.
    auto_set.
    lia.
    assumption.
Qed.

Axiom projection_finiteR: ∀ A B: Universe, ∀ f: A → B, ∀ S: set A, finite S → finite (projection S f).

Theorem rule_of_bijection: ∀ A B: U, ∀ f: A -> B, ∀ S: set A, finite S -> injective f S -> |projection S f| = |S|.
Proof.
intros A B f.
apply set_induction.
Switch 1.
intros.
replace #1 (projection {} f) with ({}).
apply projection_empty.
lia.
intros.
replace #1 (projection (x ∪ {a}) f) with (projection (x) f ∪ projection {a} f).
apply projection_union.
replace #1 (|x ∪ {a}|) with (|x| + 1).
apply finite_add_len.
assumption.
assumption.
replace #1 (projection {a} f) with ({f a}).
apply projection_singleton.
replace #1 (|projection x f ∪ {f a}|) with (|projection x f| + 1).
apply finite_add_len.
intros.
apply projection_in_intro_l in H3.
destruct H3 with (ex_ind ? ?) to (xp xp_property).
destruct xp_property with (and_ind ? ?) to (xp_property_l xp_property_r).
apply injective_unfold in H2.
apply H2 in xp_property_r.
auto_set.
auto_set.
auto_set.
apply projection_finiteR.
assumption.
Seq (add_hyp (⁨injective f x⁩)) (remove_hyp H0) (Switch 1) (add_hyp H0_o := (H0 H3)) (remove_hyp H3) (remove_hyp H0) .
lia.
apply (⁨injective_included ?0 ?2 ?4 ?6 (x ∪ {a}) ?10 ?12⁩).
assumption.
auto_set.
Qed.

Import /Arith.
Import /Logic.
Import /Eq.


Todo asl_zarb2: ∀ X: U, ∀ C: set X, ∀ n m: ℤ, n > 0 -> m > 0 -> ∀ Y: U, ∀ f: X -> Y, |projection C f| = n -> (∀ y: Y, y ∈ (projection C f) -> |{ x: X | x ∈ C ∧ f x = y }| = m) -> ∀ c: ℤ, c = n * m -> |C| = c.

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
Todo member_set_is_two_element_l: ∀ T: U, ∀ l: list T, ∀ a b, |l| = cnt a l + cnt b l -> member_set l ⊆ {a, b}.
Todo member_set_is_two_element_r: ∀ T: U, ∀ l: list T, ∀ a b, member_set l ⊆ {a, b} -> |l| = cnt a l + cnt b l.


Axiom valid_paren: list char -> Universe.
Axiom valid_paren_unfold: ∀ l, valid_paren l -> l = "" ∨ ∃ x y, valid_paren x ∧ valid_paren y ∧ l = "(" ++ x ++ ")" ++ y.
Suggest hyp default apply valid_paren_unfold in $n; Destruct.
Axiom valid_paren_fold: ∀ l, (∃ x y, valid_paren x ∧ valid_paren y ∧ l = "(" ++ x ++ ")" ++ y) -> valid_paren l.
Axiom valid_paren_empty: valid_paren "".
Todo valid_paren_elements_type: ∀ l, valid_paren l -> ∀ a, a in l -> a = '(' ∨ a = ')'.
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
Todo valid_paren_cnt_right: ∀ a, valid_paren a -> ∀ k, 2 * k = |a| -> cnt ')' a = k.

Theorem count_of_lists: ∀ T: U, ∀ S: set T, ∀ m, 0 < m -> |S| = m -> ∀ n, 0 ≤ n -> |{ l: list T | member_set l ⊆ S ∧ |l| = n }| = |S| ^ n.
Proof.
    intros.
    add_hyp (∃ x: T, x ∈ S).
    apply len_gt_0_not_empty_set.
    lia.
    destruct H2 with (ex_ind ? ?) to (d d_property).
    remove_hyp d_property.
    revert H0.
    revert H.
    revert m.
    revert S.
    revert H1.
    revert n.
    apply z_induction_simple.
    Switch 1.
    intros.
    replace #1 ({ l: list T | member_set l ⊆ S ∧ |l| = 0 }) with ({nil T}).
    apply set_equality.
    apply included_fold.
    intros.
    apply singleton_unfold in H1.
    apply eq_sym in H1.
    rewrite H1.
    apply set_from_func_fold.
    apply and_intro.
    lia.
    replace #1 (member_set []) with (set_empty T).
    apply member_set_empty.
    auto_set.
    apply included_fold.
    intros.
    apply set_from_func_unfold in H1.
    destruct H1 with (and_ind ? ?) to (H1_l H1_r).
    apply nil_unique in H1_r.
    auto_set.
    replace #1 (|S| ^ 0) with (1).
    lia.
    apply singleton_len.
    intros.
    apply (⁨asl_zarb2 ?0 ?2 (|S|) (|S| ^ n) ?8 ?10 T (head d) ?14 ?16 ?18 ?20⁩).
    apply pow_unfold_l.
    assumption.
    intros.
    add_hyp (y ∈S).
    apply projection_in_intro_l in H2.
    destruct H2 with (ex_ind ? ?) to (x x_property).
    destruct x_property with (and_ind ? ?) to (x_property_l x_property_r).
    apply set_from_func_unfold in x_property_l.
    destruct x.
    lia.
    replace #1 (head d (x0 :: l)) with (x0) in x_property_r.
    auto_list.
    replace #1 (x0) with (y) in x_property_l.
    auto_set.
    destruct x_property_l with (and_ind ? ?) to (x_property_l_l x_property_l_r).
    add_hyp (y ∈ member_set (y :: l)).
    apply member_set_cons.
    auto_set.
    apply (⁨rule_of_bijectionR ?0 (list T) tail ?4 ?6 ?8 ?10 ?12⁩).
    replace #1 (projection { x: list T | x ∈ { l: list T | member_set l ⊆ S ∧ |l| = n + 1 } ∧ head d x = y } tail) with ({ l: list T | member_set l ⊆ S ∧ |l| = n }).
    apply set_equality.
    apply included_fold.
    intros.
    apply projection_in_intro_r.
    apply (ex_intro ? ? (y :: a)).
    apply and_intro.
    auto_list.
    apply set_from_func_unfold in H4.
    apply set_from_func_fold.
    destruct H4 with (and_ind ? ?) to (H4_l H4_r).
    apply and_intro.
    auto_list.
    apply set_from_func_fold.
    apply and_intro.
    lia.
    replace #1 (member_set (y :: a)) with ({y} ∪ member_set ( a)).
    apply member_set_cons_union.
    auto_set.
    apply included_fold.
    intros.
    apply set_from_func_fold.
    apply projection_in_intro_l in H4.
    destruct H4 with (ex_ind ? ?) to (x x_property).
    destruct x_property with (and_ind ? ?) to (x_property_l x_property_r).
    apply set_from_func_unfold in x_property_l.
    destruct x_property_l with (and_ind ? ?) to (x_property_l_l x_property_l_r).
    apply set_from_func_unfold in x_property_l_l.
    destruct x_property_l_l with (and_ind ? ?) to (x_property_l_l_l x_property_l_l_r).
    destruct x.
    lia.
    replace #1 (head d (x0 :: l)) with (x0) in x_property_l_r.
    auto_list.
    replace #1 (x0) with (y) in x_property_l_l_r.
    assumption.
    replace #1 (x0) with (y) in x_property_l_l_l.
    assumption.
    replace #1 (x0) with (y) in x_property_r.
    assumption.
    replace #1 (tail (y :: l)) with (l) in x_property_r.
    auto_list.
    rewrite x_property_r.
    apply and_intro.
    lia.
    replace #1 (member_set (y :: l)) with ({y} ∪ member_set ( l)) in x_property_l_l_l.
    apply member_set_cons_union.
    auto_set.
    apply (⁨H0 ?0 m ?4 ?6⁩).
    assumption.
    assumption.
    apply pow_not_neg.
    lia.
    assumption.
    apply injective_fold.
    intros.
    apply set_from_func_unfold in H4.
    apply set_from_func_unfold in H5.
    destruct H4 with (and_ind ? ?) to (H4_l H4_r).
    apply set_from_func_unfold in H4_l.
    destruct H5 with (and_ind ? ?) to (H5_l H5_r).
    apply set_from_func_unfold in H5_l.
    destruct x.
    lia.
    destruct y0.
    lia.
    replace #1 (tail (x0 :: l)) with (l) in H6.
    auto_list.
    replace #1 (tail (x :: l0)) with (l0) in H6.
    auto_list.
    replace #1 (head d (x0 :: l)) with (x0) in H4_r.
    auto_list.
    replace #1 (head d (x :: l0)) with (x) in H5_r.
    auto_list.
    rewrite H6.
    rewrite H4_r.
    rewrite H5_r.
    auto_list.
    replace #1 (projection { l: list T | member_set l ⊆ S ∧ |l| = n + 1 } (head d)) with (S).
    apply set_equality.
    apply included_fold.
    intros.
    apply projection_in_intro_r.
    apply (ex_intro ? ? (repeat (n + 1) a)).
    apply and_intro.
    apply eq_sym.
    apply repeat_head.
    lia.
    apply set_from_func_fold.
    apply and_intro.
    apply repeat_len.
    lia.
    replace #1 (member_set (repeat (n + 1) a)) with ({a}).
    apply member_set_repeat.
    lia.
    auto_set.
    apply included_fold.
    intros.
    apply projection_in_intro_l in H2.
    destruct H2 with (ex_ind ? ?) to (x x_property).
    destruct x_property with (and_ind ? ?) to (x_property_l x_property_r).
    apply set_from_func_unfold in x_property_l.
    destruct x_property_l with (and_ind ? ?) to (x_property_l_l x_property_l_r).
    destruct x.
    lia.
    replace #1 (head d (x0 :: l)) with (x0) in x_property_r.
    auto_list.
    replace #1 (member_set (x0 :: l)) with ({x0} ∪ member_set ( l)) in x_property_l_l.
    apply member_set_cons_union.
    auto_set.
    auto_list.
    apply pow_pos.
    lia.
    assumption.
    lia.
Qed.

Theorem count_of_binary_lists: ∀ T: U, ∀ a b: T, ~ a = b -> ∀ n, 0 ≤ n -> |{ l: list T | member_set l ⊆ {a, b} ∧ |l| = n }| = 2 ^ n.
Proof.
    intros.
    replace #1 (2) with (|{a, b}|).
    apply eq_sym.
    replace #1 (2) with (1 + 1).
    lia.
    apply add_len.
    intros.
    auto_set.
    apply singleton_len.
    lia.
    apply (⁨count_of_lists ?0 ?2 2 ?6 ?8 ?10 ?12⁩).
    assumption.
    replace #1 (2) with (1 + 1).
    lia.
    apply add_len.
    intros.
    auto_set.
    apply singleton_len.
    lia.
    lia.
Qed.
Axiom factorial: ℤ -> ℤ.
Axiom factorial_0: factorial 0 = 1.
Axiom factorial_n: ∀ n: ℤ, n > 0 -> factorial n = n * factorial (n - 1).
Todo factorial_gt_0: ∀ n: ℤ, 0 ≤ n -> 0 < factorial n. 

Theorem count_permution: ∀ T: U, ∀ S: set T, ∀ n: ℤ, 0 ≤ n -> |S| = n -> |{ l: list T | member_set l ⊆ S ∧ |l| = n ∧ (unique_elements l) }| = factorial n.
Proof.
    intros.
    revert H0.
    revert S.
    revert H.
    revert n.
    apply z_induction_simple.
    Switch 1.
    intros.
    apply empty_len_unique in H0.
    rewrite H0.
    replace #1 ({ l: list T | member_set l ⊆ {} ∧ |l| = 0 ∧ unique_elements l }) with ({[]}).
    apply set_equality.
    apply included_fold.
    intros.
    apply singleton_unfold in H.
    apply eq_sym in H.
    rewrite H.
    apply set_from_func_fold.
    apply and_intro.
    apply and_intro.
    apply unique_elements_nil.
    lia.
    apply member_set_nil_included.
    apply included_fold.
    intros.
    apply set_from_func_unfold in H.
    destruct H with (and_ind ? ?) to (H_l H_r).
    destruct H_r with (and_ind ? ?) to (H_r_l H_r_r).
    apply nil_unique in H_r_l.
    auto_set.
    replace #1 (factorial 0) with (1).
    apply factorial_0.
    apply singleton_len.
    intros.
    add_hyp (∃ d: T, d ∈ S).
    apply len_gt_0_not_empty_set.
    lia.
    destruct H1 with (ex_ind ? ?) to (d d_property).
    remove_hyp d_property.
    add_from_lib asl_zarb2.
    add_hyp asl_zarb2_ex := (asl_zarb2 (list T)).
    add_hyp asl_zarb2_ex_ex := (asl_zarb2_ex ({ l: list T | member_set l ⊆ S ∧ |l| = n + 1 ∧ unique_elements l })).
    add_hyp asl_zarb2_ex_ex_ex := (asl_zarb2_ex_ex (n + 1)).
    add_hyp asl_zarb2_ex_ex_ex_ex := (asl_zarb2_ex_ex_ex (factorial n)).
    remove_hyp asl_zarb2_ex.
    remove_hyp asl_zarb2_ex_ex_ex.
    Seq (add_hyp (⁨0 < n + 1⁩)) (remove_hyp asl_zarb2_ex_ex_ex_ex) (Switch 1) (add_hyp asl_zarb2_ex_ex_ex_ex_o := (asl_zarb2_ex_ex_ex_ex H1)) (remove_hyp H1) (remove_hyp asl_zarb2_ex_ex_ex_ex).
    Seq (add_hyp (⁨0 < factorial n⁩)) (remove_hyp asl_zarb2_ex_ex_ex_ex_o) (Switch 1) (add_hyp asl_zarb2_ex_ex_ex_ex_o_o := (asl_zarb2_ex_ex_ex_ex_o H1)) (remove_hyp H1) (remove_hyp asl_zarb2_ex_ex_ex_ex_o).
    add_hyp asl_zarb2_ex_ex_ex_ex_o_o_ex := (asl_zarb2_ex_ex_ex_ex_o_o (T)).
    remove_hyp asl_zarb2_ex_ex.
    remove_hyp asl_zarb2_ex_ex_ex_ex_o_o.
    add_hyp asl_zarb2_ex_ex_ex_ex_o_o_ex_ex := (asl_zarb2_ex_ex_ex_ex_o_o_ex (head d)).
    remove_hyp asl_zarb2_ex_ex_ex_ex_o_o_ex.
    apply asl_zarb2_ex_ex_ex_ex_o_o_ex_ex.
    replace #3 (n) with (n + 1 -1).
    lia.
    apply factorial_n.
    lia.
    intros.
    remove_hyp asl_zarb2_ex_ex_ex_ex_o_o_ex_ex.
    apply projection_in_intro_l in H1.
    destruct H1 with (ex_ind ? ?) to (ly ly_property).
    destruct ly_property with (and_ind ? ?) to (ly_property_l ly_property_r).
    add_from_lib rule_of_bijectionR.
    add_hyp rule_of_bijectionR_ex := (rule_of_bijectionR (list T)).
    add_hyp rule_of_bijectionR_ex_ex := (rule_of_bijectionR_ex (list T)).
    add_hyp rule_of_bijectionR_ex_ex_ex := (rule_of_bijectionR_ex_ex (tail)).
    apply rule_of_bijectionR_ex_ex_ex.
    remove_hyp rule_of_bijectionR_ex_ex_ex.
    remove_hyp rule_of_bijectionR_ex_ex.
    remove_hyp rule_of_bijectionR_ex.
    replace #1 (projection { x: list T | x ∈ { l: list T | member_set l ⊆ S ∧ |l| = n + 1 ∧ unique_elements l } ∧ head d x = y } tail) with ({ l: list T | member_set l ⊆ (S ∖ {y}) ∧ |l| = n ∧ unique_elements l }).
    apply set_from_func_unfold in ly_property_l.
    destruct ly_property_l with (and_ind ? ?) to (ly_property_l_l ly_property_l_r).
    destruct ly_property_l_r with (and_ind ? ?) to (ly_property_l_r_l ly_property_l_r_r).
    apply set_equality.
    apply included_fold.
    intros.
    apply projection_in_intro_r.
    apply (ex_intro ? ? ([y] ++ a)).
    apply set_from_func_unfold in H1.
    destruct H1 with (and_ind ? ?) to (H1_l H1_r).
    destruct H1_r with (and_ind ? ?) to (H1_r_l H1_r_r).
    apply and_intro.
    apply eq_sym.
    apply tail_add.
    apply set_from_func_fold.
    apply and_intro.
    apply add_head.
    apply set_from_func_fold.
    apply and_intro.
    apply and_intro.
    apply unique_elements_fold.
    apply and_intro.
    assumption.
    intros.
    add_hyp (y ∈ member_set a).
    apply inlist_member_set in H1.
    assumption.
    apply included_unfold in H1_l.
    apply H1_l in H2.
    auto_set.
    lia.
    replace #1 (member_set ([y] ++ a)) with (member_set ([y] ) ∪ member_set a).
    apply member_set_append.
    replace #1 (member_set [y]) with ({y}).
    apply member_set_singleton.
    add_hyp (y ∈ S).
    apply included_unfold in ly_property_l_l.
    apply ly_property_l_l.
    rewrite ly_property_r.
    apply head_in_member_set.
    apply included_fold.
    intros.
    apply union_unfold in H2.
    destruct H2 with (or_ind ? ?).
    apply included_unfold in H1_l.
    apply H1_l in H2.
    auto_set.
    auto_set.
    apply included_fold.
    intros.
    apply set_from_func_fold.
    apply projection_in_intro_l in H1.
    destruct H1 with (ex_ind ? ?) to (ca ca_property).
    destruct ca_property with (and_ind ? ?) to (ca_property_l ca_property_r).
    apply set_from_func_unfold in ca_property_l.
    destruct ca_property_l with (and_ind ? ?) to (ca_property_l_l ca_property_l_r).
    apply set_from_func_unfold in ca_property_l_l.
    destruct ca_property_l_l with (and_ind ? ?) to (ca_property_l_l_l ca_property_l_l_r).
    destruct ca_property_l_l_r with (and_ind ? ?) to (ca_property_l_l_r_l ca_property_l_l_r_r).
    apply and_intro.
    apply and_intro.
    replace #1 (ca) with ([head d ca] ++ tail ca) in ca_property_l_l_r_r.
    apply add_head_tail.
    intros.
    replace #1 (ca) with ([]) in ca_property_l_l_r_l.
    assumption.
    lia.
    apply unique_elements_unfold in ca_property_l_l_r_r.
    rewrite ca_property_r.
    assumption.
    rewrite ca_property_r.
    apply tail_len.
    assumption.
    replace #1 (ca) with ([head d ca] ++ a) in ca_property_l_l_l.
    rewrite ca_property_r.
    apply add_head_tail.
    intros.
    replace #1 (ca) with ([]) in ca_property_l_l_r_l.
    assumption.
    lia.
    replace #1 (member_set ([head d ca] ++ a)) with (member_set ([head d ca]) ∪ member_set a) in ca_property_l_l_l.
    apply member_set_append.
    add_hyp (member_set a ⊆ S ).
    auto_set.
    replace #1 (ca) with ([y] ++ a) in ca_property_l_l_r_r.
    rewrite ca_property_r.
    apply eq_sym in ca_property_l_r.
    rewrite ca_property_l_r.
    apply add_head_tail.
    intros.
    replace #1 (ca) with ([]) in ca_property_l_l_r_l.
    assumption.
    lia.
    apply unique_elements_unfold in ca_property_l_l_r_r.
    destruct ca_property_l_l_r_r with (and_ind ? ?) to (ca_property_l_l_r_r_l ca_property_l_l_r_r_r).
    add_hyp (~ y ∈ member_set a).
    intros.
    apply member_set_inlist in H2.
    assumption.
    auto_set.
    apply H0.
    apply subset_len.
    apply set_from_func_unfold in ly_property_l.
    destruct ly_property_l with (and_ind ? ?) to (ly_property_l_l ly_property_l_r).
    apply included_unfold in ly_property_l_l.
    apply ly_property_l_l.
    rewrite ly_property_r.
    apply head_in_member_set.
    assumption.
    assumption.
    add_from_lib factorial_gt_0.
    add_hyp factorial_gt_0_ex := (factorial_gt_0 (n)).
    assumption.
    apply injective_fold.
    intros.
    apply set_from_func_unfold in H1.
    apply set_from_func_unfold in H2.
    replace #1 (y0) with ([head d x] ++ tail x).
    replace #1 (head d x) with (head d y0).
    auto_set.
    rewrite H3.
    apply add_head_tail.
    destruct H2 with (and_ind ? ?) to (H2_l H2_r).
    apply set_from_func_unfold in H2_l.
    intros.
    replace #2 (y0) with ([]) in H2_l.
    assumption.
    lia.
    apply add_head_tail.
    intros.
    destruct H1 with (and_ind ? ?) to (H1_l H1_r).
    apply set_from_func_unfold in H1_l.
    replace #2 (x) with ([]) in H1_l.
    assumption.
    lia.
    replace #1 (projection { l: list T | member_set l ⊆ S ∧ |l| = n + 1 ∧ unique_elements l } (head d)) with (S).
    apply set_equality.
    apply included_fold.
    intros.
    remove_hyp asl_zarb2_ex_ex_ex_ex_o_o_ex_ex.
    apply projection_in_intro_r.
    add_from_lib listing_set.
    add_hyp listing_set_ex := (listing_set (T)).
    add_hyp listing_set_ex_ex := (listing_set_ex (S ∖ {a})).
    Seq (add_hyp (⁨finite (S ∖ {a})⁩)) (remove_hyp listing_set_ex_ex) (Switch 1) (add_hyp listing_set_ex_ex_o := (listing_set_ex_ex H2)) (remove_hyp H2) (remove_hyp listing_set_ex_ex).
    destruct listing_set_ex_ex_o with (ex_ind ? ?) to (l l_property).
    apply (ex_intro ? ? ([a] ++ l)).
    destruct l_property with (and_ind ? ?) to (l_property_l l_property_r).
    destruct l_property_r with (and_ind ? ?) to (l_property_r_l l_property_r_r).
    apply and_intro.
    apply eq_sym.
    apply add_head.
    apply set_from_func_fold.
    apply and_intro.
    apply and_intro.
    apply unique_elements_fold.
    apply and_intro.
    assumption.
    intros.
    apply inlist_member_set in H2.
    replace #1 (member_set l) with (S ∖ {a}) in H2.
    assumption.
    auto_set.
    replace #1 (|[a] ++ l|) with (|l| + 1).
    lia.
    replace #1 (|S ∖ {a}|) with (n) in l_property_r_l.
    apply subset_len.
    assumption.
    assumption.
    assumption.
    lia.
    replace #1 (member_set ([a] ++ l)) with ({a} ∪ member_set (l)).
    apply member_set_add.
    rewrite l_property_l.
    auto_set.
    apply (⁨finite_included ?0 ?2 S ?6 ?8⁩).
    auto_set.
    apply len_ge_0_finite.
    lia.
    apply included_fold.
    intros.
    apply projection_in_intro_l in H1.
    destruct H1 with (ex_ind ? ?) to (ca ca_property).
    destruct ca_property with (and_ind ? ?) to (ca_property_l ca_property_r).
    apply set_from_func_unfold in ca_property_l.
    destruct ca_property_l with (and_ind ? ?) to (ca_property_l_l ca_property_l_r).
    apply included_unfold in ca_property_l_l.
    apply ca_property_l_l.
    rewrite ca_property_r.
    apply head_in_member_set.
    assumption.
    apply factorial_gt_0.
    assumption.
    lia.
Qed.

Theorem valid_paren_convert: ∀ l, ∀ n, |l| = 2 * n ->  valid_paren l <-> cnt '(' l = n ∧ cnt ')' l = n ∧ (∀ i, 0 < i -> i ≤ |l| -> cnt ')' (firstn l i) ≤ cnt '(' (firstn l i)).
Proof.
    apply list_induction_len.
    intros.
    destruct b.
    apply and_intro.
    intros.
    apply valid_paren_empty.
    intros.
    apply and_intro.
    apply and_intro.
    intros.
    lia.
    lia.
    lia.
    apply and_intro.
    intros.
    destruct H1 with (and_ind ? ?) to (H1_l H1_r).
    destruct H1_r with (and_ind ? ?) to (H1_r_l H1_r_r).
    add_hyp (member_set (x::l) ⊆ {'(', ')'}).
    apply member_set_is_two_element_l.
    lia.
    add_hyp (x = '(').
    apply NNPP.
    intros.
    add_hyp (x = ')').
    apply included_unfold in H1.
    add_hyp H1_ex := (H1 (x)).
    Seq (add_hyp (⁨x ∈ member_set (x :: l)⁩)) (remove_hyp H1_ex) (Switch 1) (add_hyp H1_ex_o := (H1_ex H3)) (remove_hyp H3) (remove_hyp H1_ex).
    auto_set.
    apply member_set_cons.
    add_hyp H1_r_r_ex := (H1_r_r (1)).
    Seq (add_hyp (⁨0 < 1⁩)) (remove_hyp H1_r_r_ex) (Switch 1) (add_hyp H1_r_r_ex_o := (H1_r_r_ex H4)) (remove_hyp H4) (remove_hyp H1_r_r_ex).
    Seq (add_hyp (⁨1 ≤ |x :: l|⁩)) (remove_hyp H1_r_r_ex_o) (Switch 1) (add_hyp H1_r_r_ex_o_o := (H1_r_r_ex_o H4)) (remove_hyp H4) (remove_hyp H1_r_r_ex_o).
    replace #1 ((firstn (x :: l) 1)) with ([x]) in H1_r_r_ex_o_o.
    apply firstn_cons_1.
    destruct H1_r_r_ex_o_o with (or_ind ? ?).
    replace #1 ((firstn (x :: l) 1)) with ([x]) in H1_r_r_ex_o_o.
    apply firstn_cons_1.
    revert H1_r_r_ex_o_o.
    rewrite H3.
    lia.
    replace #1 ((firstn (x :: l) 1)) with ([x]) in H1_r_r_ex_o_o.
    apply firstn_cons_1.
    revert H1_r_r_ex_o_o.
    rewrite H3.
    lia.
    lia.
    lia.
    add_hyp (∃ i, i > -1 ∧ i ≤ |l| ∧ (cnt ')' (firstn l i) = cnt '(' (firstn l i) + 1)).
    apply (ex_intro ? ? (|l|)).
    apply and_intro.
    replace #1 ((firstn l (|l|))) with (l).
    apply firstn_len.
    replace #1 ((firstn l (|l|))) with (l).
    apply firstn_len.
    revert H1_l.
    revert H1_r_l.
    revert H1_r_r.
    rewrite H2.
    lia.
    lia.
    apply ex_min in H3.
    destruct H3 with (ex_ind ? ?) to (i i_property).
    destruct i_property with (and_ind ? ?) to (i_property_l i_property_r).
    destruct i_property_r with (and_ind ? ?) to (i_property_r_l i_property_r_r).
    add_from_lib split_index.
    add_hyp split_index_ex := (split_index (char)).
    add_hyp split_index_ex_ex := (split_index_ex (l)).
    add_hyp split_index_ex_ex_ex := (split_index_ex_ex (i)).
    Seq (add_hyp (⁨0 < i⁩)) (remove_hyp split_index_ex_ex_ex) (Switch 1) (add_hyp split_index_ex_ex_ex_o := (split_index_ex_ex_ex H3)) (remove_hyp H3) (remove_hyp split_index_ex_ex_ex).
    remove_hyp split_index_ex_ex.
    remove_hyp split_index_ex.
    Seq (add_hyp (⁨i ≤ |l|⁩)) (remove_hyp split_index_ex_ex_ex_o) (Switch 1) (add_hyp split_index_ex_ex_ex_o_o := (split_index_ex_ex_ex_o H3)) (remove_hyp H3) (remove_hyp split_index_ex_ex_ex_o).
    destruct split_index_ex_ex_ex_o_o with (ex_ind ? ?) to (a a_property).
    destruct a_property with (ex_ind ? ?) to (b b_property).
    destruct b_property with (ex_ind ? ?) to (y y_property).
    destruct y_property with (and_ind ? ?) to (y_property_l y_property_r).
    destruct y_property_r with (and_ind ? ?) to (y_property_r_l y_property_r_r).
    add_hyp (y = ')').
    revert H1_r_r.
    revert H1.
    revert i_property_r_l.
    revert i_property_r_r.
    rewrite y_property_l.
    intros.
    Switch 2.
    add_hyp i_property_r_r_ex := (i_property_r_r (|l|)).
    Seq (add_hyp (⁨- 1 < |l|⁩)) (remove_hyp i_property_r_r_ex) (Switch 1) (add_hyp i_property_r_r_ex_o := (i_property_r_r_ex H3)) (remove_hyp H3) (remove_hyp i_property_r_r_ex).
    assumption.
    lia.
    Switch 1.
    apply NNPP.
    intros.
    add_hyp (y = '(').
    apply included_unfold in H1.
    add_hyp H1_ex := (H1 (y)).
    Seq (add_hyp (⁨y ∈ member_set (x :: (a ++ y :: b))⁩)) (remove_hyp H1_ex) (Switch 1) (add_hyp H1_ex_o := (H1_ex H4)) (remove_hyp H4) (remove_hyp H1_ex).
    auto_set.
    replace #1 (member_set (x :: (a ++ y :: b))) with ({x} ∪ member_set ((a ++ y :: b))).
    apply member_set_cons_union.
    replace #1 (member_set (a ++ y :: b)) with (member_set a ∪ member_set (y :: b)).
    apply member_set_append.
    replace #1 (member_set (y :: b)) with ({y} ∪ member_set (b)).
    apply member_set_cons_union.
    auto_set.
    add_hyp (∃ j, j > -1 ∧ j < i ∧ (cnt '(' (firstn a j) + 1 ≤ cnt ')' (firstn a j)) ).
    apply (ex_intro ? ? (i - 1)).
    apply and_intro.
    apply and_intro.
    destruct i_property_r_l with (and_ind ? ?) to (i_property_r_l_l i_property_r_l_r).
    replace #1 ((firstn (a ++ y :: b) i)) with (a ++ [y]) in i_property_r_l_r.
    replace #1 (firstn (a ++ y :: b) i) with (a ++ firstn (y :: b) 1).
    replace #1 (i) with ((|a| + 1)).
    lia.
    apply firstn_append_r.
    lia.
    replace #1 (firstn (y :: b) 1) with ([y]).
    apply firstn_cons_1.
    auto_list.
    replace #1 ((firstn (a ++ y :: b) i)) with ((a ++ [y])) in i_property_r_l_r.
    replace #1 (firstn (a ++ y :: b) i) with (a ++ firstn (y :: b) 1).
    replace #1 (i) with ((|a| + 1)).
    lia.
    apply firstn_append_r.
    lia.
    replace #1 (firstn (y :: b) 1) with ([y]).
    apply firstn_cons_1.
    auto_list.
    revert i_property_r_l_r.
    rewrite H4.
    intros.
    replace #1 ((firstn a (i - 1))) with (a).
    replace #1 ((i - 1)) with (|a|).
    auto_set.
    apply firstn_len.
    replace #1 ((firstn a (i - 1))) with (a).
    replace #1 ((i - 1)) with (|a|).
    auto_set.
    apply firstn_len.
    lia.
    lia.
    lia.
    apply ex_min in H5.
    destruct H5 with (ex_ind ? ?) to (j j_property).
    destruct j_property with (and_ind ? ?) to (j_property_l j_property_r).
    destruct j_property_r with (and_ind ? ?) to (j_property_r_l j_property_r_r).
    add_hyp i_property_r_r_ex := (i_property_r_r (j)).
    Seq (add_hyp (⁨- 1 < j⁩)) (remove_hyp i_property_r_r_ex) (Switch 1) (add_hyp i_property_r_r_ex_o := (i_property_r_r_ex H5)) (remove_hyp H5) (remove_hyp i_property_r_r_ex).
    add_hyp (( j ≤ |a ++ y :: b| ∧ cnt ')' (firstn (a ++ y :: b) j) = cnt '(' (firstn (a ++ y :: b) j) + 1)).
    apply and_intro.
    add_hyp (~ cnt '(' (firstn a j) + 1 < cnt ')' (firstn a j)).
    intros.
    add_hyp j_property_r_r_ex := (j_property_r_r (j - 1)).
    Seq (add_hyp (⁨- 1 < j - 1⁩)) (remove_hyp j_property_r_r_ex) (Switch 1) (add_hyp j_property_r_r_ex_o := (j_property_r_r_ex H6)) (remove_hyp H6) (remove_hyp j_property_r_r_ex).
    Seq (add_hyp (⁨j - 1 < i ∧ cnt '(' (firstn a (j - 1)) + 1 ≤ cnt ')' (firstn a (j - 1))⁩)) (remove_hyp j_property_r_r_ex_o) (Switch 1) (add_hyp j_property_r_r_ex_o_o := (j_property_r_r_ex_o H6)) (remove_hyp H6) (remove_hyp j_property_r_r_ex_o).
    lia.
    apply and_intro.
    add_from_lib cnt_of_firstn_dis_range.
    add_hyp cnt_of_firstn_dis_range_ex := (cnt_of_firstn_dis_range (char)).
    add_hyp cnt_of_firstn_dis_range_ex_ex := (cnt_of_firstn_dis_range_ex (a)).
    add_hyp cnt_of_firstn_dis_range_ex_ex_ex := (cnt_of_firstn_dis_range_ex_ex (j)).
    add_hyp cnt_of_firstn_dis_range_ex_ex_ex_ex := (cnt_of_firstn_dis_range_ex_ex_ex ('(')).
    add_hyp cnt_of_firstn_dis_range_ex_ex_ex_ex0 := (cnt_of_firstn_dis_range_ex_ex_ex (')')).
    lia.
    lia.
    add_hyp (~ j = 0).
    intros.
    replace #1 ((firstn a j)) with ([]) in H5.
    apply firstn_le_0.
    assumption.
    replace #1 ((firstn a j)) with ([]) in H5.
    apply firstn_le_0.
    assumption.
    lia.
    lia.
    destruct j_property_r_l with (and_ind ? ?) to (j_property_r_l_l j_property_r_l_r).
    replace #1 (firstn (a ++ y :: b) j) with (firstn a j).
    apply firstn_append_l.
    lia.
    replace #1 ((firstn (a ++ y :: b) j)) with ((firstn (a) j)).
    apply firstn_append_l.
    lia.
    lia.
    lia.
    lia.
    assumption.
    rewrite y_property_l.
    rewrite H3.
    rewrite H2.
    revert y_property_l.
    rewrite H3.
    intros.
    destruct i_property_r_l with (and_ind ? ?) to (i_property_r_l_l i_property_r_l_r).
    replace #1 ((firstn l i)) with (a ++ ")") in i_property_r_l_r.
    rewrite y_property_l.
    replace #1 (a ++ ')' :: b) with (a ++ ")" ++ b).
    auto_list.
    replace #1 (i) with (|a++")"|).
    lia.
    replace #3 (a ++ ")") with (firstn (a ++ ")") (|a++")"|)).
    apply eq_sym.
    apply firstn_len.
    apply firstn_append_l.
    auto_list.
    add_hyp (cnt ')' a = cnt '(' a).
    replace #1 ((firstn l i)) with ((a ++ ")")) in i_property_r_l_r.
    rewrite y_property_l.
    replace #1 (a ++ ')' :: b) with (a ++ ")" ++ b).
    auto_list.
    replace #1 (i) with (|a++")"|).
    lia.
    replace #3 (a ++ ")") with (firstn (a ++ ")") (|a++")"|)).
    apply eq_sym.
    apply firstn_len.
    apply firstn_append_l.
    auto_list.
    lia.
    add_hyp (|a| = cnt '(' a + cnt ')' a).
    apply member_set_is_two_element_r.
    revert H1.
    rewrite y_property_l.
    intros.
    replace #1 (member_set (x :: (a ++ ')' :: b))) with ({x} ∪ member_set ( (a ++ ')' :: b))) in H1.
    apply member_set_cons_union.
    replace #1 (member_set (a ++ ')' :: b)) with (member_set (a) ∪ member_set ( ')' :: b)) in H1.
    apply member_set_append.
    apply included_fold.
    intros.
    apply included_unfold in H1.
    add_hyp H1_ex := (H1 (a0)).
    auto_set.
    add_hyp (|b| = cnt '(' b + cnt ')' b).
    apply member_set_is_two_element_r.
    revert H1.
    rewrite y_property_l.
    intros.
    replace #1 (member_set (x :: (a ++ ')' :: b))) with ({x} ∪ member_set ( (a ++ ')' :: b))) in H1.
    apply member_set_cons_union.
    replace #1 (member_set (a ++ ')' :: b)) with (member_set (a) ∪ member_set( ')' :: b)) in H1.
    apply member_set_append.
    apply included_fold.
    apply included_unfold in H1.
    intros.
    add_hyp H1_ex := (H1 (a0)).
    replace #1 (member_set (')' :: b)) with ({')'} ∪ member_set ( b)) in H1_ex.
    apply member_set_cons_union.
    auto_set.
    apply valid_paren_fold.
    apply (ex_intro ? ? (a)).
    apply (ex_intro ? ? (b)).
    apply and_intro.
    apply and_intro.
    auto_list.
    add_hyp H_ex := (H (b)).
    Seq (add_hyp (⁨|b| < |x :: l|⁩)) (remove_hyp H_ex) (Switch 1) (add_hyp H_ex_o := (H_ex H7)) (remove_hyp H7) (remove_hyp H_ex).
    add_hyp H_ex_o_ex := (H_ex_o (cnt '(' b)).
    Seq (add_hyp (⁨|b| = 2 * cnt '(' b⁩)) (remove_hyp H_ex_o_ex) (Switch 1) (add_hyp H_ex_o_ex_o := (H_ex_o_ex H7)) (remove_hyp H7) (remove_hyp H_ex_o_ex).
    apply iff_imp_l in H_ex_o_ex_o.
    apply H_ex_o_ex_o.
    remove_hyp H_ex_o_ex_o.
    remove_hyp H_ex_o.
    remove_hyp H.
    apply and_intro.
    apply and_intro.
    intros.
    revert H1_r_r.
    rewrite H2.
    rewrite y_property_l.
    intros.
    replace #2 (('(' :: (a ++ ')' :: b))) with (('(' :: a ++ ")") ++ b) in H1_r_r.
    auto_list.
    add_hyp H1_r_r_ex := (H1_r_r (|'(' :: a ++ ")"| + i0)).
    Seq (add_hyp (⁨0 < |'(' :: a ++ ")"| + i0⁩)) (remove_hyp H1_r_r_ex) (Switch 1) (add_hyp H1_r_r_ex_o := (H1_r_r_ex H8)) (remove_hyp H8) (remove_hyp H1_r_r_ex).
    Seq (add_hyp (⁨|'(' :: a ++ ")"| + i0 ≤ |'(' :: (a ++ ')' :: b)|⁩)) (remove_hyp H1_r_r_ex_o) (Switch 1) (add_hyp H1_r_r_ex_o_o := (H1_r_r_ex_o H8)) (remove_hyp H8) (remove_hyp H1_r_r_ex_o).
    replace #1 (('(' :: (a ++ ')' :: b))) with ('(' :: a ++ ")" ++ b) in H1_r_r_ex_o_o.
    auto_list.
    replace #1 ((firstn ('(' :: a ++ ")" ++ b) (|'(' :: a ++ ")"| + i0))) with ('(' :: a ++ ")" ++ (firstn (b) (i0))) in H1_r_r_ex_o_o.
    apply firstn_append_r.
    assumption.
    replace #1 ((firstn ('(' :: a ++ ")" ++ b) (|'(' :: a ++ ")"| + i0))) with ('(' :: a ++ ")" ++ (firstn (b) (i0))) in H1_r_r_ex_o_o.
    apply firstn_append_r.
    assumption.
    lia.
    lia.
    lia.
    revert H1_l.
    revert H1_r_l.
    rewrite H2.
    rewrite y_property_l.
    lia.
    auto_list.
    add_hyp (cnt '(' b = cnt ')' b).
    revert H1_l.
    revert H1_r_l.
    rewrite H2.
    rewrite y_property_l.
    lia.
    lia.
    lia.
    add_hyp H_ex := (H (a)).
    Seq (add_hyp (⁨|a| < |x :: l|⁩)) (remove_hyp H_ex) (Switch 1) (add_hyp H_ex_o := (H_ex H7)) (remove_hyp H7) (remove_hyp H_ex).
    add_hyp H_ex_o_ex := (H_ex_o (cnt '(' a)).
    Seq (add_hyp (⁨|a| = 2 * cnt '(' a⁩)) (remove_hyp H_ex_o_ex) (Switch 1) (add_hyp H_ex_o_ex_o := (H_ex_o_ex H7)) (remove_hyp H7) (remove_hyp H_ex_o_ex).
    apply iff_imp_l in H_ex_o_ex_o.
    apply H_ex_o_ex_o.
    apply and_intro.
    apply and_intro.
    intros.
    remove_hyp H.
    remove_hyp H_ex_o.
    remove_hyp H_ex_o_ex_o.
    add_hyp H1_r_r_ex := (H1_r_r (i0 + 1)).
    Seq (add_hyp (⁨0 < i0 + 1⁩)) (remove_hyp H1_r_r_ex) (Switch 1) (add_hyp H1_r_r_ex_o := (H1_r_r_ex H)) (remove_hyp H) (remove_hyp H1_r_r_ex).
    Seq (add_hyp (⁨i0 + 1 ≤ |x :: l|⁩)) (remove_hyp H1_r_r_ex_o) (Switch 1) (add_hyp H1_r_r_ex_o_o := (H1_r_r_ex_o H)) (remove_hyp H) (remove_hyp H1_r_r_ex_o).
    replace #1 (firstn (x :: l) (i0 + 1)) with ('('::firstn (l) (i0)) in H1_r_r_ex_o_o.
    rewrite H2.
    apply firstn_cons.
    assumption.
    replace #1 (firstn (x :: l) (i0 + 1)) with ('('::firstn (l) (i0)) in H1_r_r_ex_o_o.
    rewrite H2.
    apply firstn_cons.
    assumption.
    revert H1_r_r_ex_o_o.
    rewrite y_property_l.
    intros.
    replace #1 (firstn (a ++ ')' :: b) i0) with (firstn (a) i0) in H1_r_r_ex_o_o.
    apply firstn_append_l.
    assumption.
    replace #1 (firstn (a ++ ')' :: b) i0) with (firstn (a ) i0) in H1_r_r_ex_o_o.
    apply firstn_append_l.
    assumption.
    add_hyp (~ cnt ')' (firstn a i0) = 1 + cnt '(' (firstn a i0)).
    intros.
    add_hyp i_property_r_r_ex := (i_property_r_r (i0)).
    Seq (add_hyp (⁨- 1 < i0⁩)) (remove_hyp i_property_r_r_ex) (Switch 1) (add_hyp i_property_r_r_ex_o := (i_property_r_r_ex H9)) (remove_hyp H9) (remove_hyp i_property_r_r_ex).
    Seq (add_hyp (⁨i0 ≤ |l| ∧ cnt ')' (firstn l i0) = cnt '(' (firstn l i0) + 1⁩)) (remove_hyp i_property_r_r_ex_o) (Switch 1) (add_hyp i_property_r_r_ex_o_o := (i_property_r_r_ex_o H9)) (remove_hyp H9) (remove_hyp i_property_r_r_ex_o).
    lia.
    apply and_intro.
    rewrite y_property_l.
    replace #1 (firstn (a ++ ')' :: b) i0) with (firstn (a) i0).
    apply firstn_append_l.
    assumption.
    replace #1 (firstn (a ++ ')' :: b) i0) with (firstn (a ) i0).
    apply firstn_append_l.
    assumption.
    lia.
    lia.
    lia.
    lia.
    lia.
    lia.
    assumption.
    auto_list.
    lia.
    lia.
    add_hyp (~ i = 0).
    intros.
    destruct i_property_r_l with (and_ind ? ?) to (i_property_r_l_l i_property_r_l_r).
    replace #1 ((firstn l i)) with ("") in i_property_r_l_r.
    rewrite H3.
    apply firstn_le_0.
    auto_list.
    replace #1 ((firstn l i)) with ("") in i_property_r_l_r.
    rewrite H3.
    apply firstn_le_0.
    auto_list.
    lia.
    lia.
    intros.
    apply and_intro.
    apply and_intro.
    intros.
    apply valid_paren_unfold in H1.
    destruct H1 with (or_ind ? ?).
    destruct H1 with (ex_ind ? ?) to (a a_property).
    destruct a_property with (ex_ind ? ?) to (b b_property).
    destruct b_property with (and_ind ? ?) to (b_property_l b_property_r).
    destruct b_property_r with (and_ind ? ?) to (b_property_r_l b_property_r_r).
    replace #1 ("(" ++ a ++ ")" ++ b) with ('(' ::( a ++ ")" ++ b)) in b_property_r_r.
    auto_list.
    apply cons_eq in b_property_r_r.
    destruct b_property_r_r with (and_ind ? ?) to (b_property_r_r_l b_property_r_r_r).
    revert H3.
    rewrite b_property_r_r_l.
    rewrite b_property_r_r_r.
    intros.
    add_hyp (∀ j, 0 ≤ j -> j ≤ |a| -> cnt ')' (firstn a j) ≤ cnt '(' (firstn a j) ).
    intros.
    add_hyp (j = 0 ∨ 0 < j).
    lia.
    destruct H5 with (or_ind ? ?).
    add_hyp H_ex := (H (a)).
    Seq (add_hyp (⁨|a| < |x :: l|⁩)) (remove_hyp H_ex) (Switch 1) (add_hyp H_ex_o := (H_ex H6)) (remove_hyp H6) (remove_hyp H_ex).
    add_hyp (2 | |a|).
    apply valid_paren_len_even.
    assumption.
    apply divide_unfold in H6.
    destruct H6 with (ex_ind ? ?) to (k k_property).
    add_hyp H_ex_o_ex := (H_ex_o (k)).
    Seq (add_hyp (⁨|a| = 2 * k⁩)) (remove_hyp H_ex_o_ex) (Switch 1) (add_hyp H_ex_o_ex_o := (H_ex_o_ex H6)) (remove_hyp H6) (remove_hyp H_ex_o_ex).
    apply iff_imp_r in H_ex_o_ex_o.
    add_hyp (cnt '(' a = k ∧ cnt ')' a = k ∧ ∀ i0: ℤ, 0 < i0 → i0 ≤ |a| → cnt ')' (firstn a i0) ≤ cnt '(' (firstn a i0)).
    assumption.
    remove_hyp H_ex_o_ex_o.
    destruct H6 with (and_ind ? ?) to (H6_l H6_r).
    destruct H6_r with (and_ind ? ?) to (H6_r_l H6_r_r).
    add_hyp H6_r_r_ex := (H6_r_r (j)).
    assumption.
    auto_set.
    rewrite b_property_r_r_r.
    lia.
    rewrite H5.
    replace #1 (firstn a 0) with ([]).
    apply firstn_le_0.
    auto_list.
    replace #1 ((firstn a 0)) with ("").
    apply firstn_le_0.
    auto_list.
    lia.
    add_hyp (⁨i ≤ |a| + 1 + 1 ∨ i  > |a| + 1 + 1⁩).
    lia.
    destruct H4 with (or_ind ? ?).
    replace #1 (('(' :: (a ++ ")" ++ b))) with (('(' :: (a ++ ")") ++ b)).
    auto_list.
    replace #1 (('(' :: (a ++ ")" ++ b))) with (('(' :: (a ++ ")") ++ b)).
    auto_list.
    replace #1 ((firstn ('(' :: (a ++ ")") ++ b) i)) with ('(' :: (a ++ ")") ++ firstn (b) (i - |'(' :: (a ++ ")")| )).
    replace #1 (i) with (|'(' :: (a ++ ")")| + (i - | '(' :: (a ++ ")")|)).
    lia.
    apply firstn_append_r.
    lia.
    replace #1 ((firstn ('(' :: (a ++ ")") ++ b) i)) with (('(' :: (a ++ ")") ++ firstn b (i - |'(' :: (a ++ ")")|))).
    replace #1 (i) with (|'(' :: (a ++ ")")| + (i - | '(' :: (a ++ ")")|)).
    lia.
    apply firstn_append_r.
    lia.
    add_hyp (cnt ')' (firstn b (i - |'(' :: (a ++ ")")|)) ≤ cnt '(' (firstn b (i - |'(' :: (a ++ ")")|))).
    add_hyp H_ex := (H (b)).
    Seq (add_hyp (⁨|b| < |x :: l|⁩)) (remove_hyp H_ex) (Switch 1) (add_hyp H_ex_o := (H_ex H5)) (remove_hyp H5) (remove_hyp H_ex).
    add_hyp (2 | |b|).
    apply valid_paren_len_even.
    assumption.
    apply divide_unfold in H5.
    destruct H5 with (ex_ind ? ?) to (k k_property).
    add_hyp H_ex_o_ex := (H_ex_o (k)).
    Seq (add_hyp (⁨|b| = 2 * k⁩)) (remove_hyp H_ex_o_ex) (Switch 1) (add_hyp H_ex_o_ex_o := (H_ex_o_ex H5)) (remove_hyp H5) (remove_hyp H_ex_o_ex).
    apply iff_imp_r in H_ex_o_ex_o.
    add_hyp (cnt '(' b = k ∧ cnt ')' b = k ∧ ∀ i0: ℤ, 0 < i0 → i0 ≤ |b| → cnt ')' (firstn b i0) ≤ cnt '(' (firstn b i0)).
    assumption.
    destruct H5 with (and_ind ? ?) to (H5_l H5_r).
    destruct H5_r with (and_ind ? ?) to (H5_r_l H5_r_r).
    add_hyp H5_r_r_ex := (H5_r_r ((i - |'(' :: (a ++ ")")|))).
    lia.
    auto_set.
    rewrite b_property_r_r_r.
    lia.
    add_hyp H1_ex := (H1 (|a|)).
    replace #1 ((firstn a (|a|))) with (a) in H1_ex.
    apply firstn_len.
    replace #1 ((firstn a (|a|))) with (a) in H1_ex.
    apply firstn_len.
    lia.
    replace #1 ((firstn ('(' :: (a ++ ")" ++ b)) i)) with ((firstn ('(' :: (a ++ ")")) i)).
    replace #1 ('(' :: (a ++ ")" ++ b)) with ('(' :: (a ++ ")") ++ b).
    auto_list.
    apply firstn_append_l.
    lia.
    replace #1 ((firstn ('(' :: (a ++ ")" ++ b)) i)) with ((firstn ('(' :: (a ++ ")")) i)).
    replace #1 ('(' :: (a ++ ")" ++ b)) with ('(' :: (a ++ ")") ++ b).
    auto_list.
    apply firstn_append_l.
    lia.
    add_hyp (i = |a| + 2 ∨ i ≤ |a| + 1).
    lia.
    destruct H5 with (or_ind ? ?).
    add_hyp H1_ex := (H1 (i - 1)).
    replace #1 (firstn ('(' :: (a ++ ")")) i) with ('(' :: firstn a (i - 1)).
    replace #1 (firstn a (i - 1)) with (firstn (a ++ ")") (i - 1)).
    apply eq_sym.
    apply firstn_append_l.
    lia.
    replace #1 (i) with (i - 1 + 1).
    lia.
    apply firstn_cons.
    lia.
    replace #1 (firstn ('(' :: (a ++ ")")) i) with (('(' :: firstn a (i - 1))).
    replace #1 (firstn a (i - 1)) with (firstn (a ++ ")") (i - 1)).
    apply eq_sym.
    apply firstn_append_l.
    lia.
    replace #1 (i) with (i - 1 + 1).
    lia.
    apply firstn_cons.
    lia.
    lia.
    replace #1 (firstn ('(' :: (a ++ ")")) i) with ('(' :: (firstn ( (a)) (i - 2) ++ ")")).
    replace #2 (")") with (firstn ")" 1).
    apply eq_sym.
    apply firstn_cons_1.
    replace #1 ((firstn a (i - 2) ++ firstn ")" 1)) with (firstn (a ++ ")") (|a| + 1)).
    replace #1 ((i - 2)) with (|a|).
    lia.
    apply eq_sym.
    replace #1 (firstn a (|a|)) with (a).
    apply firstn_len.
    apply firstn_append_r.
    lia.
    replace #1 (i) with (|a| + 1 + 1).
    lia.
    apply firstn_cons.
    lia.
    replace #1 ((firstn ('(' :: (a ++ ")")) i)) with ('(' :: (firstn a (i - 2) ++ ")")).
    replace #2 (")") with (firstn ")" 1).
    apply eq_sym.
    apply firstn_cons_1.
    replace #1 ((firstn a (i - 2) ++ firstn ")" 1)) with (firstn (a ++ ")") (|a| + 1)).
    replace #1 ((i - 2)) with (|a|).
    lia.
    apply eq_sym.
    replace #1 (firstn a (|a|)) with (a).
    apply firstn_len.
    apply firstn_append_r.
    lia.
    replace #1 (i) with (|a| + 1 + 1).
    lia.
    apply firstn_cons.
    lia.
    replace #1 (firstn a (i - 2)) with (a).
    replace #1 ((i - 2)) with (|a|).
    lia.
    apply firstn_len.
    replace #1 (firstn a (i - 2)) with (a).
    replace #1 ((i - 2)) with (|a|).
    lia.
    apply firstn_len.
    add_hyp H1_ex := (H1 (|a|)).
    replace #1 ((firstn a (|a|))) with (a) in H1_ex.
    apply firstn_len.
    replace #1 ((firstn a (|a|))) with (a) in H1_ex.
    apply firstn_len.
    lia.
    auto_list.
    apply valid_paren_cnt_right.
    auto_set.
    assumption.
    apply valid_paren_cnt_left.
    auto_set.
    assumption.
Qed.

Todo valid_paren_counting:  ∀ n, | { l | |l| = 2 * n ∧ valid_paren l } | = cm (2 * n) (n) - cm (2 * n) (n - 1).