Import /Set.
Import /List.
Import /Arith.
Import /NumberTheory.

Axiom rule_of_sum: ∀ T: Universe, ∀ A B: set T, finite T A -> finite T B -> A ∩ B = {} -> |A| + |B| = |A ∪ B|.
Theorem rule_of_minus: ∀ T: Universe, ∀ A B: set T, finite T A -> B ⊆ A -> |A ∖ B| = |A| - |B|.
Proof.
    intros.
    add_hyp (|A| = |A ∖ B| + |B|).
    apply eq_sym.
    replace #2 (A) with ((A∖B)∪B).
    auto_set.
    apply rule_of_sum.
    auto_set.
    apply finite_included in H0.
    assumption.
    assumption.
    apply (finite_included ?0 ?1 A ?3 ?4).
    auto_set.
    assumption.
    rewrite H1.
    lia.
Qed.

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
Theorem valid_paren_cnt_left: ∀ a, valid_paren a -> ∀ k, 2 * k = |a| -> cnt char '(' a = k.
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