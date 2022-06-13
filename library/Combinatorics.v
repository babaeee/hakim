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
