Import /Set.
Import /List.
Import /Arith.
Import /NumberTheory.
Import /Sigma.

Theorem rule_of_sum: ∀ T: Universe, ∀ A B: set T, finite A -> finite B -> A ∩ B = {} -> |A ∪ B| = |A| + |B|.
Proof.
intros.
apply (⁨set_induction T (λ D: (set T), A ∩ D = {} → |A ∪ D| = |A| + |D|) ?2 ?4 ?6 ?8⁩).
assumption.
assumption.
intros.
replace #1 (A ∪ (x ∪ {a})) with (A ∪ x ∪ {a}).
auto_set.
apply eq_sym.
replace #1 (|A ∪ x ∪ {a}|) with (|A ∪ x| + 1).
apply finite_add_len.
intros.
add_hyp (a ∈ A ).
auto_set.
apply eq_set_empty in H5.
add_hyp H5_ex := (H5 (a)).
auto_set.
auto_set.
replace #1 (|x ∪ {a}|) with (|x| + 1).
apply finite_add_len.
assumption.
assumption.
replace #1 (|A ∪ x|) with (|A ∪ x|).
auto_list.
replace #1 (|A ∪ x|) with (|A| + |x|).
apply H3.
apply NNPP.
intros.
apply non_empty_has_member in H6.
destruct H6 with (ex_ind ? ?) to (H6_value H6_proof).
apply set_equality_unfold in H5.
destruct H5 with (and_ind ? ?) to (H5_l H5_r).
apply included_unfold in H5_l.
add_hyp H5_l_ex := (H5_l (H6_value)).
auto_set.
lia.
intros.
replace #1 (A ∪ {}) with (A ).
auto_set.
lia.
Qed.
Axiom rule_of_sum2: ∀ T: Universe, ∀ A B: set T, finite A -> B ⊆ A -> |A| = |A ∖ B| + |B|.
Theorem rule_of_minus: ∀ T: Universe, ∀ A B: set T, finite A -> B ⊆ A -> |A ∖ B| = |A| - |B|.
Proof.
    intros.
    add_hyp (|A| = |A ∖ B| + |B|).
    replace #1 (A) with ((A∖B)∪B).
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

Theorem projection_finite: ∀ A B: U, ∀ f: A -> B, ∀ S: set A, finite S -> finite { y: B | ∃ x: A, y = f x ∧ x ∈ S }.
Proof.
    intros A B f.
    apply set_induction.
    intros.
    replace #1 ({ y: B | ∃ x0: A, y = f x0 ∧ x0 ∈ x ∪ {a} }) with ({ y: B | ∃ x0: A, y = f x0 ∧ x0 ∈ x } ∪ {f a}).
    apply set_equality.
    apply included_fold.
    intros.
    Switch 2.
    auto_set.
    Switch 2.
    replace #1 ({ y: B | ∃ x: A, y = f x ∧ x ∈ {} }) with (set_empty B).
    apply set_equality.
    auto_set.
    apply included_fold.
    intros.
    apply set_from_func_unfold in H.
    destruct H with (ex_ind ? ?) to (H_value H_proof).
    auto_set.
    auto_set.
    apply union_unfold in H2.
    apply set_from_func_fold.
    destruct H2 with (or_ind ? ?).
    apply (ex_intro ? ? (a)).
    auto_set.
    apply set_from_func_unfold in H2.
    destruct H2 with (ex_ind ? ?) to (b b_property).
    apply (ex_intro ? ? (b)).
    auto_set.
    apply included_fold.
    intros.
    apply set_from_func_unfold in H2.
    destruct H2 with (ex_ind ? ?) to (b b_property).
    destruct b_property with (and_ind ? ?) to (b_property_l b_property_r).
    apply union_fold.
    apply union_unfold in b_property_r.
    destruct b_property_r with (or_ind ? ?).
    apply or_intror.
    apply singleton_unfold in b_property_r.
    apply singleton_fold.
    rewrite b_property_r.
    auto_set.
    apply or_introl.
    apply set_from_func_fold.
    apply (ex_intro ? ? (b)).
    assumption.
Qed.
Theorem projection_finite2: ∀ A B C: U, ∀ f: A -> B -> C,
    ∀ SA: set A, ∀ SB: set B, finite SA -> finite SB
        -> finite { y: C | ∃ a: A, ∃ b: B, y = f a b ∧ a ∈ SA ∧ b ∈ SB }.
Proof.
    intros A B C f.
    intros SA SB H.
    revert SB.
    apply set_induction.
    intros.
    replace #1 ({ y: C | ∃ a0: A, ∃ b: B, y = f a0 b ∧ a0 ∈ SA ∧ b ∈ x ∪ {a} }) with ({ y: C | ∃ a0: A, ∃ b: B, y = f a0 b ∧ a0 ∈ SA ∧ b ∈ x } ∪ { y: C | ∃ a0: A, y = f a0 a ∧ a0 ∈ SA }).
    Switch 1.
    add_hyp (finite ( { y: C | ∃ a0: A, y = f a0 a ∧ a0 ∈ SA })).
    apply projection_finite.
    assumption.
    auto_set.
    Switch 1.
    replace #1 ({ y: C | ∃ a: A, ∃ b: B, y = f a b ∧ a ∈ SA ∧ b ∈ {} }) with (set_empty C).
    apply set_equality.
    auto_set.
    apply included_fold.
    intros.
    apply set_from_func_unfold in H0.
    destruct H0 with (ex_ind ? ?) to (H0_value H0_proof).
    destruct H0_proof with (ex_ind ? ?) to (H0_proof_value H0_proof_proof).
    auto_set.
    auto_set.
    apply set_equality.
    apply included_fold.
    intros.
    apply set_from_func_fold.
    apply union_unfold in H3.
    destruct H3 with (or_ind ? ?).
    apply set_from_func_unfold in H3.
    destruct H3 with (ex_ind ? ?) to (xa xa_property).
    apply (ex_intro ? ? (xa)).
    apply (ex_intro ? ? (a)).
    auto_set.
    apply set_from_func_unfold in H3.
    destruct H3 with (ex_ind ? ?) to (xa xa_property).
    destruct xa_property with (ex_ind ? ?) to (xb xb_property).
    apply (ex_intro ? ? (xa)).
    apply (ex_intro ? ? (xb)).
    auto_set.
    apply included_fold.
    intros.
    apply set_from_func_unfold in H3.
    apply union_fold.
    destruct H3 with (ex_ind ? ?) to (xa xa_property).
    destruct xa_property with (ex_ind ? ?) to (xb xb_property).
    destruct xb_property with (and_ind ? ?) to (xb_property_l xb_property_r).
    destruct xb_property_r with (and_ind ? ?) to (xb_property_r_l xb_property_r_r).
    apply union_unfold in xb_property_r_r.
    destruct xb_property_r_r with (or_ind ? ?).
    apply singleton_unfold in xb_property_r_r.
    apply or_intror.
    apply set_from_func_fold.
    rewrite xb_property_r_r.
    apply (ex_intro ? ? (xa)).
    assumption.
    apply or_introl.
    apply set_from_func_fold.
    apply (ex_intro ? ? (xa)).
    apply (ex_intro ? ? (xb)).
    assumption.
Qed.
Theorem rule_of_bijectionT: ∀ A B: U, ∀ f: A -> B, ∀ S: set A, finite S -> (∀ x y: A, x ∈ S -> y ∈ S -> f x = f y -> x = y) -> |{ y: B | ∃ x: A, y = f x ∧ x ∈ S }| = |S|.
Proof.
    intros A B f.
    apply set_induction.
    intros.
    replace #1 (|x ∪ {a}|) with (|x|+ |{a}|).
    apply rule_of_sum.
    auto_set.
    auto_set.
    assumption.
    replace #1 ({ y: B | ∃ x0: A, y = f x0 ∧ x0 ∈ x ∪ {a} }) with ({ y: B | ∃ x0: A, y = f x0 ∧ x0 ∈ x } ∪ { f a }).
    apply set_equality.
    apply included_fold.
    intros.
    apply union_unfold in H3.
    apply set_from_func_fold.
    destruct H3 with (or_ind ? ?).
    apply singleton_unfold in H3.
    apply (ex_intro ? ? (a)).
    auto_set.
    apply set_from_func_unfold in H3.
    destruct H3 with (ex_ind ? ?) to (H3_value H3_proof).
    apply (ex_intro ? ? (H3_value)).
    auto_set.
    apply included_fold.
    intros.
    apply set_from_func_unfold in H3.
    apply union_fold.
    destruct H3 with (ex_ind ? ?) to (w w_property).
    destruct w_property with (and_ind ? ?) to (w_property_l w_property_r).
    apply union_unfold in w_property_r.
    destruct w_property_r with (or_ind ? ?).
    apply singleton_unfold in w_property_r.
    apply or_intror.
    apply singleton_fold.
    rewrite w_property_l.
    rewrite w_property_r.
    auto_list.
    apply or_introl.
    apply set_from_func_fold.
    apply (ex_intro ? ? (w)).
    assumption.
    replace #1 (|{ y: B | ∃ x0: A, y = f x0 ∧ x0 ∈ x } ∪ {f a}|) with (|{ y: B | ∃ x0: A, y = f x0 ∧ x0 ∈ x }| + |{f a}|).
    apply rule_of_sum.
    apply set_equality.
    auto_set.
    apply included_fold.
    intros.
    apply intersection_unfold in H3.
    destruct H3 with (and_ind ? ?) to (H3_l H3_r).
    apply singleton_unfold in H3_r.
    apply set_from_func_unfold in H3_l.
    destruct H3_l with (ex_ind ? ?) to (b b_property).
    destruct b_property with (and_ind ? ?) to (b_property_l b_property_r).
    add_hyp (f a = f b).
    auto_set.
    apply H2 in H3.
    auto_set.
    auto_set.
    auto_set.
    auto_set.
    apply projection_finite.
    assumption.
    replace #1 (|{ y: B | ∃ x0: A, y = f x0 ∧ x0 ∈ x }|) with (|x|).
    apply H0.
    intros.
    apply H2.
    assumption.
    auto_set.
    auto_set.
    replace #1 (|{f a}|) with (1).
    apply singleton_len.
    replace #1 (|{a}|) with (1).
    apply singleton_len.
    auto_list.
    intros.
    replace #1 ({ y: B | ∃ x: A, y = f x ∧ x ∈ {} }) with (set_empty B).
    apply set_equality.
    auto_set.
    apply included_fold.
    intros.
    apply set_from_func_unfold in H0.
    destruct H0 with (ex_ind ? ?) to (H0_value H0_proof).
    auto_set.
    add_from_lib empty_len.
    add_hyp empty_len_ex := (empty_len (A)).
    add_hyp empty_len_ex0 := (empty_len (B)).
    auto_set.
Qed.

Theorem rule_of_bijection_product: ∀ A B C: U, ∀ f: A -> B -> C,
    ∀ SA: set A, ∀ SB: set B, finite SA -> finite SB
        -> (∀ xa ya: A, ∀ xb yb: B, xa ∈ SA -> ya ∈ SA -> xb ∈ SB -> yb ∈ SB -> f xa xb = f ya yb -> xa = ya ∧ xb = yb)
        -> |{ y: C | ∃ a: A, ∃ b: B, y = f a b ∧ a ∈ SA ∧ b ∈ SB }| = |SA| * |SB|.
Proof.
    intros A B C f SA SB H.
    revert SB.
    apply set_induction.
    intros.
    replace #1 ({ y: C | ∃ a0: A, ∃ b: B, y = f a0 b ∧ a0 ∈ SA ∧ b ∈ x ∪ {a} }) with ({ y: C | ∃ a0: A, ∃ b: B, y = f a0 b ∧ a0 ∈ SA ∧ b ∈ x } ∪ { y: C | ∃ a0: A, y = f a0 a ∧ a0 ∈ SA }).
    apply set_equality.
    apply included_fold.
    intros.
    apply set_from_func_fold.
    apply union_unfold in H4.
    destruct H4 with (or_ind ? ?).
    apply set_from_func_unfold in H4.
    destruct H4 with (ex_ind ? ?) to (H4_value H4_proof).
    apply (ex_intro ? ? (H4_value)).
    apply (ex_intro ? ? (a)).
    auto_set.
    apply set_from_func_unfold in H4.
    destruct H4 with (ex_ind ? ?) to (xa xa_property).
    destruct xa_property with (ex_ind ? ?) to (xb xb_property).
    apply (ex_intro ? ? (xa)).
    apply (ex_intro ? ? (xb)).
    auto_set.
    apply included_fold.
    intros.
    apply union_fold.
    apply set_from_func_unfold in H4.
    destruct H4 with (ex_ind ? ?) to (xa xa_property).
    destruct xa_property with (ex_ind ? ?) to (xb xb_property).
    destruct xb_property with (and_ind ? ?) to (xb_property_l xb_property_r).
    destruct xb_property_r with (and_ind ? ?) to (xb_property_r_l xb_property_r_r).
    apply union_unfold in xb_property_r_r.
    destruct xb_property_r_r with (or_ind ? ?).
    apply singleton_unfold in xb_property_r_r.
    apply or_intror.
    apply set_from_func_fold.
    apply (ex_intro ? ? (xa)).
    rewrite xb_property_r_r.
    assumption.
    apply or_introl.
    apply set_from_func_fold.
    apply (ex_intro ? ? (xa)).
    apply (ex_intro ? ? (xb)).
    assumption.
    replace #1 (|{ y: C | ∃ a0: A, ∃ b: B, y = f a0 b ∧ a0 ∈ SA ∧ b ∈ x } ∪ { y: C | ∃ a0: A, y = f a0 a ∧ a0 ∈ SA }|) with (|{ y: C | ∃ a0: A, ∃ b: B, y = f a0 b ∧ a0 ∈ SA ∧ b ∈ x }| + |{ y: C | ∃ a0: A, y = f a0 a ∧ a0 ∈ SA }|).
    apply rule_of_sum.
    apply set_equality.
    auto_set.
    apply included_fold.
    intros.
    apply intersection_unfold in H4.
    destruct H4 with (and_ind ? ?) to (H4_l H4_r).
    apply set_from_func_unfold in H4_l.
    apply set_from_func_unfold in H4_r.
    destruct H4_l with (ex_ind ? ?) to (xa1 xa1_property).
    destruct H4_r with (ex_ind ? ?) to (xa2 xa2_property).
    destruct xa1_property with (ex_ind ? ?) to (xb xb_property).
    destruct xa2_property with (and_ind ? ?) to (xa2_property_l xa2_property_r).
    destruct xb_property with (and_ind ? ?) to (xb_property_l xb_property_r).
    replace #1 (a0) with (f xa2 a) in xb_property_l.
    assumption.
    apply H3 in xb_property_l.
    auto_set.
    auto_set.
    assumption.
    assumption.
    auto_set.
    apply projection_finite.
    assumption.
    apply (⁨projection_finite2 ?0 ?2 ?4 f ?8 ?10 ?12 ?14⁩).
    assumption.
    assumption.
    replace #1 (|x ∪ {a}|) with (|x| + 1).
    apply finite_add_len.
    assumption.
    assumption.
    replace #1 (|{ y: C | ∃ a0: A, y = f a0 a ∧ a0 ∈ SA }|) with (|SA|).
    apply rule_of_bijectionT.
    intros.
    apply H3 in H6.
    auto_set.
    auto_set.
    assumption.
    assumption.
    assumption.
    assumption.
    replace #1 (|{ y: C | ∃ a0: A, ∃ b: B, y = f a0 b ∧ a0 ∈ SA ∧ b ∈ x }|) with (|SA|*|x|).
    apply H1.
    intros.
    apply H3.
    assumption.
    auto_set.
    auto_set.
    assumption.
    assumption.
    lia.
    intros.
    replace #1 ({ y: C | ∃ a: A, ∃ b: B, y = f a b ∧ a ∈ SA ∧ b ∈ {} }) with (set_empty C).
    apply set_equality.
    auto_set.
    apply included_fold.
    intros.
    apply set_from_func_unfold in H1.
    destruct H1 with (ex_ind ? ?) to (H1_value H1_proof).
    destruct H1_proof with (ex_ind ? ?) to (H1_proof_value H1_proof_proof).
    auto_set.
    lia.
Qed.

