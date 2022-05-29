Import /Set.
Import /Arith.

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