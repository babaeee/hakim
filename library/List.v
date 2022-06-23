Import /Induction.

Todo list_len_concat_lt: ∀ A: U, ∀ x y: list A, ~ x = nil A -> |y| < |x++y|.
Theorem list_induction_len: ∀ A: U, ∀ P: list A -> U, (∀ b: list A, (∀ a: list A, |a| < |b| -> P a) -> P b) -> ∀ a: list A, P a.
Proof.
    intros.
    add_hyp (∃ k, k = |a|).
    apply (ex_intro ? ? (|a|)).
    auto_list.
    destruct H0 with (ex_ind ? ?) to (k k_property).
    add_hyp (0 ≤ k).
    lia.
    revert k_property.
    revert a.
    revert H0.
    revert k.
    apply z_induction_strong.
    intros.
    apply H.
    intros.
    apply (⁨H1 (|a0|) ?2 ?4 ?6 ?8⁩).
    auto_list.
    lia.
    lia.
Qed.

Todo nil_unique: ∀ A: U, ∀ l: list A, |l| = 0 -> l = [].

Axiom repeat: ∀ A: U, ℤ -> A -> list A.
Todo repeat_unique: ∀ A: U, ∀ x: A, ∀ l: list A, cnt x l = |l| -> l = repeat (|l|) x.
Todo repeat_len: ∀ A: U, ∀ x: A, ∀ t: ℤ, 0 ≤ t -> |repeat t x| = t.
Todo repeat_cnt: ∀ A: U, ∀ x: A, ∀ t: ℤ, 0 ≤ t -> cnt x (repeat t x) = t.
Todo repeat_cnt_others: ∀ A: U, ∀ x y: A, ∀ t: ℤ, 0 ≤ t -> ~ x = y -> cnt y (repeat t x) = 0.

Axiom member_set: ∀ A: U, list A -> set A.
Todo member_set_subset: ∀ A: U, ∀ l: list A, ∀ m: set A, member_set l ⊆ m -> l = [] ∨ ∃ h: A, ∃ t: list A, h ∈ m ∧ l = [h] ++ t ∧ member_set t ⊆ m.
Todo member_set_empty: ∀ A: U, member_set (nil A) = {}.
Todo member_set_singleton: ∀ A: U, ∀ x: A, member_set ([x]) = {x}.
Todo member_set_append: ∀ A: U, ∀ x y: list A, member_set (x ++ y) = member_set x ∪ member_set y.
Suggest goal auto apply member_set_empty; Trivial.
Suggest goal auto apply member_set_singleton; Trivial.
Suggest goal auto apply member_set_append; Trivial.
