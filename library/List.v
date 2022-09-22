Import /Induction.

Axiom #1 head: ∀ A: U, A -> list A -> A.
Axiom cons_nil_case: ∀ A: U, ∀ x: list A, x = nil A ∨ ∃ y: list A, ∃ a: A, x = cons A a y.

Axiom head_nil: ∀ A: U, ∀ default: A, head default [] = default.
Axiom head_cons: ∀ A: U, ∀ default: A, ∀ x: list A, ∀ a: A, head default (cons A a x) = a.

Axiom #1 tail: ∀ A: U, list A -> list A.

Axiom tail_nil: ∀ A: U, tail (nil A) = nil A.
Axiom tail_cons: ∀ A: U, ∀ x: list A, ∀ a: A, tail (cons A a x) = x.

Todo tail_add: ∀ A: U, ∀ x: list A, ∀ a: A, tail ([a] ++ x) = x.
Axiom cons_head_tail: ∀ A: U, ∀ default: A, ∀ x: list A, x = cons A (head default x) (tail x).
Axiom cons_to_add_list: ∀ A: U, ∀ x: list A, ∀ a: A, cons A a x = [a] ++ x.

Todo add_head_tail: ∀ A: U, ∀ default: A, ∀ x: list A, x = [head default x] ++ (tail x).
Todo list_len_concat_lt: ∀ A: U, ∀ x y: list A, ~ x = nil A -> |y| < |x++y|.
Todo add_head: ∀ A: U, ∀ default: A, ∀ x: list A, ∀ a: A, head default ([a] ++ x) = a.
Todo Inhabit_not_empty_list: ∀ T: U, ∀ x: list T, |x| > 0 -> ∃ x: T, True.

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

Todo tail_len: ∀ T: U, ∀ x: list T, ∀ n: ℤ, |x| = n + 1 → |tail x| = n.
Suggest goal auto apply tail_len; Trivial.

Theorem list_len_gt_0: ∀ A: U, ∀ x: list A, 0 ≤ |x|.
Proof.
    intros A.
    apply list_induction_len.
    intros.
    add_from_lib cons_nil_case.
    add_hyp cons_nil_case_ex := (cons_nil_case (A)).
    add_hyp cons_nil_case_ex_ex := (cons_nil_case_ex (b)).
    destruct cons_nil_case_ex_ex with (or_ind ? ?).
    destruct cons_nil_case_ex_ex with (ex_ind ? ?) to (a a_property).
    destruct a_property with (ex_ind ? ?) to (e e_property).
    add_hyp H_ex := (H (a)).
    replace #1 (|b|) with (|a| + 1).
    replace #1 (b) with (cons A e a).
    assumption.
    lia.
    Seq (add_hyp (⁨|a| < |b|⁩)) (remove_hyp H_ex) (Switch 1) (add_hyp H_ex_o := (H_ex H0)) (remove_hyp H0) (remove_hyp H_ex) .
    lia.
    replace #1 (b) with (cons A e a).
    assumption.
    lia.
    lia.
Qed.
Theorem nil_unique: ∀ A: U, ∀ l: list A, |l| = 0 -> l = [].
Proof.
    intros.
    add_from_lib cons_nil_case.
    add_hyp cons_nil_case_ex := (cons_nil_case (A)).
    add_hyp cons_nil_case_ex_ex := (cons_nil_case_ex (l)).
    destruct cons_nil_case_ex_ex with (or_ind ? ?).
    destruct cons_nil_case_ex_ex with (ex_ind ? ?) to (y y_property).
    destruct y_property with (ex_ind ? ?) to (a a_property).
    replace #1 (l) with (cons A a y) in H.
    assumption.
    lia.
    assumption.
Qed.
Axiom #1 repeat: ∀ A: U, ℤ -> A -> list A.
Axiom repeat_intro: ∀ A: U, ∀ x: A, ∀ t: ℤ, 0 ≤ t -> repeat t x = [x] ++ repeat (t - 1) x.
Todo repeat_unique: ∀ A: U, ∀ x: A, ∀ l: list A, cnt x l = |l| -> l = repeat (|l|) x.
Todo repeat_len: ∀ A: U, ∀ x: A, ∀ t: ℤ, 0 ≤ t -> |repeat t x| = t.
Todo repeat_cnt: ∀ A: U, ∀ x: A, ∀ t: ℤ, 0 ≤ t -> cnt x (repeat t x) = t.
Todo repeat_cnt_others: ∀ A: U, ∀ x y: A, ∀ t: ℤ, 0 ≤ t -> ~ x = y -> cnt y (repeat t x) = 0.
Todo repeat_head: ∀ A: U, ∀ default: A, ∀ x: A, ∀ t: ℤ, 0 < t -> head default (repeat t x) = x.

Axiom #1 member_set: ∀ A: U, list A -> set A.
Todo member_set_subset: ∀ A: U, ∀ l: list A, ∀ m: set A, member_set l ⊆ m -> l = [] ∨ ∃ h: A, ∃ t: list A, h ∈ m ∧ l = [h] ++ t ∧ member_set t ⊆ m.
Todo member_set_empty: ∀ A: U, member_set (nil A) = {}.
Todo member_set_singleton: ∀ A: U, ∀ x: A, member_set ([x]) = {x}.
Todo member_set_append: ∀ A: U, ∀ x y: list A, member_set (x ++ y) = member_set x ∪ member_set y.
Todo member_set_cons: ∀ T: U, ∀ x: list T, ∀ a: T, a ∈ member_set (cons T a x).
Todo head_in_member_set: ∀ T: U, ∀ x: list T, ∀ default: T, (head default x) ∈ member_set x.
Todo member_set_repeat: ∀ T: U, ∀ x: T, ∀ t: ℤ, 0 < t -> member_set (repeat t x) = {x}.
Suggest goal auto apply member_set_empty; Trivial.
Suggest goal auto apply member_set_singleton; Trivial.
Suggest goal auto apply member_set_append; Trivial.

