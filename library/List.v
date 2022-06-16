Todo list_len_concat_lt: ∀ A: U, ∀ x y: list A, ~ x = nil A -> |y| < |x++y|.
Todo list_induction_len: ∀ A: U, ∀ P: list A -> U, (∀ b: list A, (∀ a: list A, |a| < |b| -> P a) -> P b) -> ∀ a: list A, P a.

Axiom repeat: ∀ A: U, ℤ -> A -> list A.
Todo repeat_unique: ∀ A: U, ∀ x: A, ∀ l: list A, cnt x l = |l| -> l = repeat (|l|) x.
Todo repeat_len: ∀ A: U, ∀ x: A, ∀ t: ℤ, 0 ≤ t -> |repeat t x| = t.
Todo repeat_cnt: ∀ A: U, ∀ x: A, ∀ t: ℤ, 0 ≤ t -> cnt x (repeat t x) = t.
Todo repeat_cnt_others: ∀ A: U, ∀ x y: A, ∀ t: ℤ, 0 ≤ t -> ~ x = y -> cnt y (repeat t x) = 0.
