Import /Set.

Axiom multi: (set ℤ) -> ℤ.
Axiom multi_empty: multi {} = 1.
Axiom multi_atom: ∀ a: ℤ, multi {a} = a.
Axiom multi_split: ∀ A B: set ℤ, B ⊆ A ->  multi A = multi B * multi (A ∖ B).

Axiom P_hold_for_multi: ∀ P: ℤ -> U, ∀ A: set ℤ, finite A -> P 1 -> (∀ x: ℤ, x ∈ A -> P x) -> (∀ x y: ℤ, P x ∧ P y -> P (x * y))-> P (multi A).
Axiom P_hold_for_multi_not_complete: ∀ P: ℤ -> U, ∀ A: set ℤ, finite A -> (A = {} -> False) -> (∀ x: ℤ, x ∈ A -> P x) -> (∀ x y: ℤ, P x ∧ P y -> P (x * y))-> P (multi A).
