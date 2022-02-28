Import Set.

Axiom multi: (set ℤ) -> ℤ.
Axiom multi_empty: eq ℤ (multi ({})) 1.
Axiom multi_atom: ∀ a: ℤ, eq ℤ (multi ({a})) a.
Axiom multi_split: ∀ A B: set ℤ, B ⊆ A -> eq ℤ (multi B * multi (A ∖ B)) (multi A).

Axiom P_hold_for_multi: ∀ A: set ℤ, ∀ P: ℤ -> U, finite ℤ A -> P 1 -> (∀ x: ℤ, x ∈ A -> P x) -> (∀ x y: ℤ, P x ∧ P y -> P (x * y))-> P (multi A).