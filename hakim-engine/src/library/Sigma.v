Theorem sigma_is_zero: ∀ a: ℤ, ∀ f: ℤ -> ℤ, eq ℤ (sigma a a f) 0.
Proof. intros. lia. Qed.
Theorem sigma_atom: ∀ a: ℤ, ∀ f: ℤ -> ℤ, eq ℤ (sigma a (a+1) f) (f a).
Proof. intros. lia. Qed.
Theorem sigma_atom_minus: ∀ a: ℤ, ∀ f: ℤ -> ℤ, eq ℤ (sigma (a-1) a f) (f (a-1)).
Proof. intros. lia. Qed.
Theorem sigma_plus: ∀ a b c: ℤ, ∀ f: ℤ -> ℤ, eq ℤ (sigma a b f + sigma b c f) (sigma a c f).
Proof. intros. lia. Qed.
Axiom sigma_factor: ∀ a b c: ℤ, ∀ f: ℤ -> ℤ, c * sigma a b f = sigma a b (λ i: ℤ, c * f i).
