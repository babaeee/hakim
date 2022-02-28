Axiom sigma: ℤ -> ℤ -> (ℤ -> ℤ) -> ℤ.
Axiom sigma_is_zero: ∀ a: ℤ, ∀ f: ℤ -> ℤ, eq ℤ (sigma a a f) 0.
Axiom sigma_atom: ∀ a: ℤ, ∀ f: ℤ -> ℤ, eq ℤ (sigma a (a+1) f) (f a).
Axiom sigma_plus: ∀ a b c: ℤ, ∀ f: ℤ -> ℤ, eq ℤ (sigma a b f + sigma b c f) (sigma a c f).
Axiom sigma_factor: ∀ a b c: ℤ, ∀ f: ℤ -> ℤ, c * sigma a b f = sigma a b (λ i: ℤ, c * f i).
