Theorem sigma_is_zero: ∀ a: ℤ, ∀ f: ℤ -> ℤ, eq ℤ (sigma a a f) 0.
Proof. intros. lia. Qed.
Theorem sigma_atom: ∀ a: ℤ, ∀ f: ℤ -> ℤ, eq ℤ (sigma a (a+1) f) (f a).
Proof. intros. lia. Qed.
Theorem sigma_atom_minus: ∀ a: ℤ, ∀ f: ℤ -> ℤ, eq ℤ (sigma (a-1) a f) (f (a-1)).
Proof. intros. lia. Qed.
Theorem sigma_plus: ∀ a b c: ℤ, ∀ f: ℤ -> ℤ, eq ℤ (sigma a b f + sigma b c f) (sigma a c f).
Proof. intros. lia. Qed.
Todo sigma_factor: ∀ a b c: ℤ, ∀ f: ℤ -> ℤ, c * sigma a b f = sigma a b (λ i: ℤ, c * f i).
Todo sigma_f_equal: ∀ a b: ℤ, ∀ f g: ℤ -> ℤ, (∀ i, a ≤ i -> i < b -> f i = g i) -> sigma a b f = sigma a b g.
Todo sigma_neg1: ∀ n: ℤ, ∀ f: ℤ -> ℤ, sigma (-n) 0 (λ i: ℤ, - f i) = sigma 0 (n+1) f.
