Import /Function.

Axiom z_simple_recdep: ∀ k: ℤ, ∀ P: ℤ -> U, ∀ a: P k, ∀ b: (∀ n: ℤ, k ≤ n -> P n -> P (n+1)), ∃ f: (∀ n: ℤ, k ≤ n -> P n), ∀ n: ℤ, (∀ kp: k ≤ k, f k kp = a) ∧ ∀ kp: k ≤ n, ∀ kp2: k ≤ n + 1, f (n+1) kp2 = b n kp (f n kp).

Theorem z_simple_induction: ∀ k: ℤ, ∀ P: ℤ -> U, P k -> (∀ n: ℤ, k ≤ n -> P n -> P (n+1)) -> (∀ n: ℤ, k ≤ n -> P n).
Proof.
    intros.
    add_from_lib z_simple_recdep.
    add_hyp z_simple_recdep_ex := (z_simple_recdep (k)).
    add_hyp z_simple_recdep_ex_ex := (z_simple_recdep_ex (P)).
    add_hyp z_simple_recdep_ex_ex_ex := (z_simple_recdep_ex_ex (H)).
    add_hyp z_simple_recdep_ex_ex_ex_ex := (z_simple_recdep_ex_ex_ex (H0)).
    destruct z_simple_recdep_ex_ex_ex_ex with (ex_ind ? ?) to (f f_property).
    apply f.
    assumption.
Qed.

Todo z_simple_recursion: ∀ k: ℤ, ∀ B: U, ∀ a: B, ∀ b: ℤ -> B -> B, ∃ f: ℤ -> B, f k = a ∧ ∀ n: ℤ, k ≤ n -> f (n+1) = b n (f n).
