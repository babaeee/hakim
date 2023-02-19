Import /NumberTheory;

Todo Rtotal_order: ∀ x: ℝ, ∀ a: ℝ, x = a ∨ x < a ∨ x > a;

Todo Q_lt: ∀ a b c d: ℤ, ~ b = 0 -> ~ d = 0 -> a * d < b * c -> a / b < c / d;
Suggest goal default apply Q_lt with label a / b < c / d => a * d < b * c;

Todo Rle_trans: ∀ a b c: ℝ, a ≤ b -> b ≤ c -> a ≤ c;
Suggest goal default apply Rle_trans with label a ≤ c => enter b so that a ≤ b and b ≤ c;
Todo Rle_lt_trans: ∀ a b c: ℝ, a ≤ b -> b < c -> a < c;
Suggest goal default apply Rle_lt_trans with label a < c => enter b so that a ≤ b and b < c;
Todo Rlt_le_trans: ∀ a b c: ℝ, a < b -> b ≤ c -> a < c;
Suggest goal default apply Rlt_le_trans with label a < c => enter b so that a < b and b ≤ c;

Todo Rplus_le_compat: ∀ a b c d: ℝ, a ≤ b -> c ≤ d -> a + c ≤ b + d;
Suggest goal default apply Rplus_le_compat with label a + c ≤ b + d => a ≤ b and c ≤ d;
Todo Rplus_lt_le_compat: ∀ a b c d: ℝ, a < b -> c ≤ d -> a + c < b + d;
Suggest goal default apply Rplus_lt_le_compat with label a + c < b + d => a < b and c ≤ d;
Todo Rplus_le_lt_compat: ∀ a b c d: ℝ, a ≤ b -> c < d -> a + c < b + d;
Suggest goal default apply Rplus_le_lt_compat with label a + c < b + d => a ≤ b and c < d;

Todo lt_pow_2: ∀ a b: ℝ, a * a < b * b -> a < b;

Axiom sqrt: ℝ -> ℝ;

Axiom sqrt_def: ∀ x: ℝ, 0. ≤ x -> sqrt x * sqrt x = x;

Axiom in_q_unfold: ∀ x: ℝ, x ∈ ℚ -> ∃ a b: ℤ, x = a / b ∧ gcd a b = 1 ∧ b > 0;

Suggest hyp default apply in_q_unfold in $n with label x ∈ ℚ => ∃ a b: ℤ, a / b = x ∧ gcd a b = 1 ∧ b > 0;
 
Todo in_q_plus: ∀ a b: ℝ, a ∈ ℚ -> b ∈ ℚ -> (a + b) ∈ ℚ;
Suggest goal default apply in_q_plus with label (a + b) ∈ ℚ => a ∈ ℚ and b ∈ ℚ;
Todo in_q_minus: ∀ a b: ℝ, a ∈ ℚ -> b ∈ ℚ -> (a - b) ∈ ℚ;
Suggest goal default apply in_q_minus with label (a - b) ∈ ℚ => a ∈ ℚ and b ∈ ℚ;
Todo in_q_mult: ∀ a b: ℝ, a ∈ ℚ -> b ∈ ℚ -> (a * b) ∈ ℚ;
Suggest goal default apply in_q_mult with label (a * b) ∈ ℚ => a ∈ ℚ and b ∈ ℚ;

Todo pow_2_gt_Q: ∀ a b: ℝ, a ∈ ℚ -> b ∈ ℚ -> a ^ 2. < b ^ 2. -> a < b;
Todo pow_2_ge_Q: ∀ a b: ℝ, a ∈ ℚ -> b ∈ ℚ -> a ^ 2. ≤ b ^ 2. -> a ≤ b;

Theorem multiple_gt_Q: ∀ x: ℝ, ∀ e: ℝ, x ∈ ℚ -> e ∈ ℚ -> e > 0. -> ∃ N, N > 0 ∧ (N / 1) * e > x;
Proof;
    intros;
    apply in_q_unfold in H;
    destruct H with (ex_ind ? ?) to (a a_property);
    destruct a_property with (ex_ind ? ?) to (b b_property);
    destruct b_property with (and_ind ? ?) to (b_property_l b_property_r);
    rewrite b_property_l;
    apply in_q_unfold in H0;
    destruct H0 with (ex_ind ? ?) to (c c_property);
    destruct c_property with (ex_ind ? ?) to (d d_property);
    destruct d_property with (and_ind ? ?) to (d_property_l d_property_r);
    rewrite d_property_l;
    add_from_lib multiple_gt;
    add_hyp multiple_gt_ex := (multiple_gt (b * c));
    add_hyp multiple_gt_ex_ex := (multiple_gt_ex (a * d));
    Seq (add_hyp (⁨0 < b * c⁩)) (remove_hyp multiple_gt_ex_ex) (Switch 1) (add_hyp multiple_gt_ex_ex_o := (multiple_gt_ex_ex H)) (remove_hyp H) (remove_hyp multiple_gt_ex_ex);
    destruct multiple_gt_ex_ex_o with (ex_ind ? ?) to (N N_property);
    apply (ex_intro ? ? (N));
    apply and_intro;
    replace #1 (N / 1 * (c / d)) with ( (N * c / d));
    lra;
    apply Q_lt ;
    lia;
    lia;
    lia;
    assumption;
    add_hyp (c > 0);
    replace #1 (e) with (c / d) in H1;
    assumption;
    lra;
    apply zero_lt_mult_pos ;
    assumption;
    assumption;
Qed;

Definition upper_bound := λ E: set ℝ, λ x, ∀ y, y ∈ E -> y ≤ x;

Todo upper_bound_unfold: ∀ E: set ℝ, ∀ x, upper_bound E x -> ∀ y, y ∈ E -> y ≤ x;
Todo upper_bound_fold: ∀ E: set ℝ, ∀ x, (∀ y, y ∈ E -> y ≤ x) -> upper_bound E x;
Suggest hyp default apply upper_bound_unfold in $n with label upper_bound E x => ∀ y, y ∈ E -> y ≤ x;
Suggest goal default apply upper_bound_fold with label upper_bound E x => ∀ y, y ∈ E -> y ≤ x;

Definition lower_bound := λ E: set ℝ, λ x, ∀ y, y ∈ E -> x ≤ y;
 
Todo lower_bound_unfold: ∀ E: set ℝ, ∀ x, lower_bound E x -> ∀ y, y ∈ E -> x ≤ y;
Todo lower_bound_fold: ∀ E: set ℝ, ∀ x, (∀ y, y ∈ E -> x ≤ y) -> lower_bound E x;
Suggest hyp default apply lower_bound_unfold in $n with label lower_bound E x => ∀ y, y ∈ E -> x ≤ y;
Suggest goal default apply lower_bound_fold with label lower_bound E x => ∀ y, y ∈ E -> x ≤ y;

Definition lub := λ E: set ℝ, λ x, upper_bound E x ∧ (∀ y, upper_bound E y -> x ≤ y);

Todo lub_unfold: ∀ E: set ℝ, ∀ x, lub E x -> upper_bound E x ∧ (∀ y, upper_bound E y -> x ≤ y);
Todo lub_fold: ∀ E: set ℝ, ∀ x, upper_bound E x ∧ (∀ y, upper_bound E y -> x ≤ y) -> lub E x;
Suggest hyp default apply lub_unfold in $n with label lub E x => upper_bound E x ∧ (∀ y, upper_bound E y -> x ≤ y);
Suggest goal default apply lub_fold with label lub E x => upper_bound E x ∧ (∀ y, upper_bound E y -> x ≤ y);

Definition glb := λ E: set ℝ, λ x, lower_bound E x ∧ (∀ y, lower_bound E y -> y ≤ x);

Todo glb_unfold: ∀ E: set ℝ, ∀ x, glb E x -> lower_bound E x ∧ (∀ y, lower_bound E y -> y ≤ x);
Todo glb_fold: ∀ E: set ℝ, ∀ x, lower_bound E x ∧ (∀ y, lower_bound E y -> y ≤ x) -> glb E x;
Suggest hyp default apply glb_unfold in $n with label glb E x => lower_bound E x ∧ (∀ y, lower_bound E y -> y ≤ x);
Suggest goal default apply glb_fold with label glb E x => lower_bound E x ∧ (∀ y, lower_bound E y -> y ≤ x);

Todo sup_in_Q_not_exits: ~ ∃ x, x ∈ ℚ ∧ lub ({a | a * a < 2.}) x;

Axiom extR: U;
Axiom Fin: ℝ -> extR;
Axiom p_infty: extR;
Axiom m_infty: extR;
Axiom Rext_total: ∀ r: extR, r = p_infty ∨ r = m_infty ∨ ∃ x, r = Fin x;

Axiom real: extR -> ℝ;
Axiom real_fin: ∀ r: ℝ, real (Fin r) = r;

Definition is_Fin := λ r: extR, Fin (real r) = r;

Axiom extR_lt: ∀ a b: ℝ, a < b -> Fin a < Fin b; 
Axiom extR_le: ∀ a b: ℝ, a ≤ b -> Fin a ≤ Fin b;
Axiom p_infty_ge: ∀ r: extR, r ≤ p_infty;
Axiom m_infty_le: ∀ r: extR, m_infty ≤ r;

Todo extRtotal_order: ∀ x a: extR, x = a ∨ x < a ∨ x > a;

Axiom Fin_plus: ∀ x y: ℝ, Fin x + Fin y = Fin (x + y);
Axiom p_infty_plus: ∀ r: extR, ~ r = m_infty -> r + p_infty = p_infty;
Axiom m_infty_plus: ∀ r: extR, ~ r = p_infty -> r + m_infty = m_infty;
Axiom extR_comm: ∀ x y: extR, x + y = y + x;

Axiom Fin_minus: ∀ x y: ℝ, Fin x - Fin y = Fin (x - y);
Axiom p_infty_minus: ∀ r: extR, ~ r = p_infty -> r - p_infty = m_infty;
Axiom m_infty_minus: ∀ r: extR, ~ r = m_infty -> r - m_infty = p_infty;


Axiom Fin_mult: ∀ x y: ℝ, Fin x * Fin y = Fin (x * y);
Axiom p_infty_mult: p_infty * p_infty = p_infty;
Axiom m_infty_mult: m_infty * m_infty = p_infty;
Axiom p_infty_mult_Fin_pos: ∀ r: ℝ, r > 0. -> Fin r * p_infty = p_infty;
Axiom p_infty_mult_Fin_neg: ∀ r: ℝ, r < 0. -> Fin r * p_infty = m_infty;
Axiom m_infty_mult_Fin_pos: ∀ r: ℝ, r > 0. -> Fin r * m_infty = m_infty;
Axiom m_infty_mult_Fin_neg: ∀ r: ℝ, r < 0. -> Fin r * m_infty = p_infty;

Axiom Fin_div: ∀ x y: ℝ, (Fin x) / (Fin y) = x / y;
Axiom p_infty_div: ∀ r: ℝ, (Fin r) / p_infty = 0.;
Axiom m_infty_div: ∀ r: ℝ, (Fin r) / m_infty = 0.;

Definition is_cut := λ S: set ℝ, (∀ a b, a < b -> b ∈ S -> a ∈ S) ∧ (∀ a, a ∈ S -> ∃ b, a < b ∧ b ∈ S);