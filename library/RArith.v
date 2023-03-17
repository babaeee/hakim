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

Definition bounded_abow := λ E: set ℝ, (∃ x, upper_bound E x);

Todo bounded_abow_unfold: ∀ E: set ℝ, bounded_abow E -> (∃ x, upper_bound E x);
Todo bounded_abow_fold: ∀ E: set ℝ, (∃ x, upper_bound E x) -> bounded_abow E;
Suggest hyp default apply bounded_abow_unfold in $n with label bounded_abow E => (∃ x, upper_bound E x);
Suggest goal default apply bounded_abow_fold with label bounded_abow E => (∃ x, upper_bound E x);

Definition lower_bound := λ E: set ℝ, λ x, ∀ y, y ∈ E -> x ≤ y;

Todo lower_bound_unfold: ∀ E: set ℝ, ∀ x, lower_bound E x -> ∀ y, y ∈ E -> x ≤ y;
Todo lower_bound_fold: ∀ E: set ℝ, ∀ x, (∀ y, y ∈ E -> x ≤ y) -> lower_bound E x;
Suggest hyp default apply lower_bound_unfold in $n with label lower_bound E x => ∀ y, y ∈ E -> x ≤ y;
Suggest goal default apply lower_bound_fold with label lower_bound E x => ∀ y, y ∈ E -> x ≤ y;

Definition lub := λ E: set ℝ, λ x, upper_bound E x ∧ (∀ y, upper_bound E y -> x ≤ y);

Todo lub_unfold: ∀ E: set ℝ, ∀ x, lub E x -> upper_bound E x ∧ (∀ y, upper_bound E y -> x ≤ y);
Todo lub_fold: ∀ E: set ℝ, ∀ x, upper_bound E x -> (∀ y, upper_bound E y -> x ≤ y) -> lub E x;
Suggest hyp default apply lub_unfold in $n with label lub E x => upper_bound E x ∧ (∀ y, upper_bound E y -> x ≤ y);
Suggest goal default apply lub_fold with label lub E x => upper_bound E x ∧ (∀ y, upper_bound E y -> x ≤ y);

Definition glb := λ E: set ℝ, λ x, lower_bound E x ∧ (∀ y, lower_bound E y -> y ≤ x);

Todo glb_unfold: ∀ E: set ℝ, ∀ x, glb E x -> lower_bound E x ∧ (∀ y, lower_bound E y -> y ≤ x);
Todo glb_fold: ∀ E: set ℝ, ∀ x, lower_bound E x -> (∀ y, lower_bound E y -> y ≤ x) -> glb E x;
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

Definition is_cut := λ S: set ℝ, ~ (∀ a, a ∈ ℚ -> a ∈ S) ∧ (∃ a, a ∈ S) ∧ (∀ a, a ∈ S -> a ∈ ℚ) ∧ (∀ a b, a ∈ ℚ -> a < b -> b ∈ S -> a ∈ S) ∧ (∀ a, a ∈ S -> ∃ b, a < b ∧ b ∈ S);

Todo is_cut_unfold: ∀ S: set ℝ, is_cut S -> ~ (∀ a, a ∈ ℚ -> a ∈ S) ∧ (∃ a, a ∈ S) ∧ (∀ a, a ∈ S -> a ∈ ℚ) ∧ (∀ a b, a ∈ ℚ -> a < b -> b ∈ S -> a ∈ S) ∧ (∀ a, a ∈ S -> ∃ b, a < b ∧ b ∈ S);
Suggest hyp default apply is_cut_unfold in $n with label is_cut S => ~ S = ℚ ∧ ~ S = {} ∧ S ⊆ ℚ ∧ (∀ a b, a ∈ ℚ -> a < b -> b ∈ S -> a ∈ S) ∧ (∀ a, a ∈ S -> ∃ b, a < b ∧ b ∈ S);
Todo is_cut_fold: ∀ S: set ℝ, (~ (∀ a, a ∈ ℚ -> a ∈ S)) -> (∃ a, a ∈ S) -> (∀ a, a ∈ S -> a ∈ ℚ) -> (∀ a b, a ∈ ℚ -> a < b -> b ∈ S -> a ∈ S) -> (∀ a, a ∈ S -> ∃ b, a < b ∧ b ∈ S) -> is_cut S;
Suggest goal default apply is_cut_fold with label is_cut S => ~ S = ℚ ∧ ~ S = {} ∧ S ⊆ ℚ ∧ (∀ a b, a ∈ ℚ -> a < b -> b ∈ S -> a ∈ S) ∧ (∀ a, a ∈ S -> ∃ b, a < b ∧ b ∈ S);

Axiom cut: ℝ -> set ℝ;
Axiom r_is_cut: ∀ r: ℝ, is_cut (cut r);
Suggest goal apply r_is_cut with label Trivial;
Axiom le_cut: ∀ a b, cut a ⊆ cut b -> a ≤ b;
Suggest goal default apply le_cut with label a ≤ b => cut a ⊆ cut b;
Axiom cut_le: ∀ a b, a ≤ b -> cut a ⊆ cut b;
Suggest hyp default apply cut_le in $n with label a ≤ b => cut a ⊆ cut b;

Todo cut_eq: ∀ a b, cut a = cut b -> a = b;

Todo in_cut_prop: ∀ r: ℝ, ∀ b, b ∈ cut r -> b ∈ ℚ ∧ (∀ a, a ∈ ℚ -> a < b -> a ∈ cut r) ∧ (∃ c, b < c ∧ c ∈ ℚ ∧ c ∈ cut r);
Suggest hyp default apply in_cut_prop in $n with label b ∈ cut r => b ∈ ℚ ∧ (∀ a, a ∈ ℚ -> a < b -> a ∈ cut r) ∧ (∃ c, b < c ∧ c ∈ cut r);

Axiom rcut: set ℝ → ℝ;
Axiom rcut_of_cut: ∀ r: ℝ, rcut (cut r) = r;
Axiom cut_have_rcut: ∀ S: set ℝ, is_cut S -> ∃ r: ℝ, S = cut r;
Todo cut_of_rcut: ∀ S: set ℝ, is_cut S -> cut (rcut S) = S;

Theorem lub_prop: ∀ E: set ℝ, ∀ not_empty: (∃ x, x ∈ E), bounded_abow E -> ∃ a, lub E a;
Proof;
    intros;
    add_from_lib cut_have_rcut;
    add_hyp cut_have_rcut_ex := (cut_have_rcut ({ q | ∃ a, a ∈ E ∧ q ∈ cut a }));
    Seq (add_hyp (⁨is_cut { q: ℝ | ∃ a: ℝ, a ∈ E ∧ q ∈ cut a }⁩)) (remove_hyp cut_have_rcut_ex) (Switch 1) (add_hyp cut_have_rcut_ex_o := (cut_have_rcut_ex H0)) (remove_hyp H0) (remove_hyp cut_have_rcut_ex);
    destruct cut_have_rcut_ex_o with (ex_ind ? ?) to (sup sup_property);
    apply (ex_intro ? ? (sup));
    apply lub_fold;
    intros;
    apply le_cut;
    apply included_fold;
    intros;
    replace #1 (cut sup) with ({ q: ℝ | ∃ a0: ℝ, a0 ∈ E ∧ q ∈ cut a0 }) in H1;
    auto_set;
    apply set_from_func_unfold in H1;
    destruct H1 with (ex_ind ? ?) to (a0 a0_property);
    apply upper_bound_unfold in H0;
    add_hyp H0_ex := (H0 (a0));
    Seq (add_hyp (⁨a0 ∈ E⁩)) (remove_hyp H0_ex) (Switch 1) (add_hyp H0_ex_o := (H0_ex H1)) (remove_hyp H1) (remove_hyp H0_ex);
    apply cut_le in H0_ex_o;
    auto_set;
    assumption;
    apply upper_bound_fold;
    intros;
    apply le_cut;
    apply eq_sym in sup_property;
    rewrite sup_property;
    apply included_fold;
    intros;
    apply set_from_func_fold;
    apply (ex_intro ? ? (y));
    assumption;
    apply is_cut_fold;
    intros;
    apply set_from_func_unfold in H0;
    destruct H0 with (ex_ind ? ?) to (a0 a0_property);
    destruct a0_property with (and_ind ? ?) to (a0_property_l a0_property_r);
    add_hyp (is_cut (cut a0));
    apply r_is_cut;
    apply is_cut_unfold in H0;
    destruct H0 with (and_ind ? ?) to (H0_l H0_r);
    destruct H0_r with (and_ind ? ?) to (H0_r_l H0_r_r);
    destruct H0_r_r with (and_ind ? ?) to (H0_r_r_l H0_r_r_r);
    destruct H0_r_r_r with (and_ind ? ?) to (H0_r_r_r_l H0_r_r_r_r);
    add_hyp H0_r_r_r_r_ex := (H0_r_r_r_r (a));
    Seq (add_hyp (⁨a ∈ cut a0⁩)) (remove_hyp H0_r_r_r_r_ex) (Switch 1) (add_hyp H0_r_r_r_r_ex_o := (H0_r_r_r_r_ex H0)) (remove_hyp H0) (remove_hyp H0_r_r_r_r_ex);
    destruct H0_r_r_r_r_ex_o with (ex_ind ? ?) to (b b_property);
    apply (ex_intro ? ? (b));
    apply and_intro;
    apply set_from_func_fold;
    apply (ex_intro ? ? (a0));
    assumption;
    assumption;
    assumption;
    intros;
    apply set_from_func_fold;
    apply set_from_func_unfold in H2;
    destruct H2 with (ex_ind ? ?) to (a0 a0_property);
    destruct a0_property with (and_ind ? ?) to (a0_property_l a0_property_r);
    add_hyp (is_cut (cut a0));
    apply r_is_cut;
    apply is_cut_unfold in H2;
    destruct H2 with (and_ind ? ?) to (H2_l H2_r);
    destruct H2_r with (and_ind ? ?) to (H2_r_l H2_r_r);
    destruct H2_r_r with (and_ind ? ?) to (H2_r_r_l H2_r_r_r);
    destruct H2_r_r_r with (and_ind ? ?) to (H2_r_r_r_l H2_r_r_r_r);
    add_hyp H2_r_r_r_l_ex := (H2_r_r_r_l (a));
    add_hyp H2_r_r_r_l_ex_ex := (H2_r_r_r_l_ex (b));
    Seq (add_hyp (⁨a ∈ ℚ⁩)) (remove_hyp H2_r_r_r_l_ex_ex) (Switch 1) (add_hyp H2_r_r_r_l_ex_ex_o := (H2_r_r_r_l_ex_ex H2)) (remove_hyp H2) (remove_hyp H2_r_r_r_l_ex_ex);
    Seq (add_hyp (⁨a < b⁩)) (remove_hyp H2_r_r_r_l_ex_ex_o) (Switch 1) (add_hyp H2_r_r_r_l_ex_ex_o_o := (H2_r_r_r_l_ex_ex_o H2)) (remove_hyp H2) (remove_hyp H2_r_r_r_l_ex_ex_o);
    Seq (add_hyp (⁨b ∈ cut a0⁩)) (remove_hyp H2_r_r_r_l_ex_ex_o_o) (Switch 1) (add_hyp H2_r_r_r_l_ex_ex_o_o_o := (H2_r_r_r_l_ex_ex_o_o H2)) (remove_hyp H2) (remove_hyp H2_r_r_r_l_ex_ex_o_o);
    apply (ex_intro ? ? (a0));
    assumption;
    assumption;
    assumption;
    assumption;
    intros;
    apply set_from_func_unfold in H0;
    destruct H0 with (ex_ind ? ?) to (a0 a0_property);
    destruct a0_property with (and_ind ? ?) to (a0_property_l a0_property_r);
    apply in_cut_prop in a0_property_r ;
    assumption;
    destruct not_empty with (ex_ind ? ?) to (x x_property);
    add_hyp (∃ t, t ∈ cut x);
    add_hyp (is_cut (cut x));
    apply r_is_cut ;
    apply is_cut_unfold in H0 ;
    assumption;
    destruct H0 with (ex_ind ? ?) to (t t_property);
    apply (ex_intro ? ? (t));
    apply set_from_func_fold ;
    apply (ex_intro ? ? (x));
    assumption;
    apply bounded_abow_unfold in H ;
    destruct H with (ex_ind ? ?) to (x x_property);
    add_hyp ({ q: ℝ | ∃ a0: ℝ, a0 ∈ E ∧ q ∈ cut a0 } ⊆ cut x);
    apply included_fold ;
    intros;
    apply set_from_func_unfold in H ;
    destruct H with (ex_ind ? ?) to (a0 a0_property);
    apply upper_bound_unfold in x_property ;
    add_hyp x_property_ex := (x_property (a0));
    Seq (add_hyp (⁨a0 ∈ E⁩)) (remove_hyp x_property_ex) (Switch 1) (add_hyp x_property_ex_o := (x_property_ex H)) (remove_hyp H) (remove_hyp x_property_ex) ;
    apply cut_le in x_property_ex_o ;
    auto_set;
    assumption;
    intros;
    add_hyp (is_cut (cut x));
    apply r_is_cut ;
    apply is_cut_unfold in H1 ;
    destruct H1 with (and_ind ? ?) to (H1_l H1_r) ;
    apply not_forall_imply_exists in H1_l ;
    destruct H1_l with (ex_ind ? ?) to (x0 x0_property);
    apply not_forall_imply_exists in x0_property ;
    destruct x0_property with (ex_ind ? ?) to (G G_property);
    add_hyp H0_ex := (H0 (x0));
    auto_set;
Qed;

Axiom cut_plus: ∀ A B: set ℝ, is_cut A -> is_cut B -> A + B = {c | ∃ a b, c = a + b ∧ a ∈ A ∧ b ∈ B };
Todo cut_plus_is_cut: ∀ A B: set ℝ, is_cut A -> is_cut B -> is_cut (A + B);
Axiom plus_cut: ∀ a b: ℝ, cut (a + b) = cut a + cut b;
Axiom cut_0: cut 0. = {q | q ∈ ℚ ∧ q < 0.};
Axiom cut_neg: ∀ A: set ℝ, is_cut A -> - A = {p | p ∈ ℚ ∧ ∃ r, r ∈ ℚ ∧ r > 0. ∧ ~ (-p) - r ∈ A};
Axiom cut_neg_is_cut: ∀ A: set ℝ, is_cut A -> is_cut (-A);
Axiom cut_minus: ∀ A B: set ℝ, is_cut A -> is_cut B -> A - B = A + (-B);
Todo cut_minus_0: ∀ r: ℝ, cut r - (cut r) = cut 0.;
Axiom neg_cut: ∀ a: ℝ, cut (- a) = - cut a;
Axiom minus_cut: ∀ a b: ℝ, cut (a - b) = cut a - cut b;

Axiom cut_mult_pos: ∀ A B: set ℝ, is_cut A -> is_cut B -> cut 0. ⊆ A -> ~ A = cut 0. -> cut 0. ⊆ B -> ~ B = cut 0. -> A * B  = {p | ∃ a b, p ∈ ℚ ∧ p ≤ a * b ∧ a > 0. ∧ b > 0. ∧ a ∈ A ∧ b ∈ B };
Todo cut_mult_pos_is_cut: ∀ A B: set ℝ, is_cut A -> is_cut B -> cut 0. ⊆ A -> ~ A = cut 0. -> cut 0. ⊆ B -> ~ B = cut 0. -> is_cut (A * B);
Axiom Rmult_l_0: ∀ r: ℝ, cut r * cut 0. = cut 0.;
Axiom Rmult_r_0: ∀ r: ℝ, cut 0.* cut r = cut 0.;
Axiom mult_cut_pos_pos: ∀ a b: ℝ, a > 0. -> b > 0. -> cut a * cut b = cut a * cut b;
Axiom mult_cut_pos_neg: ∀ a b: ℝ, a > 0. -> b < 0. -> cut a * cut b =  - (cut a * (- cut b));
Axiom mult_cut_neg_pos: ∀ a b: ℝ, a < 0. -> b > 0. -> cut a * cut b =  - ((- cut a) * cut b);
Axiom mult_cut_neg_neg: ∀ a b: ℝ, a < 0. -> b < 0. -> cut a * cut b =  ((- cut a) * (- cut b));

Todo cut_mult_plus: ∀ A B C: set ℝ, is_cut A -> is_cut B -> is_cut C -> A * (B + C) = A * B + A * C;

Axiom cut_of_q: ∀ q, q ∈ ℚ -> cut q = { x | x ∈ ℚ ∧ x < q };

Axiom sup: set ℝ -> ℝ;
Axiom sup_lub: ∀ E: set ℝ, (∃ x, x ∈ E) -> bounded_abow E -> lub E (sup E);

Todo lub_eq_sup: ∀ A: set ℝ, ∀ s, lub A s -> sup A = s;
Suggest goal apply lub_eq_sup with label sup A = s => lub A s;
Todo eq_sup_lub: ∀ A: set ℝ, ∀ s, sup A = s -> lub A s;
Suggest hyp apply eq_sup_lub in $n with label sup A = s => lub A s;