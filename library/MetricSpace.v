Definition Metric := λ X:U, λ d: X -> X -> ℝ, ∀ x y z: X, d x x = 0. ∧ d x y ≥ 0. ∧ (d x y = 0. -> x = y) ∧ d x y = d y x ∧ d x z ≤ d x y + d y z;

Todo Metric_unfold: ∀ X: U, ∀ d: X -> X -> ℝ, Metric X d -> ( ∀ x y: X, d x y ≥ 0. ∧ (d x y = 0. -> x = y) ∧ (x = y -> d x y = 0.)) ∧ (∀ x y, d x y = d y x) ∧ (∀ x y z, d x z ≤ d x y + d y z);
Todo Metric_fold: ∀ X: U, ∀ d: X -> X -> ℝ, (∀ x y z: X, d x x = 0. ∧ d x y ≥ 0. ∧ (d x y = 0. -> x = y) ∧ d x y = d y x ∧ d x z ≤ d x y + d y z) -> Metric X d;
Suggest hyp default chain (apply Metric_unfold in $n) (destruct $n with (and_ind ? ?) to ($n_no_neg $n)) (destruct $n with (and_ind ? ?) to  ($n_sym $n_triangle_ineq)) with label Metric X d => (∀ x y: X, d x y ≥ 0. ∧ (d x y = 0. -> x = y) ) ∧ (∀ x y, d x y = d y x) ∧ (∀ x y z, d x z ≤ d x y + d y z);
Suggest goal default apply Metric_fold with label Metric X d => ∀ x y z: X, d x y ≥ 0. ∧ (d x y = 0. -> x = y) ∧ d x y = d y x ∧ d x z ≤ d x y + d y z;

Definition #1 ball := λ X: U, λ d: X → X → ℝ, λ u: X, λ r: ℝ, {x | d u x < r};

Definition #1 open_set := λ X: U, λ d: X → X → ℝ, λ U: set X, ∀ x: X, x ∈ U -> ∃ r: ℝ, r > 0. ∧ (∀ y: X, d x y < r -> y ∈ U);
Definition #1 is_lim_point := λ X: U, λ d: X → X → ℝ, λ E: set X, λ x: X, ∀ e: ℝ, e > 0. -> ∃ y, y ∈ E ∧ ~ y = x ∧ d x y < e;
Definition #1 close_set := λ X: U, λ d: X → X → ℝ, λ E: set X, ∀ x, is_lim_point d E x -> x ∈ E;

Todo open_set_unfold: ∀ X: U, ∀ d: X → X → ℝ, ∀ U: set X, open_set d U -> ∀ x: X, x ∈ U -> ∃ r: ℝ, r > 0. ∧ (∀ y: X, d x y < r -> y ∈ U);
Todo open_set_fold: ∀ X: U, ∀ d: X → X → ℝ, ∀ U: set X, (∀ x: X, x ∈ U -> ∃ r: ℝ, r > 0. ∧ (∀ y: X, d x y < r -> y ∈ U)) -> open_set d U;
Suggest hyp default apply open_set_unfold in $n with label open_set d U => ∀ x: X, x ∈ U -> ∃ r: ℝ, r > 0. ∧ (∀ y: X, d x y < r -> y ∈ U);
Suggest goal default apply open_set_fold with label open_set d U => ∀ x: X, x ∈ U -> ∃ r: ℝ, r > 0. ∧ (∀ y: X, d x y < r -> y ∈ U);

Todo is_lim_point_unfold: ∀ X: U, ∀ d: X → X → ℝ, ∀ E: set X, ∀ x: X, is_lim_point d E x -> ∀ e: ℝ, e > 0. -> ∃ y, y ∈ E ∧ ~ y = x ∧ d x y < e;
Todo is_lim_point_fold: ∀ X: U, ∀ d: X → X → ℝ, ∀ E: set X, ∀ x: X, (∀ e: ℝ, e > 0. -> ∃ y, y ∈ E ∧ ~ y = x ∧ d x y < e) -> is_lim_point d E x;
Suggest hyp default apply is_lim_point_unfold in $n with label is_lim_point d E x => ∀ e: ℝ, e > 0. -> ∃ y, y ∈ E ∧ ~ y = x ∧ d x y < e;
Suggest goal default apply is_lim_point_fold with label is_lim_point d E x => ∀ e: ℝ, e > 0. -> ∃ y, y ∈ E ∧ ~ y = x ∧ d x y < e;

Todo close_set_unfold: ∀ X: U, ∀ d: X → X → ℝ, ∀ E: set X, close_set d E -> ∀ x, is_lim_point d E x -> x ∈ E;
Todo close_set_fold: ∀ X: U, ∀ d: X → X → ℝ, ∀ E: set X, (∀ x, is_lim_point d E x -> x ∈ E) -> close_set d E;
Suggest hyp default apply close_set_unfold in $n with label close_set d E => ∀ x, is_lim_point d E x -> x ∈ E;
Suggest goal default apply close_set_fold with label close_set d E => ∀ x, is_lim_point d E x -> x ∈ E;

Import /Set;

Todo close_set_to_open_set: ∀ X: U, ∀ d: X → X → ℝ, ∀ E: set X, open_set d (complement E) -> close_set d E;
Todo open_set_to_close_set: ∀ X: U, ∀ d: X → X → ℝ, ∀ E: set X, close_set d E -> open_set d (complement E);
Suggest hyp apply open_set_to_close_set in $n with label close_set d E => open_set d (complement E);
Suggest goal apply close_set_to_open_set with label close_set d E => open_set d (complement E);

Definition #1 Int := λ X: U, λ d: X → X → ℝ, λ E: set X, {x | ∃ r: ℝ, r > 0. ∧ (∀ y: X, d x y < r -> y ∈ E) };
Definition #1 Cl := λ X: U, λ d: X → X → ℝ, λ E: set X, {x | x ∈ E ∨ is_lim_point d E x };

Todo Int_unfold: ∀ X: U, ∀ d: X → X → ℝ, ∀ E: set X, ∀ x: X, x ∈ Int d E -> ∃ r: ℝ, r > 0. ∧ (∀ y: X, d x y < r -> y ∈ E);
Todo Int_fold: ∀ X: U, ∀ d: X → X → ℝ, ∀ E: set X, ∀ x: X, (∃ r: ℝ, r > 0. ∧ (∀ y: X, d x y < r -> y ∈ E)) -> x ∈ Int d E;
Suggest hyp default apply Int_unfold in $n with label x ∈ Int d E => ∃ r: ℝ, r > 0. ∧ (∀ y: X, d x y < r -> y ∈ E);
Suggest goal default apply Int_fold with label x ∈ Int d E => ∃ r: ℝ, r > 0. ∧ (∀ y: X, d x y < r -> y ∈ E);

Todo Cl_unfold: ∀ X: U, ∀ d: X → X → ℝ, ∀ E: set X, ∀ x: X, x ∈ Cl d E -> x ∈ E ∨ is_lim_point d E x;
Todo Cl_fold: ∀ X: U, ∀ d: X → X → ℝ, ∀ E: set X, ∀ x: X, x ∈ E ∨ is_lim_point d E x -> x ∈ Cl d E;
Suggest hyp default apply Cl_unfold in $n with label x ∈ Cl d E => x ∈ E ∨ is_lim_point d E x;
Suggest goal default apply Cl_fold with label x ∈ Cl d E => x ∈ E ∨ is_lim_point d E x;

Theorem Int_incl: ∀ X: Universe, ∀ d: X → X → ℝ, Metric X d → ∀ E: set X, Int d E ⊆ E;
Proof;    
    intros;
    apply included_fold ;
    intros;
    apply Int_unfold in H0 ;
    destruct H0 with (ex_ind ? ?) to (ق ق_property);
    destruct ق_property with (and_ind ? ?) to (ق_property_l ق_property_r) ;
    add_hyp ق_property_r_ex := (ق_property_r (a));
    chain (apply Metric_unfold in H) (destruct H with (and_ind ? ?) to (H_no_neg H)) (destruct H with (and_ind ? ?) to  (H_sym H_triangle_ineq)) ;
    add_hyp H_no_neg_ex := (H_no_neg (a));
    add_hyp H_no_neg_ex_ex := (H_no_neg_ex (a));
    z3;
Qed;