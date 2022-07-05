Import /Graph.
Import /Induction.

Axiom #1 win_f: ∀ A: U, A -> dGraph A -> U.
Axiom win_f_def: ∀ A: U, ∀ G: dGraph A, well_founded_rel G -> ∀ a b: A, (a, b) ∈ dedge_set G -> ~ win_f b G -> win_f a G.
Axiom lose_f_def: ∀ A: U, ∀ G: dGraph A, well_founded_rel G
    -> ∀ a: A, (∀ b: A, (a, b) ∈ dedge_set G -> win_f b G) -> ~ win_f a G.

Theorem stupid_game_dec2:
    ∀ stupid_game: dGraph ?,
    well_founded_rel stupid_game
    -> dedge_set stupid_game = { x | ∃ k, 0 ≤ k ∧ (x = (k + 1, k) ∨ x = (k + 2, k)) }
    -> ∀ n, 0 ≤ n -> ~ win_f (3*n) stupid_game ∧ win_f (3*n + 1) stupid_game ∧ win_f (3*n+2) stupid_game.
Proof.
    intros G wf ed.
    apply z_induction_simple.
    Switch 1.
    add_hyp (~ win_f 0 G).
    apply lose_f_def.
    rewrite ed.
    intros.
    apply set_from_func_unfold in H.
    destruct H with (ex_ind ? ?) to (H_value H_proof).
    destruct H_proof with (and_ind ? ?) to (H_proof_l H_proof_r).
    destruct H_proof_r with (or_ind ? ?).
    apply pair_eq in H_proof_r.
    lia.
    apply pair_eq in H_proof_r.
    lia.
    assumption.
    apply and_intro.
    apply and_intro.
    apply (⁨win_f_def ?0 ?2 ?4 ?6 0 ?10 ?12⁩).
    assumption.
    rewrite ed.
    apply set_from_func_fold.
    apply (ex_intro ? ? (0)).
    lia.
    assumption.
    apply (⁨win_f_def ?0 ?2 ?4 ?6 0 ?10 ?12⁩).
    assumption.
    rewrite ed.
    apply set_from_func_fold.
    apply (ex_intro ? ? (0)).
    lia.
    assumption.
    replace #1 ((3 * 0)) with (0).
    lia.
    assumption.
    intros.
    add_hyp (~ win_f (3 * (n + 1)) G).
    apply lose_f_def.
    rewrite ed.
    intros.
    apply set_from_func_unfold in H1.
    destruct H1 with (ex_ind ? ?) to (k k_property).
    destruct k_property with (and_ind ? ?) to (k_property_l k_property_r).
    destruct k_property_r with (or_ind ? ?).
    apply pair_eq in k_property_r.
    destruct k_property_r with (and_ind ? ?) to (k_property_r_l k_property_r_r).
    replace #1 (b) with (3*n+1).
    lia.
    assumption.
    replace #1 (b) with (3*n+2).
    apply pair_eq in k_property_r.
    lia.
    assumption.
    assumption.
    apply and_intro.
    apply and_intro.
    apply (⁨win_f_def ?0 ?2 ?4 ?6 (3 * (n + 1)) ?10 ?12⁩).
    assumption.
    rewrite ed.
    apply set_from_func_fold.
    apply (ex_intro ? ? (3*(n+1))).
    lia.
    assumption.
    apply (⁨win_f_def ?0 ?2 ?4 ?6 (3 * (n + 1)) ?10 ?12⁩).
    assumption.
    rewrite ed.
    apply set_from_func_fold.
    apply (ex_intro ? ? (3*(n+1))).
    lia.
    assumption.
    assumption.
Qed.

Theorem nim_2_bag:
    ∀ nim2: dGraph (ℤ ∧ ℤ),
    well_founded_rel nim2
    -> dedge_set nim2 = { e | ∃ a b c, 0 ≤ a ∧ 0 ≤ b ∧ b < c ∧ (e = ((a, c), (a, b)) ∨ e = ((c, a), (b, a))) }
    -> ∀ a b, 0 ≤ a -> 0 ≤ b -> ~ win_f (a, b) nim2 <-> a = b.
Proof.
    intros nim2 wf edges.
    intros a b H.
    revert b.
    revert H.
    revert a.
    apply z_induction_strong.
    intros.
    add_hyp (∀ k, 0 ≤ k -> k < n -> win_f (n, k) nim2).
    intros.
    apply (⁨win_f_def ?0 ?2 ?4 ?6 (k, k) ?10 ?12⁩).
    add_hyp H0_ex := (H0 (k)).
    Seq (add_hyp (⁨0 ≤ k⁩)) (remove_hyp H0_ex) (Switch 1) (add_hyp H0_ex_o := (H0_ex H4)) (remove_hyp H4) (remove_hyp H0_ex) .
    Seq (add_hyp (⁨k < n⁩)) (remove_hyp H0_ex_o) (Switch 1) (add_hyp H0_ex_o_o := (H0_ex_o H4)) (remove_hyp H4) (remove_hyp H0_ex_o) .
    add_hyp H0_ex_o_o_ex := (H0_ex_o_o (k)).
    Seq (add_hyp (⁨0 ≤ k⁩)) (remove_hyp H0_ex_o_o_ex) (Switch 1) (add_hyp H0_ex_o_o_ex_o := (H0_ex_o_o_ex H4)) (remove_hyp H4) (remove_hyp H0_ex_o_o_ex) .
    destruct H0_ex_o_o_ex_o with (and_ind ? ?) to (H0_ex_o_o_ex_o_l H0_ex_o_o_ex_o_r).
    apply H0_ex_o_o_ex_o_r.
    auto_list.
    assumption.
    assumption.
    assumption.
    rewrite edges.
    apply set_from_func_fold.
    apply (ex_intro ? ? (k)).
    apply (ex_intro ? ? (k)).
    apply (ex_intro ? ? (n)).
    lia.
    assumption.
    add_hyp (~ win_f (n, n) nim2).
    apply lose_f_def.
    rewrite edges.
    intros.
    apply set_from_func_unfold in H3.
    destruct H3 with (ex_ind ? ?) to (p p_property).
    destruct p_property with (ex_ind ? ?) to (q q_property).
    destruct q_property with (ex_ind ? ?) to (r r_property).
    destruct r_property with (and_ind ? ?) to (r_property_l r_property_r).
    destruct r_property_r with (and_ind ? ?) to (r_property_r_l r_property_r_r).
    destruct r_property_r_r with (and_ind ? ?) to (r_property_r_r_l r_property_r_r_r).
    destruct r_property_r_r_r with (or_ind ? ?).
    apply pair_eq in r_property_r_r_r.
    destruct r_property_r_r_r with (and_ind ? ?) to (r_property_r_r_r_l r_property_r_r_r_r).
    apply pair_eq in r_property_r_r_r_l.
    destruct r_property_r_r_r_l with (and_ind ? ?) to (r_property_r_r_r_l_l r_property_r_r_r_l_r).
    rewrite r_property_r_r_r_r.
    apply eq_sym in r_property_r_r_r_l_r.
    rewrite r_property_r_r_r_l_r.
    add_hyp H0_ex := (H0 (q)).
    Seq (add_hyp (⁨0 ≤ q⁩)) (remove_hyp H0_ex) (Switch 1) (add_hyp H0_ex_o := (H0_ex H3)) (remove_hyp H3) (remove_hyp H0_ex) .
    Seq (add_hyp (⁨q < n⁩)) (remove_hyp H0_ex_o) (Switch 1) (add_hyp H0_ex_o_o := (H0_ex_o H3)) (remove_hyp H3) (remove_hyp H0_ex_o) .
    add_hyp H0_ex_o_o_ex := (H0_ex_o_o (n)).
    Seq (add_hyp (⁨0 ≤ n⁩)) (remove_hyp H0_ex_o_o_ex) (Switch 1) (add_hyp H0_ex_o_o_ex_o := (H0_ex_o_o_ex H3)) (remove_hyp H3) (remove_hyp H0_ex_o_o_ex) .
    destruct H0_ex_o_o_ex_o with (and_ind ? ?) to (H0_ex_o_o_ex_o_l H0_ex_o_o_ex_o_r).
    apply NNPP.
    intros.
    apply H0_ex_o_o_ex_o_l in H3.
    lia.
    assumption.
    lia.
    assumption.
    apply pair_eq in r_property_r_r_r.
    destruct r_property_r_r_r with (and_ind ? ?) to (r_property_r_r_r_l r_property_r_r_r_r).
    apply pair_eq in r_property_r_r_r_l.
    destruct r_property_r_r_r_l with (and_ind ? ?) to (r_property_r_r_r_l_l r_property_r_r_r_l_r).
    rewrite r_property_r_r_r_r.
    apply eq_sym in r_property_r_r_r_l_l.
    rewrite r_property_r_r_r_l_l.
    apply H2.
    lia.
    assumption.
    assumption.
    apply and_intro.
    intros n_eq_b.
    apply eq_sym in n_eq_b.
    rewrite n_eq_b.
    assumption.
    intros.
    apply NNPP.
    intros.
    add_hyp (n < b ∨ n > b).
    lia.
    destruct H6 with (or_ind ? ?).
    apply H4.
    apply H2.
    assumption.
    assumption.
    apply H4.
    apply (⁨win_f_def ?0 ?2 ?4 ?6 (n, n) ?10 ?12⁩).
    assumption.
    rewrite edges.
    apply set_from_func_fold.
    apply (ex_intro ? ? (n)).
    apply (ex_intro ? ? (n)).
    apply (ex_intro ? ? (b)).
    lia.
    assumption.
Qed.
    
