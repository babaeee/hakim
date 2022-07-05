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


    
