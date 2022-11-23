Import /Set;
Import /Tuples;

Axiom dGraph: U -> U;
Axiom #1 dvertex_set: ∀ A: U, dGraph A -> set A;
Axiom #1 dedge_set: ∀ A: U, dGraph A -> set (A ∧ A);
Axiom #1 well_founded_rel: ∀ A: U, dGraph A -> U;
