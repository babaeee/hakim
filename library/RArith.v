
Axiom plus_comm: forall x y, rplus x y = rplus y x.
Axiom plus_assoc: forall x y z, rplus (rplus x y) z = rplus x (rplus y z).
Axiom plus_zero: forall x,  rplus x (0 / 1) = x.
Axiom plus_invers: forall x, exits y, rplus x y = (0 / 1).
