From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Lemma phi_y {A}:
  forall (phi: A -> Prop),
    (exists y: A, phi y).
Proof.
Admitted.

Lemma existence_property_under_a_context {A}: 
  forall (phi: A -> Prop), (exists y: A, phi y)
    -> (exists pf, phi pf).
Proof.
move=> phi lemma.
apply phi_y.
Qed.
