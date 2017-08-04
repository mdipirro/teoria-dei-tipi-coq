From mathcomp Require Import ssreflect.

Definition T (a: Prop) := Type.

(* Implicazione *)

Definition implicazione (a b : Prop) : Prop := forall x: T a, b.

Definition implicazione_el_a : forall a b g g' d: Prop,
(implicazione ((g /\ (implicazione a b)) /\ g') d) -> Prop.
Proof.
move=> a b g g' d hp.
apply (implicazione g a).
Defined.

Definition implicazione_el_delta : forall a b g g' d: Prop,
(implicazione ((g /\ (implicazione a b)) /\ g') d) -> Prop.
Proof.
move=> a b g g' d hp.
apply (implicazione (b /\ g') d).
Defined.

(* Congiunzione *)
Definition congiunzione (a b: Prop) : Prop := forall p: Prop, 
  implicazione (forall x: T a, forall y: T b, p) p.

(* Disgiunzione *)
Definition disgiunzione (a b: Prop) : Prop := forall p: Prop,
  implicazione (congiunzione (a -> p) (b -> p)) p.