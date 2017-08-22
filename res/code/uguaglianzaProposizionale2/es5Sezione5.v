From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

(* Definizione di MartinLof come sopra *)

Definition pf_p (x: unit) : eq x tt.
Proof.
case: x.
apply: erefl.
Defined.

Definition pf_m (x: unit) : MartinLof.eq unit x tt.
Proof.
case: x.
apply: MartinLof.refl unit tt.
Defined.
