From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

(* Definizione di MartinLof come in precedenza *)

Fixpoint add1 (x: nat) (y: nat) : nat :=
match x with
  | 0 => y
  | S n => S (add1 n y)
end.

Fixpoint add2 (x: nat) (y: nat) : nat :=
match y with
  | 0 => x
  | S n => S (add2 x n)
end.

(* Lemmi usando l'uguaglianza di Coq necessari per provare alcuni lemmi usati *)
Lemma add1_x_S_p (x: nat) (n: nat) : add1 x (S n) = S (add1 x n).
Proof.
by [].
Qed.

Lemma add2_0_y_p (y: nat) : add2 0 y = y.
Proof.
elim: y.
  by [].
move=> n hp.
by rewrite //= hp.
Qed.

Lemma add2_S_y_p (n: nat) (y: nat) : add2 (S n) y = S (add2 n y).
Proof.
elim: y.
  by [].
move=> m hp.
by rewrite //= hp.
Qed.

(* Lemmi utilizzati per l'esercizio *)
Lemma add1_x_0_m (x: nat) : MartinLof.eq nat (add1 x 0) x.
Proof.
elim: x.
  apply: MartinLof.refl.
move=> n hp.
rewrite //=.
apply: (MartinLof.el nat (fun a b p => MartinLof.eq nat (S a) (S b))
  _ (add1 n 0) n hp) => x.
apply: MartinLof.refl.
Qed.

Lemma add2_0_y_m (y: nat) : MartinLof.eq nat (add2 0 y) y.
Proof.
elim: y.
  apply: MartinLof.refl.
move=> n hp.
rewrite //=.
apply: (MartinLof.el nat (fun a b p => MartinLof.eq nat (S a) (S b))
  _ (add2 0 n) n hp) => x.
apply: MartinLof.refl.
Qed.

Lemma add1_x_S_m (x: nat) (n: nat) : 
MartinLof.eq nat (add1 x (S n)) (S (add1 x n)).
Proof.
elim: x.
  apply: MartinLof.refl.
move=> n0 hp.
rewrite //=.
apply: (MartinLof.el nat (fun a b p => MartinLof.eq nat (S a) (S b))
  _ (add1 n0 (S n)) (S (add1 n0 n)) hp) => x.
apply: MartinLof.refl.
Qed.

Lemma add2_S_y_m (n: nat) (y: nat) : 
MartinLof.eq nat (add2 (S n) y) (S (add2 n y)).
Proof.
elim: y.
  apply: MartinLof.refl.
move=> n0 hp.
rewrite //=.
apply: (MartinLof.el nat (fun a b p => MartinLof.eq nat (S a) (S b))
  _ (add2 (S n) n0) (S (add2 n n0)) hp) => x.
apply: MartinLof.refl.
Qed.

Lemma ml_riflessivita {A} (x y: A) : MartinLof.eq A x y -> MartinLof.eq A y x.
Proof.
move=> hp.
apply: (MartinLof.el A (fun a b p => MartinLof.eq A b a) _ x y hp) => z.
apply: MartinLof.refl.
Qed.

Lemma add1_comm_m (x: nat) (y: nat) : MartinLof.eq nat (add1 x y) (add1 y x).
Proof.
elim: x.
  rewrite //=.
  apply (ml_riflessivita (add1 y 0) y (add1_x_0_m y)).
move=> n0 hp.
rewrite //=.
replace (add1 y (S n0)) with (S (add1 y n0)).
  apply: (MartinLof.el nat (fun a b p => MartinLof.eq nat (S a) (S b))
    _ (add1 n0 y) (add1 y n0) hp) => x.
  apply: MartinLof.refl.
apply (eq_sym (add1_x_S_p y n0)).
Qed.

Lemma pf_m (x: nat) (y: nat) : MartinLof.eq nat (add1 x y) (add2 x y).
Proof.
elim: x.
  rewrite //=.
  replace (add2 0 y) with y.
    apply: MartinLof.refl.
  apply (eq_sym (add2_0_y_p y)).
move=> n hp.
rewrite //=.
replace (add2 (S n) y) with (S (add2 n y)).
  apply: (MartinLof.el nat (fun a b p => MartinLof.eq nat (S a) (S b))
    _ (add1 n y) (add2 n y) hp) => x.
  apply: MartinLof.refl.
apply (eq_sym (add2_S_y_p n y)).
Qed.
