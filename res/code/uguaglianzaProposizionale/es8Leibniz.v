From mathcomp Require Import ssreflect.

(* Definizione di Leibniz come in 2 *)

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

Lemma add1_x_0_l (x: nat) : Leibniz.eq (add1 x 0) x.
Proof.
elim: x.
  apply: Leibniz.refl.
move=> n hp.
apply (Leibniz.e_id_l nat (fun a b => Leibniz.eq (S a) (S b)) (add1 n 0) n hp
  (fun x => Leibniz.refl (S x))).
Qed.

Lemma add2_0_y_l (y: nat) : Leibniz.eq (add2 0 y) y.
Proof.
elim: y.
  apply: Leibniz.refl.
move=> n hp.
apply (Leibniz.e_id_l nat (fun a b => Leibniz.eq (S a) (S b)) (add2 0 n) n hp
  (fun x => Leibniz.refl (S x))).
Qed.

Lemma add1_x_S_l (x: nat) (n: nat) : Leibniz.eq (add1 x (S n)) (S (add1 x n)).
Proof.
elim: x.
  apply: Leibniz.refl.
move=> n0 hp.
rewrite //=.
apply (Leibniz.e_id_l nat (fun a b => Leibniz.eq (S a) (S b)) 
  (add1 n0 (S n)) (S (add1 n0 n)) hp (fun x => Leibniz.refl (S x))).
Qed.

Lemma add2_S_y_l (n: nat) (y: nat) : Leibniz.eq (add2 (S n) y) (S (add2 n y)).
Proof.
elim: y.
  apply: Leibniz.refl.
move=> n0 hp.
rewrite //=.
apply (Leibniz.e_id_l nat (fun a b => Leibniz.eq (S a) (S b)) 
  (add2 (S n) n0) (S (add2 n n0)) hp (fun x => Leibniz.refl (S x))).
Qed.

Lemma l_riflessivita {A} (x y: A) : Leibniz.eq x y -> Leibniz.eq y x.
Proof.
move=> hp.
apply (Leibniz.e_id_l A (fun a b => Leibniz.eq b a) x y hp 
(fun x => Leibniz.refl x)) => z.
Qed.

Lemma add1_comm_l (x: nat) (y: nat) : Leibniz.eq (add1 x y) (add1 y x).
Proof.
elim: x.
  rewrite //=.
  apply (l_riflessivita (add1 y 0) y (add1_x_0_l y)).
move=> n0 hp.
rewrite //=.
replace (add1 y (S n0)) with (S (add1 y n0)).
  apply (Leibniz.e_id_l nat (fun a b => Leibniz.eq (S a) (S b)) 
  (add1 n0 y) (add1 y n0) hp (fun x => Leibniz.refl (S x))).
apply (eq_sym (add1_x_S_p y n0)).
Qed.

Lemma pf_l (x: nat) (y: nat) : Leibniz.eq (add1 x y) (add2 x y).
Proof.
elim: x.
  rewrite //=.
  replace (add2 0 y) with y.
    apply: Leibniz.refl.
  apply (eq_sym (add2_0_y_p y)).
move=> n hp.
rewrite //=.
replace (add2 (S n) y) with (S (add2 n y)).
  apply (Leibniz.e_id_l nat (fun a b => Leibniz.eq (S a) (S b)) 
  (add1 n y) (add2 n y) hp (fun x => Leibniz.refl (S x))).
apply (eq_sym (add2_S_y_p n y)).
Qed.