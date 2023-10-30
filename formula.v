Require Import Lia.
Require Import Reals Lra.

Open Scope R_scope.

(* Basic definitions for metric spaces *)
Record MetricSpace : Type := {
  point :> Type;
  distance : point -> point -> R;
 
  distance_nonneg : forall x y : point, 0 <= distance x y;
  distance_sym : forall x y : point, distance x y = distance y x;
  distance_triangle : forall x y z : point,
    distance x z <= distance x y + distance y z;
  distance_refl : forall x : point, distance x x = 0;
}.

Lemma R_distance_triangle : forall x y z : R,
  Rabs (x - z) <= Rabs (x - y) + Rabs (y - z).
Proof.
  intros x y z.
  replace (x - z) with ((x - y) + (y - z)) by lra.
  apply Rabs_triang.
Qed.

Lemma R_distance_refl : forall x : R, Rabs (x - x) = 0.
Proof.
  intro x.
  rewrite Rminus_diag_eq; auto.
  apply Rabs_R0.
Qed.

Definition R_MetricSpace : MetricSpace :=
  {|
    point := R;
    distance x y := Rabs (x - y);
    distance_nonneg x y := Rabs_pos (x - y);
    distance_sym x y := Rabs_minus_sym x y;
    distance_triangle x y z := R_distance_triangle x y z;
    distance_refl x := R_distance_refl x
  |}.
