Require Import HoTT.
From GR.bicategories.lax_functor Require Import
     lax_functor.
From GR.groupoid.grpd_bicategory Require Import
     grpd_bicategory.

(** Groupoids are closed under sums. *)
Definition sum_groupoid (G₁ G₂ : groupoid) : groupoid.
Proof.
  simple refine (Build_grpd _ _ _ _ _ _ _ _ _ _) ; simpl.
  - exact (G₁ + G₂).
  - intros [x | x] [y | y].
    + exact (G₁ x y).
    + exact (BuildhSet Empty).
    + exact (BuildhSet Empty).
    + exact (G₂ x y).
  - intros [x | x] ; apply e.
  - intros [? | ?] [? | ?] ; contradiction || apply inv.
  - intros [? | ?] [? | ?] [? | ?] ; contradiction || apply comp.
  - intros [? | ?] [? | ?] [? | ?] [? | ?] ; try contradiction ; apply grpd_right_assoc.
  - intros [? | ?] [? | ?] ; try contradiction ; apply grpd_left_identity.
  - intros [? | ?] [? | ?] ; try contradiction ; apply grpd_right_identity.
  - intros [? | ?] [? | ?] ; try contradiction ; apply grpd_left_inverse.
  - intros [? | ?] [? | ?] ; try contradiction ; apply grpd_right_inverse.
Defined.    