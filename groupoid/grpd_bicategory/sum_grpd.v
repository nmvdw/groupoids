Require Import HoTT.
From GR.bicategories.lax_functor Require Import
     lax_functor.
From GR.groupoid.grpd_bicategory Require Import
     grpd_bicategory.

(** Groupoids are closed under sums. *)
Definition sum_groupoid (G₁ G₂ : groupoid) : groupoid.
Proof.
  simple refine (Build_grpd _ _ _ _ _ _ _ _ _ _) ; simpl.
  - exact (under G₁ + under G₂).
  - intros [x | x] [y | y].
    + exact (hom G₁ x y).
    + exact (BuildhSet Empty).
    + exact (BuildhSet Empty).
    + exact (hom G₂ x y).
  - intros [x | x] ; apply e.
  - intros [? | ?] [? | ?] ; contradiction || apply inv.
  - intros [? | ?] [? | ?] [? | ?] ; contradiction || apply comp.
  - intros [? | ?] [? | ?] [? | ?] [? | ?] ; try contradiction ; apply car.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ec.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ce.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ic.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ci.
Defined.    