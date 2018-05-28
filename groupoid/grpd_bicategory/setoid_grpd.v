Require Import HoTT.
From GR.bicategories.lax_functor Require Import
     lax_functor.
From GR.groupoid.grpd_bicategory Require Import
     grpd_bicategory.
From GR.setoid Require Import
     setoid.

(** Every setoid induces a groupoid. *)
Definition setoid_to_groupoid (R : setoid) : groupoid.
Proof.
  simple refine (Build_grpd _ _ _ _ _ _ _ _ _ _) ; simpl.
  - exact (setoid.under R).
  - exact (fun a₁ a₂ => BuildhSet (rel R a₁ a₂)).
  - exact refl.
  - exact (@sym R).
  - exact (@trans R).
  - cbn ; intros.
    apply path_ishprop.
  - cbn ; intros.
    apply path_ishprop.
  - cbn ; intros.
    apply path_ishprop.
  - cbn ; intros.
    apply path_ishprop.
  - cbn ; intros.
    apply path_ishprop.
Defined.