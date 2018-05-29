Require Import HoTT.
From GR.bicategories.bicategory Require Import
     bicategory examples.discrete_bicategory.
From GR.bicategories.lax_functor Require Import
     lax_functor.
From GR.groupoid.grpd_bicategory Require Import
     grpd_bicategory.
From GR.setoid Require Import
     setoid setoid_adjunction.

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

Definition setoid_bicat `{Univalence} : BiCategory
  := discrete_bicategory (setoids_precat).

(*
Definition setoid_to_groupoid_functor `{Univalence}
  : LaxFunctor setoid_bicat grpd.
Proof.
  simple refine (Build_LaxFunctor _ _ _ _ _ _ _ _ _ _).
  - apply setoid_to_groupoid.
  - cbn ; intros R₁ R₂.
    simple refine (Build_Functor _ _ _ _ _ _) ; cbn.
    + intros f.
      simple refine (Build_Functor _ _ _ _ _ _) ; simpl.
      * apply f.
      * intros.
        apply f ; assumption.
      * intros ; simpl.
        apply path_ishprop.
      * intros.
        apply path_ishprop.
    + intros f₁ f₂ p ; induction p.
      simple refine (Build_NaturalTransformation _ _ _ _) ; simpl.
      * intros x.
        apply refl.
      * intros.
        apply path_ishprop.
    + intros f₁ f₂ f₃ p₁ p₂ ; simpl.
      induction p₁, p₂ ; simpl.
      simple refine (path_natural_transformation _ _ _) ; simpl.
      intros x ; cbn.
      apply path_ishprop.
    + intros x ; simpl.
      simple refine (path_natural_transformation _ _ _) ; simpl.
      intro ; apply path_ishprop.
  - intros R₁ R₂ R₃.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [f₁ f₂] ; simpl.
      simple refine (Build_NaturalTransformation _ _ _ _).
      * intros x ; simpl in *.
        apply refl.
      * intros ; apply path_ishprop.
    + intros [f₁ f₂] [p₁ p₂] [q₁ q₂] ; simpl.
      simple refine (path_natural_transformation _ _ _) ; simpl.
      intro x.
      apply path_ishprop.
  - intros R ; simpl.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros x ; simpl in *.
      apply refl.
    + intros.
      apply path_ishprop.
  - intros R₁ R₂ f ; simpl.
    simple refine (path_natural_transformation _ _ _) ; simpl.
    intro x.
    apply path_ishprop.
  - intros ; simpl.
    simple refine (path_natural_transformation _ _ _) ; simpl.
    intro x.
    apply path_ishprop.
  - intros ; simpl.
    simple refine (path_natural_transformation _ _ _) ; simpl.
    intro x.
    apply path_ishprop.
Defined.
*)