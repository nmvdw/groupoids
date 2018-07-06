Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.lax_functor
     lax_functor.examples.composition
     lax_functor.examples.identity
     lax_functor.examples.inclusion
     lax_functor.examples.restriction
     lax_functor.examples.factor_full_sub.

Definition restriction_identity
           `{Univalence}
           (C : BiCategory)
           (P : C -> hProp)
  : lax_factor
      (lax_restriction (lax_id_functor C) P)
      P
      (fun X => X.2)
    =
    lax_id_functor (full_sub C P).
Proof.
  apply path_LaxFunctor.
  simple refine (path_LaxFunctor_d _ _ _).
  - reflexivity.
  - reflexivity.
  - split.
    + reflexivity.
    + reflexivity.
Defined.

Definition restriction_composition
           `{Univalence}
           {C₁ C₂ C₃ : BiCategory}
           (F₂ : LaxFunctor C₂ C₃) (F₁ : LaxFunctor C₁ C₂)
           (P : C₁ -> hProp)
  : lax_comp F₂ (lax_restriction F₁ P)
    =
    lax_restriction (lax_comp F₂ F₁) P.
Proof.
  apply path_LaxFunctor.
  simple refine (path_LaxFunctor_d _ _ _).
  - reflexivity.
  - reflexivity.
  - split.
    + reflexivity.
    + reflexivity.
Defined.