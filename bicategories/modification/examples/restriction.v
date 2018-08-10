Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.lax_functor
     lax_functor.examples.restriction
     lax_transformation.lax_transformation
     lax_transformation.examples.restriction
     modification.modification
     general_category.

Section Restriction.
  Context {C D : BiCategory}
          {F G : LaxFunctor C D}
          {η₁ η₂ : LaxTransformation F G}.
  Variable (P : C -> hProp)
           (σ : modification η₁ η₂).

  Definition lax_restriction_modification
    : modification
        (lax_restriction_transformation P η₁)
        (lax_restriction_transformation P η₂).
  Proof.
    simple refine (Build_Modification _ _).
    - exact (fun X => mod_component σ X.1).
    - exact (fun X Y f => mod_commute σ f). 
  Defined.
End Restriction.