Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.lax_functor
     lax_functor.examples.factor_full_sub
     lax_transformation.lax_transformation
     lax_transformation.examples.factor_full_sub
     modification.modification
     general_category.

Section Factor.
  Context {C D : BiCategory}
          {F G : LaxFunctor C D}
          {η₁ η₂ : LaxTransformation F G}.
  Variable (P : D -> hProp)
           (σ : modification η₁ η₂)
           (FH : forall (X : C), P (F X))
           (GH : forall (X : C), P (G X)).

  Definition factor_modification
    : modification
        (lax_factor_transformation P η₁ FH GH)
        (lax_factor_transformation P η₂ FH GH)
    := Build_Modification
         (fun A => mod_component σ A)
         (fun A B f => mod_commute σ f).
End Factor.