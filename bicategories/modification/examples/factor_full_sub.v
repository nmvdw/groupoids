Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.lax_functor
     lax_functor.examples.factor_full_sub
     lax_transformation.lax_transformation
     lax_transformation.examples.factor_full_sub
     modification.modification
     general_category.

Definition factor_modification
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F G}
           (P : D -> hProp)
           (σ : Modification η₁ η₂)
           (FH : forall (X : C), P (F X))
           (GH : forall (X : C), P (G X))
  : Modification
      (lax_factor_transformation P η₁ FH GH)
      (lax_factor_transformation P η₂ FH GH)
  := Build_Modification
       (fun A => mod_component σ A)
       (fun A B f => mod_commute σ f).