Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.examples.identity
     general_category.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.

Section EqualTransformation.
  Context `{Univalence}
          {C D : BiCategory}.
  
  Definition eq_transformation {F G : LaxFunctor C D} (p : F = G)
    : LaxTransformation F G
    := match p with
       | idpath => identity_transformation F
       end.

  Global Instance eq_pseudo {F G : LaxFunctor C D} (p : F = G)
    : is_pseudo_transformation (eq_transformation p)
    := match p with
       | idpath => _
       end.
End EqualTransformation.