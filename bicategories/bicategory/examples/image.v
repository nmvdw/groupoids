Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.examples.full_sub
     bicategory.adjoint
     bicategory.univalent
     bicategory.locally_strict
     bicategory.strict
     lax_functor.lax_functor.

Definition image
           {C D : BiCategory}
           (F : LaxFunctor C D)
  : BiCategory
  := full_sub D (fun Y => merely {X : C & F X = Y }).

Global Instance univalent_image
       `{Univalence}
       {C D : BiCategory}
       `{@Univalent _ D}
       (F : LaxFunctor C D)
  : Univalent (image F)
  := _.

Global Instance is_2category_image
       {C D : BiCategory}
       `{is_2category D}
       (F : LaxFunctor C D)
  : is_2category (image F).
Proof.
  apply is_2category_full_sub.
  apply _.
Defined.