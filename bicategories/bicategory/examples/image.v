Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.examples.full_sub
     bicategory.adjoint
     bicategory.univalent
     lax_functor.lax_functor.

Definition image
           {C D : BiCategory}
           (F : LaxFunctor C D)
  : BiCategory
  := full_sub D (fun Y => merely {X : C & F X = Y }).