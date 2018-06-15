Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories.bicategory Require Import
     bicategory
     equivalence
     examples.precat.
From GR.bicategories Require Import
     modification.modification.
From GR.bicategories.lax_transformation Require Import
     lax_transformation.
From GR.bicategories.lax_functor Require Import
     lax_functor
     examples.identity
     examples.composition.

Record BiAdjunction_unit_counit
       `{Univalence}
       (C D : BiCategory)
  := { left_adjoint_unit_counit : LaxFunctor D C ;
       right_adjoint_unit_counit : LaxFunctor C D ;
       unit : LaxTransformation (lax_id_functor D) (lax_comp right_adjoint left_adjoint) ;
       counit : LaxTransformation (lax_comp left_adjoint right_adjoint) (lax_id_functor C)
    }.