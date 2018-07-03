Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories.bicategory Require Import
     bicategory
     equivalence
     examples.precat.
From GR.bicategories.lax_functor Require Import
     lax_functor
     laws.composition_laws.
Require Import GR.bicategories.lax_functor.examples.identity.
Require Import GR.bicategories.lax_functor.examples.composition.
From GR.bicategories.lax_transformation Require Import
     lax_transformation
     examples.equal_transformation
     examples.whisker_L
     examples.whisker_R.
Require Import GR.bicategories.lax_transformation.examples.identity.
Require Import GR.bicategories.lax_transformation.examples.composition.
From GR.bicategories Require Import
     modification.modification.

Record BiAdjunction_d
       `{Univalence}
       (C D : BiCategory)
  := Build_BiAdjunction_d
       { left_adjoint : LaxFunctor C D ;
         left_adjoint_pseudo : is_pseudo_functor left_adjoint ;
         right_adjoint : LaxFunctor D C ;
         right_adjoint_pseudo : is_pseudo_functor right_adjoint ;
         unit_d : LaxTransformation
                  (lax_id_functor C)
                  (lax_comp right_adjoint left_adjoint) ;
         counit_d : LaxTransformation
                    (lax_comp left_adjoint right_adjoint)
                    (lax_id_functor D) ;
       }.

Arguments Build_BiAdjunction_d {_ C D} _ _ _ _ _ _.
Arguments left_adjoint {_ C D}.
Arguments right_adjoint {_ C D}.
Arguments unit_d {_ C D}.
Arguments counit_d {_ C D}.

Global Instance left_adjoint_pseudo_functor
       `{Univalence}
       {C D : BiCategory}
       (F : BiAdjunction_d C D)
  : is_pseudo_functor (left_adjoint F).
Proof.
  apply left_adjoint_pseudo.
Defined.

Global Instance right_adjoint_pseudo_functor
       `{Univalence}
       {C D : BiCategory}
       (F : BiAdjunction_d C D)
  : is_pseudo_functor (right_adjoint F).
Proof.
  apply right_adjoint_pseudo.
Defined.

Definition is_biadjunction
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction_d C D)
  : Type.
Proof.
  refine (_ * _).
  - exact {m : modification
                  (compose
                     (eq_transformation (lax_comp_right_identity (left_adjoint F))^)
                     (compose
                        (whisker_R (left_adjoint F) (unit_d F))
                        (compose
                           (eq_transformation (lax_comp_associative _ _ _)^)
                           (compose
                              (whisker_L (left_adjoint F) (counit_d F))
                              (eq_transformation (lax_comp_left_identity (left_adjoint F)))
                           )
                        )
                     )
                  )
                  (identity_transformation (left_adjoint F))
               & is_pseudo_modification m}.
  - exact {m : modification
                 (compose
                    (eq_transformation (lax_comp_left_identity (right_adjoint F))^)
                    (compose
                       (whisker_L (right_adjoint F) (unit_d F))
                       (compose
                          (eq_transformation (lax_comp_associative _ _ _))
                          (compose
                             (whisker_R (right_adjoint F) (counit_d F))
                             (eq_transformation (lax_comp_right_identity (right_adjoint F)))
                          )
                       )
                    )
                 )
                 (identity_transformation (right_adjoint F))
               & is_pseudo_modification m}.
Defined.