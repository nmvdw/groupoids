Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory lax_functor.lax_functor
     lax_transformation.lax_transformation modification.modification.

Definition id_modification
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : LaxTransformation F G)
  : modification η η.
Proof.
  simple refine (_;_).
  - intros X.
    exact 1%morphism.
  - intros A B f ; cbn.
    unfold bc_whisker_r, bc_whisker_l.
    exact (ap (fun z => _ o z)%morphism (identity_of _ _)
              @ right_identity _ _ _ _
              @ ((left_identity _ _ _ _)^)
              @ (ap (fun z => z o _)%morphism (identity_of _ _))^).
Defined.