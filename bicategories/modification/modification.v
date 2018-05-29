Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory lax_functor.lax_functor lax_transformation.lax_transformation.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.

Record modification
       `{Univalence}
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       (σ₁ σ₂ : LaxTransformation F G)
  := {
      mod_component : forall (A : C),
        two_cell (laxcomponent_of σ₁ A) (laxcomponent_of σ₂ A) ;
      mod_commute : forall (A B : C) (f : Hom C A B),
            ((laxnaturality_of σ₂ f)
               o
               (bc_whisker_r _ (Fmor G f) (mod_component A))
             =
             (bc_whisker_l (Fmor F f) _ (mod_component B))
               o
               (laxnaturality_of σ₁ f)
            )%morphism
    }.

Arguments mod_component {_ C D F G σ₁ σ₂} _ A.
Arguments mod_commute {_ C D F G σ₁ σ₂} _ A B f.