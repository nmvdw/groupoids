Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory lax_functor.lax_functor lax_transformation.lax_transformation.

Definition modification
       `{Univalence}
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       (σ₁ σ₂ : LaxTransformation F G)
  := {mc : forall (A : C),
        two_cell (laxcomponent_of σ₁ A) (laxcomponent_of σ₂ A) &
        forall (A B : C) (f : Hom C A B),
          ((laxnaturality_of σ₂ f)
             o
             (bc_whisker_r _ (Fmor G f) (mc A))
           =
           (bc_whisker_l (Fmor F f) _ (mc B))
             o
             (laxnaturality_of σ₁ f)
          )%morphism
     }.

Definition Build_Modification
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {σ₁ σ₂ : LaxTransformation F G}
           (mc : forall (A : C), two_cell
                                   (laxcomponent_of σ₁ A)
                                   (laxcomponent_of σ₂ A))
           (mn : forall (A B : C) (f : Hom C A B),
               ((laxnaturality_of σ₂ f)
                  o
                  (bc_whisker_r _ (Fmor G f) (mc A))
                =
                (bc_whisker_l (Fmor F f) _ (mc B))
                  o
                  (laxnaturality_of σ₁ f)
               )%morphism)
  : modification σ₁ σ₂
  := (mc;mn).

Definition mod_component
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {σ₁ σ₂ : LaxTransformation F G}
           (m : modification σ₁ σ₂)
  : forall (A : C), two_cell (laxcomponent_of σ₁ A) (laxcomponent_of σ₂ A)
  := m.1.

Definition mod_commute
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {σ₁ σ₂ : LaxTransformation F G}
           (m : modification σ₁ σ₂)
  := m.2.

Definition path_modification
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {σ₁ σ₂ : LaxTransformation F G}
           {p q : modification σ₁ σ₂}
           (r : mod_component p = mod_component q)
  : p = q
  := path_sigma_hprop _ _ r.

Global Instance modification_hset
       `{Univalence}
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       {σ₁ σ₂ : LaxTransformation F G}
  : IsHSet (modification σ₁ σ₂)
  := _.

Class is_pseudo_modification
      `{Univalence}
      {C D : BiCategory}
      {F G : LaxFunctor C D}
      {σ₁ σ₂ : LaxTransformation F G}
      (p : modification σ₁ σ₂)
  := { mc_iso : forall (A : C),
         IsIsomorphism (mod_component p A)
     }.