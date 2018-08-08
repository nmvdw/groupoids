Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory lax_functor.lax_functor lax_transformation.lax_transformation.

Definition modification_d
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η₁ η₂ : LaxTransformation F G)
  : Type
  := forall (A : C), two_cell (laxcomponent_of η₁ A) (laxcomponent_of η₂ A).

Definition is_modification
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F G}
           (σ : modification_d η₁ η₂)
  : Type
  := forall (A B : C) (f : Hom C A B),
    ((laxnaturality_of η₂ f)
       o
       (bc_whisker_r _ (Fmor G f) (σ A))
     =
     (bc_whisker_l (Fmor F f) _ (σ B))
       o
       (laxnaturality_of η₁ f)
    )%morphism.

Definition modification
       `{Univalence}
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       (η₁ η₂ : LaxTransformation F G)
  := {σ : modification_d η₁ η₂ & is_modification σ}.

Definition Build_Modification
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F G}
           (mc : modification_d η₁ η₂)
           (mn : is_modification mc)
  : modification η₁ η₂
  := (mc;mn).

Definition mod_component
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {σ₁ σ₂ : LaxTransformation F G}
           (m : modification σ₁ σ₂)
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