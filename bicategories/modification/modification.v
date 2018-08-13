Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory lax_functor.lax_functor lax_transformation.lax_transformation.

Definition modification_d
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η₁ η₂ : LaxTransformation F G)
  : Type
  := forall (A : C), η₁ A ==> η₂ A.

Definition is_modification
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F G}
           (σ : modification_d η₁ η₂)
  : Type
  := forall (A B : C) (f : C⟦A,B⟧),
    laxnaturality_of η₂ f ∘ ((G ₁ f) ▻ σ A)
    =
    (σ B ◅ (F ₁ f)) ∘ laxnaturality_of η₁ f.

Definition modification
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       (η₁ η₂ : LaxTransformation F G)
  := {m : modification_d η₁ η₂ & is_modification m}.

Definition Build_Modification
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F G}
           (mc : modification_d η₁ η₂)
           (mn : is_modification mc)
  : modification η₁ η₂
  := (mc;mn).

Definition mod_component
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F G}
           (m : modification η₁ η₂)
  : forall (A : C), η₁ A ==> η₂ A
  := m.1.

Coercion mod_component : modification >-> Funclass.

Definition mod_commute
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F G}
           (m : modification η₁ η₂)
  : forall {A B : C} (f : C⟦A,B⟧),
    laxnaturality_of η₂ f ∘ ((G ₁ f) ▻ m A)
    =
    (m B ◅ (F ₁ f)) ∘ laxnaturality_of η₁ f
  := m.2.

Definition path_modification
           `{Funext}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {σ₁ σ₂ : LaxTransformation F G}
           {p q : modification σ₁ σ₂}
           (r : mod_component p = mod_component q)
  : p = q
  := path_sigma_hprop _ _ r.

Global Instance modification_hset
       `{Funext}
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       {σ₁ σ₂ : LaxTransformation F G}
  : IsHSet (modification σ₁ σ₂)
  := _.

Class is_pseudo_modification
      {C D : BiCategory}
      {F G : LaxFunctor C D}
      {σ₁ σ₂ : LaxTransformation F G}
      (m : modification σ₁ σ₂)
  := { mc_iso : forall (A : C),
         IsIsomorphism (mod_component m A)
     }.

Global Instance mod_component_is_iso_pseudo
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       {σ₁ σ₂ : LaxTransformation F G}
       (m : modification σ₁ σ₂)
       `{is_pseudo_modification _ _ _ _ _ _ m}
       (A : C)
  : IsIsomorphism (mod_component m A)
  := mc_iso A.