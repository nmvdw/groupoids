Require Import HoTT.
From HoTT.Categories Require Import Category Functor.
From GR.bicategories Require Import
     bicategory.bicategory lax_functor.lax_functor lax_transformation.lax_transformation.

Definition Modification_d
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η₁ η₂ : LaxTransformation F G)
  : Type
  := forall (A : C), η₁ A ==> η₂ A.

Definition is_modification
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F G}
           (σ : Modification_d η₁ η₂)
  : Type
  := forall (A B : C) (f : C⟦A,B⟧),
    laxnaturality_of η₂ f ∘ ((G ₁ f) ◅ σ A)
    =
    (σ B ▻ (F ₁ f)) ∘ laxnaturality_of η₁ f.

Definition Modification
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       (η₁ η₂ : LaxTransformation F G)
  := {m : Modification_d η₁ η₂ & is_modification m}.

Definition Build_Modification
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F G}
           (mc : Modification_d η₁ η₂)
           (mn : is_modification mc)
  : Modification η₁ η₂
  := (mc;mn).

Definition mod_component
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F G}
           (m : Modification η₁ η₂)
  : forall (A : C), η₁ A ==> η₂ A
  := m.1.

Coercion mod_component : Modification >-> Funclass.

Definition mod_commute
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F G}
           (m : Modification η₁ η₂)
  : forall {A B : C} (f : C⟦A,B⟧),
    laxnaturality_of η₂ f ∘ ((G ₁ f) ◅ m A)
    =
    (m B ▻ (F ₁ f)) ∘ laxnaturality_of η₁ f
  := m.2.

Definition path_modification
           `{Funext}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {σ₁ σ₂ : LaxTransformation F G}
           {p q : Modification σ₁ σ₂}
           (r : mod_component p = mod_component q)
  : p = q
  := path_sigma_hprop _ _ r.

Global Instance modification_hset
       `{Funext}
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       {σ₁ σ₂ : LaxTransformation F G}
  : IsHSet (Modification σ₁ σ₂)
  := _.

Class iso_modification
      {C D : BiCategory}
      {F G : LaxFunctor C D}
      {σ₁ σ₂ : LaxTransformation F G}
      (m : Modification σ₁ σ₂)
  := mc_iso : forall (A : C),
      IsIsomorphism (mod_component m A).

Global Instance is_hprop_iso_modification
       `{Univalence}
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       {σ₁ σ₂ : LaxTransformation F G}
       (m : Modification σ₁ σ₂)
  : IsHProp (iso_modification m).
Proof.
  unfold iso_modification.
  apply _.
Qed.

Definition IsoModification
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (σ₁ σ₂ : LaxTransformation F G)
  : Type
  := {m : Modification σ₁ σ₂ & iso_modification m}.

Ltac make_iso_modification := simple refine (_;_).

Coercion iso_modification_to_modification
         `{Univalence}
         {C D : BiCategory}
         {F G : LaxFunctor C D}
         {σ₁ σ₂ : LaxTransformation F G}
         (m : IsoModification σ₁ σ₂)
  : Modification σ₁ σ₂
  := m.1.

Global Instance is_iso_iso_modification
       `{Univalence}
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       {σ₁ σ₂ : LaxTransformation F G}
       (m : IsoModification σ₁ σ₂)
  : iso_modification m
  := m.2.

Global Instance iso_mod_component_is_iso
       `{Univalence}
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       {σ₁ σ₂ : LaxTransformation F G}
       (m : IsoModification σ₁ σ₂)
       (A : C)
  : IsIsomorphism (mod_component m A)
  := mc_iso A.