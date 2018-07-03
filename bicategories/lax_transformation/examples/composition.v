Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     general_category.

Section Precomposition.
  Context `{Univalence}
          {C : BiCategory}.
  
  Definition precomp_compose_1
             {X Y Z : C}
             (f : Hom C X Y)
             (g : Hom C Y Z)
             (W : C)
  : NaturalTransformation
      (precomp (c_m (g,f)) W)
      (precomp f W o precomp g W)%functor.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h.
      exact (@morphism_inverse (_ -> _) _ _ (@assoc _ C X Y Z W) _ (h,g,f)).
    - intros h₁ h₂ α ; cbn.
      pose (@morphism_inverse (_ -> _) _ _ (@assoc _ C X Y Z W) _) as m.
      rewrite <- (commutes m (h₁,g,f) (h₂,g,f) (α,1,1)%morphism) ; cbn.
      rewrite identity_of.
      reflexivity.
  Defined.

  Definition precomp_compose_2
             {X Y Z : C}
             (f : Hom C X Y)
             (g : Hom C Y Z)
             (W : C)
    : NaturalTransformation
        (precomp f W o precomp g W)%functor
        (precomp (c_m (g,f)) W).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h.
      exact (assoc (h,g,f)).
    - intros h₁ h₂ α ; cbn.
      pose (@assoc _ C X Y Z W) as m.
      rewrite (commutes m (h₁,g,f) (h₂,g,f) (α,1,1)%morphism) ; cbn.
      rewrite identity_of.
      reflexivity.
  Defined.

  Global Instance precomp_compose_1_iso
         {X Y Z : C}
         (f : Hom C X Y)
         (g : Hom C Y Z)
         (W : C)
    : @IsIsomorphism (_ -> _) _ _ (precomp_compose_1 f g W).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - exact (precomp_compose_2 f g W).
    - apply path_natural_transformation.
      intros h ; cbn.
      apply right_inverse.
    - apply path_natural_transformation.
      intros h ; cbn.
      apply left_inverse.
  Defined.

  Definition postcomp_compose_1
             {X Y Z : C}
             (f : Hom C X Y)
             (g : Hom C Y Z)
             (W : C)
    : NaturalTransformation
        (postcomp (c_m (g,f)) W)
        (postcomp g W o postcomp f W)%functor.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h.
      exact (assoc (g,f,h)).
    - intros h₁ h₂ α ; cbn.
      pose (@assoc _ C W X Y Z) as m.
      rewrite <- (commutes m (g,f,h₁) (g,f,h₂) (1,1,α)%morphism) ; cbn.
      rewrite identity_of.
      reflexivity.
  Defined.

  Definition postcomp_compose_2
             {X Y Z : C}
             (f : Hom C X Y)
             (g : Hom C Y Z)
             (W : C)
    : NaturalTransformation
        (postcomp g W o postcomp f W)%functor
        (postcomp (c_m (g,f)) W).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h.
      exact (@morphism_inverse (_ -> _) _ _ (@assoc _ C W X Y Z) _ (g,f,h)).
    - intros h₁ h₂ α ; cbn.
      pose (@morphism_inverse (_ -> _) _ _ (@assoc _ C W X Y Z) _) as m.
      rewrite (commutes m (g,f,h₁) (g,f,h₂) (1,1,α)%morphism) ; cbn.
      rewrite identity_of.
      reflexivity.
  Defined.

  Global Instance postcomp_compose_1_iso
         {X Y Z : C}
         (f : Hom C X Y)
         (g : Hom C Y Z)
         (W : C)
    : @IsIsomorphism (_ -> _) _ _ (postcomp_compose_1 f g W).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - exact (postcomp_compose_2 f g W).
    - apply path_natural_transformation.
      intros h ; cbn.
      apply left_inverse.
    - apply path_natural_transformation.
      intros h ; cbn.
      apply right_inverse.
  Defined.

  Definition precomp_postcomp
             {W X Y Z : C}
             (f : Hom C W X)
             (g : Hom C Y Z)
    : NaturalTransformation
        (precomp f Z o postcomp g X)%functor
        (postcomp g W o precomp f Y)%functor.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; simpl.
      exact (assoc (g,h,f)).
    - intros h₁ h₂ α.
      pose (@assoc _ C W X Y Z) as m.
      exact (commutes m (g,h₁,f) (g,h₂,f) (1,α,1)%morphism).
  Defined.

  Definition postcomp_precomp
             {W X Y Z : C}
             (f : Hom C W X)
             (g : Hom C Y Z)
    : NaturalTransformation
        (postcomp g W o precomp f Y)%functor
        (precomp f Z o postcomp g X)%functor.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; simpl.
      exact (@morphism_inverse (_ -> _) _ _ (@assoc _ C W X Y Z) _ (g,h,f)).
    - intros h₁ h₂ α ; cbn.
      pose (@morphism_inverse (_ -> _) _ _ (@assoc _ C W X Y Z) _) as m.
      rewrite (commutes m (g,h₁,f) (g,h₂,f) (1,α,1)%morphism) ; cbn.
      reflexivity.
  Defined.

  Global Instance precomp_postcomp_iso
         {W X Y Z : C}
         (f : Hom C W X)
         (g : Hom C Y Z)
    : @IsIsomorphism (_ -> _) _ _ (precomp_postcomp f g).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - exact (postcomp_precomp f g).
    - apply path_natural_transformation.
      intros h ; cbn.
      apply left_inverse.
    - apply path_natural_transformation.
      intros h ; cbn.
      apply right_inverse.
  Defined.
End Precomposition.

Section Composition.
  Context `{Univalence}
          {C D : BiCategory}
          {F₁ F₂ F₃ : LaxFunctor C D}.
  Variable (σ₁ : LaxTransformation F₁ F₂) (σ₂ : LaxTransformation F₂ F₃).
  
  Definition compose_component (X : C)
    : Hom D (F₁ X) (F₃ X)
    := c_m (laxcomponent_of_d σ₂.1 X,laxcomponent_of_d σ₁.1 X).

  Definition compose_naturality
             (X Y : C)
    : NaturalTransformation
        (precomp (compose_component X) (F₃ Y) o Fmor F₃)
        (postcomp (compose_component Y) (F₁ X) o Fmor F₁)
    := (whisker_r (postcomp_compose_2 _ _ _) (Fmor F₁)
          o (Composition.associator_2 _ _ _)
          o (whisker_l _ (@laxnaturality_of _ _ _ _ _ σ₁ X Y))
          o (Composition.associator_1 _ _ _)
          o (whisker_r (precomp_postcomp _ _) (Fmor F₂))
          o (Composition.associator_2 _ _ _)
          o (whisker_l _ (@laxnaturality_of _ _ _ _ _ σ₂ X Y))
          o (Composition.associator_1 _ _ _)
          o (whisker_r (precomp_compose_1 (laxcomponent_of σ₁ X) (laxcomponent_of σ₂ X) (F₃ Y))
                       (Fmor F₃))
      )%natural_transformation.

  Global Instance compose_naturality_pseudo
         `{@is_pseudo_transformation _ _ _ _ _ σ₁}
         `{@is_pseudo_transformation _ _ _ _ _ σ₂}
         (X Y : C)
    : @IsIsomorphism (_ -> _) _ _ (compose_naturality X Y).
  Proof.
    unfold compose_naturality.
    repeat (apply Morphisms.isisomorphism_compose).
    - apply _.
    - apply _.
    - apply iso_whisker_l.
      apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply iso_whisker_l.
      apply _.
    - apply _.
    - apply _.
  Defined.
  
  Definition compose_d
    : LaxTransformation_d F₁ F₃
    := Build_LaxTransformation_d compose_component compose_naturality.

  Definition compose_d_is_lax
    : is_lax_transformation compose_d.
  Admitted.

  Definition compose
    : LaxTransformation F₁ F₃
    := Build_LaxTransformation compose_d compose_d_is_lax.
End Composition.