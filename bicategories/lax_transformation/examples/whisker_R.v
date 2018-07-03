Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     lax_functor.lax_functor
     lax_functor.examples.composition
     lax_transformation.lax_transformation
     general_category.

Section WhiskerR.
  Context `{Univalence}
          {C D E : BiCategory}
          {F₁ F₂ : LaxFunctor C D}.
  Variable (G : LaxFunctor D E)
           (σ : LaxTransformation F₁ F₂).
  Context `{@is_pseudo_functor _ _ _ G}.
  
  Definition whisker_R_component (X : C)
    : Hom E (G (F₁ X)) (G (F₂ X))
    := Fmor G (laxcomponent_of σ X).

  Definition Fmor_precomp (X Y : C)
    : NaturalTransformation
        (precomp ((Fmor G) (laxcomponent_of σ X)) (lax_comp_obj G F₂ Y) o Fmor G)%functor
        (Fmor G o precomp (laxcomponent_of σ X) (F₂ Y))%functor.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; simpl.
      exact (@Fcomp _ _ _ G (F₁ X) (F₂ X) (F₂ Y) (h,laxcomponent_of σ X)).
    - intros h₁ h₂ α ; simpl.
      pose (@Fcomp _ _ _ G (F₁ X) (F₂ X) (F₂ Y)) as m.
      rewrite <- (commutes m (h₁,laxcomponent_of σ X) (h₂,laxcomponent_of σ X) (α,1)%morphism).
      simpl.
      rewrite identity_of.
      reflexivity.
  Defined.

  Definition Fmor_precomp_inv (X Y : C)
    : NaturalTransformation
        (Fmor G o precomp (laxcomponent_of σ X) (F₂ Y))%functor
        (precomp ((Fmor G) (laxcomponent_of σ X)) (lax_comp_obj G F₂ Y) o Fmor G)%functor.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; simpl.
      exact (@morphism_inverse (_ -> _)
                               _
                               _
                               (@Fcomp _ _ _ G (F₁ X) (F₂ X) (F₂ Y))
                               (@Fcomp_iso _ _ _ G _ (F₁ X) (F₂ X) (F₂ Y))
                               (h,laxcomponent_of σ X)).
    - intros h₁ h₂ α ; simpl.
      pose (@morphism_inverse (_ -> _)
                              _
                              _
                              (@Fcomp _ _ _ G (F₁ X) (F₂ X) (F₂ Y))
                              (@Fcomp_iso _ _ _ G _ (F₁ X) (F₂ X) (F₂ Y))
           ) as m.
      rewrite (commutes m (h₁,laxcomponent_of σ X) (h₂,laxcomponent_of σ X) (α,1)%morphism).
      simpl.
      rewrite identity_of.
      reflexivity.
  Defined.

  Global Instance Fmor_precomp_iso (X Y : C)
    : @IsIsomorphism (_ -> _) _ _ (Fmor_precomp X Y).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - exact (Fmor_precomp_inv X Y).
    - apply path_natural_transformation.
      intro g ; simpl.
      pose (@left_inverse (_ -> _)
                          _
                          _
                          (@Fcomp _ _ _ G (F₁ X) (F₂ X) (F₂ Y))
                          (@Fcomp_iso _ _ _ G _ (F₁ X) (F₂ X) (F₂ Y))) as p.
      apply (equiv_path_natural_transformation _ _ p (g,laxcomponent_of σ X)).
    - apply path_natural_transformation.
      intro g ; simpl.
      pose (@right_inverse (_ -> _)
                           _
                           _
                           (@Fcomp _ _ _ G (F₁ X) (F₂ X) (F₂ Y))
                           (@Fcomp_iso _ _ _ G _ (F₁ X) (F₂ X) (F₂ Y))) as p.
      apply (equiv_path_natural_transformation _ _ p (g,laxcomponent_of σ X)).
  Defined.

  Definition Fmor_postcomp (X Y : C)
    : NaturalTransformation
        (postcomp ((Fmor G) (laxcomponent_of σ X)) (lax_comp_obj G F₁ Y) o Fmor G)%functor
        (Fmor G o postcomp (laxcomponent_of σ X) (F₁ Y))%functor.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; simpl.
      exact (@Fcomp _ _ _ G (F₁ Y) (F₁ X) (F₂ X) (laxcomponent_of σ X,h)).
    - intros h₁ h₂ α ; simpl.
      pose (@Fcomp _ _ _ G (F₁ Y) (F₁ X) (F₂ X)) as m.
      rewrite <- (commutes m (laxcomponent_of σ X,h₁) (laxcomponent_of σ X,h₂) (1,α)%morphism).
      simpl.
      rewrite identity_of.
      reflexivity.
  Defined.

  Definition Fmor_postcomp_inv (X Y : C)
    : NaturalTransformation
        (Fmor G o postcomp (laxcomponent_of σ X) (F₁ Y))%functor
        (postcomp ((Fmor G) (laxcomponent_of σ X)) (lax_comp_obj G F₁ Y) o Fmor G)%functor.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; simpl.
      exact (@morphism_inverse (_ -> _)
                               _
                               _
                               (@Fcomp _ _ _ G (F₁ Y) (F₁ X) (F₂ X))
                               (@Fcomp_iso _ _ _ G _ (F₁ Y) (F₁ X) (F₂ X))
                               (laxcomponent_of σ X,h)).
    - intros h₁ h₂ α ; simpl.
      pose (@morphism_inverse (_ -> _)
                              _
                              _
                              (@Fcomp _ _ _ G (F₁ Y) (F₁ X) (F₂ X))
                              (@Fcomp_iso _ _ _ G _ (F₁ Y) (F₁ X) (F₂ X))) as m.
      rewrite (commutes m).
      simpl.
      rewrite identity_of.
      reflexivity.
  Defined.

  Global Instance Fmor_postcomp_iso (X Y : C)
    : @IsIsomorphism (_ -> _) _ _ (Fmor_postcomp X Y).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - exact (Fmor_postcomp_inv X Y).
    - apply path_natural_transformation.
      intro g ; simpl.
      pose (@left_inverse (_ -> _)
                          _
                          _
                          (@Fcomp _ _ _ G (F₁ Y) (F₁ X) (F₂ X))
                          (@Fcomp_iso _ _ _ G _ (F₁ Y) (F₁ X) (F₂ X))) as p.
      exact (equiv_path_natural_transformation _ _ p (laxcomponent_of σ X,g)).
    - apply path_natural_transformation.
      intro g ; simpl.
      pose (@right_inverse (_ -> _)
                           _
                           _
                           (@Fcomp _ _ _ G (F₁ Y) (F₁ X) (F₂ X))
                           (@Fcomp_iso _ _ _ G _ (F₁ Y) (F₁ X) (F₂ X))) as p.
      exact (equiv_path_natural_transformation _ _ p (laxcomponent_of σ X,g)).
  Defined.

  Definition whisker_R_naturality (X Y : C)
    : NaturalTransformation
        (precomp ((Fmor G) (laxcomponent_of σ X)) (lax_comp_obj G F₂ Y) o (Fmor G o Fmor F₂))
        (postcomp ((Fmor G) (laxcomponent_of σ Y)) (lax_comp_obj G F₁ X) o (Fmor G o Fmor F₁))
    := ((Composition.associator_1 _ _ _)
          o ((Fmor_postcomp_inv Y X) oR _)
          o (Composition.associator_2 _ _ _)
          o (_ oL (@laxnaturality_of _ _ _ _ _ σ X Y))
          o (Composition.associator_1 _ _ _)
          o ((Fmor_precomp X Y) oR (Fmor F₂))
          o (Composition.associator_2 _ _ _)
       )%natural_transformation.

  Global Instance whisker_R_naturality_pseudo
         `{@is_pseudo_transformation _ _ _ _ _ σ}
         (X Y : C)
    : @IsIsomorphism (_ -> _) _ _ (whisker_R_naturality X Y).
  Proof.
    repeat (apply Morphisms.isisomorphism_compose).
    - apply _.
    - apply iso_whisker_r.
      exact (Morphisms.isisomorphism_inverse (Fmor_postcomp_iso Y X)).
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
  Defined.

  Definition whisker_R_d : LaxTransformation_d (lax_comp G F₁) (lax_comp G F₂).
  Proof.
    simple refine (Build_LaxTransformation_d _ _).
    - exact whisker_R_component.
    - exact whisker_R_naturality.
  Defined.

  Definition whisker_R_d_is_lax : is_lax_transformation whisker_R_d.
  Admitted.

  Definition whisker_R
    : LaxTransformation (lax_comp G F₁) (lax_comp G F₂)
    := Build_LaxTransformation whisker_R_d whisker_R_d_is_lax.
End WhiskerR.