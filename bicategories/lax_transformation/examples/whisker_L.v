Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     lax_functor.lax_functor
     lax_functor.examples.composition
     lax_transformation.lax_transformation
     general_category.

Section WhiskerL.
  Context `{Univalence}
          {C D E : BiCategory}
          {G₁ G₂ : LaxFunctor D E}.
  Variable (F : LaxFunctor C D)
           (σ : LaxTransformation G₁ G₂).

  Definition whisker_L_component (X : C)
    : Hom E (G₁ (F X)) (G₂ (F X))
    := laxcomponent_of_d σ.1 (F X).
  
  Definition whisker_L_naturality (X Y : C)
    : NaturalTransformation
        (c_m o (1 * const_functor (whisker_L_component X)) o Fmor (lax_comp G₂ F))
        (c_m o (const_functor (whisker_L_component Y) * 1) o Fmor (lax_comp G₁ F)).
  Proof.
    refine (_ o (whisker_r (@laxnaturality_of_d _ _ _ _ _ σ.1 (F X) (F Y)) (Fmor_d F.1))
              o _)%natural_transformation
    ; unfold precomp, postcomp, whisker_L_component, lax_comp, lax_comp_d, lax_comp_mor, Fmor in *
    ; simpl in *.
    - apply Composition.associator_1.
    - apply Composition.associator_2.
  Defined.

  Global Instance whisker_L_naturality_pseudo
         `{@is_pseudo_transformation _ _ _ _ _ σ}
         (X Y : C)
    : @IsIsomorphism (_ -> _) _ _ (whisker_L_naturality X Y)
    := _.

  Definition whisker_L_d
    : LaxTransformation_d (lax_comp G₁ F) (lax_comp G₂ F).
  Proof.
    simple refine (Build_LaxTransformation_d _ _).
    - exact whisker_L_component.
    - exact whisker_L_naturality.
  Defined.

  Definition whisker_L_d_is_lax
    : is_lax_transformation whisker_L_d.
  Proof.
  (*split.
  - intros X ; cbn.
    rewrite !left_identity, !right_identity.
    destruct (σ.2) as [fst snd].
    specialize (fst (F X)).
    unfold lax_comp_id, lax_comp_obj ; cbn.
    pose (@laxnaturality_of _ _ _ _ _ σ (F X) (F X)).
    pose (commutes n (Fmor F (id_m X)) (Fmor F (id_m X))).
    unfold precomp, postcomp, n in p.
    unfold hcomp.
    simpl in p.
    rewrite <- (left_identity _ _ _ 1)%morphism.
    simpl.
    unfold whisker_L_component.
    pose (p (Fid F X)).
    rewrite composition_of.
    rewrite (composition_of c_m _ _ _ (Fid G₂ (F X), 1)%morphism).*)
  Admitted.

  Definition whisker_L
    : LaxTransformation (lax_comp G₁ F) (lax_comp G₂ F)
    := Build_LaxTransformation whisker_L_d whisker_L_d_is_lax.
End WhiskerL.