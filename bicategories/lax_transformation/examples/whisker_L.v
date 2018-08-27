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
  Context {C D E : BiCategory}
          {G₁ G₂ : LaxFunctor D E}.
  Variable (F : LaxFunctor C D)
           (σ : LaxTransformation G₁ G₂).

  Definition whisker_L_d
    : LaxTransformation_d (lax_comp G₁ F) (lax_comp G₂ F).
  Proof.
    make_lax_transformation.
    - exact (fun X => σ (F X)).
    - exact (fun X Y f => laxnaturality_of σ (F ₁ f)).
  Defined.

  Definition whisker_L_d_is_lax
    : is_lax_transformation whisker_L_d.
  Proof.
    make_is_lax_transformation.
    - intros X Y f g α ; simpl in * ; unfold bc_whisker_r.
      apply (laxnaturality_natural σ).
    - intros X ; simpl in * ; unfold bc_whisker_r.
      unfold Fid ; simpl.
      rewrite <- (vcomp_left_identity (id₂ (σ (F X)))).
      rewrite !interchange.
      rewrite !vcomp_assoc.
      rewrite (ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
      rewrite <- (transformation_unit σ (F X)).
      rewrite <- !vcomp_assoc.
      f_ap.
      apply σ.
    - intros X Y Z f g ; simpl in * ; unfold bc_whisker_r.
      unfold Fcomp₁ ; simpl in *.
      rewrite <- (vcomp_left_identity (id₂ (σ (F Z)))).
      rewrite interchange.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
      rewrite <- (transformation_assoc σ (F ₁ f) (F ₁ g)).
      rewrite <- (vcomp_left_identity (id₂ (σ (F X)))).
      rewrite interchange.
      rewrite <- !vcomp_assoc.
      f_ap.
      apply σ.
  Qed.

  Definition whisker_L
    : LaxTransformation (lax_comp G₁ F) (lax_comp G₂ F)
    := Build_LaxTransformation whisker_L_d whisker_L_d_is_lax.

  Global Instance whisker_l_is_pseudo
         `{is_pseudo_transformation _ _ _ _ σ}
    : is_pseudo_transformation whisker_L.
  Proof.
    split.
    intros X Y f ; cbn in *.
    apply _.
  Defined.
End WhiskerL.