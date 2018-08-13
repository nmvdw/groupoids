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
  Context `{Funext}
          {C D E : BiCategory}
          {F₁ F₂ : LaxFunctor C D}.
  Variable (G : LaxFunctor D E)
           (σ : LaxTransformation F₁ F₂).
  Context `{is_pseudo _ _ G}.

  Definition whisker_R_d
    : LaxTransformation_d (lax_comp G F₁) (lax_comp G F₂).
  Proof.
    make_lax_transformation.
    - exact (fun X => G ₁ (σ X)).
    - intros X Y f ; cbn in *.
      exact ((Fcomp₁_inv G (σ Y) (F₁ ₁ f))
               ∘ (G ₂ (laxnaturality_of σ f))
               ∘ Fcomp₁ G (F₂ ₁ f) (σ X)).
  Defined.

  Definition whisker_R_d_is_lax
    : is_lax_transformation whisker_R_d.
  Proof.
    make_is_lax_transformation.
    - intros X Y f g α ; simpl in *.
      rewrite !vcomp_assoc.
      pose (Fcomp₂ G (F₂ ₂ α) (id₂ (σ X))) as p.
      rewrite Fmor₂_id₂ in p.
      rewrite p ; clear p.
      rewrite <- !vcomp_assoc.
      f_ap.
      rewrite <- (Fmor₂_id₂ G (σ Y)).
      rewrite <- (Fcomp₁_inv_naturality G (id₂ (σ Y)) (F₁ ₂ α)).
      rewrite !vcomp_assoc.
      f_ap.
      rewrite <- (Fmor₂_vcomp G (laxnaturality_of σ f) (id₂ (σ Y) * (F₁ ₂ α))).
      rewrite <- (Fmor₂_vcomp G ((F₂ ₂ α) * id₂ (σ X)) (laxnaturality_of σ g)).
      rewrite laxnaturality_natural.
      reflexivity.
    - intros X ; cbn in *.
      pose (transformation_unit σ X).
      admit.
    - admit.
  Admitted.

  Definition whisker_R
    : LaxTransformation (lax_comp G F₁) (lax_comp G F₂)
    := Build_LaxTransformation whisker_R_d whisker_R_d_is_lax.

  Global Instance whisker_R_is_pseudo
         `{is_pseudo_transformation _ _ _ _ σ}
    : is_pseudo_transformation whisker_R.
  Proof.
    split.
    intros ; cbn in *.
    apply _.
    Defined.
End WhiskerR.