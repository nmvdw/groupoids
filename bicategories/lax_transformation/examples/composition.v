Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     general_category.

Section Composition.
  Context `{Funext}
          {C D : BiCategory}
          {F₁ F₂ F₃ : LaxFunctor C D}.
  Variable (σ₁ : LaxTransformation F₁ F₂) (σ₂ : LaxTransformation F₂ F₃).

  Definition compose_d : LaxTransformation_d F₁ F₃.
  Proof.
    make_lax_transformation.
    - exact (fun X => σ₂ X · σ₁ X).
    - intros X Y f ; cbn in *.
      exact ((assoc_inv (σ₂ Y) (σ₁ Y) (F₁ ₁ f))
               ∘ ((σ₂ Y) ▻ laxnaturality_of σ₁ f)
               ∘ assoc (σ₂ Y) (F₂ ₁ f) (σ₁ X)
               ∘ (laxnaturality_of σ₂ f ◅ (σ₁ X))
               ∘ assoc_inv (F₃ ₁ f) (σ₂ X) (σ₁ X)).
  Defined.

  Definition compose_d_is_lax
    : is_lax_transformation compose_d.
  Admitted.

  Definition compose
    : LaxTransformation F₁ F₃
    := Build_LaxTransformation compose_d compose_d_is_lax.

  Global Instance compose_is_pseudo
         `{is_pseudo_transformation _ _ _ _ σ₁}
         `{is_pseudo_transformation _ _ _ _ σ₂}
    : is_pseudo_transformation compose.
  Proof.
    split.
    apply _.
  Defined.
End Composition.