Require Import HoTT.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.lax_functor
     lax_functor.examples.factor_full_sub
     lax_transformation.lax_transformation
     lax_transformation.examples.composition
     lax_transformation.examples.factor_full_sub
     modification.modification
     modification.examples.composition.

Section FactorCompModification.
  Context `{Univalence}
          {C D : BiCategory}
          {F₁ F₂ F₃ : PseudoFunctor C D}.
  Variable (P : D -> hProp)
           (FP₁ : forall (X : C), P(F₁ X))
           (FP₂ : forall (X : C), P(F₂ X))
           (FP₃ : forall (X : C), P(F₃ X))
           (η₁ : LaxTransformation F₁ F₂)
           (η₂ : LaxTransformation F₂ F₃).

  Definition factor_comp_modification_d
    : Modification_d
        (compose (lax_factor_transformation P η₁ FP₁ FP₂)
                 (lax_factor_transformation P η₂ FP₂ FP₃))
        (lax_factor_transformation P (compose η₁ η₂) FP₁ FP₃)
    := fun _ => id₂ _.

  Definition factor_comp_modification_is_modification
    : is_modification factor_comp_modification_d.
  Proof.
    intros X Y f.
    unfold factor_comp_modification_d ; cbn.
    rewrite (hcomp_id₂ (F₃ ₁ f)).
    rewrite (hcomp_id₂ _ (F₁ ₁ f)).
    refine (vcomp_right_identity _ @ _ @ (vcomp_left_identity _)^).
    reflexivity.
  Qed.

  Definition factor_comp_modification
    : IsoModification
        (compose (lax_factor_transformation P η₁ FP₁ FP₂)
                 (lax_factor_transformation P η₂ FP₂ FP₃))
        (lax_factor_transformation P (compose η₁ η₂) FP₁ FP₃).
  Proof.
    exists (Build_Modification
              factor_comp_modification_d
              factor_comp_modification_is_modification).
    intros X ; apply _.
  Defined.
End FactorCompModification.