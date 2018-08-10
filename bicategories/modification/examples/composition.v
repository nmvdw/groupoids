Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     modification.modification.

Section CompositionModification.
  Context {C D : BiCategory}
          {F G : LaxFunctor C D}
          {η₁ η₂ η₃ : LaxTransformation F G}.
  Variable (σ₂ : modification η₂ η₃)
           (σ₁ : modification η₁ η₂).

  Definition comp_modification_d : modification_d η₁ η₃
    := fun A => σ₂ A ∘ σ₁ A.

  Definition comp_modification_is_modification
    : is_modification comp_modification_d.
  Proof.
    intros A B f.
    unfold comp_modification_d, bc_whisker_l, bc_whisker_r in * ; cbn in *.
    rewrite <- (vcomp_left_identity (id₂ (G ₁ f))).
    rewrite <- (vcomp_left_identity (id₂ (F ₁ f))).
    rewrite !interchange.
    rewrite <- !vcomp_assoc.
    rewrite mod_commute.
    rewrite !vcomp_assoc.
    rewrite mod_commute.
    unfold bc_whisker_l, bc_whisker_r.
    reflexivity.
  Qed.

  Definition comp_modification : modification η₁ η₃
    := Build_Modification comp_modification_d comp_modification_is_modification.

  Global Instance comp_modification_pseudo
         `{is_pseudo_modification _ _ _ _ _ _ σ₁}
         `{is_pseudo_modification _ _ _ _ _ _ σ₂}
    : is_pseudo_modification comp_modification.
  Proof.
    split ; apply _.
  Defined.
End CompositionModification.