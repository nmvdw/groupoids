Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.examples.identity
     lax_transformation.examples.composition
     modification.modification
     general_category.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.

Section WhiskerL.
  Context `{Univalence}
          {C D : BiCategory}
          {F₁ F₂ F₃ : LaxFunctor C D}
          {η₁ η₂ : LaxTransformation F₂ F₃}.
  Variable (ε : LaxTransformation F₁ F₂)
           (m : modification η₁ η₂).

  Definition whisker_L_mod_d
    : modification_d (composition.compose ε η₁) (composition.compose ε η₂)
    := fun A => m A ◅ ε A.

  Definition whisker_L_is_mod
    : is_modification whisker_L_mod_d.
  Proof.
    intros A B f ; cbn in *.
    unfold whisker_L_mod_d, bc_whisker_l, bc_whisker_r.
    rewrite <- !vcomp_assoc.
    rewrite <- assoc_inv_natural.
    rewrite !vcomp_assoc.
    f_ap.
    rewrite assoc_inv_natural.
    rewrite <- !vcomp_assoc.
    rewrite hcomp_id₂.    
    f_ap.
    rewrite !vcomp_assoc.
    rewrite <- !interchange.
    rewrite (mod_commute m f).
    unfold bc_whisker_l.
    rewrite !vcomp_right_identity.
    rewrite <- !vcomp_assoc.
    rewrite <- interchange.
    rewrite vcomp_right_identity, vcomp_left_identity.
    rewrite !vcomp_assoc.
    rewrite <- (vcomp_left_identity (id₂ (ε A))).
    rewrite !interchange.
    rewrite <- !vcomp_assoc.
    rewrite vcomp_left_identity.
    f_ap.
    rewrite !vcomp_assoc.
    rewrite assoc_natural.
    rewrite <- !vcomp_assoc.
    f_ap.
    rewrite <- interchange.
    rewrite hcomp_id₂, vcomp_left_identity, vcomp_right_identity.
    reflexivity.
  Qed.

  Definition whisker_L_mod
    : modification (composition.compose ε η₁) (composition.compose ε η₂)
    := Build_Modification whisker_L_mod_d whisker_L_is_mod.

  Global Instance whisker_L_mod_pseudo
         `{is_pseudo_modification _ _ _ _ _ _ m}
    : is_pseudo_modification whisker_L_mod.
  Proof.
    split ; apply _.
  Defined.
End WhiskerL.