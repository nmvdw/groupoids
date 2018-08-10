Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.examples.identity
     lax_transformation.examples.composition
     modification.modification
     general_category.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.

Section LeftIdentityInv.
  Context `{Univalence}
          {C D : BiCategory}
          {F₁ F₂ : LaxFunctor C D}.
  Variable (η : LaxTransformation F₁ F₂).

  Definition left_identity_inv_mod_d
    : modification_d η (composition.compose η (identity_transformation F₂))
    := fun A => left_unit_inv (η A).

  Definition left_identity_inv_is_mod : is_modification left_identity_inv_mod_d.
  Proof.
    intros A B f ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r, left_identity_inv_mod_d.
    rewrite !vcomp_assoc.
    rewrite <- (vcomp_left_identity (id₂ (η A))).
    rewrite interchange.
    rewrite !vcomp_assoc.
    rewrite triangle_r.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ (_ ∘ (_ ∘ z))))) (vcomp_assoc _ _ _)^).
    rewrite assoc_left.
    rewrite vcomp_left_identity.
    rewrite <- !vcomp_assoc.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    pose @left_unit_inv_assoc as p.
    unfold bc_whisker_l in p.
    rewrite p ; clear p.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    rewrite assoc_left.
    rewrite vcomp_left_identity.
    rewrite !vcomp_assoc.
    rewrite <- interchange.
    rewrite left_unit_left.
    rewrite vcomp_left_identity, hcomp_id₂, vcomp_right_identity.
    rewrite <- left_unit_inv_natural.
    rewrite <- !vcomp_assoc.
    rewrite <- left_unit_inv_assoc.
    reflexivity.
  Qed.

  Definition left_identity_inv_mod
    : modification η (composition.compose η (identity_transformation F₂))
    := Build_Modification left_identity_inv_mod_d left_identity_inv_is_mod.

  Global Instance left_identity_inv_mod_pseudo
    : is_pseudo_modification left_identity_inv_mod.
  Proof.
    split ; apply _.
  Defined.
End LeftIdentityInv.