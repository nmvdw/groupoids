Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.examples.identity
     lax_transformation.examples.composition
     modification.modification.

Section RightIdentityInv.
  Context `{Univalence}
          {C D : BiCategory}
          {F₁ F₂ : LaxFunctor C D}.
  Variable (η : LaxTransformation F₁ F₂).

  Local Notation right_identity_inv_mod_d
    := (fun (A : C) => right_unit_inv (η A) : η A ==> compose (identity_transformation F₁) η A).

  Definition right_identity_inv_is_mod : is_modification right_identity_inv_mod_d.
  Proof.
    intros A B f ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite !vcomp_assoc.
    rewrite <- (vcomp_left_identity (id₂ (η B))).
    rewrite interchange.
    rewrite !vcomp_assoc.
    rewrite <- right_unit_inv_assoc.
    rewrite (ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    pose @right_unit_assoc as p.
    unfold bc_whisker_r in p.
    rewrite <- p ; clear p.
    rewrite (ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    rewrite right_unit_natural.
    rewrite !vcomp_assoc.
    rewrite right_unit_left.
    rewrite <- vcomp_assoc.
    rewrite triangle_r_inv.
    rewrite !vcomp_assoc, vcomp_right_identity.
    reflexivity.
  Qed.

  Definition right_identity_inv_mod
    : PseudoModification η (composition.compose (identity_transformation F₁) η).
  Proof.
    make_pseudo_modification.
    - exact (Build_Modification right_identity_inv_mod_d right_identity_inv_is_mod).
    - intros X ; cbn.
      apply _.
  Defined.
End RightIdentityInv.
