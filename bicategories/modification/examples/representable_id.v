Require Import HoTT.
From HoTT.Categories Require Import Functor NaturalTransformation.
From GR.bicategories Require Import
     bicategory.univalent
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.examples.identity
     modification.modification
     general_category
     lax_functor.examples.representable
     lax_transformation.examples.representable
     modification.examples.representable.
From GR.bicategories.bicategory.examples Require Import
     precat
     cat
     opposite
     pseudo_functors_bicat.

Section RepresentableId.
  Context `{Univalence}
          {C : BiCategory}.
  Variable (X : C).

  Definition representable_id_d
    : Modification_d (identity_transformation _) (representable1 (id₁ X)).
  Proof.
    intros Y.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; cbn in *.
      exact (left_unit_inv h).
    - intros h₁ h₂ α ; cbn in *.
      apply left_unit_inv_natural.
  Defined.

  Definition representable_id_is_modification
    : is_modification representable_id_d.
  Proof.
    intros Y₁ Y₂ f.
    apply path_natural_transformation.
    intros h ; cbn in *.
    rewrite !left_identity, !right_identity.
    rewrite left_unit_inv_assoc.
    rewrite <- associativity.
    rewrite <- inverse_of_assoc, right_inverse.
    apply left_identity.
  Qed.

  Definition representable_id
    : Modification (identity_transformation _) (representable1 (id₁ X))
    := Build_Modification representable_id_d representable_id_is_modification.
End RepresentableId.

Section RepresentableIdInv.
  Context `{Univalence}
          {C : BiCategory}.
  Variable (X : C).

  Definition representable_id_inv_d
    : Modification_d (representable1 (id₁ X)) (identity_transformation _).
  Proof.
    intros Y.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; cbn in *.
      exact (left_unit h).
    - intros h₁ h₂ α ; cbn in *.
      apply left_unit_natural.
  Defined.

  Definition representable_id_inv_is_modification
    : is_modification representable_id_inv_d.
  Proof.
    intros Y₁ Y₂ f.
    apply path_natural_transformation.
    intros h ; cbn in *.
    unfold bc_whisker_l.
    rewrite hcomp_id₂, !left_identity, !right_identity.
    apply left_unit_assoc.
  Qed.

  Definition representable_id_inv
    : Modification (representable1 (id₁ X)) (identity_transformation _)
    := Build_Modification representable_id_inv_d representable_id_inv_is_modification.
End RepresentableIdInv.

Section UnivalentRepresentableId.
  Context `{Univalence}
          {C : BiCategory}
          `{LocallyUnivalent C}.
  Variable (X : C).

  Definition univalent_representable_id_d
    : Modification_d (identity_transformation _) (univalent_representable1 (id₁ X)).
  Proof.
    intros Y.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; cbn in *.
      exact (left_unit_inv h).
    - intros h₁ h₂ α ; cbn in *.
      apply left_unit_inv_natural.
  Defined.

  Definition univalent_representable_id_is_modification
    : is_modification univalent_representable_id_d.
  Proof.
    intros Y₁ Y₂ f.
    apply path_natural_transformation.
    intros h ; cbn in *.
    rewrite !left_identity, !right_identity.
    rewrite left_unit_inv_assoc.
    rewrite <- associativity.
    rewrite <- inverse_of_assoc, right_inverse.
    apply left_identity.
  Qed.

  Definition univalent_representable_id
    : Modification (identity_transformation _) (univalent_representable1 (id₁ X))
    := Build_Modification
         univalent_representable_id_d
         univalent_representable_id_is_modification.
End UnivalentRepresentableId.

Section UnivalentRepresentableIdInv.
  Context `{Univalence}
          {C : BiCategory}
          `{LocallyUnivalent C}.
  Variable (X : C).

  Definition univalent_representable_id_inv_d
    : Modification_d (univalent_representable1 (id₁ X)) (identity_transformation _).
  Proof.
    intros Y.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; cbn in *.
      exact (left_unit h).
    - intros h₁ h₂ α ; cbn in *.
      apply left_unit_natural.
  Defined.

  Definition univalent_representable_id_inv_is_modification
    : is_modification univalent_representable_id_inv_d.
  Proof.
    intros Y₁ Y₂ f.
    apply path_natural_transformation.
    intros h ; cbn in *.
    unfold bc_whisker_l.
    rewrite hcomp_id₂, !left_identity, !right_identity.
    apply left_unit_assoc.
  Qed.

  Definition univalent_representable_id_inv
    : Modification (univalent_representable1 (id₁ X)) (identity_transformation _)
    := Build_Modification
         univalent_representable_id_inv_d
         univalent_representable_id_inv_is_modification.
End UnivalentRepresentableIdInv.