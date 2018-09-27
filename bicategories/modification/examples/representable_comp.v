Require Import HoTT.
From HoTT.Categories Require Import Functor NaturalTransformation.
From GR.bicategories Require Import
     bicategory.univalent
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.examples.composition
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

Section RepresentableComp.
  Context `{Univalence}
          {C : BiCategory}
          {X₁ X₂ X₃ : C}.
  Variable (g : C⟦X₂,X₃⟧)
           (f : C⟦X₁,X₂⟧).

  Definition representable_comp_d
    : Modification_d
        (composition.compose (representable1 f) (representable1 g))
        (representable1 (g · f)).
  Proof.
    intros Z.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; cbn in *.
      apply assoc_inv.
    - intros h₁ h₂ α ; cbn in *.
      unfold bc_whisker_l.
      rewrite <- hcomp_id₂.
      apply assoc_inv_natural.
  Defined.

  Definition representable_comp_is_modification
    : is_modification representable_comp_d.
  Proof.
    intros Z₁ Z₂ h.
    apply path_natural_transformation.
    intros φ ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite !hcomp_id₂, !left_identity, !right_identity.
    rewrite <- !associativity.
    apply inverse_pentagon_5.
  Qed.

  Definition representable_comp
    : Modification
        (composition.compose (representable1 f) (representable1 g))
        (representable1 (g · f))
    := Build_Modification representable_comp_d representable_comp_is_modification.
End RepresentableComp.

Section RepresentableCompInv.
  Context `{Univalence}
          {C : BiCategory}
          {X₁ X₂ X₃ : C}.
  Variable (g : C⟦X₂,X₃⟧)
           (f : C⟦X₁,X₂⟧).

  Definition representable_comp_inv_d
    : Modification_d
        (representable1 (g · f))
        (composition.compose (representable1 f) (representable1 g)).
  Proof.
    intros Z.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; cbn in *.
      apply assoc.
    - intros h₁ h₂ α ; cbn in *.
      unfold bc_whisker_l.
      rewrite <- hcomp_id₂.
      apply assoc_natural.
  Defined.

  Definition representable_comp_inv_is_modification
    : is_modification representable_comp_inv_d.
  Proof.
    intros Z₁ Z₂ h.
    apply path_natural_transformation.
    intros φ ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite !hcomp_id₂, !left_identity, !right_identity.
    symmetry.
    apply pentagon.
  Qed.

  Definition representable_comp_inv
    : Modification
        (representable1 (g · f))
        (composition.compose (representable1 f) (representable1 g))
    := Build_Modification representable_comp_inv_d representable_comp_inv_is_modification.
End RepresentableCompInv.