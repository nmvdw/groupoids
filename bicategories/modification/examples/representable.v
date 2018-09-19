Require Import HoTT.
From HoTT.Categories Require Import Functor NaturalTransformation.
From GR.bicategories Require Import
     bicategory.univalent
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     modification.modification
     modification.examples.factor_full_sub
     general_category
     lax_functor.examples.representable
     lax_transformation.examples.representable.
From GR.bicategories.bicategory.examples Require Import
     precat
     cat
     opposite
     pseudo_functors_bicat.

Section RepresentableModification.
  Context `{Univalence}
          {C : BiCategory}
          {X Y : C}
          {f g : C⟦X,Y⟧}.
  Variable (α : f ==> g).

  Definition representable2_d
    : Modification_d (representable1 f) (representable1 g).
  Proof.
    intros Z.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; cbn in *.
      exact (α ▻ h).
    - intros Z₁ Z₂ h ; cbn in *.
      pose @interchange as p.
      unfold bc_whisker_l, bc_whisker_r, vcomp in *.
      rewrite <- !p.
      rewrite !left_identity, !right_identity.
      reflexivity.
  Defined.

  Definition representable2_is_modification
    : is_modification representable2_d.
  Proof.
    intros Z₁ Z₂ h.
    apply path_natural_transformation.
    intros φ ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite hcomp_id₂, left_identity, right_identity.
    rewrite <- hcomp_id₂.
    apply assoc_natural.
  Qed.

  Definition representable2
    : Modification (representable1 f) (representable1 g)
    := Build_Modification representable2_d representable2_is_modification.
End RepresentableModification.

Definition univalent_representable2
           `{Univalence}
           {C : BiCategory}
           `{LocallyUnivalent C}
           {X Y : C}
           {f g : C⟦X,Y⟧}
           (α : f ==> g)
  : Modification (univalent_representable1 f) (univalent_representable1 g)
  := factor_modification _ (representable2 α) _ _.
