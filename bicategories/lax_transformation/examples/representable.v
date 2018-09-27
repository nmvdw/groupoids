Require Import HoTT.
From HoTT.Categories Require Import Functor NaturalTransformation.
From GR.bicategories Require Import
     bicategory.univalent
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     modification.modification
     general_category
     lax_functor.examples.representable
     lax_transformation.examples.factor_full_sub.
From GR.bicategories.bicategory.examples Require Import
     precat
     cat
     opposite
     pseudo_functors_bicat.

Definition representable1_d
           `{Univalence}
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : PseudoTransformation_d (representable0 X) (representable0 Y).
Proof.
  make_pseudo_transformation.
  - intros Z ; cbn.
    simple refine (Build_Functor _ _ _ _ _ _).
    + intros h ; simpl in *.
      exact (f · h).
    + intros h₁ h₂ α ; simpl in *.
      exact(f ◅ α).
    + intros ; simpl in *.
      apply bc_whisker_l_compose.
    + intros ; simpl in *.
      apply hcomp_id₂.
  - intros Z₁ Z₂ h.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros ; cbn in *.
      apply assoc.
    + intros ; cbn in *.
      apply assoc_natural.
  - intros Z₁ Z₂ h.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros ; cbn in *.
      apply assoc_inv.
    + intros ; cbn in *.
      apply assoc_inv_natural.
Defined.

Definition representable1_is_pseudo
           `{Univalence}
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : is_pseudo_transformation_p (representable1_d f).
Proof.
  make_is_pseudo_transformation.
  - intros Z₁ Z₂ g₁ g₂ α.
    apply path_natural_transformation.
    intros h ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite hcomp_id₂, !left_identity, !right_identity.
    rewrite <- hcomp_id₂.
    apply assoc_natural.
  - intros Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    rewrite !right_identity, left_identity.
    rewrite right_unit_inv_assoc.
    rewrite <- associativity.
    rewrite <- inverse_of_assoc, right_inverse.
    apply left_identity.
  - intros Z₁ Z₂ Z₃ g₁ g₂.
    apply path_natural_transformation.
    intros h ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite !hcomp_id₂.
    rewrite !left_identity, !right_identity.
    apply pentagon.
  - intros Z₁ Z₂ g.
    apply path_natural_transformation.
    intros h ; cbn in *.
    apply assoc_left.
  - intros Z₁ Z₂ g.
    apply path_natural_transformation.
    intros h ; cbn in *.
    apply assoc_right.
Qed.

Definition representable1
           `{Univalence}
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : PseudoTransformation (representable0 X) (representable0 Y)
  := Build_PseudoTransformation (representable1_d f) (representable1_is_pseudo f).