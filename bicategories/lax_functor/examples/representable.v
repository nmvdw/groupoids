Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.bicategory_laws
     lax_functor.lax_functor
     general_category.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories.bicategory.examples Require Import
     precat
     opposite.

Definition representable_d
           `{Univalence}
           {C : BiCategory}
           (X : C)
  : PseudoFunctor_d (op C) PreCat.
Proof.
  make_pseudo_functor.
  - exact (fun Y => C⟦Y,X⟧).
  - intros Y₁ Y₂ f ; cbn in *.
    simple refine (Build_Functor _ _ _ _ _ _).
    + exact (fun g => g · f).
    + intros g₁ g₂ α ; cbn.
      exact (α ◅ f).
    + intros g₁ g₂ g₃ α₁ α₂ ; cbn in *.
      pose @interchange as p.
      unfold bc_whisker_l, vcomp in *.
      rewrite <- p.
      rewrite left_identity.
      reflexivity.
    + intros g ; cbn in *.
      apply hcomp_id₂.
  - intros Y₁ Y₂ f g α ; cbn in *.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros h ; cbn in *.
      exact (h ▻ α).
    + intros h₁ h₂ β ; cbn in *.
      pose @interchange as p.
      unfold bc_whisker_r, bc_whisker_l, vcomp in *.
      rewrite <- !p.
      rewrite !left_identity, !right_identity.
      reflexivity.
  - intros Y₁ Y₂ Y₃ g f ; cbn in *.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros h ; cbn in *.
      exact (assoc h f g).
    + intros h₁ h₂ β ; cbn in *.
      pose @assoc_natural as p.
      unfold bc_whisker_r, bc_whisker_l, vcomp in *.
      rewrite p.
      rewrite hcomp_id₂.
      reflexivity.
  - intros Y ; cbn in *.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros f ; cbn in *.
      exact (right_unit_inv f).
    + intros f₁ f₂ α ; cbn in *.
      apply right_unit_inv_natural.
  - intros Y₁ Y₂ Y₃ g f ; cbn in *.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros h ; cbn in *.
      exact (assoc_inv h f g).
    + intros h₁ h₂ α ; cbn in *.
      pose @assoc_inv_natural as p.
      unfold bc_whisker_r, bc_whisker_l, vcomp in *.
      rewrite <- p.
      rewrite hcomp_id₂.
      reflexivity.
  - intros Y ; cbn in *.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros f ; cbn in *.
      exact (right_unit f).
    + intros f₁ f₂ α ; cbn in *.
      apply right_unit_natural.
Defined.

Definition representable_d_is_pseudo
           `{Univalence}
           {C : BiCategory}
           (X : C)
  : is_pseudo_functor_p (representable_d X).
Proof.
  make_is_pseudo.
  - intros Y₁ Y₂ f.
    apply path_natural_transformation.
    intro g ; cbn in *.
    unfold bc_whisker_r.
    exact (hcomp_id₂ g f).
  - intros Y₁ Y₂ f g h α β.
    apply path_natural_transformation.
    intro k ; cbn in *.
    pose @interchange as p.
    unfold vcomp in p.
    rewrite <- p.
    rewrite left_identity.
    reflexivity.
  - intros Y₁ Y₂ Y₃ f₁ f₂ g₁ g₂ α β.
    apply path_natural_transformation.
    intro k ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r.
    pose @interchange as p.
    unfold vcomp in p.
    rewrite <- p ; clear p.
    rewrite left_identity, right_identity.
    apply assoc_natural.
  - intros Y₁ Y₂ f.
    apply path_natural_transformation.
    intro g ; cbn in *.
    unfold bc_whisker_r, bc_whisker_l.
    rewrite left_identity.
    pose @triangle_r.
    unfold vcomp in p.
    rewrite <- p ; clear p.
    pose @interchange.
    unfold vcomp in p.
    rewrite <- p.
    rewrite <- inverse_of_right_unit, right_inverse, left_identity.
    symmetry ; apply hcomp_id₂.
  - intros Y₁ Y₂ f.
    apply path_natural_transformation.
    intro g ; cbn in *.
    pose @right_unit_assoc as p.
    unfold bc_whisker_r, bc_whisker_l, vcomp in *.
    rewrite right_identity.
    rewrite <- p ; clear p.
    rewrite <- inverse_of_right_unit, right_inverse.
    reflexivity.
  - intros Y₁ Y₂ Y₃ Y₄ h g f.
    apply path_natural_transformation.
    intros k ; cbn.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite !hcomp_id₂, left_identity, !right_identity.
    apply pentagon_2.
  - intros Y₁ Y₂ Y₃ g f.
    apply path_natural_transformation.
    intros k ; cbn in *.
    apply assoc_right.
  - intros Y₁ Y₂ Y₃ g f.
    apply path_natural_transformation.
    intros k ; cbn in *.
    apply assoc_left.
  - intros Y.
    apply path_natural_transformation.
    intros k ; cbn in *.
    apply right_unit_right.
  - intros Y.
    apply path_natural_transformation.
    intros k ; cbn in *.
    apply right_unit_left.
Qed.

Definition representable
           `{Univalence}
           {C : BiCategory}
           (X : C)
  : LaxFunctor (op C) PreCat
  := Build_PseudoFunctor (representable_d X) (representable_d_is_pseudo X).

Global Instance representable_is_pseudo
       `{Univalence}
       {C : BiCategory}
       (X : C)
  : is_pseudo (representable X)
  := _.