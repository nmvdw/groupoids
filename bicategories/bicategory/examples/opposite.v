Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category.
From GR.bicategories.bicategory Require Import
     bicategory bicategory_laws.

Section OpBiCategory.
  Context `{Univalence}.
  Variable (C : BiCategory).

  Definition op_d : BiCategory_d.
  Proof.
    make_bicategory.
    - exact C.
    - exact (fun X Y => C⟦Y,X⟧).
    - exact (fun X => id₁ X).
    - intros X Y Z [f₁ f₂] ; cbn.
      exact (f₂ · f₁).
    - intros X Y Z [f₁ f₂] [g₁ g₂] [η₁ η₂] ; simpl in *.
      exact (η₂ * η₁).
    - intros X Y f ; simpl in *.
      apply right_unit .
    - intros X Y f ; simpl in *.
      apply right_unit_inv.
    - intros X Y f ; simpl in *.
      apply left_unit.
    - intros X Y f ; simpl in *.
      apply left_unit_inv.
    - intros W X Y Z h g f ; simpl in *.
      apply assoc_inv.
    - intros W X Y Z h g f ; simpl in *.
      apply assoc.
  Defined.

  Definition op_is_bicategory : is_bicategory op_d.
  Proof.
    make_is_bicategory.
    - intros X Y Z f ; simpl in *.
      apply hcomp_id₂.
    - intros X Y Z [f₁ f₂] [g₁ g₂] [h₁ h₂] [η₁ η₂] [ε₁ ε₂] ; simpl in *.
      apply interchange.
    - intros X Y f g η ; simpl in *.
      apply right_unit_natural.
    - intros X Y f g η ; simpl in *.
      apply right_unit_inv_natural.
    - intros X Y f g η ; simpl in *.
      apply left_unit_natural.
    - intros X Y f g η ; simpl in *.
      apply left_unit_inv_natural.
    - intros X Y f ; simpl in *.
      apply right_unit_left.
    - intros X Y f ; simpl in *.
      apply right_unit_right.
    - intros X Y f ; simpl in *.
      apply left_unit_left.
    - intros X Y f ; simpl in *.
      apply left_unit_right.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ ηh ηg ηf ; simpl in *.
      apply assoc_inv_natural.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ ηh ηg ηf ; simpl in *.
      apply assoc_natural.
    - intros W X Y Z f g h ; simpl in *.
      apply assoc_right.
    - intros W X Y Z f g h ; simpl in *.
      apply assoc_left.
    - intros X Y Z g f ; simpl in *.
      exact (triangle_l f g)^.
    - intros W V X Y Z k h g f ; simpl in *.
      rewrite <- !inverse_of_assoc.
      rewrite <- !inverse_id.
      rewrite <- !hcomp_inverse.
      rewrite <- !inverse_compose.
      apply path_inverse.
      pose (pentagon f g h k) as p.
      refine (p @ _).
      apply associativity.
  Qed.

  Definition op (C : BiCategory) : BiCategory
    := Build_BiCategory op_d op_is_bicategory.
End OpBiCategory.