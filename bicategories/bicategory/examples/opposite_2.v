Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category.
From GR.bicategories.bicategory Require Import
     bicategory bicategory_laws univalent.

Section OpBiCategory.
  Variable (C : BiCategory).

  Definition op₂_hom (X Y : C) : PreCategory
    := @Build_PreCategory
         (C⟦X,Y⟧)
         (fun f g => g ==> f)
         (fun f => id₂ f)
         (fun _ _ _ α β => β ∘ α)
         (fun _ _ _ _ α β γ => (vcomp_assoc α β γ)^)
         (fun _ _ α => vcomp_right_identity α)
         (fun _ _ β => vcomp_left_identity β)
         _.

  Definition op2_d : BiCategory_d.
  Proof.
    make_bicategory.
    - exact C.
    - exact op₂_hom.
    - exact (fun X => id₁ X).
    - intros X Y Z [f₁ f₂] ; cbn.
      exact (f₁ · f₂).
    - intros X Y Z [f₁ f₂] [g₁ g₂] [η₁ η₂] ; simpl in *.
      exact (η₁ * η₂).
    - intros X Y f ; simpl in *.
      apply left_unit_inv .
    - intros X Y f ; simpl in *.
      apply left_unit.
    - intros X Y f ; simpl in *.
      apply right_unit_inv.
    - intros X Y f ; simpl in *.
      apply right_unit.
    - intros W X Y Z h g f ; simpl in *.
      apply assoc_inv.
    - intros W X Y Z h g f ; simpl in *.
      apply assoc.
  Defined.

  Definition op2_is_bicategory : is_bicategory op2_d.
  Proof.
    make_is_bicategory.
    - intros X Y Z [g f] ; simpl in *.
      apply hcomp_id₂.
    - intros X Y Z [f₁ f₂] [g₁ g₂] [h₁ h₂] [η₁ η₂] [ε₁ ε₂] ; simpl in *.
      apply interchange.
    - intros X Y f g η ; simpl in *.
      exact (left_unit_inv_natural _)^.
    - intros X Y f g η ; simpl in *.
      exact (left_unit_natural _)^.
    - intros X Y f g η ; simpl in *.
      exact (right_unit_inv_natural _)^.
    - intros X Y f g η ; simpl in *.
      exact (right_unit_natural _)^.
    - intros X Y f ; simpl in *.
      apply left_unit_left.
    - intros X Y f ; simpl in *.
      apply left_unit_right.
    - intros X Y f ; simpl in *.
      apply right_unit_left.
    - intros X Y f ; simpl in *.
      apply right_unit_right.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ ηh ηg ηf ; simpl in *.
      exact (assoc_inv_natural _ _ _)^.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ ηh ηg ηf ; simpl in *.
      exact (assoc_natural _ _ _)^.
    - intros W X Y Z f g h ; simpl in *.
      apply assoc_left.
    - intros W X Y Z f g h ; simpl in *.
      apply assoc_right.
    - intros X Y Z g f ; simpl in *.
      apply triangle_r_inv.
    - intros V W X Y Z k h g f ; simpl in *.
      rewrite <- !vcomp_assoc.
      apply inverse_pentagon.
  Qed.

  Definition op2 : BiCategory
    := Build_BiCategory op2_d op2_is_bicategory.
End OpBiCategory.