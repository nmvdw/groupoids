Require Import HoTT.
From GR.bicategories Require Import
     general_category bicategory.bicategory.

Section ArrowSubcategory.
  Variable (C : BiCategory)
           (P : forall (X Y : C), C⟦X,Y⟧ -> hProp)
           (Pid : forall (X : C), P X X (id₁ X))
           (Pcomp : forall (X Y Z : C) (f : C⟦X,Y⟧) (g : C⟦Y,Z⟧),
               P X Y f -> P Y Z g -> P X Z (g · f)).

  Definition arrow_subcat_morphisms (X Y : C) : PreCategory.
  Proof.
    simple refine (@Build_PreCategory
                     {f : C⟦X,Y⟧ & P X Y f}
                     (fun f g => morphism (C⟦X,Y⟧) f.1 g.1)
                     _ _ _ _ _ _).
    - intros [f Hf] ; simpl in *.
      exact (id₂ f).
    - intros [f Hf] [g Hg] [h Hh] α β ; simpl in *.
      exact (α ∘ β).
    - intros [f₁ Hf₁] [f₂ Hf₂] [f₃ Hf₃] [f₄ Hf₄] α₁ α₂ α₃ ; simpl in *.
      apply vcomp_assoc.
    - intros [f Hf] [g Hg] α ; simpl in *.
      apply vcomp_left_identity.
    - intros [f Hf] [g Hg] α ; simpl in *.
      apply vcomp_right_identity.
  Defined.

  Definition arrow_subcat_d : BiCategory_d.
  Proof.
    make_bicategory.
    - exact C.
    - intros X Y.
      exact (arrow_subcat_morphisms X Y).
    - intros X ; simpl in *.
      exact (id₁ X;Pid X).
    - intros X Y Z [[f Hf] [g Hg]] ; simpl in *.
      exact (f · g;Pcomp X Y Z g f Hg Hf).
    - intros X Y Z [[f₁ Hf₁] [g₁ Hg₁]] [[f₂ Hf₂] [g₂ Hg₂]] [α β] ; simpl in *.
      exact (α * β).
    - intros X Y [f Hf] ; simpl in *.
      exact (left_unit f).
    - intros X Y [f Hf] ; simpl in *.
      exact (left_unit_inv f).
    - intros X Y [f Hf] ; simpl in *.
      exact (right_unit f).
    - intros X Y [f Hf] ; simpl in *.
      exact (right_unit_inv f).
    - intros W X Y Z [h Hh] [g Hg] [f Hf] ; simpl in *.
      exact (assoc h g f).
    - intros W X Y Z [h Hh] [g Hg] [f Hf] ; simpl in *.
      exact (assoc_inv h g f).
  Defined.

  Definition arrow_subcat_is_bicategory : is_bicategory arrow_subcat_d.
  Proof.
    make_is_bicategory.
    - intros X Y Z [[f Hf] [g Hg]] ; simpl in *.
      exact (hcomp_id₂ f g).
    - intros X Y Z
             [[f₁ Hf₁] [g₁ Hg₁]] [[f₂ Hf₂] [g₂ Hg₂]] [[f₃ Hf₃] [g₃ Hg₃]]
             [α₁ α₂] [β₁ β₂]
      ; simpl in *.
      apply interchange.
    - intros X Y f g α ; simpl in *.
      apply left_unit_natural.
    - intros X Y f g α ; simpl in *.
      apply left_unit_inv_natural.
    - intros X Y f g α ; simpl in *.
      apply right_unit_natural.
    - intros X Y f g α ; simpl in *.
      apply right_unit_inv_natural.
    - intros X Y f ; simpl in *.
      apply left_unit_left.
    - intros X Y f ; simpl in *.
      apply left_unit_right.
    - intros X Y f ; simpl in *.
      apply right_unit_left.
    - intros X Y f ; simpl in *.
      apply right_unit_right.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ ηh ηg ηf ; simpl in *.
      apply assoc_natural.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ ηh ηg ηf ; simpl in *.
      apply assoc_inv_natural.
    - intros W X Y Z f g h ; simpl in *.
      apply assoc_left.
    - intros W X Y Z f g h ; simpl in *.
      apply assoc_right.
    - intros X Y Z g f ; simpl in *.
      apply triangle_r.
    - intros V W X Y Z k h g f ; simpl in *.
      apply pentagon.
  Qed.

  Definition arrow_subcat : BiCategory
    := Build_BiCategory arrow_subcat_d arrow_subcat_is_bicategory.
End ArrowSubcategory.