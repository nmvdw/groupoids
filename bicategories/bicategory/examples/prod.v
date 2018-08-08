Require Import HoTT.
From HoTT.Categories Require Import
     Category Category.Prod NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category bicategory.bicategory.

Local Notation "x ₁" := (Datatypes.fst x) (at level 80).
Local Notation "x ₂" := (Datatypes.snd x) (at level 80).

Section ProductBicategory.
  Context `{Univalence}.
  Variable (C D : BiCategory).

  Definition prod_d : BiCategory_d.
  Proof.
    make_bicategory.
    - exact (Datatypes.prod (Obj C) (Obj D)).
    - exact (fun x y => Category.Prod.prod (C⟦x ₁ , y ₁⟧) (D⟦x ₂ ,y ₂⟧)).
    - exact (fun X => (id₁ (X ₁), id₁ (X ₂))).
    - intros [X₁ X₂] [Y₁ Y₂] [Z₁ Z₂] [[g₁ g₂] [f₁ f₂]] ; simpl in *.
      exact (g₁ · f₁,g₂ · f₂).
    - intros [X₁ X₂] [Y₁ Y₂] [Z₁ Z₂]
             [[f₁ f₂] [f₃ f₄]] [[g₁ g₂] [g₃ g₄]]
             [[η₁ η₂] [η₃ η₄]] ; simpl in *.
      exact (η₁ * η₃,η₂ * η₄).
    - intros [X₁ X₂] [Y₁ Y₂] [f₁ f₂] ; simpl in *.
      split ; apply left_unit.
    - intros [X₁ X₂] [Y₁ Y₂] [f₁ f₂] ; simpl in *.
      split ; apply left_unit_inv.
    - intros [X₁ X₂] [Y₁ Y₂] [f₁ f₂] ; simpl in *.
      split ; apply right_unit.
    - intros [X₁ X₂] [Y₁ Y₂] [f₁ f₂] ; simpl in *.
      split ; apply right_unit_inv.
    - intros [W₁ W₂] [X₁ X₂] [Y₁ Y₂] [Z₁ Z₂] [h₁ h₂] [g₁ g₂] [f₁ f₂] ; simpl in *.
      split ; apply assoc.
    - intros [W₁ W₂] [X₁ X₂] [Y₁ Y₂] [Z₁ Z₂] [h₁ h₂] [g₁ g₂] [f₁ f₂] ; simpl in *.
      split ; apply assoc_inv.
  Defined.

  Definition prod_is_bicategory : is_bicategory prod_d.
  Proof.
    make_is_bicategory ; intros ; simpl in *.
    - apply path_prod ; apply hcomp_id₂.
    - apply path_prod ; apply interchange.
    - apply path_prod ; apply left_unit_natural.
    - apply path_prod ; apply left_unit_inv_natural.
    - apply path_prod ; apply right_unit_natural.
    - apply path_prod ; apply right_unit_inv_natural.
    - apply path_prod ; apply left_unit_left.
    - apply path_prod ; apply left_unit_right.
    - apply path_prod ; apply right_unit_left.
    - apply path_prod ; apply right_unit_right.
    - apply path_prod ; apply assoc_natural.
    - apply path_prod ; apply assoc_inv_natural.
    - apply path_prod ; apply assoc_left.
    - apply path_prod ; apply assoc_right.
    - apply path_prod ; apply triangle_r.
    - apply path_prod ; apply pentagon.
  Qed.

  Definition prod : BiCategory
    := Build_BiCategory prod_d prod_is_bicategory.
End ProductBicategory.
