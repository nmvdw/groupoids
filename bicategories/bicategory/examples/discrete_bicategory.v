Require Import HoTT.
From HoTT.Categories Require Import
     Category Category.Prod NaturalTransformation FunctorCategory DiscreteCategory.
From GR.bicategories Require Import
     general_category bicategory.bicategory bicategory.univalent.

Section DiscreteBiCategory.
  Variable (C : PreCategory).

  Definition discrete_bicategory_d : BiCategory_d.
  Proof.
    make_bicategory.
    - exact C.
    - exact (fun x y => discrete_category (morphism C x y)).
    - intros X ; simpl in *.
      exact 1%morphism.
    - intros X Y Z [g f] ; simpl in *.
      exact (g o f)%morphism.
    - intros X Y Z [f₁ f₂] [g₁ g₂] [p₁ p₂] ; simpl in *.
      exact (ap (fun z => f₁ o z) p₂ @ ap (fun z => z o g₂) p₁)%morphism.
    - intros X Y f ; simpl in *.
      apply left_identity.
    - intros X Y f ; simpl in *.
      exact (left_identity _ _ _ _)^.
    - intros X Y f ; simpl in *.
      apply right_identity.
    - intros X Y f ; simpl in *.
      exact (right_identity _ _ _ _)^.
    - intros W X Y Z h g f ; simpl in *.
      apply associativity.
    - intros W X Y Z h g f ; simpl in *.
      exact (associativity _ _ _ _ _ _ _ _)^.
  Defined.

  Definition discrete_is_bicategory : is_bicategory discrete_bicategory_d.
  Proof.
    make_is_bicategory.
    - reflexivity.
    - intros X Y Z [f₁ f₂] [g₁ g₂] [h₁ h₂] [p₁ p₂] [q₁ q₂] ; simpl in *.
      induction p₁, p₂, q₁, q₂ ; simpl.
      reflexivity.
    - intros X Y f g p ; simpl in *.
      induction p ; simpl.
      exact (concat_1p _ @ (concat_p1 _)^).
    - intros X Y f g p ; simpl in *.
      induction p ; simpl.
      exact (concat_1p _ @ (concat_p1 _)^).
    - intros X Y f g p ; simpl in *.
      induction p ; simpl.
      exact (concat_1p _ @ (concat_p1 _)^).
    - intros X Y f g p ; simpl in *.
      induction p ; simpl.
      exact (concat_1p _ @ (concat_p1 _)^).
    - intros X Y f ; simpl in *.
      exact (concat_Vp _).
    - intros X Y f ; simpl in *.
      exact (concat_pV _).
    - intros X Y f ; simpl in *.
      exact (concat_Vp _).
    - intros X Y f ; simpl in *.
      exact (concat_pV _).
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ p q r ; simpl in *.
      induction p, q, r ; simpl.
      exact (concat_1p _ @ (concat_p1 _)^).
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ p q r ; simpl in *.
      induction p, q, r ; simpl.
      exact (concat_1p _ @ (concat_p1 _)^).
    - intros W X Y Z f g h ; simpl in *.
      exact (concat_Vp _).
    - intros W X Y Z f g h ; simpl in *.
      exact (concat_pV _).
    - intros ; apply path_ishprop.
    - intros ; apply path_ishprop.
  Qed.

  Definition discrete_bicategory : BiCategory
    := Build_BiCategory discrete_bicategory_d discrete_is_bicategory.

  Definition discrete_locally_univalent
    : locally_univalent discrete_bicategory.
  Proof.
    intros X Y f g.
    cbn in *.
    apply isequiv_biinv.
    split.
    - simple refine (_;_).
      + intros iso.
        apply iso.
      + intro p ; cbn in *.
        induction p ; simpl.
        reflexivity.
    - simple refine (_;_).
      + intros iso.
        apply iso.
      + intro iso ; cbn in *.
        destruct iso as [p Hp] ; cbn in *.
        apply path_isomorphic ; cbn.
        induction p ; cbn.
        reflexivity.
  Qed.
End DiscreteBiCategory.