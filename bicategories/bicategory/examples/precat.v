Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category bicategory.bicategory.

Section CatBiCategory.
  Context `{Funext}.

  Definition precat_d : BiCategory_d.
  Proof.
    make_bicategory.
    - exact PreCategory.
    - exact functor_category.
    - exact (fun _ => 1%functor).
    - exact (fun _ _ _ F => fst F o snd F)%functor.
    - intros C₁ C₂ C₃ [F₁ F₂] [G₁ G₂] [η₁ η₂] ; simpl in *.
      exact (whisker_r η₁ G₂ o whisker_l F₁ η₂)%natural_transformation.
    - intros C₁ C₂ F ; simpl in *.
      apply Composition.left_identity_natural_transformation_1.
    - intros C₁ C₂ F ; simpl in *.
      apply Composition.left_identity_natural_transformation_2.
    - intros C₁ C₂ F ; simpl in *.
      apply Composition.right_identity_natural_transformation_1.
    - intros C₁ C₂ F ; simpl in *.
      apply Composition.right_identity_natural_transformation_2.
    - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ ; simpl in *.
      apply Composition.associator_1.
    - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ ; simpl in *.
      apply Composition.associator_2.
  Defined.

  Definition precat_is_bicategory : is_bicategory precat_d.
  Proof.
    make_is_bicategory.
    - intros C₁ C₂ C₃ [F₁ F₂] ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite identity_of, left_identity.
      reflexivity.
    - intros C₁ C₂ C₃ [F₁ F₂] [G₁ G₂] [H₁ H₂] [η₁ η₂] [ε₁ ε₂] ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite composition_of.
      rewrite !associativity.
      f_ap.
      rewrite <- !associativity.
      f_ap.
      apply ε₁.
    - intros C₁ C₂ F G η ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite !left_identity, right_identity.
      reflexivity.
    - intros C₁ C₂ F₁ F₂ η ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite !left_identity, right_identity.
      reflexivity.
    - intros C₁ C₂ F₁ F₂ η ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite identity_of, left_identity, right_identity.
      reflexivity.
    - intros C₁ C₂ F₁ F₂ η ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite identity_of, left_identity, !right_identity.
      reflexivity.
    - intros C₁ C₂ F ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      apply left_identity.
    - intros C₁ C₂ F ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      apply left_identity.
    - intros C₁ C₂ F ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      apply left_identity.
    - intros C₁ C₂ F ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      apply left_identity.
    - intros C₁ C₂ C₃ C₄ H₁ H₂ G₁ G₂ F₁ F₂ ηH ηG ηF ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite left_identity, right_identity, !composition_of, !associativity.
      reflexivity.
    - intros C₁ C₂ C₃ C₄ H₁ H₂ G₁ G₂ F₁ F₂ ηH ηG ηF ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite left_identity, right_identity, !composition_of, !associativity.
      reflexivity.
    - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      apply left_identity.
    - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      apply left_identity.
    - intros C₁ C₂ C₃ G F ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite !identity_of, !left_identity.
      reflexivity.
    - intros C₁ C₂ C₃ C₄ C₅ F₁ F₂ F₃ F₄ ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite !identity_of, !left_identity.
      reflexivity.
  Qed.

  Definition PreCat : BiCategory
    := Build_BiCategory precat_d precat_is_bicategory.
End CatBiCategory.