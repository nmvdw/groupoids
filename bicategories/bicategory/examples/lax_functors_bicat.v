Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.transformation_category
     lax_transformation.examples.identity
     lax_transformation.examples.composition
     modification.modification
     modification.examples.identity
     modification.examples.composition
     modification.examples.left_identity
     modification.examples.left_identity_inv
     modification.examples.right_identity
     modification.examples.right_identity_inv
     modification.examples.associativity
     modification.examples.associativity_inv
     modification.examples.whisker_L
     modification.examples.whisker_R
     general_category.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.

Section LaxFunctors.
  Context `{Funext}.
  Variable (C D : BiCategory).

  Definition lax_functors_d : BiCategory_d.
  Proof.
    make_bicategory.
    - exact (LaxFunctor C D).
    - exact transformation_category.
    - intros F ; cbn.
      exact (identity_transformation F).
    - intros F₁ F₂ F₃ [η₂ η₁] ; cbn in *.
      exact (composition.compose η₁ η₂).
    - intros F₁ F₂ F₃ [η₁ η₂] [ε₁ ε₂] [m₁ m₂] ; cbn in *.
      exact (comp_modification (whisker_R_mod m₂ ε₁) (whisker_L_mod η₂ m₁)).
    - intros F₁ F₂ η ; cbn in *.
      apply left_identity_mod.
    - intros F₁ F₂ η ; cbn in *.
      apply left_identity_inv_mod.
    - intros F₁ F₂ η ; cbn in *.
      apply right_identity_mod.
    - intros F₁ F₂ η ; cbn in *.
      apply right_identity_inv_mod.
    - intros F₁ F₂ F₃ F₄ η₁ η₂ η₃ ; cbn in *.
      apply assoc_mod.
    - intros F₁ F₂ F₃ F₄ η₁ η₂ η₃ ; cbn in *.
      apply assoc_inv_mod.
  Defined.

  Definition lax_functors_is_bicategory : is_bicategory lax_functors_d.
  Proof.
    make_is_bicategory.
    - intros X Y Z [g f] ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      unfold comp_modification_d, whisker_R_mod, whisker_L_mod, id_modification ; cbn.
      unfold whisker_R_mod_d, whisker_L_mod_d, id_modification_d ; cbn.
      unfold bc_whisker_l, bc_whisker_r.
      rewrite !hcomp_id₂.
      rewrite vcomp_left_identity.
      reflexivity.
    - intros X Y Z [f₁ f₂] [g₁ g₂] [h₁ h₂] [η₁ η₂] [ε₁ ε₂] ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      unfold comp_modification_d, whisker_R_mod, whisker_L_mod, id_modification ; cbn.
      unfold whisker_R_mod_d, whisker_L_mod_d, id_modification_d, comp_modification_d ; cbn.
      unfold comp_modification_d, bc_whisker_l, bc_whisker_r.
      rewrite <- !interchange.
      rewrite !vcomp_left_identity, !vcomp_right_identity.
      reflexivity.
    - intros X Y f g η ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      unfold comp_modification_d ; cbn.
      unfold left_identity_mod_d, comp_modification_d, id_modification ; cbn.
      unfold whisker_R_mod_d, whisker_L_mod_d, id_modification_d ; cbn.
      unfold bc_whisker_l, bc_whisker_r.
      unfold left_identity_mod_d ; cbn.
      rewrite hcomp_id₂.
      rewrite !vcomp_right_identity.
      apply left_unit_natural.
    - intros X Y f g η ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      unfold comp_modification_d ; cbn.
      unfold left_identity_inv_mod_d, comp_modification_d, id_modification ; cbn.
      unfold whisker_R_mod_d, whisker_L_mod_d, id_modification_d ; cbn.
      unfold bc_whisker_l, bc_whisker_r.
      rewrite hcomp_id₂.
      rewrite !vcomp_right_identity.
      apply left_unit_inv_natural.
    - intros X Y f g η ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      unfold comp_modification_d ; cbn.
      unfold right_identity_mod_d, comp_modification_d, id_modification ; cbn.
      unfold whisker_R_mod_d, whisker_L_mod_d, id_modification_d ; cbn.
      unfold bc_whisker_l, bc_whisker_r.
      rewrite hcomp_id₂.
      rewrite !vcomp_left_identity.
      apply right_unit_natural.
    - intros X Y f g η ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      unfold comp_modification_d ; cbn.
      unfold right_identity_inv_mod_d, comp_modification_d, id_modification ; cbn.
      unfold whisker_R_mod_d, whisker_L_mod_d, id_modification_d ; cbn.
      unfold bc_whisker_l, bc_whisker_r.
      rewrite hcomp_id₂.
      rewrite !vcomp_left_identity.
      apply right_unit_inv_natural.
    - intros X Y f ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      apply left_unit_left.
    - intros X Y f ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      apply left_unit_right.
    - intros X Y f ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      apply right_unit_left.
    - intros X Y f ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      apply right_unit_right.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ m₁ m₂ m₃ ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      repeat (unfold comp_modification_d ; cbn).
      unfold whisker_R_mod_d, whisker_L_mod_d ; cbn.
      unfold comp_modification_d ; cbn.
      unfold whisker_R_mod_d, whisker_L_mod_d ; cbn.
      unfold bc_whisker_l, bc_whisker_r.
      rewrite <- !interchange.
      rewrite !vcomp_left_identity, !vcomp_right_identity.
      apply assoc_natural.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ m₁ m₂ m₃ ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      repeat (unfold comp_modification_d ; cbn).
      unfold whisker_R_mod_d, whisker_L_mod_d ; cbn.
      unfold comp_modification_d ; cbn.
      unfold whisker_R_mod_d, whisker_L_mod_d ; cbn.
      unfold bc_whisker_l, bc_whisker_r.
      rewrite <- !interchange.
      rewrite !vcomp_left_identity, !vcomp_right_identity.
      apply assoc_inv_natural.
    - intros W X Y Z f g h ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      apply assoc_left.
    - intros W X Y Z f g h ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      apply assoc_right.
    - intros X Y Z g f ; cbn in *.
      apply path_modification.
      funext x ; cbn.
      unfold comp_modification_d ; cbn.
      unfold whisker_R_mod_d, whisker_L_mod_d, comp_modification_d ; cbn.
      unfold id_modification_d, right_identity_mod_d, whisker_R_mod_d, whisker_L_mod_d ; cbn.
      unfold id_modification_d, left_identity_mod_d, bc_whisker_l, bc_whisker_r ; cbn.
      rewrite !hcomp_id₂.
      rewrite !vcomp_left_identity, !vcomp_right_identity.
      rewrite triangle_r.
      reflexivity.
    - intros V W X Y Z k h g f ; cbn in *.
      apply path_modification.
      funext x ; cbn.
      repeat (unfold comp_modification_d ; cbn).
      unfold whisker_R_mod_d, whisker_L_mod_d ; cbn.
      unfold id_modification_d, bc_whisker_l, bc_whisker_r ; cbn.
      rewrite pentagon.
      rewrite !vcomp_assoc.
      rewrite hcomp_id₂, !vcomp_left_identity, hcomp_id₂.
      rewrite vcomp_left_identity.
      reflexivity.
  Qed.

  Definition Lax : BiCategory
    := Build_BiCategory lax_functors_d lax_functors_is_bicategory.
End LaxFunctors.