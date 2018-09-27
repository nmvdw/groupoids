Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor.
From GR.bicategories Require Import
     bicategory.bicategory_laws
     bicategory.univalent
     bicategory.locally_strict
     bicategory.strict
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.transformation_category
     modification.modification.
Require Import GR.bicategories.lax_transformation.examples.composition.
Require Import GR.bicategories.lax_transformation.examples.identity.
Require Import GR.bicategories.modification.examples.associativity_inv.
Require Import GR.bicategories.modification.examples.associativity.
Require Import GR.bicategories.modification.examples.composition.
Require Import GR.bicategories.modification.examples.identity.
Require Import GR.bicategories.modification.examples.left_identity_inv.
Require Import GR.bicategories.modification.examples.left_identity.
Require Import GR.bicategories.modification.examples.right_identity_inv.
Require Import GR.bicategories.modification.examples.right_identity.
Require Import GR.bicategories.modification.examples.whisker_L.
Require Import GR.bicategories.modification.examples.whisker_R.

Section LaxFunctors.
  Context `{Univalence}.
  Variable (C D : BiCategory).

  Definition lax_functors_d : BiCategory_d.
  Proof.
    make_bicategory.
    - exact (LaxFunctor C D).
    - exact transformation_category.
    - intros F ; cbn.
      exact (identity_transformation F).
    - intros F₁ F₂ F₃ [η₂ η₁] ; cbn in *.
      exact (compose η₁ η₂).
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
      unfold bc_whisker_l, bc_whisker_r.
      rewrite !hcomp_id₂.
      rewrite vcomp_left_identity.
      reflexivity.
    - intros X Y Z [f₁ f₂] [g₁ g₂] [h₁ h₂] [η₁ η₂] [ε₁ ε₂] ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      unfold bc_whisker_l, bc_whisker_r.
      rewrite <- !interchange.
      rewrite !vcomp_left_identity, !vcomp_right_identity.
      reflexivity.
    - intros X Y f g η ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      unfold bc_whisker_l, bc_whisker_r.
      rewrite hcomp_id₂.
      rewrite !vcomp_right_identity.
      apply left_unit_natural.
    - intros X Y f g η ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      unfold bc_whisker_l, bc_whisker_r.
      rewrite hcomp_id₂.
      rewrite !vcomp_right_identity.
      apply left_unit_inv_natural.
    - intros X Y f g η ; simpl in *.
      apply path_modification.
      funext x ; cbn.
      unfold bc_whisker_l, bc_whisker_r.
      rewrite hcomp_id₂.
      rewrite !vcomp_left_identity.
      apply right_unit_natural.
    - intros X Y f g η ; simpl in *.
      apply path_modification.
      funext x ; cbn.
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
      unfold bc_whisker_l, bc_whisker_r.
      rewrite <- !interchange.
      rewrite !vcomp_left_identity, !vcomp_right_identity.
      apply assoc_natural.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ m₁ m₂ m₃ ; simpl in *.
      apply path_modification.
      funext x ; cbn.
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
      unfold bc_whisker_l, bc_whisker_r ; cbn.
      rewrite !hcomp_id₂.
      rewrite !vcomp_left_identity, !vcomp_right_identity.
      rewrite triangle_r.
      reflexivity.
    - intros V W X Y Z k h g f ; cbn in *.
      apply path_modification.
      funext x ; cbn.
      unfold bc_whisker_l, bc_whisker_r ; cbn.
      rewrite pentagon.
      rewrite !vcomp_assoc.
      rewrite hcomp_id₂, !vcomp_left_identity, hcomp_id₂.
      rewrite vcomp_left_identity.
      reflexivity.
  Qed.

  Definition Lax : BiCategory
    := Build_BiCategory lax_functors_d lax_functors_is_bicategory.

  Section StrictFunctors.
    Variable (HD : is_2category D).

    Definition strict_left_functor
               {F G : Lax}
               (η : Lax ⟦F,G⟧)
      : id₁ G · η = η.
    Proof.
      simple refine (path_laxtransformation _ _).
      - intros Z ; cbn.
        apply strict_left_unit.
        apply HD.
      - intros A B f ; cbn.
        rewrite !idtoiso_strict_left_unit.
        apply left_identity_is_mod.
    Defined.

    Definition strict_right_functor
               {F G : Lax}
               (η : Lax ⟦F,G⟧)
      : η · id₁ F = η.
    Proof.
      simple refine (path_laxtransformation _ _).
      - intros Z ; cbn.
        apply strict_right_unit.
        apply HD.
      - intros A B f ; cbn.
        rewrite !idtoiso_strict_right_unit.
        apply right_identity_is_mod.
    Defined.

    Definition strict_assoc_functor
               {F₁ F₂ F₃ F₄ : Lax}
               (η₁ : Lax ⟦F₃,F₄⟧)
               (η₂ : Lax ⟦F₂,F₃⟧)
               (η₃ : Lax ⟦F₁,F₂⟧)
      : η₁ · η₂ · η₃ = η₁ · (η₂ · η₃).
    Proof.
      simple refine (path_laxtransformation _ _).
      - intros Z ; cbn.
        apply strict_assoc.
        apply HD.
      - intros A B f ; cbn.
        rewrite !idtoiso_strict_assoc.
        apply assoc_d_is_modification.
    Defined.

    Definition idtoiso_strict_left_unit_functor
               {F₁ F₂ : Lax}
               (η : LaxTransformation F₁ F₂)
      : @morphism_isomorphic _ _ _ (idtoiso (Lax ⟦F₁,F₂⟧) (strict_left_functor η))
        =
        @left_unit Lax _ _ η.
    Proof.
      apply path_modification.
      funext X ; simpl.
      rewrite mod_component_idtoiso.
      rewrite ap_laxcomponent_path_laxtransformation.
      apply idtoiso_strict_left_unit.
    Qed.

    Definition idtoiso_strict_right_unit_functor
               {F₁ F₂ : Lax}
               (η : LaxTransformation F₁ F₂)
      : @morphism_isomorphic _ _ _ (idtoiso (Lax ⟦F₁,F₂⟧) (strict_right_functor η))
        =
        @right_unit Lax _ _ η.
    Proof.
      apply path_modification.
      funext X ; simpl.
      rewrite mod_component_idtoiso.
      rewrite ap_laxcomponent_path_laxtransformation.
      apply idtoiso_strict_right_unit.
    Qed.

    Definition strict_lax : IsStrict Lax.
    Proof.
      make_strict.
      - exact @strict_left_functor.
      - exact @strict_right_functor.
      - exact @strict_assoc_functor.
      - intros ; apply path_ishprop.
      - intros ; apply path_ishprop.
      - exact @idtoiso_strict_left_unit_functor.
      - exact @idtoiso_strict_right_unit_functor.
      - intros F₁ F₂ F₃ F₄ η₁ η₂ η₃ ; simpl in *.
        apply path_modification.
        funext X ; simpl.
        rewrite mod_component_idtoiso.
        rewrite ap_laxcomponent_path_laxtransformation.
        apply idtoiso_strict_assoc.
    Defined.

    Global Instance is_2_category_Lax
      : is_2category Lax.
    Proof.
      split.
      - intros X Y.
        apply _.
      - apply strict_lax.
    Qed.
  End StrictFunctors.
End LaxFunctors.