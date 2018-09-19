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
     lax_transformation.examples.representable
     modification.examples.representable
     modification.examples.representable_id
     modification.examples.representable_comp.
From GR.bicategories.bicategory.examples Require Import
     precat
     cat
     opposite
     pseudo_functors_bicat.

Definition yoneda_d
           `{Univalence}
           (C : BiCategory)
  : PseudoFunctor_d C (Pseudo (op C) PreCat).
Proof.
  make_pseudo_functor.
  - exact representable0.
  - exact (@representable1 _ C).
  - exact (@representable2 _ C).
  - exact (@representable_comp _ C).
  - exact representable_id.
  - exact (@representable_comp_inv _ C).
  - exact representable_id_inv.
Defined.

Definition yoneda_is_pseudo
           `{Univalence}
           (C : BiCategory)
  : is_pseudo_functor_p (yoneda_d C).
Proof.
  make_is_pseudo.
  - intros X₁ X₂ f.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    apply hcomp_id₂.
  - intros X₁ X₂ f₁ f₂ f₃ α β.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    apply bc_whisker_r_compose.
  - intros X₁ X₂ X₃ f₁ f₂ g₁ g₂ α β.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite hcomp_id₂, !left_identity, !right_identity.
    pose @interchange as p.
    unfold vcomp in p.
    rewrite <- p.
    rewrite left_identity, right_identity.
    apply assoc_inv_natural.
  - intros X₁ X₂ f.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite hcomp_id₂, !left_identity, !right_identity.
    rewrite triangle_r.
    unfold vcomp.
    rewrite <- inverse_of_assoc, <- inverse_of_left_unit.
    rewrite !associativity.
    rewrite !(ap (fun z => _ o z)%morphism (associativity _ _ _ _ _ _ _ _)^).
    rewrite right_inverse, left_identity.
    pose @interchange as p.
    unfold vcomp in p.
    rewrite <- p.
    rewrite !left_identity, right_inverse.
    rewrite hcomp_id₂.
    reflexivity.
  - intros X₁ X₂ f.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    rewrite left_unit_assoc.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite hcomp_id₂, !left_identity, !right_identity.
    rewrite <- inverse_of_assoc, <- inverse_of_left_unit.
    rewrite !associativity.
    rewrite !(ap (fun z => _ o z)%morphism (associativity _ _ _ _ _ _ _ _)^).
    rewrite right_inverse, left_identity.
    rewrite right_inverse.
    reflexivity.
  - intros X₁ X₂ X₃ X₄ f₁ f₂ f₃.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite !hcomp_id₂, !left_identity, !right_identity.
    apply inverse_pentagon_6.
  - intros X₁ X₂ X₃ f₁ f₂.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    apply assoc_left.
  - intros X₁ X₂ X₃ f₁ f₂.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    apply assoc_right.
  - intros X.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    apply left_unit_right.
  - intros X.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    apply left_unit_left.
Qed.

Definition yoneda
           `{Univalence}
           (C : BiCategory)
  : PseudoFunctor C (Pseudo (op C) PreCat)
  := Build_PseudoFunctor (yoneda_d C) (yoneda_is_pseudo C).

Definition univalent_yoneda_d
           `{Univalence}
           (C : BiCategory)
           `{LocallyUnivalent C}
  : PseudoFunctor_d C (Pseudo (op C) Cat).
Proof.
  make_pseudo_functor.
  - exact univalent_representable0.
  - exact (@univalent_representable1 _ C _).
  - exact (@univalent_representable2 _ C _).
  - exact (@univalent_representable_comp _ C _).
  - exact univalent_representable_id.
  - exact (@univalent_representable_comp_inv _ C _).
  - exact univalent_representable_id_inv.
Defined.

Definition univalent_yoneda_is_pseudo
           `{Univalence}
           (C : BiCategory)
           `{LocallyUnivalent C}
  : is_pseudo_functor_p (univalent_yoneda_d C).
Proof.
  make_is_pseudo.
  - intros X₁ X₂ f.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    apply hcomp_id₂.
  - intros X₁ X₂ f₁ f₂ f₃ α β.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    apply bc_whisker_r_compose.
  - intros X₁ X₂ X₃ f₁ f₂ g₁ g₂ α β.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite hcomp_id₂, !left_identity, !right_identity.
    pose @interchange as p.
    unfold vcomp in p.
    rewrite <- p.
    rewrite left_identity, right_identity.
    apply assoc_inv_natural.
  - intros X₁ X₂ f.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite hcomp_id₂, !left_identity, !right_identity.
    rewrite triangle_r.
    unfold vcomp.
    rewrite <- inverse_of_assoc, <- inverse_of_left_unit.
    rewrite !associativity.
    rewrite !(ap (fun z => _ o z)%morphism (associativity _ _ _ _ _ _ _ _)^).
    rewrite right_inverse, left_identity.
    pose @interchange as p.
    unfold vcomp in p.
    rewrite <- p.
    rewrite !left_identity, right_inverse.
    rewrite hcomp_id₂.
    reflexivity.
  - intros X₁ X₂ f.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    rewrite left_unit_assoc.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite hcomp_id₂, !left_identity, !right_identity.
    rewrite <- inverse_of_assoc, <- inverse_of_left_unit.
    rewrite !associativity.
    rewrite !(ap (fun z => _ o z)%morphism (associativity _ _ _ _ _ _ _ _)^).
    rewrite right_inverse, left_identity.
    rewrite right_inverse.
    reflexivity.
  - intros X₁ X₂ X₃ X₄ f₁ f₂ f₃.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite !hcomp_id₂, !left_identity, !right_identity.
    apply inverse_pentagon_6.
  - intros X₁ X₂ X₃ f₁ f₂.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    apply assoc_left.
  - intros X₁ X₂ X₃ f₁ f₂.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    apply assoc_right.
  - intros X.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    apply left_unit_right.
  - intros X.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros h ; cbn in *.
    apply left_unit_left.
Qed.

Definition univalent_yoneda
           `{Univalence}
           (C : BiCategory)
           `{LocallyUnivalent C}
  : PseudoFunctor C (Pseudo (op C) Cat)
  := Build_PseudoFunctor (univalent_yoneda_d C) (univalent_yoneda_is_pseudo C).