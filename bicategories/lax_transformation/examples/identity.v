Require Import HoTT.
Require Import HoTT.Categories.Functor.
From GR.bicategories Require Import
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     general_category.

Section IdentityTransformation.
  Context {C D : BiCategory}
          `{Univalence}.
  Variable (F : LaxFunctor C D).

  Definition identity_transformation_d : PseudoTransformation_d F F.
  Proof.
    make_pseudo_transformation.
    - exact (fun X => id₁ (F X)).
    - intros X Y f ; simpl in *.
      exact (left_unit_inv (F ₁ f) ∘ right_unit (F ₁ f)).
    - intros X Y f ; simpl in *.
      exact (right_unit_inv (F ₁ f) ∘ left_unit (F ₁ f)).
  Defined.

  Definition is_lax_identity_transformation
    : is_pseudo_transformation_p identity_transformation_d.
  Proof.
    make_is_pseudo_transformation.
    - intros X Y f g α ; simpl in *.
      rewrite vcomp_assoc.
      rewrite right_unit_natural.
      rewrite <- vcomp_assoc.
      rewrite left_unit_inv_natural.
      rewrite !vcomp_assoc.
      reflexivity.
    - intros X ; simpl in *.
      rewrite <- right_unit_id_is_left_unit_id.
      rewrite !vcomp_assoc.
      rewrite right_unit_right.
      rewrite vcomp_right_identity.
      rewrite right_unit_natural.
      rewrite <- vcomp_assoc.
      rewrite left_unit_inv_natural.
      rewrite right_unit_id_is_left_unit_id.
      rewrite vcomp_assoc.
      rewrite left_unit_right.
      apply vcomp_right_identity.
    - intros X Y Z f g ; simpl in *.
      rewrite vcomp_assoc.
      rewrite right_unit_natural.
      rewrite <- vcomp_assoc.
      rewrite left_unit_inv_natural.
      symmetry.
      rewrite <- (vcomp_left_identity (id₂ (F ₁ f))).
      rewrite <- (vcomp_left_identity (id₂ (F ₁ g))).
      rewrite !interchange.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ z))) (vcomp_assoc _ _ _)^).
      rewrite triangle_l.
      rewrite <- interchange.
      rewrite left_unit_left.
      rewrite vcomp_left_identity, hcomp_id₂.
      rewrite !vcomp_left_identity.
      f_ap.
      rewrite <- right_unit_assoc.
      rewrite <- !vcomp_assoc.
      f_ap.
      pose (left_unit_inv_assoc (F ₁ g) (F ₁ f)) as p.
      unfold bc_whisker_r in p.
      rewrite p ; clear p.
      rewrite <- vcomp_assoc.
      rewrite assoc_left.
      apply vcomp_left_identity.
    - intros X Y f ; simpl in *.
      rewrite !vcomp_assoc.
      rewrite (ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
      rewrite right_unit_left, vcomp_left_identity.
      apply left_unit_right.
    - intros X Y f ; simpl in *.
      rewrite !vcomp_assoc.
      rewrite (ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
      rewrite left_unit_left, vcomp_left_identity.
      apply right_unit_right.
  Qed.

  Definition identity_transformation
    : PseudoTransformation F F
    := Build_PseudoTransformation identity_transformation_d is_lax_identity_transformation.
End IdentityTransformation.
