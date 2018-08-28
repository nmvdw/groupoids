Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_functor.examples.composition
     lax_functor.examples.identity
     lax_transformation.lax_transformation
     lax_transformation.examples.identity
     general_category.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.

Section LaxRightIdentity.
  Context `{Funext}
          {C D : BiCategory}.
  Variable (F : LaxFunctor C D).
  
  Definition lax_right_identity_d
    : PseudoTransformation_d (lax_comp F (lax_id_functor C)) F.
  Proof.
    make_pseudo_transformation.
    - exact (fun X => id₁ (F X)).
    - exact (fun X Y f => (left_unit_inv (F ₁ f)) ∘ right_unit (F ₁ f)).
    - exact (fun X Y f => right_unit_inv (F ₁ f) ∘ left_unit (F ₁ f)).
  Defined.

  Definition is_lax_right_d
    : is_pseudo_transformation_p lax_right_identity_d.
  Proof.
    make_is_pseudo_transformation.
    - intros X Y f g α ; simpl.
      rewrite vcomp_assoc.
      rewrite right_unit_natural.
      rewrite <- vcomp_assoc.
      rewrite left_unit_inv_natural.
      rewrite !vcomp_assoc.
      reflexivity.
    - intros X ; cbn in *.
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
      rewrite !vcomp_right_identity.
      rewrite Fmor₂_id₂, vcomp_left_identity.
      reflexivity.
    - intros X Y Z f g ; cbn in *.
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
      rewrite vcomp_left_identity, hcomp_id₂, Fmor₂_id₂.
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

  Definition lax_right_identity
    : LaxTransformation (lax_comp F (lax_id_functor C)) F
    := Build_PseudoTransformation lax_right_identity_d is_lax_right_d.

  Global Instance right_identity_pseudo
    : is_pseudo_transformation lax_right_identity
    := _.
End LaxRightIdentity.
