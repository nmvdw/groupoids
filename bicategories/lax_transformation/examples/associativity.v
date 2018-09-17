Require Import HoTT.
Require Import HoTT.Categories.Functor.
From GR.bicategories Require Import
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_functor.examples.composition
     lax_functor.examples.identity
     lax_transformation.lax_transformation
     lax_transformation.examples.identity
     general_category.

Section LaxAssociativity.
  Context `{Funext}
          {C₁ C₂ C₃ C₄ : BiCategory}.
  Variable (F₃ : LaxFunctor C₃ C₄)
           (F₂ : LaxFunctor C₂ C₃)
           (F₁ : LaxFunctor C₁ C₂).
  
  Definition lax_associativity_d
    : PseudoTransformation_d
        (lax_comp (lax_comp F₃ F₂) F₁)
        (lax_comp F₃ (lax_comp F₂ F₁)).
  Proof.
    make_pseudo_transformation.
    - exact (fun X => id₁ (F₃ (F₂ (F₁ X)))).
    - exact (fun X Y f => left_unit_inv _ ∘ right_unit _).
    - exact (fun X Y f => right_unit_inv _ ∘ left_unit _).
  Defined.

  Definition is_lax_associativity_d
    : is_pseudo_transformation_p lax_associativity_d.
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
      rewrite <- !vcomp_assoc.
      repeat f_ap.
      rewrite Fmor₂_vcomp.
      reflexivity.
    - intros X Y Z f g ; cbn in *.
      rewrite vcomp_assoc.
      rewrite right_unit_natural.
      rewrite <- vcomp_assoc.
      rewrite left_unit_inv_natural.
      symmetry.
      rewrite <- (vcomp_left_identity (id₂ (F₃ ₁ (F₂ ₁ (F₁ ₁ f))))).
      rewrite <- (vcomp_left_identity (id₂ (F₃ ₁ (F₂ ₁ (F₁ ₁ g))))).
      rewrite !interchange.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ z))) (vcomp_assoc _ _ _)^).
      rewrite triangle_l.
      rewrite <- interchange.
      rewrite left_unit_left.
      rewrite vcomp_left_identity, hcomp_id₂.
      rewrite !vcomp_left_identity.
      rewrite <- right_unit_assoc.
      rewrite <- !vcomp_assoc.
      f_ap.
      rewrite Fmor₂_vcomp.
      rewrite !vcomp_assoc.
      f_ap.
      pose (left_unit_inv_assoc (F₃ ₁ (F₂ ₁ (F₁ ₁ g))) (F₃ ₁ (F₂ ₁ (F₁ ₁ f)))) as p.
      unfold bc_whisker_r in p.
      rewrite p ; clear p.
      rewrite <- !vcomp_assoc.
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
      
  Definition lax_associativity
    : LaxTransformation (lax_comp (lax_comp F₃ F₂) F₁) (lax_comp F₃ (lax_comp F₂ F₁))
    := Build_PseudoTransformation lax_associativity_d is_lax_associativity_d.

  Global Instance lax_associativity_pseudo
    : is_pseudo_transformation lax_associativity
    := _.
End LaxAssociativity.
