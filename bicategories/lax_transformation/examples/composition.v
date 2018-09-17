Require Import HoTT.
Require Import HoTT.Categories.Functor.
From GR.bicategories Require Import
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     general_category.

Lemma inverse_pentagon_6
      {C : BiCategory}
      {V W X Y Z : C}
      (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
      (g : C⟦W,X⟧) (f : C⟦V,W⟧)
  : assoc_inv k (h · g) f ∘ id₂ k * assoc_inv h g f
    =
    assoc k h g * id₂ f ∘ assoc_inv (k · h) g f ∘ assoc_inv k h (g · f).
Proof.
  unfold vcomp, id₂.
  rewrite !associativity.
  refine (Morphisms.iso_moveL_Mp _ _ _) ; simpl.
  symmetry.
  rewrite <- !associativity.
  apply inverse_pentagon.
Qed.

Section Composition.
  Context `{Funext}
          {C D : BiCategory}
          {F₁ F₂ F₃ : LaxFunctor C D}.
  Variable (σ₁ : LaxTransformation F₁ F₂) (σ₂ : LaxTransformation F₂ F₃).

  Definition compose_d : LaxTransformation_d F₁ F₃.
  Proof.
    make_lax_transformation.
    - exact (fun X => σ₂ X · σ₁ X).
    - intros X Y f ; cbn in *.
      exact ((assoc_inv (σ₂ Y) (σ₁ Y) (F₁ ₁ f))
               ∘ ((σ₂ Y) ◅ laxnaturality_of σ₁ f)
               ∘ assoc (σ₂ Y) (F₂ ₁ f) (σ₁ X)
               ∘ (laxnaturality_of σ₂ f ▻ (σ₁ X))
               ∘ assoc_inv (F₃ ₁ f) (σ₂ X) (σ₁ X)).
  Defined.

  Definition compose_d_is_lax
    : is_lax_transformation compose_d.
  Proof.
    make_is_lax_transformation.
    - intros X Y f g α ; cbn in *.
      unfold bc_whisker_l, bc_whisker_r.
      rewrite !vcomp_assoc.
      rewrite <- hcomp_id₂.
      rewrite assoc_inv_natural.
      rewrite <- !vcomp_assoc.
      f_ap.
      rewrite !vcomp_assoc.
      rewrite <- interchange.
      rewrite laxnaturality_natural.
      rewrite interchange.      
      rewrite <- !vcomp_assoc.
      f_ap.
      rewrite !vcomp_assoc.
      rewrite assoc_natural.
      rewrite <- !vcomp_assoc.
      f_ap.
      rewrite !vcomp_assoc.
      rewrite <- interchange.
      rewrite laxnaturality_natural.
      rewrite vcomp_left_identity.
      rewrite <- (vcomp_left_identity (id₂ (σ₂ Y))).
      rewrite interchange.
      rewrite <- !vcomp_assoc, vcomp_left_identity.
      f_ap.
      rewrite assoc_inv_natural.
      rewrite hcomp_id₂.
      reflexivity.
    - intros X ; cbn.
      rewrite !vcomp_assoc.
      unfold bc_whisker_l, bc_whisker_r.
      rewrite <- hcomp_id₂.
      rewrite assoc_inv_natural.
      rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ z))) (vcomp_assoc _ _ _)^).
      rewrite <- interchange.
      rewrite transformation_unit.
      rewrite vcomp_right_identity, !vcomp_assoc.
      rewrite <- (vcomp_right_identity (id₂ (σ₁ X))).
      rewrite interchange.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
      rewrite assoc_natural.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
      rewrite <- interchange.
      rewrite transformation_unit.
      rewrite !vcomp_assoc.
      rewrite interchange.
      rewrite <- !vcomp_assoc.
      rewrite assoc_inv_natural.
      rewrite !vcomp_assoc.
      rewrite vcomp_right_identity.
      f_ap.
      rewrite <- (vcomp_right_identity (id₂ (σ₂ X))).
      rewrite interchange.
      rewrite <- !vcomp_assoc.
      rewrite <- right_unit_inv_assoc.
      rewrite !vcomp_assoc.
      f_ap.
      rewrite <- triangle_l.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
      rewrite assoc_right, vcomp_left_identity.
      rewrite <- (vcomp_left_identity (id₂ (σ₁ X))).
      rewrite interchange.
      rewrite <- !vcomp_assoc, vcomp_left_identity.
      rewrite <- interchange.
      rewrite right_unit_left, vcomp_left_identity, hcomp_id₂.
      rewrite vcomp_left_identity.
      pose @left_unit_assoc as p.
      unfold bc_whisker_r in p.
      rewrite p ; clear p.
      rewrite !vcomp_assoc.
      rewrite assoc_left, vcomp_right_identity.
      reflexivity.
    - intros X Y Z f g ; cbn in *.
      unfold bc_whisker_l, bc_whisker_r.
      rewrite !vcomp_assoc.
      rewrite <- hcomp_id₂.
      rewrite assoc_inv_natural.
      rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ z))) (vcomp_assoc _ _ _)^).
      rewrite <- interchange.
      rewrite transformation_assoc.
      rewrite !vcomp_assoc.
      rewrite interchange.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
      rewrite assoc_natural.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
      rewrite <- interchange.
      rewrite transformation_assoc.
      rewrite !vcomp_assoc.
      rewrite interchange.
      rewrite <- !vcomp_assoc.
      rewrite assoc_inv_natural.
      rewrite !vcomp_assoc.
      rewrite hcomp_id₂.
      f_ap.
      rewrite <- (vcomp_left_identity (id₂ (σ₂ Z))).
      rewrite interchange.
      rewrite !vcomp_assoc.
      rewrite vcomp_left_identity.
      rewrite <- (vcomp_left_identity (id₂ (F₁ ₁ f))).
      rewrite interchange.
      rewrite <- !vcomp_assoc.
      rewrite inverse_pentagon_2.
      rewrite !vcomp_assoc.
      repeat f_ap.
      rewrite <- !vcomp_assoc.
      do 3 (rewrite <- (vcomp_left_identity (id₂ (σ₂ Z))) ; rewrite interchange).
      rewrite <- !vcomp_assoc, !vcomp_left_identity.
      rewrite assoc_inv_natural.
      do 3 (rewrite <- (vcomp_left_identity (id₂ (F₁ ₁ f))) ; rewrite interchange).
      rewrite !vcomp_assoc.
      rewrite !vcomp_left_identity.
      f_ap.
      rewrite <- !vcomp_assoc.
      rewrite inverse_pentagon_6.
      rewrite !vcomp_assoc.
      f_ap.
      rewrite (ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
      rewrite assoc_inv_natural.
      rewrite <- (vcomp_left_identity (id₂ (σ₁ X))).
      rewrite interchange.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ z))) (vcomp_assoc _ _ _))^.
      rewrite <- pentagon.
      rewrite !vcomp_assoc.
      rewrite (ap (fun z => (_ ∘ (_ ∘ z))) (vcomp_assoc _ _ _)^).
      rewrite assoc_right, vcomp_left_identity.
      rewrite <- (vcomp_left_identity (id₂ (F₃ ₁ g))).
      rewrite interchange.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
      rewrite <- inverse_pentagon.
      rewrite <- !vcomp_assoc.
      rewrite <- assoc_inv_natural.
      rewrite !vcomp_assoc.
      repeat f_ap.
      rewrite !hcomp_id₂.
      rewrite <- (vcomp_left_identity (id₂ (F₃ ₁ g))).
      rewrite interchange.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
      rewrite assoc_inv_natural.
      rewrite !vcomp_assoc, hcomp_id₂.
      rewrite <- !vcomp_assoc.
      rewrite <- interchange, !vcomp_left_identity, !vcomp_right_identity.
      rewrite !vcomp_assoc.
      do 3 (rewrite <- (vcomp_left_identity (id₂ (σ₁ X))) ; rewrite interchange).
      rewrite !vcomp_left_identity, !vcomp_assoc.
      rewrite inverse_pentagon_4.
      rewrite <- !vcomp_assoc.
      repeat f_ap.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
      rewrite assoc_natural.
      rewrite !vcomp_assoc.
      rewrite <- !vcomp_assoc.
      rewrite <- interchange, hcomp_id₂, vcomp_left_identity, vcomp_right_identity.
      rewrite !vcomp_assoc.
      f_ap.
      rewrite <- (vcomp_left_identity (id₂ (F₃ ₁ g))).
      rewrite interchange.
      rewrite <- !vcomp_assoc.
      rewrite inverse_pentagon_2.
      rewrite !vcomp_assoc.
      repeat f_ap.
      rewrite <- (vcomp_left_identity (id₂ (F₃ ₁ g))).
      rewrite interchange.
      rewrite !vcomp_left_identity.
      rewrite <- !vcomp_assoc.
      rewrite assoc_inv_natural.
      reflexivity.
  Qed.

  Definition compose
    : LaxTransformation F₁ F₃
    := Build_LaxTransformation compose_d compose_d_is_lax.
End Composition.

Definition compose_pseudo
           `{Univalence}
           {C D : BiCategory}
          {F₁ F₂ F₃ : LaxFunctor C D}
          (σ₁ : PseudoTransformation F₁ F₂) (σ₂ : PseudoTransformation F₂ F₃)
  : PseudoTransformation F₁ F₃.
Proof.
  make_pseudo_transformation_lax.
  - exact (compose σ₁ σ₂).
  - intros X Y f ; cbn.
    apply _.
Defined.