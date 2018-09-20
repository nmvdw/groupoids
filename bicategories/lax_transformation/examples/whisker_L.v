Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_functor.examples.composition
     lax_transformation.lax_transformation
     general_category.

Lemma F_assoc_inv₁
       {C D : BiCategory}
       (F : LaxFunctor C D)
       `{is_pseudo _ _ F}
      {W X Y Z : C}
      (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
  : Fcomp₁_inv F h (g · f) ∘ (F ₂ assoc h g f)
    =
    (id₂ (F ₁ h) * Fcomp₁ F g f)
      ∘ assoc (F ₁ h) (F ₁ g) (F ₁ f)
      ∘ (Fcomp₁_inv F h g * id₂ (F ₁ f))
      ∘ Fcomp₁_inv F (h · g) f.
Proof.
  refine (vcomp_move_R_Mp _ _ _ _).
  rewrite <- !vcomp_assoc.
  refine (vcomp_move_L_pM _ _ _ _).
  refine (vcomp_move_L_pM _ _ _ _).
  symmetry. 
  apply F_assoc.
Qed.

Lemma F_assoc_inv₂
       {C D : BiCategory}
       (F : LaxFunctor C D)
       `{is_pseudo _ _ F}
      {W X Y Z : C}
      (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
  : (Fcomp₁_inv F (h · g) f)
      ∘ (F ₂ assoc_inv h g f) ∘ Fcomp₁ F h (g · f)
    =
    (Fcomp₁ F h g * id₂ (F ₁ f))
      ∘ assoc_inv (F ₁ h) (F ₁ g) (F ₁ f)
      ∘ id₂ (F ₁ h) * Fcomp₁_inv F g f.
Proof.
  refine (vcomp_move_R_Mp _ _ _ _).
  rewrite <- !vcomp_assoc.
  refine (vcomp_move_L_pM _ _ _ _).
  refine (vcomp_move_L_pM _ _ _ _).
  apply F_assoc.
Qed.

Section WhiskerL.
  Context `{Univalence}
          {C D E : BiCategory}
          {F₁ F₂ : LaxFunctor C D}.
  Variable (G : LaxFunctor D E)
           (σ : LaxTransformation F₁ F₂).
  Context `{is_pseudo _ _ G}.

  Definition whisker_L_d
    : LaxTransformation_d (lax_comp G F₁) (lax_comp G F₂).
  Proof.
    make_lax_transformation.
    - exact (fun X => G ₁ (σ X)).
    - intros X Y f ; cbn in *.
      exact ((Fcomp₁_inv G (σ Y) (F₁ ₁ f))
               ∘ (G ₂ (laxnaturality_of σ f))
               ∘ Fcomp₁ G (F₂ ₁ f) (σ X)).
  Defined.

  Definition whisker_L_d_is_lax
    : is_lax_transformation whisker_L_d.
  Proof.
    make_is_lax_transformation.
    - intros X Y f g α ; simpl in *.
      rewrite !vcomp_assoc.
      pose (Fcomp₂ G (F₂ ₂ α) (id₂ (σ X))) as p.
      rewrite Fmor₂_id₂ in p.
      rewrite p ; clear p.
      rewrite <- !vcomp_assoc.
      f_ap.
      rewrite <- (Fmor₂_id₂ G (σ Y)).
      rewrite <- (Fcomp₁_inv_naturality G (id₂ (σ Y)) (F₁ ₂ α)).
      rewrite !vcomp_assoc.
      f_ap.
      rewrite <- (Fmor₂_vcomp G (laxnaturality_of σ f) (id₂ (σ Y) * (F₁ ₂ α))).
      rewrite <- (Fmor₂_vcomp G ((F₂ ₂ α) * id₂ (σ X)) (laxnaturality_of σ g)).
      rewrite laxnaturality_natural.
      reflexivity.
    - intros X ; cbn in *.
      rewrite !vcomp_assoc.
      rewrite <- Fmor₂_id₂.
      rewrite <- (vcomp_right_identity (G ₂ id₂ (σ X))).
      rewrite !interchange.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
      rewrite Fcomp₂.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
      rewrite <- Fmor₂_vcomp.
      rewrite (transformation_unit σ X).
      rewrite !vcomp_assoc.
      rewrite F_left_unit.
      rewrite !Fmor₂_vcomp.
      rewrite <- !vcomp_assoc.      
      repeat f_ap.
      rewrite !vcomp_assoc.
      rewrite (F_right_unit_inv G).
      rewrite <- !vcomp_assoc.
      f_ap.
      rewrite !Fcomp₁_inv_naturality.
      f_ap.
      rewrite <- !interchange.
      rewrite !vcomp_right_identity.
      rewrite vcomp_assoc.
      unfold Fid_inv.
      rewrite vcomp_right_inverse, vcomp_right_identity.
      reflexivity.
    - intros X Y Z f g ; cbn in *.
      rewrite !vcomp_assoc.
      rewrite <- (vcomp_right_identity (id₂ (G ₁ σ X))).
      rewrite !interchange.
      rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
      rewrite <- Fmor₂_id₂.
      rewrite Fcomp₂.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
      rewrite <- Fmor₂_vcomp.
      rewrite transformation_assoc.
      rewrite !vcomp_assoc.
      rewrite !Fmor₂_vcomp.
      rewrite <- !vcomp_assoc.
      rewrite Fcomp₁_inv_naturality.
      rewrite !vcomp_assoc.
      rewrite Fmor₂_id₂.
      rewrite <- (vcomp_right_identity (id₂ (G ₁ σ Z))).
      rewrite interchange.
      rewrite !vcomp_assoc.
      rewrite !vcomp_right_identity.
      f_ap.
      rewrite <- !vcomp_assoc.
      rewrite F_assoc_inv₁.
      rewrite !vcomp_assoc.
      repeat f_ap.
      rewrite <- (vcomp_right_identity (id₂ (G ₁ (F₁ ₁ f)))).
      rewrite !interchange.
      rewrite !vcomp_assoc, !vcomp_right_identity.
      f_ap.
      rewrite <- !vcomp_assoc.
      rewrite Fcomp₁_inv_naturality.
      rewrite !vcomp_assoc.
      rewrite <- (vcomp_right_identity (id₂ (G ₁ (F₁ ₁ f)))).
      rewrite !interchange.
      rewrite !vcomp_assoc, !Fmor₂_id₂.
      f_ap.
      pose (F_assoc G (F₂ ₁ g) (F₂ ₁ f) (σ X))^ as p.
      rewrite vcomp_assoc in p.
      rewrite p ; clear p.
      rewrite <- !vcomp_assoc.
      f_ap.
      rewrite !vcomp_assoc.
      rewrite <- (vcomp_right_identity (id₂ (G ₁ (F₂ ₁ g)))).
      rewrite interchange.
      rewrite vcomp_right_identity.
      rewrite <- !vcomp_assoc.
      rewrite <- F_assoc_inv₂.
      rewrite !vcomp_assoc.
      repeat f_ap.
      rewrite <- !vcomp_assoc.
      rewrite <- Fcomp₂.
      rewrite !vcomp_assoc.
      rewrite Fmor₂_id₂.
      repeat f_ap.
      rewrite <- interchange.
      rewrite vcomp_right_identity.
      reflexivity.
  Qed.

  Definition whisker_L
    : LaxTransformation (lax_comp G F₁) (lax_comp G F₂)
    := Build_LaxTransformation whisker_L_d whisker_L_d_is_lax.
End WhiskerL.

Global Instance whisker_L_is_pseudo
       `{Univalence}
       {C D E : BiCategory}
       {F₁ F₂ : LaxFunctor C D}
       (G : LaxFunctor D E)
       `{is_pseudo _ _ G}
       (η : LaxTransformation F₁ F₂)
       `{is_pseudo_transformation _ _ _ _ η}
  : is_pseudo_transformation (whisker_L G η).
Proof.
  intros X Y f ; cbn.
  apply _.
Defined.

Definition whisker_L_pseudo
           `{Univalence}
           {C D E : BiCategory}
           {F₁ F₂ : LaxFunctor C D}
           (G : PseudoFunctor D E)
           (σ : PseudoTransformation F₁ F₂)
  : PseudoTransformation (lax_comp G F₁) (lax_comp G F₂).
Proof.
  make_pseudo_transformation_lax.
  - exact (whisker_L G σ).
  - exact (whisker_L_is_pseudo G σ).
Defined.