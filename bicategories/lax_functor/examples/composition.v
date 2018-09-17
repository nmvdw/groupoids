Require Import HoTT.
Require Import HoTT.Categories.Functor.
From GR.bicategories Require Import
     bicategory.bicategory
     lax_functor.lax_functor.

Section FunctorComposition.
  Context {C D E : BiCategory}.
  Variable (G : LaxFunctor D E) (F : LaxFunctor C D).

  Definition compose_mor (X Y : C)
    : Functor (C ⟦ X, Y ⟧) (E ⟦ G (F X), G (F Y) ⟧).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - exact (fun f => G ₁ (F ₁ f)).
    - exact (fun _ _ η => G ₂ (F ₂ η)).
    - intros f g h η₁ η₂ ; simpl in *.
      exact ((ap (fun z => G ₂ z) (Fmor₂_vcomp _ _ _))
               @ Fmor₂_vcomp _ _ _).
    - intros f ; simpl in *.
      exact ((ap (fun z => G ₂ z) (Fmor₂_id₂ _ _))
               @ Fmor₂_id₂ _ _).
  Defined.

  Definition lax_comp_d : LaxFunctor_d C E.
  Proof.
    make_laxfunctor.
    - exact (G o F).
    - simple refine (fun X Y => Build_Functor _ _ _ _ _ _).
      + exact (fun f => G ₁ (F ₁ f)).
      + exact (fun _ _ η => G ₂ (F ₂ η)).
      + intros f g h η₁ η₂ ; simpl in *.
        exact ((ap (fun z => G ₂ z) (Fmor₂_vcomp _ _ _))
                 @ Fmor₂_vcomp _ _ _).
      + intros f ; simpl in *.
        exact ((ap (fun z => G ₂ z) (Fmor₂_id₂ _ _))
                 @ Fmor₂_id₂ _ _).
    - intros X Y Z g f ; simpl in *.
      exact (G ₂ (Fcomp₁ F g f) ∘ Fcomp₁ G (Fmor F Y Z g) (Fmor F X Y f)).
    - intros X.
      exact (G ₂ (Fid F X) ∘ Fid G (F X)).
  Defined.

  Definition comp_is_lax : is_lax lax_comp_d.
  Proof.
    make_is_lax.
    - intros X Y Z g₁ g₂ f₁ f₂ η₁ η₂ ; simpl in *.
      rewrite vcomp_assoc.
      rewrite (Fcomp₂ G (F ₂ η₁) (F ₂ η₂)).
      rewrite <- !vcomp_assoc.
      rewrite <- !Fmor₂_vcomp.
      rewrite (Fcomp₂ F η₁ η₂).
      reflexivity.
    - intros X Y f ; simpl in *.
      transitivity (left_unit (G ₁ (F ₁ f))).
      { reflexivity. }
      rewrite !F_left_unit.
      rewrite !Fmor₂_vcomp, !vcomp_assoc.
      repeat f_ap.
      rewrite <- !vcomp_assoc.
      rewrite <- Fcomp₂.
      rewrite !vcomp_assoc.
      rewrite <- interchange.
      rewrite vcomp_right_identity.
      rewrite Fmor₂_id₂.
      reflexivity.
    - intros X Y f ; simpl in *.
      transitivity (right_unit (G ₁ (F ₁ f))).
      { reflexivity. }
      rewrite !F_right_unit.
      rewrite !Fmor₂_vcomp, !vcomp_assoc.
      repeat f_ap.
      rewrite <- !vcomp_assoc.
      rewrite <- Fcomp₂.
      rewrite !vcomp_assoc.
      rewrite <- interchange.
      rewrite vcomp_right_identity.
      rewrite Fmor₂_id₂.
      reflexivity.
    - intros W X Y Z h g f ; simpl in *.
      rewrite <- (vcomp_left_identity (id₂ _)).
      symmetry.
      rewrite <- (vcomp_left_identity (id₂ _)).
      rewrite !interchange.
      symmetry.
      pose (F_assoc G (F ₁ h) (F ₁ g) (F ₁ f)) as assoc1.
      pose (F_assoc F h g f) as assoc2.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
      pose (Fcomp₂ G (id₂ (F ₁ h)) (Fcomp₁ F g f)) as p.
      rewrite Fmor₂_id₂ in p.
      rewrite p ; clear p.
      rewrite !vcomp_assoc.
      rewrite (ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
      rewrite assoc1 ; clear assoc1.
      rewrite <- !vcomp_assoc.
      repeat f_ap.
      rewrite <- !Fmor₂_vcomp.
      rewrite assoc2 ; clear assoc2.
      rewrite !vcomp_assoc.
      pose (Fcomp₂ G (Fcomp₁ F h g) (id₂ (F ₁ f))) as p.
      rewrite Fmor₂_id₂ in p.
      rewrite p.
      rewrite <- !vcomp_assoc.
      rewrite !Fmor₂_vcomp.
      reflexivity.
  Qed.

  Definition lax_comp : LaxFunctor C E
    := Build_LaxFunctor lax_comp_d comp_is_lax.
End FunctorComposition.

Definition pseudo_comp
           `{Univalence}
           {C D E : BiCategory}
           (G : PseudoFunctor D E) (F : PseudoFunctor C D)
  : PseudoFunctor C E.
Proof.
  make_pseudo_functor_lax.
  - exact (lax_comp G F).
  - simpl.
    split ; apply _.
Defined.