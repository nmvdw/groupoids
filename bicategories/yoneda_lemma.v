Require Import HoTT.
From HoTT.Categories Require Import
     Functor
     NaturalTransformation
     FunctorCategory.
From GR.bicategories Require Import
     bicategory.equivalence
     bicategory.adjoint
     bicategory.equiv_to_adjequiv
     bicategory.univalent
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_functor.weak_equivalence
     lax_transformation.lax_transformation
     modification.modification
     general_category
     lax_functor.examples.yoneda
     lax_functor.examples.representable
     lax_transformation.examples.representable
     modification.examples.composition
     modification.examples.identity
     modification.examples.representable
     modification.examples.representable_id
     modification.examples.representable_comp.
From GR.bicategories.bicategory.examples Require Import
     precat
     cat
     opposite
     pseudo_functors_bicat.

Section YonedaLemma.
  Context `{Univalence}
          {C : BiCategory}.
  Variable (F : PseudoFunctor (op C) PreCat)
           (X : C).

  Definition yoneda_to_presheaf
    : Functor (Pseudo (op C) PreCat⟦representable0 X, F⟧) (F X).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - exact (fun η => η.1.1 X (id₁ X)).
    - exact (fun _ _ α => α.1 X (id₁ X)).
    - reflexivity.
    - reflexivity.
  Defined.

  Definition presheaf_to_yoneda_m_d_help₁
             (x : F X)
             {Y₁ Y₂ : C}
             (f : C ⟦ Y₂, Y₁ ⟧)
             {h₁ h₂ : C ⟦Y₁,X⟧}
             (α : h₁ ==> h₂)
    : ((Fcomp₁ F f h₂) x o (F ₁ f) _1 ((F ₂ α) x))%morphism
      =
      ((F ₂ (α ▻ f)) x o (Fcomp₁ F f h₁) x)%morphism.
  Proof.
    pose (equiv_path_natural_transformation _ _ (Fcomp₂ F (id₂ f) α) x) as p.
    cbn in p.
    rewrite <- p ; clear p.
    pose (equiv_path_natural_transformation _ _ (@Fmor₂_id₂ _ _ F _ _ f) ((F ₁ h₂) x)) as p.
    cbn in p.
    rewrite p.
    rewrite left_identity.
    reflexivity.
  Qed.

  Definition presheaf_to_yoneda_m_d_help₂
             (x : F X)
             {Y₁ Y₂ : C}
             (f : C ⟦ Y₂, Y₁ ⟧)
             {h₁ h₂ : C ⟦Y₁,X⟧}
             (α : h₁ ==> h₂)
    : ((Fcomp₁_inv F f h₂) x o (F ₂ (α ▻ f)) x)%morphism
      =
      ((F ₁ f) _1 ((F ₂ α) x) o (Fcomp₁_inv F f h₁) x)%morphism.
  Proof.
    pose (equiv_path_natural_transformation _ _ (Fcomp₁_inv_naturality F (id₂ f) α) x) as p.
    cbn in *.
    rewrite p ; clear p.
    pose (equiv_path_natural_transformation _ _ (@Fmor₂_id₂ _ _ F _ _ f) ((F ₁ h₂) x)) as p.
    cbn in p.
    rewrite p.
    rewrite left_identity.
    reflexivity.
  Qed.

  Definition presheaf_to_yoneda_m_d (x : F X)
    : PseudoTransformation_d (representable0 X) F.
  Proof.
    make_pseudo_transformation.
    - intros Z ; cbn in *.
      exact (apply_functor (F Z) x o Fmor F X Z)%functor.
    - intros Y₁ Y₂ f.
      simple refine (Build_NaturalTransformation _ _ _ _).
      + intros h ; cbn in *.
        exact (Fcomp₁ F f h x).
      + intros h₁ h₂ α.
        exact (presheaf_to_yoneda_m_d_help₁ x f α).
    - intros Y₁ Y₂ f.
      simple refine (Build_NaturalTransformation _ _ _ _).
      + intros h ; cbn.
        exact (Fcomp₁_inv F f h x).
      + intros h₁ h₂ α.
        exact (presheaf_to_yoneda_m_d_help₂ x f α).
  Defined.

  Definition presheaf_to_yoneda_m_is_pseudo (x : F X)
    : is_pseudo_transformation_p (presheaf_to_yoneda_m_d x).
  Proof.
    make_is_pseudo_transformation.
    - intros Y₁ Y₂ f₁ f₂ α.
      apply path_natural_transformation.
      intros f ; cbn in *.
      rewrite identity_of, left_identity, right_identity.
      pose (equiv_path_natural_transformation _ _ (Fcomp₂ F α (id₂ f)) x) as p.
      cbn in p.
      rewrite <- p ; clear p.
      f_ap.
      pose (equiv_path_natural_transformation _ _ (Fmor₂_id₂ F f) x).
      rewrite p.
      cbn.
      rewrite identity_of.
      rewrite right_identity.
      reflexivity.
    - intros Z.
      apply path_natural_transformation.
      intros f ; cbn in *.
      rewrite !left_identity, !right_identity.
      pose (equiv_path_natural_transformation _ _ (F_left_unit_inv_2 F f) x) as p.
      cbn in p.
      rewrite p ; clear p.
      rewrite !right_identity.
      reflexivity.
    - intros Y₁ Y₂ Y₃ f₁ f₂.
      apply path_natural_transformation.
      intros g ; cbn in *.
      rewrite !identity_of, !left_identity, !right_identity.
      pose (equiv_path_natural_transformation _ _ (F_assoc_inv F f₂ f₁ g) x) as p.
      cbn in p.
      rewrite !identity_of, !left_identity, !right_identity in p.
      apply p.
    - intros Y₁ Y₂ f.
      apply path_natural_transformation.
      intros g ; cbn in *.
      apply (equiv_path_natural_transformation _ _ (vcomp_right_inverse (Fcomp₁ F f g)) x).
    - intros Y₁ Y₂ f.
      apply path_natural_transformation.
      intros g ; cbn in *.
      apply (equiv_path_natural_transformation _ _ (vcomp_left_inverse (Fcomp₁ F f g)) x).
  Qed.

  Definition presheaf_to_yoneda_m (x : F X)
    : PseudoTransformation (representable0 X) F
    := Build_PseudoTransformation
         (presheaf_to_yoneda_m_d x)
         (presheaf_to_yoneda_m_is_pseudo x).

  Definition presheaf_to_yoneda_2_d
             {x y : F X}
             (f : Core.morphism (F X) x y)
    : Modification_d (presheaf_to_yoneda_m x) (presheaf_to_yoneda_m y).
  Proof.
    intros Z.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; cbn in *.
      exact (morphism_of (F ₁ h) f).
    - intros h₁ h₂ α ; cbn in *.
      exact (commutes (F ₂ α) _ _ f)^.
  Defined.

  Definition presheaf_to_yoneda_2_is_modification
             {x y : F X}
             (f : Core.morphism (F X) x y)
    : is_modification (presheaf_to_yoneda_2_d f).
  Proof.
    intros Z₁ Z₂ h.
    apply path_natural_transformation.
    intros ϕ ; cbn in *.
    rewrite !identity_of, !left_identity, !right_identity.
    exact (commutes (Fcomp₁ F h ϕ) _ _ f).
  Qed.

  Definition presheaf_to_yoneda_2
             (x y : F X)
             (f : Core.morphism (F X) x y)
    : Modification (presheaf_to_yoneda_m x) (presheaf_to_yoneda_m y)
    := Build_Modification
         (presheaf_to_yoneda_2_d f)
         (presheaf_to_yoneda_2_is_modification f).

  Definition presheaf_to_yoneda_2_comp
             (Y₁ Y₂ Y₃ : F X)
             (h₁ : Core.morphism (F X) Y₁ Y₂)
             (h₂ : Core.morphism (F X) Y₂ Y₃)
    : presheaf_to_yoneda_2 Y₁ Y₃ (h₂ o h₁)%morphism
      =
      comp_modification (presheaf_to_yoneda_2 Y₂ Y₃ h₂) (presheaf_to_yoneda_2 Y₁ Y₂ h₁).
  Proof.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros ϕ ; cbn.
    apply composition_of.
  Qed.

  Definition presheaf_to_yoneda_2_id
             (Y : F X)
    : presheaf_to_yoneda_2 Y Y 1 = id_modification (presheaf_to_yoneda_m Y).
  Proof.
    apply path_modification.
    funext Z.
    apply path_natural_transformation.
    intros ϕ ; cbn.
    apply identity_of.
  Qed.

  Definition presheaf_to_yoneda
    : Functor (F X) (Pseudo (op C) PreCat⟦representable0 X, F⟧).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - exact presheaf_to_yoneda_m.
    - exact presheaf_to_yoneda_2.
    - exact presheaf_to_yoneda_2_comp.
    - exact presheaf_to_yoneda_2_id.
  Defined.

  Definition presheaf_to_yoneda_to_presheaf
    : (NaturalTransformation (yoneda_to_presheaf o presheaf_to_yoneda) 1)%functor.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros x ; cbn.
      exact (Fid_inv F X x).
    - intros x y f.
      cbn in *.
      exact (commutes (Fid_inv F X) x y f).
  Defined.

  Definition presheaf_to_yoneda_to_presheaf_inv
    : (NaturalTransformation 1 (yoneda_to_presheaf o presheaf_to_yoneda))%functor.   
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros x ; cbn.
      exact (Fid F X x).
    - intros x y f.
      cbn in *.
      exact (commutes (Fid F X) x y f).
  Defined.

  Definition presheaf_to_yoneda_to_presheaf_retr
    : (presheaf_to_yoneda_to_presheaf
         o presheaf_to_yoneda_to_presheaf_inv = 1)%natural_transformation.
  Proof.
    apply path_natural_transformation.
    intros Y ; cbn.
    exact (equiv_path_natural_transformation _ _ (vcomp_left_inverse (Fid F X)) Y).
  Qed.

  Definition presheaf_to_yoneda_to_presheaf_sect
    : (presheaf_to_yoneda_to_presheaf_inv
         o presheaf_to_yoneda_to_presheaf = 1)%natural_transformation.
  Proof.
    apply path_natural_transformation.
    intros Y ; cbn.
    exact (equiv_path_natural_transformation _ _ (vcomp_right_inverse (Fid F X)) Y).
  Qed.

  Global Instance iso_presheaf_to_yoneda_to_presheaf
    : @IsIsomorphism (_ -> _) _ _ presheaf_to_yoneda_to_presheaf.
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - exact presheaf_to_yoneda_to_presheaf_inv.
    - exact presheaf_to_yoneda_to_presheaf_sect.
    - exact presheaf_to_yoneda_to_presheaf_retr.
  Defined.

  Opaque representable0.

  Definition yoneda_to_presheaf_to_yoneda_m_d_help
             (σ : LaxTransformation (representable0 X) F)
             {Y : op C}
             {h₁ h₂ : (representable0 X).1 Y}
             (α : Core.morphism ((representable0 X).1 Y) h₁ h₂)
    : (((σ.1 Y) _1 (left_unit h₂))
         o laxnaturality_of σ h₂ (id₁ X)
         o (F ₂ α) (σ.1 X (id₁ X))
       =
       ((σ Y) _1 α)
         o ((σ.1 Y) _1 (left_unit h₁)
         o laxnaturality_of σ h₁ (id₁ X)))%morphism.
  Proof.
    pose (equiv_path_natural_transformation _ _ (laxnaturality_natural σ α) (id₁ X)).
    cbn in p.
    unfold bc_whisker_l, bc_whisker_r in p.
    rewrite identity_of in p.
    rewrite <- (right_identity _ _ _ ((F ₂ α) _)).
    rewrite !associativity.
    rewrite p.
    clear p.
    rewrite left_identity.
    rewrite <- !associativity.
    rewrite <- composition_of.
    pose (left_unit_natural α) as p.
    unfold vcomp in p.
    rewrite p.
    rewrite composition_of.
    reflexivity.
  Qed.

  Definition yoneda_to_presheaf_to_yoneda_m_d
             (σ : PseudoTransformation (representable0 X) F)
    : Modification_d (presheaf_to_yoneda (yoneda_to_presheaf σ)).1 σ.
  Proof.
    intros Y.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; cbn.
      exact ((morphism_of (σ.1 Y) (left_unit h))
                o Core.components_of (laxnaturality_of σ h) (id₁ X))%morphism.
    - intros h₁ h₂ α.
      exact (yoneda_to_presheaf_to_yoneda_m_d_help σ α).
  Defined.

  Definition yoneda_to_presheaf_to_yoneda_m_is_modification
             (σ : PseudoTransformation (representable0 X) F)
    : is_modification (yoneda_to_presheaf_to_yoneda_m_d σ).
  Proof.
    intros Y₁ Y₂ f.
    apply path_natural_transformation.
    intros h ; cbn.
    rewrite (Fmor₂_id₂ F).
    rewrite !left_identity.
    rewrite !right_identity.
    pose (equiv_path_natural_transformation _ _ (transformation_assoc σ h f) (id₁ X)) as p.
    cbn in p.
    rewrite !identity_of, !left_identity, !right_identity in p.
    rewrite !associativity.
    rewrite p ; clear p.
    rewrite composition_of.
    rewrite <- !associativity.
    rewrite (commutes (laxnaturality_of σ f)).
    rewrite <- composition_of ; simpl.
    repeat f_ap.
    (* To see what's happening, do
       Transparent representable0.
       simpl.
     *)
    apply left_unit_assoc.
  Qed.

  Definition yoneda_to_presheaf_to_yoneda_m
             (σ : PseudoTransformation (representable0 X) F)
    : Modification (presheaf_to_yoneda (yoneda_to_presheaf σ)).1 σ
    := Build_Modification
         (yoneda_to_presheaf_to_yoneda_m_d σ)
         (yoneda_to_presheaf_to_yoneda_m_is_modification σ).
  
  Definition yoneda_to_presheaf_to_yoneda
    : (NaturalTransformation (presheaf_to_yoneda o yoneda_to_presheaf) 1)%functor.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - exact yoneda_to_presheaf_to_yoneda_m.
    - intros h₁ h₂ α.
      apply path_modification.
      funext Z.
      apply path_natural_transformation.
      intros g.
      cbn.
      rewrite <- !associativity.
      rewrite (commutes (α.1 Z)).
      rewrite !associativity.
      f_ap.
      pose (equiv_path_natural_transformation _ _ (α.2 X Z g) (id₁ X)) as p.
      cbn in p.
      rewrite !identity_of, !left_identity, !right_identity in p.
      apply p.
  Defined.

  Definition yoneda_to_presheaf_to_yoneda_inv_m_help
             (σ : PseudoTransformation (representable0 X) F)
             (Y : op C)
             {h₁ h₂ : Core.object ((representable0 X) Y)}
             (α : Core.morphism ((representable0 X) Y) h₁ h₂)
    : (((laxnaturality_of σ h₂)^-1 (id₁ X))
         o (σ Y) _1 (left_unit_inv h₂)
         o (σ Y) _1 α
      =
      ((F ₂ α) (σ.1 X (id₁ X)))
        o (((laxnaturality_of σ h₁)^-1 (id₁ X))
             o (σ Y) _1 (left_unit_inv h₁)))%morphism.
  Proof.
    refine (iso_moveR_Mp _ _ _) ; simpl.
    rewrite <- !associativity.
    do 2 refine (iso_moveL_pM _ _ _) ; simpl.
    pose (equiv_path_natural_transformation _ _ (laxnaturality_natural σ α) (id₁ X)).
    cbn in p.
    unfold bc_whisker_l, bc_whisker_r in p.
    rewrite identity_of in p.
    rewrite <- (right_identity _ _ _ ((F ₂ α) _)).
    rewrite !associativity.
    rewrite p ; clear p.
    rewrite left_identity.
    rewrite <- !associativity.
    rewrite <- composition_of.
    pose (left_unit_natural α) as p.
    unfold vcomp in p.
    rewrite <- p.
    rewrite composition_of.
    reflexivity.
  Qed.

  Definition yoneda_to_presheaf_to_yoneda_inv_m_d
             (σ : PseudoTransformation (representable0 X) F)
    : Modification_d σ (presheaf_to_yoneda (yoneda_to_presheaf σ)).1.
  Proof.
    intros Y.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; cbn.
      exact ((Core.components_of (laxnaturality_of σ h)^-1 (id₁ X))
               o morphism_of (σ Y) (left_unit_inv h))%morphism.
    - intros h₁ h₂ α.
      exact (yoneda_to_presheaf_to_yoneda_inv_m_help σ Y α).
  Defined.

  Definition yoneda_to_presheaf_to_yoneda_inv_m_is_modification
             (σ : PseudoTransformation (representable0 X) F)
    : is_modification (yoneda_to_presheaf_to_yoneda_inv_m_d σ).
  Proof.
    intros Y₁ Y₂ f.
    apply path_natural_transformation.
    intros h ; cbn.
    rewrite !identity_of.
    rewrite !left_identity.
    rewrite !right_identity.
    refine (iso_moveR_pM _ _ _). simpl.
    rewrite !associativity.
    do 2 refine (iso_moveL_Mp _ _ _) ; simpl.
    pose (equiv_path_natural_transformation _ _ (transformation_assoc σ h f) (id₁ X)) as p.
    cbn in p.
    rewrite !identity_of, !left_identity, !right_identity in p.
    rewrite p ; clear p.
    rewrite composition_of.
    rewrite <- !associativity.
    rewrite (commutes (laxnaturality_of σ f)).
    rewrite <- composition_of ; simpl.
    repeat f_ap.
    symmetry.
    apply left_unit_assoc.
  Qed.

  Definition yoneda_to_presheaf_to_yoneda_inv_m
             (σ : PseudoTransformation (representable0 X) F)
    : Modification σ (presheaf_to_yoneda (yoneda_to_presheaf σ)).1
    := Build_Modification
         (yoneda_to_presheaf_to_yoneda_inv_m_d σ)
         (yoneda_to_presheaf_to_yoneda_inv_m_is_modification σ).
  
  Definition yoneda_to_presheaf_to_yoneda_inv
    : (NaturalTransformation 1 (presheaf_to_yoneda o yoneda_to_presheaf))%functor.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - exact yoneda_to_presheaf_to_yoneda_inv_m.
    - intros h₁ h₂ α.
      apply path_modification.
      funext Z.
      apply path_natural_transformation.
      intros g ; cbn.
      rewrite <- !associativity.
      refine (iso_moveR_Mp _ _ _) ; simpl.
      rewrite <- !associativity.
      do 2 refine (iso_moveL_pM _ _ _) ; simpl.
      rewrite (commutes (α.1 Z)).
      rewrite !associativity.
      f_ap.
      pose (equiv_path_natural_transformation _ _ (α.2 X Z g) (id₁ X)) as p.
      cbn in p.
      rewrite !identity_of, !left_identity, !right_identity in p.
      apply p^.
  Defined.

  Definition yoneda_to_presheaf_to_yoneda_retr
    : (yoneda_to_presheaf_to_yoneda
         o yoneda_to_presheaf_to_yoneda_inv = 1)%natural_transformation.
  Proof.
    apply path_natural_transformation.
    intros σ.
    apply path_modification.
    funext Y.
    apply path_natural_transformation.
    intros x ; cbn.
    rewrite !associativity.
    rewrite !(ap (fun z => _ o z)%morphism (associativity _ _ _ _ _ _ _ _)^).
    rewrite iso_component.
    rewrite right_inverse.
    rewrite left_identity.
    rewrite <- composition_of.
    rewrite <- inverse_of_left_unit, right_inverse.
    apply identity_of.
  Qed.

  Definition yoneda_to_presheaf_to_yoneda_sect
    : (yoneda_to_presheaf_to_yoneda_inv
         o yoneda_to_presheaf_to_yoneda = 1)%natural_transformation.
  Proof.
    apply path_natural_transformation.
    intros σ.
    apply path_modification.
    funext Y.
    apply path_natural_transformation.
    intros x ; cbn.
    rewrite !associativity.
    rewrite !(ap (fun z => _ o z)%morphism (associativity _ _ _ _ _ _ _ _)^).
    rewrite <- composition_of.
    rewrite <- inverse_of_left_unit, left_inverse.
    rewrite identity_of, left_identity.
    rewrite iso_component.
    apply left_inverse.
  Qed.

  Global Instance iso_yoneda_to_presheaf_to_yoneda
    : @IsIsomorphism (_ -> _) _ _ yoneda_to_presheaf_to_yoneda.
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - exact yoneda_to_presheaf_to_yoneda_inv.
    - exact yoneda_to_presheaf_to_yoneda_sect.
    - exact yoneda_to_presheaf_to_yoneda_retr.
  Defined.

  Definition yoneda_lemma
    : @adjoint_equivalence PreCat (Pseudo (op C) PreCat⟦representable0 X,F⟧) (F X).
  Proof.
    simple refine (equiv_to_adjequiv _ _).
    - exact yoneda_to_presheaf.
    - simple refine (@Build_IsEquivalence
                       PreCat
                       _
                       _
                       _
                       presheaf_to_yoneda _ _ _ _).
  Defined.
End YonedaLemma.

Section YonedaLocalEquivalence.
  Context `{Univalence}
          {C : BiCategory}.
  Variable (X Y : C).

  Definition yoneda_to_presheaf_representable_m_d
             (f : C⟦X,Y⟧)
    : Modification_d (yoneda C ₁ f).1 (presheaf_to_yoneda (representable0 Y) X f).1.
  Proof.
    intros Z.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; cbn in *.
      apply id₂.
    - intros ; cbn.
      unfold id₂.
      rewrite left_identity, right_identity.
      reflexivity.
  Defined.

  Definition yoneda_to_presheaf_representable_is_modification
             (f : C⟦X,Y⟧)
    : is_modification (yoneda_to_presheaf_representable_m_d f).
  Proof.
    intros Z₁ Z₂ h.
    apply path_natural_transformation.
    intros q.
    cbn in *.
    unfold id₂, bc_whisker_l, bc_whisker_r.
    rewrite !hcomp_id₂, !left_identity, right_identity.
    reflexivity.
  Qed.

  Definition yoneda_to_presheaf_representable_m
             (f : C⟦X,Y⟧)
    : Modification (yoneda C ₁ f).1 (presheaf_to_yoneda (representable0 Y) X f).1
    := Build_Modification
         (yoneda_to_presheaf_representable_m_d f)
         (yoneda_to_presheaf_representable_is_modification f).

  Definition yoneda_to_presheaf_representable
    : NaturalTransformation (Fmor (yoneda C) X Y) (presheaf_to_yoneda (representable0 Y) X).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - exact yoneda_to_presheaf_representable_m.
    - intros Z₁ Z₂ h.
      apply path_modification.
      funext Z₃.
      apply path_natural_transformation.
      intros g ; cbn.
      rewrite left_identity, right_identity.
      reflexivity.
  Defined.

  (* TODO: slow when reading definition *)
  Definition presheaf_representable_to_yoneda_m_d
             (f : C⟦X,Y⟧)
    : Modification_d (presheaf_to_yoneda (representable0 Y) X f).1 (yoneda C ₁ f).1.
  Proof.
    intros Z.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros h ; cbn in *.
      apply id₂.
    - intros ; cbn.
      unfold id₂.
      rewrite left_identity, right_identity.
      reflexivity.
  Defined.

  Definition presheaf_representable_to_yoneda_is_modification
             (f : C⟦X,Y⟧)
    : is_modification (presheaf_representable_to_yoneda_m_d f).
  Proof.
    intros Z₁ Z₂ h.
    apply path_natural_transformation.
    intros q.
    cbn in *.
    unfold id₂, bc_whisker_l, bc_whisker_r.
    rewrite !hcomp_id₂, !left_identity, right_identity.
    reflexivity.
  Qed.

  (* TODO: slow when reading definition *)
  Definition presheaf_representable_to_yoneda_m
             (f : C⟦X,Y⟧)
    := Build_Modification
         (presheaf_representable_to_yoneda_m_d f)
         (presheaf_representable_to_yoneda_is_modification f).

  Definition presheaf_representable_to_yoneda
    : NaturalTransformation (presheaf_to_yoneda (representable0 Y) X) (Fmor (yoneda C) X Y).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - exact presheaf_representable_to_yoneda_m.
    - intros Z₁ Z₂ h.
      apply path_modification.
      funext Z₃.
      apply path_natural_transformation.
      intros g ; cbn.
      rewrite left_identity, right_identity.
      reflexivity.
  Defined.

  Global Instance iso_presheaf_representable_to_yoneda
    : @IsIsomorphism (_ -> _) _ _ presheaf_representable_to_yoneda.
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - exact yoneda_to_presheaf_representable.
    - apply path_natural_transformation.
      intros f.
      apply path_modification.
      funext Z.
      apply path_natural_transformation.
      intros g ; cbn.
      apply left_identity.
    - apply path_natural_transformation.
      intros f.
      apply path_modification.
      funext Z.
      apply path_natural_transformation.
      intros g ; cbn.
      apply left_identity.
  Defined.
  
  Definition yoneda_local_equivalence_help
    : @is_equivalence PreCat _ _ (Fmor (yoneda C) X Y).
  Proof.
    refine (@iso_equiv PreCat
                       (C ⟦ X, Y ⟧)
                       (Pseudo (op C) PreCat ⟦ (yoneda C) X, (yoneda C) Y ⟧)
                       (presheaf_to_yoneda (representable0 Y) X)
                       (Fmor (yoneda C) X Y)                    
                       _
                       presheaf_representable_to_yoneda
                       _).
    apply (adjoint_equivalence_is_equivalence
             (inv_equivalence (yoneda_lemma (representable0 Y) X))).
  Defined.
End YonedaLocalEquivalence.

Definition yoneda_local_equivalence
           `{Univalence}
           (C : BiCategory)
  : local_equivalence (yoneda C)
  := fun X Y =>
       (@equiv_to_adjequiv _ PreCat _ _
                           (Fmor (yoneda C) X Y)
                           (yoneda_local_equivalence_help X Y)).2.