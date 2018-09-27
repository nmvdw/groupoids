Require Import HoTT.
From HoTT.Categories Require Import
     Functor
     NaturalTransformation
     FunctorCategory.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.adjoint
     bicategory.equivalence
     bicategory.equiv_to_adjequiv
     bicategory.examples.cat
     bicategory.examples.arrow_subcategory
     bicategory.examples.full_sub
     bicategory.examples.lax_functors_bicat
     bicategory.examples.precat
     bicategory.examples.pseudo_functors_bicat
     lax_functor.lax_functor
     lax_functor.weak_equivalence
     lax_functor.examples.factor_full_sub
     lax_transformation.lax_transformation
     lax_transformation.transformation_category
     lax_transformation.examples.identity
     lax_transformation.examples.composition
     lax_transformation.examples.factor_full_sub
     lax_transformation.examples.inclusion_transformation
     modification.modification
     modification.examples.composition
     modification.examples.identity
     modification.examples.factor_full_sub
     modification.examples.factor_id_modification
     modification.examples.factor_comp_modification.

Definition comp_modification_pseudo_functor
      `{Univalence}
      {C D : BiCategory}
      {F G : PseudoFunctor C D}
      {η₁ η₂ η₃ : PseudoTransformation F G}
      (m₁ : Modification η₂ η₃) (m₂ : Modification η₁ η₂)
      (A : C)
  : (@vcomp (Pseudo C D) _ _ _ _ _ m₁ m₂ : Modification _ _) A
    =
    m₁ A ∘ m₂ A
  := idpath.

Section RestrictImageFunctor.
  Context `{Univalence}
          {C₁ C₂ C₃ : BiCategory}.
  Variable (F : PseudoFunctor C₁ (Pseudo C₂ C₃))
           (P : C₃ -> hProp)
           (HP : forall (X : C₁) (Y : C₂), P ((F X : PseudoFunctor C₂ C₃) Y)).

  Definition restrict_image_functor_d
    : PseudoFunctor_d C₁ (Pseudo C₂ (full_sub C₃ P)).
  Proof.
    make_pseudo_functor.
    - intros X.
      exact (pseudo_factor (F X) P (HP X)).
    - intros X Y f ; simpl.
      exact (pseudo_factor_transformation _ (F ₁ f) _ _).
    - intros X Y f g α ; simpl.
      exact (factor_modification _ (F ₂ α) _ _).
    - intros X Y Z g f ; simpl.
      refine (comp_modification (factor_modification _ (Fcomp₁ F g f) _ _) _).
      apply factor_comp_modification.
    - intros X ; simpl.
      refine (comp_modification (factor_modification _ (Fid F X) _ _) _).
      apply factor_id_modification.
    - intros X Y Z g f ; cbn.
      exact (factor_modification _ (Fcomp₁_inv F g f) _ _).
    - intros X ; simpl.
      exact (factor_modification _ (Fid_inv F X) _ _).
  Defined.    

  Definition restrict_image_functor_is_pseudo
    : is_pseudo_functor_p restrict_image_functor_d.
  Proof.
    make_is_pseudo.
    - intros X Y f.
      apply path_modification.
      funext Z ; cbn.
      rewrite Fmor₂_id₂.
      reflexivity.
    - intros X Y f g h η ε.
      apply path_modification.
      funext Z ; cbn.
      rewrite Fmor₂_vcomp.
      reflexivity.
    - intros X Y Z f₁ f₂ g₁ g₂ η₁ η₂.
      apply path_modification.
      funext A ; simpl.
      unfold factor_comp_modification_d ; cbn.
      rewrite !vcomp_right_identity.
      exact (ap (fun z => mod_component z A) (Fcomp₂ F η₂ η₁)).
    - intros X Y f.
      apply path_modification.
      funext A ; simpl.
      unfold factor_id_modification_d, factor_comp_modification_d ; cbn.
      rewrite !vcomp_right_identity.
      exact (ap (fun z => mod_component z A) (F_right_unit F f)).
    - intros X Y f.
      apply path_modification.
      funext A ; simpl.
      unfold factor_id_modification_d, factor_comp_modification_d ; cbn.
      rewrite !vcomp_right_identity.
      exact (ap (fun z => mod_component z A) (F_left_unit F f)).      
    - intros W X Y Z h g f.
      apply path_modification.
      funext A ; cbn.
      unfold factor_id_modification_d, factor_comp_modification_d ; cbn.
      rewrite !vcomp_right_identity.
      exact (ap (fun z => mod_component z A) (F_assoc F h g f)).
    - intros X Y Z g f.
      apply path_modification.
      funext A ; cbn.
      unfold factor_id_modification_d, factor_comp_modification_d ; cbn.
      rewrite <- !vcomp_assoc.
      rewrite vcomp_right_identity.
      pose (vcomp_left_inverse (Fcomp₁ F g f)).
      refine ((comp_modification_pseudo_functor (Fcomp₁_inv F g f) (Fcomp₁ F g f) A)^ @ _).
      rewrite vcomp_left_inverse.
      reflexivity.
    - intros X Y Z g f.
      apply path_modification.
      funext A ; cbn.
      unfold factor_id_modification_d, factor_comp_modification_d ; cbn.
      rewrite vcomp_right_identity.
      refine ((comp_modification_pseudo_functor (Fcomp₁ F g f) (Fcomp₁_inv F g f) A)^ @ _).
      rewrite vcomp_right_inverse.
      reflexivity.
    - intros X.
      apply path_modification.
      funext A ; cbn.
      unfold factor_id_modification_d, factor_comp_modification_d ; cbn.
      rewrite vcomp_right_identity.
      refine ((comp_modification_pseudo_functor (Fid F X) (Fid_inv F X) A)^ @ _).
      rewrite vcomp_right_inverse.
      reflexivity.
    - intros X.
      apply path_modification.
      funext A ; cbn.
      unfold factor_id_modification_d, factor_comp_modification_d ; cbn.
      rewrite vcomp_right_identity.
      refine ((comp_modification_pseudo_functor (Fid_inv F X) (Fid F X) A)^ @ _).
      rewrite vcomp_left_inverse.
      reflexivity.
  Qed.

  Definition restrict_image_functor
    : PseudoFunctor C₁ (Pseudo C₂ (full_sub C₃ P))
    := Build_PseudoFunctor
         restrict_image_functor_d
         restrict_image_functor_is_pseudo.

  Definition inclusion_pseudo
             (X Y : C₁)
    : Functor
        (Pseudo C₂ C₃ ⟦ F X, F Y ⟧)
        (Pseudo C₂ (full_sub C₃ P) ⟦restrict_image_functor X,restrict_image_functor Y⟧).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - intros η.
      exact (pseudo_factor_transformation _ η _ _).
    - intros η₁ η₂ m.
      exact (factor_modification _ m _ _).
    - intros η₁ η₂ η₃ m₁ m₂.
      apply path_modification.
      reflexivity.
    - intros η.
      apply path_modification.
      reflexivity.
  Defined.

  Definition inclusion_pseudo_inv
             (X Y : C₁)
    : Functor
        (Pseudo C₂ (full_sub C₃ P) ⟦restrict_image_functor X,restrict_image_functor Y⟧)
        (Pseudo C₂ C₃ ⟦ F X, F Y ⟧).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - intros η.
      apply (pseudo_inclusion_transformation _ _ _ η).
    - intros η₁ η₂ ; exact idmap.
    - intros.
      apply path_modification.
      reflexivity.
    - intros.
      apply path_modification.
      reflexivity.
  Defined.

  Definition inclusion_pseudo_inclusion_pseudo_inv_comp_d
             {X Y : C₁}
             (η : PseudoTransformation
                    (lax_factor (F X : PseudoFunctor _ _) P (HP X))
                    (lax_factor (F Y : PseudoFunctor _ _) P (HP Y)))
    : Modification_d
        ((inclusion_pseudo X Y o inclusion_pseudo_inv X Y)%functor η).1
        η
    := fun _ => id₂ _.

  Definition inclusion_pseudo_inclusion_pseudo_inv_is_modification
             {X Y : C₁}
             (η : PseudoTransformation
                    (lax_factor (F X : PseudoFunctor _ _) P (HP X))
                    (lax_factor (F Y : PseudoFunctor _ _) P (HP Y)))
    : is_modification (inclusion_pseudo_inclusion_pseudo_inv_comp_d η).
  Proof.
    intros Z₁ Z₂ f.
    refine (ap (fun z => _ ∘ z) (hcomp_id₂ _ _) @ _).
    refine (_ @ ap (fun z => z ∘ _) (hcomp_id₂ _ _)^).
    exact (vcomp_right_identity _ @ (vcomp_left_identity _)^).
  Qed.

  Definition inclusion_pseudo_inclusion_pseudo_inv
             (X Y : C₁)
    : NaturalTransformation
        (inclusion_pseudo X Y o inclusion_pseudo_inv X Y)%functor
        1%functor.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros η.
      exact (Build_Modification
               (inclusion_pseudo_inclusion_pseudo_inv_comp_d η)
               (inclusion_pseudo_inclusion_pseudo_inv_is_modification η)).
    - intros Z₁ Z₂ f.
      apply path_modification.
      funext h ; simpl.
      exact (vcomp_left_identity _ @ (vcomp_right_identity _)^).
  Defined.

  Global Instance is_isomorphism_inclusion_pseudo_inclusion_pseudo_inv
         (X Y : C₁)
    : @IsIsomorphism (_ -> _) _ _ (inclusion_pseudo_inclusion_pseudo_inv X Y).
  Proof.
    apply isisomorphism_natural_transformation.
    intros η.
    apply arrow_subcategory_isomorphism.
    apply _.
  Defined.

  Definition inclusion_pseudo_inv_inclusion_pseudo_comp_d
             {X Y : C₁}
             (η : PseudoTransformation
                    (F X : PseudoFunctor _ _)
                    (F Y : PseudoFunctor _ _))
    : Modification_d
        ((inclusion_pseudo_inv X Y o inclusion_pseudo X Y)%functor η).1
        η
    := fun _ => id₂ _.

  Definition inclusion_pseudo_inv_inclusion_pseudo_is_modification
             {X Y : C₁}
             (η : PseudoTransformation
                    (F X : PseudoFunctor _ _)
                    (F Y : PseudoFunctor _ _))
    : is_modification (inclusion_pseudo_inv_inclusion_pseudo_comp_d η).
  Proof.
    intros Z₁ Z₂ f.
    refine (ap (fun z => _ ∘ z) (hcomp_id₂ _ _) @ _).
    refine (_ @ ap (fun z => z ∘ _) (hcomp_id₂ _ _)^).
    exact (vcomp_right_identity _ @ (vcomp_left_identity _)^).
  Qed.

  Definition inclusion_pseudo_inv_inclusion_pseudo
             (X Y : C₁)
    : NaturalTransformation
        (inclusion_pseudo_inv X Y o inclusion_pseudo X Y)%functor
        1%functor.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros η.
      exact (Build_Modification
               (inclusion_pseudo_inv_inclusion_pseudo_comp_d η)
               (inclusion_pseudo_inv_inclusion_pseudo_is_modification η)).
    - intros Z₁ Z₂ f.
      apply path_modification.
      funext h ; simpl.
      exact (vcomp_left_identity _ @ (vcomp_right_identity _)^).
  Defined.

  Global Instance is_isomorphism_inclusion_pseudo_inv_inclusion_pseudo
         (X Y : C₁)
    : @IsIsomorphism (_ -> _) _ _ (inclusion_pseudo_inv_inclusion_pseudo X Y).
  Proof.
    apply isisomorphism_natural_transformation.
    intros η.
    apply arrow_subcategory_isomorphism.
    apply _.
  Defined.  

  Definition inclusion_pseudo_equivalence
             (X Y : C₁)
    : @is_equivalence PreCat _ _ (inclusion_pseudo X Y)
    := @Build_IsEquivalence PreCat
                            _ _
                            (inclusion_pseudo X Y)
                            (inclusion_pseudo_inv X Y)
                            (inclusion_pseudo_inclusion_pseudo_inv X Y)
                            (inclusion_pseudo_inv_inclusion_pseudo X Y)
                            _ _.

  Definition Fmor_restrict_image_functor
             (X Y : C₁)
    : (Fmor restrict_image_functor X Y = inclusion_pseudo X Y o Fmor F X Y)%functor.
  Proof.
    simple refine (path_functor_natural _ _).
    - reflexivity.
    - intros η₁ η₂ m.
      apply path_modification.
      funext Z ; cbn.
      rewrite vcomp_left_identity, vcomp_right_identity.
      reflexivity.
  Defined.
    
  Definition restrict_image_functor_local_equivalence
             (local : local_equivalence F)
    : local_equivalence restrict_image_functor.
  Proof.
    intros X Y.
    rewrite Fmor_restrict_image_functor.
    pose (@equiv_to_adjequiv
            _ PreCat _ _
            (inclusion_pseudo X Y) (inclusion_pseudo_equivalence X Y)) as a₁.
    pose ((Fmor F X Y;local X Y) : @adjoint_equivalence PreCat _ _) as a₂.
    apply (comp_adjequiv a₂ a₁).
  Defined.
End RestrictImageFunctor.