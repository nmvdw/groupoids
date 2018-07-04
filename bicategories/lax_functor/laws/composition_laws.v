Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     lax_functor.lax_functor
     lax_functor.examples.composition
     lax_functor.examples.identity.

Definition lax_comp_associative
           `{Univalence}
           {C₁ C₂ C₃ C₄ : BiCategory}
           (F₃ : LaxFunctor C₃ C₄)
           (F₂ : LaxFunctor C₂ C₃)
           (F₁ : LaxFunctor C₁ C₂)
  : lax_comp (lax_comp F₃ F₂) F₁ = lax_comp F₃ (lax_comp F₂ F₁).
Proof.
  apply path_LaxFunctor.
  simple refine (path_LaxFunctor_d _ _ _).
  - reflexivity.
  - intros X Y ; cbn.
    unfold lax_comp ; simpl.
    unfold lax_comp_mor ; cbn.
    unfold lax_comp_mor.
    apply Functor.Composition.associativity.
  - split.
    + intros X ; cbn.
Admitted.
      
Definition lax_comp_left_identity
           `{Univalence}
           {C D : BiCategory}
           (F : LaxFunctor C D)
  : lax_comp (lax_id_functor D) F = F.
Proof.
  (*apply path_LaxFunctor.
  simple refine (path_LaxFunctor_d _ _ _).
  - reflexivity.
  - intros X Y ; cbn.
    unfold lax_comp_mor, lax_id_functor, Fmor ; cbn.
    exact (@Functor.Composition.left_identity
             _
             (Hom C X Y)
             (Hom D (Fobj F X) (Fobj F Y))
             (Fmor_d F.1)).
  - split.
    + intros X ; simpl.
      unfold lax_comp_mor, lax_id_functor, lax_id_functor_d, lax_comp_id, Fmor, Fid ; cbn.
      unfold paths_rect, paths_ind.
      pose (@Functor.Composition.left_identity
                 _
                 (Hom C X X)
                 (Hom D (F X) (F X))
                 (Fmor F))^.
      unfold Fmor in p.
      cbn in p.
      induction p.
      simpl.
      compute.
      induction p ; compute.*)
Admitted.

Definition lax_comp_right_identity
           `{Univalence}
           {C D : BiCategory}
           (F : LaxFunctor C D)
  : lax_comp F (lax_id_functor C) = F.
Proof.
  apply path_LaxFunctor.
  simple refine (path_LaxFunctor_d _ _ _).
  - reflexivity.
  - intros X Y ; cbn.
    unfold lax_comp_mor, lax_id_functor, Fmor ; cbn.
    apply Functor.Composition.right_identity.
  - split.
    + intros ; cbn.
Admitted.
(* unfold lax_comp_mor, lax_id_functor, lax_comp_id, lax_id_functor_d ; simpl.
      pose (Functor.Composition.right_identity (@Fmor_d _ _ _ F.1 X X)).
      induction p.
      cbn.
      rewrite identity_of, left_identity.
      pose (Functor.Composition.right_identity (@Fmor _ _ _ F X X)).
      induction p.
      
      cbn.
      reflexivity.
      pose (Functor.Composition.right_identity (@Fmor _ _ _ F X X)).
      induction p.

      path_induction.
      induction p ; simpl.
      induction (Functor.Composition.right_identity (@Fmor_d _ _ _ F.1 X X)).
      admit.
    + intros ; cbn.
      apply path_natural_transformation.
      intros [g f] ; cbn.
      induction (Functor.Composition.right_identity (@Fmor_d _ _ _ F.1 X Y)).
      induction (Functor.Composition.right_identity (@Fmor_d _ _ _ F.1 Y Z)).
      induction (Functor.Composition.right_identity (@Fmor_d _ _ _ F.1 X Z)).
      cbn.
      apply path_natural_transformation.
      destruct F as [F_d F_p] ; cbn.
      destruct F_d ; cbn.
      unfold Functor.Composition.right_identity.
      unfold Paths.path_functor_uncurried ; cbn.
      appl
      reflexivity.
      cbn in *.*)