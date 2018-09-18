Require Import HoTT.
From HoTT.Categories Require Import
     Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category bicategory.bicategory bicategory.strict.

Definition components_idtoiso
           `{Funext}
           {C D : PreCategory}
           {F G : Functor C D}
           (p : F = G)
           (X : C)
  : components_of (@morphism_isomorphic _ _ _ (idtoiso (C -> D) p)) X
    =
    idtoiso D (ap (fun H => object_of H X) p).
Proof.
  induction p ; cbn.
  reflexivity.
Qed.

Definition ap_path_functor_uncurried
           `{Funext}
           {C D : PreCategory}
           {F G : Functor C D}
           (p : Core.object_of F = Core.object_of G)
           Hp
           (X : C)
  : ap (fun H => object_of H X) (Paths.path_functor_uncurried _  _ (p;Hp)) = ap10 p X.
Proof.
  destruct F as [Fobj Fmor FC FI], G as [Gobj Gmor GC GI] ; cbn in *.
  induction p ; cbn in *.
  induction Hp ; simpl.
  assert (FC = GC) as ->.
  { apply path_ishprop. }
  assert (FI = GI) as ->.
  { apply path_ishprop. }
  cbn.
  rewrite Paths.path_functor_uncurried_idpath.
  reflexivity.
Qed.

Section CatBiCategory.
  Context `{Funext}.

  Definition precat_d : BiCategory_d.
  Proof.
    make_bicategory.
    - exact PreCategory.
    - exact functor_category.
    - exact (fun _ => 1%functor).
    - exact (fun _ _ _ F => fst F o snd F)%functor.
    - intros C₁ C₂ C₃ [F₁ F₂] [G₁ G₂] [η₁ η₂] ; simpl in *.
      exact (whisker_r η₁ G₂ o whisker_l F₁ η₂)%natural_transformation.
    - intros C₁ C₂ F ; simpl in *.
      apply Composition.left_identity_natural_transformation_1.
    - intros C₁ C₂ F ; simpl in *.
      apply Composition.left_identity_natural_transformation_2.
    - intros C₁ C₂ F ; simpl in *.
      apply Composition.right_identity_natural_transformation_1.
    - intros C₁ C₂ F ; simpl in *.
      apply Composition.right_identity_natural_transformation_2.
    - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ ; simpl in *.
      apply Composition.associator_1.
    - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ ; simpl in *.
      apply Composition.associator_2.
  Defined.

  Definition precat_is_bicategory : is_bicategory precat_d.
  Proof.
    make_is_bicategory.
    - intros C₁ C₂ C₃ [F₁ F₂] ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite identity_of, left_identity.
      reflexivity.
    - intros C₁ C₂ C₃ [F₁ F₂] [G₁ G₂] [H₁ H₂] [η₁ η₂] [ε₁ ε₂] ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite composition_of.
      rewrite !associativity.
      f_ap.
      rewrite <- !associativity.
      f_ap.
      apply ε₁.
    - intros C₁ C₂ F G η ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite !left_identity, right_identity.
      reflexivity.
    - intros C₁ C₂ F₁ F₂ η ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite !left_identity, right_identity.
      reflexivity.
    - intros C₁ C₂ F₁ F₂ η ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite identity_of, left_identity, right_identity.
      reflexivity.
    - intros C₁ C₂ F₁ F₂ η ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite identity_of, left_identity, !right_identity.
      reflexivity.
    - intros C₁ C₂ F ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      apply left_identity.
    - intros C₁ C₂ F ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      apply left_identity.
    - intros C₁ C₂ F ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      apply left_identity.
    - intros C₁ C₂ F ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      apply left_identity.
    - intros C₁ C₂ C₃ C₄ H₁ H₂ G₁ G₂ F₁ F₂ ηH ηG ηF ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite left_identity, right_identity, !composition_of, !associativity.
      reflexivity.
    - intros C₁ C₂ C₃ C₄ H₁ H₂ G₁ G₂ F₁ F₂ ηH ηG ηF ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite left_identity, right_identity, !composition_of, !associativity.
      reflexivity.
    - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      apply left_identity.
    - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      apply left_identity.
    - intros C₁ C₂ C₃ G F ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite !identity_of, !left_identity.
      reflexivity.
    - intros C₁ C₂ C₃ C₄ C₅ F₁ F₂ F₃ F₄ ; simpl in *.
      apply path_natural_transformation.
      intros X ; simpl.
      rewrite !identity_of, !left_identity.
      reflexivity.
  Qed.

  Definition PreCat : BiCategory
    := Build_BiCategory precat_d precat_is_bicategory.

  Definition StrictPreCat : IsStrict PreCat.
  Proof.
    make_strict.
    - intros C D F ; cbn in *.
      apply Laws.left_identity.
    - intros C D f ; cbn in *.
      apply Laws.right_identity.
    - intros W X Y Z h g f ; cbn in *.
      apply Laws.associativity.
    - intros C₁ C₂ C₃ G F ; cbn in *.
      rewrite <- (Laws.triangle F G).
      reflexivity.
    - intros C₁ C₂ C₃ C₄ C₅ F₁ F₂ F₃ F₄ ; cbn in *.
      rewrite (Laws.pentagon F₄ F₃ F₂ F₁).
      rewrite concat_pp_p.
      reflexivity.
    - intros C D F ; cbn in *.
      apply path_natural_transformation.
      intros X ; cbn.
      rewrite components_idtoiso.
      unfold Laws.left_identity.
      rewrite (@ap_path_functor_uncurried _ _ _ (1 o F) F idpath idpath).
      reflexivity.
    - intros C D F ; cbn in *.
      apply path_natural_transformation.
      intros X ; cbn.
      rewrite components_idtoiso.
      unfold Laws.right_identity.
      rewrite (@ap_path_functor_uncurried _ _ _ (F o 1) F idpath idpath).
      reflexivity.
    - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ ; cbn in *.
      apply path_natural_transformation.
      intros X ; cbn.
      rewrite components_idtoiso.
      unfold Laws.associativity.
      rewrite (@ap_path_functor_uncurried
                 _ _ _
                 (F₁ o F₂ o F₃) (F₁ o (F₂ o F₃)) idpath idpath).
      reflexivity.
  Defined.
End CatBiCategory.