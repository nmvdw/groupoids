Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category bicategory.bicategory.

Section CatBiCategory.
  Context `{Univalence}.
  
  Definition cat_H (C₁ C₂ : PreCategory) : PreCategory
    := functor_category C₁ C₂.

  Definition comp_funct (C₁ C₂ C₃ : PreCategory)
    : Functor (cat_H C₂ C₃ * cat_H C₁ C₂) (cat_H C₁ C₃).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - cbn ; intros [p₁ p₂].
      exact (p₁ o p₂)%functor.
    - intros [F₁ F₂] [G₁ G₂] [r₁ r₂] ; cbn in *.
      exact (whisker_r r₁ G₂ o whisker_l F₁ r₂)%natural_transformation.
    - intros [F₁ F₂] [G₁ G₂] [H₁ H₂] [a₁ a₂] [b₁ b₂] ; cbn in *.
      apply path_natural_transformation.
      intros x ; cbn.
      rewrite composition_of.
      rewrite !associativity.
      f_ap.
      rewrite <- !associativity.
      f_ap.
      apply a₁.
    - intros [F₁ F₂].
      cbn in *.
      rewrite NaturalTransformation.Composition.Laws.whisker_r_left_identity.
      rewrite NaturalTransformation.Composition.Laws.whisker_l_right_identity.
      apply NaturalTransformation.Composition.Laws.left_identity.
  Defined.

  Definition nUnitor_l (C₁ C₂ : PreCategory)
    : @NaturalTransformation
        (cat_H C₁ C₂)
        (cat_H C₁ C₂)
        (comp_funct C₁ C₂ C₂ o (@const_functor (cat_H C₁ C₂) (cat_H C₂ C₂)
                                               (Functor.identity C₂) * 1))
        (Functor.identity (cat_H C₁ C₂)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros C ; cbn.
      simple refine (Build_NaturalTransformation _ _ _ _).
      * intros X ; cbn.
        apply identity.
      * intros X Y f ; cbn.
        rewrite left_identity, right_identity.
        reflexivity.
    + intros F G a ; cbn.
      apply path_natural_transformation.
      intros x ; cbn.
      rewrite !left_identity, right_identity.
      reflexivity.
  Defined.

  Definition nUnitor_l_inv (C₁ C₂ : PreCategory)
    : @NaturalTransformation
        (cat_H C₁ C₂)
        (cat_H C₁ C₂)
        (Functor.identity (cat_H C₁ C₂))
        (comp_funct C₁ C₂ C₂ o (@const_functor (cat_H C₁ C₂) (cat_H C₂ C₂)
                                               (Functor.identity C₂) * 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros C ; cbn.
      simple refine (Build_NaturalTransformation _ _ _ _).
      * intros X ; cbn.
        apply identity.
      * intros X Y f ; cbn.
        rewrite left_identity, right_identity.
        reflexivity.
    + intros F G a ; cbn.
      apply path_natural_transformation.
      intros x ; cbn.
      rewrite !left_identity, right_identity.
      reflexivity.
  Defined.

  Global Instance nUnitor_l_iso (C₁ C₂ : PreCategory)
    : @IsIsomorphism (cat_H C₁ C₂ -> cat_H C₁ C₂) _ _ (nUnitor_l C₁ C₂).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply nUnitor_l_inv.
    - cbn.
      apply path_natural_transformation.
      intros F ; cbn in *.
      apply path_natural_transformation.
      intros X ; cbn in *.
      apply left_identity.
    - cbn.
      apply path_natural_transformation.
      intros F ; cbn in *.
      apply path_natural_transformation.
      intros X ; cbn in *.
      apply left_identity.
  Defined.

  Definition nUnitor_r (C₁ C₂ : PreCategory)
    : @NaturalTransformation
        (cat_H C₁ C₂)
        (cat_H C₁ C₂)
        (comp_funct C₁ C₁ C₂ o (1 * @const_functor (cat_H C₁ C₂) (cat_H C₁ C₁)
                                                   (Functor.identity C₁)))
        (Functor.identity (cat_H C₁ C₂)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros F ; cbn.
      simple refine (Build_NaturalTransformation _ _ _ _).
      * intros X ; cbn.
        apply identity.
      * intros X Y f ; cbn.
        rewrite left_identity, right_identity.
        reflexivity.
    + intros F G a ; cbn.
      apply path_natural_transformation.
      intros x ; cbn.
      rewrite identity_of, !left_identity, right_identity.
      reflexivity.
  Defined.

  Definition nUnitor_r_inv (C₁ C₂ : PreCategory)
    : @NaturalTransformation
        (cat_H C₁ C₂)
        (cat_H C₁ C₂)
        (Functor.identity (cat_H C₁ C₂))
        (comp_funct C₁ C₁ C₂ o (1 * @const_functor (cat_H C₁ C₂) (cat_H C₁ C₁)
                                                   (Functor.identity C₁))).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros F ; cbn.
      simple refine (Build_NaturalTransformation _ _ _ _).
      * intros X ; cbn.
        apply identity.
      * intros X Y f ; cbn.
        rewrite left_identity, right_identity.
        reflexivity.
    + intros F G a ; cbn.
      apply path_natural_transformation.
      intros x ; cbn.
      rewrite identity_of, left_identity, !right_identity.
      reflexivity.
  Defined.

  Global Instance nUnitor_r_iso (C₁ C₂ : PreCategory)
    : @IsIsomorphism (cat_H C₁ C₂ -> cat_H C₁ C₂) _ _ (nUnitor_r C₁ C₂).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply nUnitor_r_inv.
    - cbn.
      apply path_natural_transformation.
      intros F ; cbn in *.
      apply path_natural_transformation.
      intros X ; cbn in *.
      apply left_identity.
    - cbn.
      apply path_natural_transformation.
      intros F ; cbn in *.
      apply path_natural_transformation.
      intros X ; cbn in *.
      apply left_identity.
  Defined.

  Definition nAssociator (C₁ C₂ C₃ C₄ : PreCategory)
    : NaturalTransformation
        (comp_funct C₁ C₂ C₄ o (comp_funct C₂ C₃ C₄, 1))
        (comp_funct C₁ C₃ C₄ o (1, comp_funct C₁ C₂ C₃)
                        o assoc_prod (cat_H C₃ C₄) (cat_H C₂ C₃) (cat_H C₁ C₂)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [[F₁ F₂] F₃] ; cbn in *.
      simple refine (Build_NaturalTransformation _ _ _ _).
      * intros X ; cbn.
        apply identity.
      * intros X Y f ; cbn.
        rewrite left_identity, right_identity.
        reflexivity.
    + intros [[F₁ F₂] F₃] [[G₁ G₂] G₃] [[f₁ f₂] f₃].
      apply path_natural_transformation ; cbn in *.
      intros x.
      rewrite left_identity, right_identity, composition_of.
      rewrite !associativity.
      reflexivity.
  Defined.

  Definition nAssociator_inv (C₁ C₂ C₃ C₄ : PreCategory)
    : NaturalTransformation
        (comp_funct C₁ C₃ C₄ o (1, comp_funct C₁ C₂ C₃)
                    o assoc_prod (cat_H C₃ C₄) (cat_H C₂ C₃) (cat_H C₁ C₂))
        (comp_funct C₁ C₂ C₄ o (comp_funct C₂ C₃ C₄, 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [[F₁ F₂] F₃] ; cbn in *.
      simple refine (Build_NaturalTransformation _ _ _ _).
      * intros X ; cbn.
        apply identity.
      * intros X Y f ; cbn.
        rewrite left_identity, right_identity.
        reflexivity.
    + intros [[F₁ F₂] F₃] [[G₁ G₂] G₃] [[f₁ f₂] f₃].
      apply path_natural_transformation ; cbn in *.
      intros x.
      rewrite left_identity, right_identity, composition_of.
      rewrite !associativity.
      reflexivity.
  Defined.

  Global Instance nAssociator_iso (C₁ C₂ C₃ C₄ : PreCategory)
    : @IsIsomorphism ((cat_H C₃ C₄ * cat_H C₂ C₃) * cat_H C₁ C₂
                      -> cat_H C₁ C₄)
                     _ _ (nAssociator C₁ C₂ C₃ C₄).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply nAssociator_inv.
    - cbn.
      apply path_natural_transformation.
      intros [[F₁ F₂] F₃] ; cbn in *.
      apply path_natural_transformation.
      intros C ; cbn.
      apply left_identity.
    - cbn.
      apply path_natural_transformation.
      intros [[F₁ F₂] F₃] ; cbn in *.
      apply path_natural_transformation.
      intros C ; cbn.
      apply left_identity.
  Defined.

  Definition Cat : BiCategory.
  Proof.
    simple refine
           {|Obj := PreCategory ;
             Hom := cat_H ;
             id_m := _ ;
             c_m := comp_funct ;
             un_l := nUnitor_l ;
             un_r := nUnitor_r ;
             assoc := nAssociator|}.
    - intros C₁ C₂ C₃ F G ; cbn in *.
      apply path_natural_transformation ; cbn.
      intros C.
      rewrite left_identity, right_identity.
      reflexivity.
    - intros C₁ C₂ C₃ C₄ C₅ F₁ F₂ F₃ F₄.
      apply path_natural_transformation.
      intros C ; cbn in *.
      rewrite !identity_of, !left_identity.
      reflexivity.
  Defined.
End CatBiCategory.