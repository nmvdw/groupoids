Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category.
From GR.bicategories.bicategory Require Import
     bicategory bicategory_laws.

Section OpBiCategory.
  Context `{Univalence}.

  Definition op_comp (C : BiCategory) (X Y Z : C)
    : Functor (Hom C Z Y * Hom C Y X) (Hom C Z X).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _) ; cbn.
    - intros [g f].
      exact (c_m (f,g)).
    - intros [g₁ g₂] [f₁ f₂] [α₁ α₂] ; cbn in *.
      refine (morphism_of _ _).
      split ; cbn.
      + exact α₂.
      + exact α₁.
    - intros [h₁ h₂] [g₁ g₂] [f₁ f₂] [α₁ α₂] [β₁ β₂] ; cbn in *.
      exact (composition_of (@c_m _ C Z Y X) (h₂,h₁) (g₂,g₁) (f₂,f₁) (α₂,α₁) (β₂,β₁)).
    - intros [f g] ; cbn.
      apply identity_of.
  Defined.

  Definition oUnitor_l {C : BiCategory} (X Y : C)
    : @NaturalTransformation
        (Hom C Y X)
        (Hom C Y X)
        (op_comp C X Y Y o (@const_functor (Hom C Y X) (Hom C Y Y)
                                               (id_m Y) * 1))
        (Functor.identity (Hom C Y X)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros f ; cbn.
      exact (@un_r _ C Y X f).
    - intros g f α ; cbn.
      exact (commutes (@un_r _ C Y X) g f α).
  Defined.

  Definition oUnitor_l_inv {C : BiCategory} (X Y : C)
    : @NaturalTransformation
        (Hom C Y X)
        (Hom C Y X)
        (Functor.identity (Hom C Y X))
        (op_comp C X Y Y o (@const_functor (Hom C Y X) (Hom C Y Y)
                                           (id_m Y) * 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros f ; cbn.
      apply (@un_r_iso _ C Y X).
    - intros g f α ; cbn.
      pose (FunctorCategory.Morphisms.inverse (@un_r _ C Y X)) as n.
      apply (commutes n).
  Defined.
  
  Global Instance oUnitor_l_iso {C : BiCategory} (X Y : C)
    : @IsIsomorphism (_ -> _) _ _ (oUnitor_l X Y).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply oUnitor_l_inv.
    - cbn.
      apply path_natural_transformation.
      intros f ; cbn in *.
      exact (@left_inverse _ _ _ (@un_r _ C Y X f) _).
    - cbn.
      apply path_natural_transformation.
      intros f ; cbn in *.
      exact (@right_inverse _ _ _ (@un_r _ C Y X f) _).
  Defined.

  Definition oUnitor_r {C : BiCategory} (X Y : C)
    : @NaturalTransformation
        (Hom C Y X)
        (Hom C Y X)
        (op_comp C X X Y o (1 * @const_functor (Hom C Y X) (Hom C X X)
                                             (id_m X)))
        (Functor.identity (Hom C Y X)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros f ; cbn.
      exact (@un_l _ C Y X f).
    - intros g f α ; cbn.
      exact (commutes (@un_l _ C Y X) g f α).
  Defined.

  Definition oUnitor_r_inv {C : BiCategory} (X Y : C)
    : @NaturalTransformation
        (Hom C Y X)
        (Hom C Y X)
        (Functor.identity (Hom C Y X))
        (op_comp C X X Y o (1 * @const_functor (Hom C Y X) (Hom C X X)
                                             (id_m X))).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros f ; cbn.
      apply (@un_l_iso _ C Y X).
    - intros g f α ; cbn.
      pose (FunctorCategory.Morphisms.inverse (@un_l _ C Y X)) as n.
      apply (commutes n).
  Defined.

  Global Instance oUnitor_r_iso {C : BiCategory} (X Y : C)
    : @IsIsomorphism (_ -> _) _ _ (oUnitor_r X Y).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply oUnitor_r_inv.
    - cbn.
      apply path_natural_transformation.
      intros f ; cbn in *.
      exact (@left_inverse _ _ _ (@un_l _ C Y X f) _).
    - cbn.
      apply path_natural_transformation.
      intros f ; cbn in *.
      exact (@right_inverse _ _ _ (@un_l _ C Y X f) _).
  Defined.

  Definition oAssociator {C : BiCategory} (V X Y Z : C)
    : NaturalTransformation
        (op_comp C V X Z o (op_comp C X Y Z, 1))
        (op_comp C V Y Z o (1, op_comp C V X Y)
                    o assoc_prod (Hom C Z Y) (Hom C Y X) (Hom C X V)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros [[h g] f] ; cbn in *.
      exact (FunctorCategory.Morphisms.inverse (@assoc _ C Z Y X V) (f,g,h)).
    - intros [[h₁ h₂] h₃] [[g₁ g₂] g₃] [[α₁ α₂] α₃] ; cbn in *.
      pose (FunctorCategory.Morphisms.inverse (@assoc _ C Z Y X V)) as n.
      exact (commutes n (h₃,h₂,h₁) (g₃,g₂,g₁) (α₃,α₂,α₁)).
  Defined.

  Definition oAssociator_inv {C : BiCategory} (V X Y Z : C)
    : NaturalTransformation
        (op_comp C V Y Z o (1, op_comp C V X Y)
                 o assoc_prod (Hom C Z Y) (Hom C Y X) (Hom C X V))
        (op_comp C V X Z o (op_comp C X Y Z, 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros [[h g] f] ; cbn in *.
      exact (@assoc _ C Z Y X V (f,g,h)).
    - intros [[h₁ h₂] h₃] [[g₁ g₂] g₃] [[α₁ α₂] α₃] ; cbn in *.
      exact (commutes (@assoc _ C Z Y X V) (h₃,h₂,h₁) (g₃,g₂,g₁) (α₃,α₂,α₁)).
  Defined.

  Global Instance oAssociator_iso {C : BiCategory} (V X Y Z : C)
    : @IsIsomorphism (_ -> _) _ _ (oAssociator V X Y Z).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply oAssociator_inv.
    - cbn.
      apply path_natural_transformation.
      intros [[f₁ f₂] f₃] ; cbn in *.
      exact (@right_inverse _ _ _ (@assoc _ C _ _ _ _ (f₃,f₂,f₁)) _).
    - cbn.
      apply path_natural_transformation.
      intros [[f₁ f₂] f₃] ; cbn in *.
      exact (@left_inverse _ _ _ (@assoc _ C _ _ _ _ (f₃,f₂,f₁)) _).
  Defined.

  Definition op (C : BiCategory) : BiCategory.
  Proof.
    simple refine (Build_BiCategory C
                                    (fun X Y => Hom C Y X)
                                    id_m
                                    (op_comp C)
                                    oUnitor_l
                                    oUnitor_r
                                    oAssociator
                                    _
                                    _).
    - intros X Y Z g f ; cbn in *.
      exact (triangle_l f g)^.
    - intros W V X Y Z k h g f ; cbn in *.
      pose (pentagon C Z Y X V W f g h k).
      rewrite <- !inverse_id.
      rewrite <- !inverse_pair.
      rewrite !inverse_of.
      rewrite <- !inverse_compose.
      apply path_inverse.
      rewrite p.
      apply associativity.
  Defined.
End OpBiCategory.