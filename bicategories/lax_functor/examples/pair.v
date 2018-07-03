Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory bicategory.examples.prod
     lax_functor.lax_functor.

Section PairFunctor.
  Context `{Univalence}
          {C₁ C₂ D₁ D₂ : BiCategory}.
  Variable (F₁ : LaxFunctor C₁ D₁) (F₂ : LaxFunctor C₂ D₂).
  
  Definition lax_pair_comp 
             (X₁ Y₁ Z₁ : C₁)
             (X₂ Y₂ Z₂ : C₂)
    : NaturalTransformation
        (prod_c_m D₁ D₂ (functor_prod F₁ F₂ (X₁, X₂)) (functor_prod F₁ F₂ (Y₁, Y₂))
                  (functor_prod F₁ F₂ (Z₁, Z₂)) o (Fmor F₁, Fmor F₂, (Fmor F₁, Fmor F₂)))
        ((Fmor F₁, Fmor F₂) o prod_c_m C₁ C₂ (X₁, X₂) (Y₁, Y₂) (Z₁, Z₂)).
  Proof.
    pose (@Fcomp _ _ _ F₁ X₁ Y₁ Z₁) as n₁.
    pose (@Fcomp _ _ _ F₂ X₂ Y₂ Z₂) as n₂.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [[f₁ f₂] [g₁ g₂]] ; cbn in *.
      exact (n₁ (f₁,g₁),n₂ (f₂,g₂)).
    + intros [[f₁ f₂] [g₁ g₂]] [[h₁ h₂] [k₁ k₂]] [[α₁ α₂] [β₁ β₂]] ; cbn in *.
      exact (path_prod' (commutes n₁ (f₁,g₁) (h₁,k₁) (α₁,β₁))
                        (commutes n₂ (f₂,g₂) (h₂,k₂) (α₂,β₂))).
  Defined.

  Definition lax_pair_comp_inv
             `{@is_pseudo_functor _ _ _ F₁} `{@is_pseudo_functor _ _ _ F₂}
             (X₁ Y₁ Z₁ : C₁)
             (X₂ Y₂ Z₂ : C₂)
    : NaturalTransformation
        ((Fmor F₁, Fmor F₂) o prod_c_m C₁ C₂ (X₁, X₂) (Y₁, Y₂) (Z₁, Z₂))
        (prod_c_m D₁ D₂ (functor_prod F₁ F₂ (X₁, X₂)) (functor_prod F₁ F₂ (Y₁, Y₂))
                  (functor_prod F₁ F₂ (Z₁, Z₂)) o (Fmor F₁, Fmor F₂, (Fmor F₁, Fmor F₂))).
  Proof.
    pose (@morphism_inverse (_ -> _) _ _ (@Fcomp _ _ _ F₁ X₁ Y₁ Z₁) Fcomp_iso) as n₁.
    pose (@morphism_inverse (_ -> _) _ _ (@Fcomp _ _ _ F₂ X₂ Y₂ Z₂) Fcomp_iso) as n₂.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [[f₁ f₂] [g₁ g₂]] ; cbn in *.
      exact (n₁ (f₁,g₁),n₂ (f₂,g₂)).
    + intros [[f₁ f₂] [g₁ g₂]] [[h₁ h₂] [k₁ k₂]] [[α₁ α₂] [β₁ β₂]] ; cbn in *.
      exact (path_prod' (commutes n₁ (f₁,g₁) (h₁,k₁) (α₁,β₁))
                        (commutes n₂ (f₂,g₂) (h₂,k₂) (α₂,β₂))).
  Defined.

  Global Instance lax_pair_comp_iso
         `{@is_pseudo_functor _ _ _ F₁} `{@is_pseudo_functor _ _ _ F₂}
         (X₁ Y₁ Z₁ : C₁)
         (X₂ Y₂ Z₂ : C₂)
    : @IsIsomorphism (_ -> _) _ _ (lax_pair_comp X₁ Y₁ Z₁ X₂ Y₂ Z₂).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply lax_pair_comp_inv ; apply _.
    - apply path_natural_transformation.
      intros [[f₁ f₂] [g₁ g₂]] ; cbn.
      pose (@left_inverse (_ -> _) _ _ (@Fcomp _ _ _ F₁ X₁ Y₁ Z₁) Fcomp_iso) as p₁.
      pose (@left_inverse (_ -> _) _ _ (@Fcomp _ _ _ F₂ X₂ Y₂ Z₂) Fcomp_iso) as p₂.
      pose (equiv_path_natural_transformation _ _ p₁ (f₁,g₁)) as q₁.
      pose (equiv_path_natural_transformation _ _ p₂ (f₂,g₂)) as q₂.
      cbn in q₁, q₂.
      rewrite q₁, q₂.
      reflexivity.
    - apply path_natural_transformation.
      intros [[f₁ f₂] [g₁ g₂]] ; cbn.
      pose (@right_inverse (_ -> _) _ _ (@Fcomp _ _ _ F₁ X₁ Y₁ Z₁) Fcomp_iso) as p₁.
      pose (@right_inverse (_ -> _) _ _ (@Fcomp _ _ _ F₂ X₂ Y₂ Z₂) Fcomp_iso) as p₂.
      pose (equiv_path_natural_transformation _ _ p₁ (f₁,g₁)) as q₁.
      pose (equiv_path_natural_transformation _ _ p₂ (f₂,g₂)) as q₂.
      cbn in q₁, q₂.
      rewrite q₁, q₂.
      reflexivity.
  Defined.

  Definition lax_pair_d : LaxFunctor_d (prod C₁ C₂) (prod D₁ D₂).
  Proof.
    simple refine (Build_LaxFunctor_d _ _ _ _).
    - exact (functor_prod F₁ F₂).
    - exact (fun X Y => (Fmor F₁ , Fmor F₂)%functor).
    - intros [X₁ X₂] [Y₁ Y₂] [Z₁ Z₂] ; cbn.
      apply lax_pair_comp.
    - intros [X₁ X₂].
      exact (Fid F₁ X₁,Fid F₂ X₂).
  Defined.

  Definition lax_pair_d_is_lax : is_lax lax_pair_d.
  Proof.
    repeat split.
    - intros [X₁ X₂] [Y₁ Y₂] [f₁ f₂] ; cbn in *.
      apply path_prod' ; [apply F₁ | apply F₂].
    - intros [X₁ X₂] [Y₁ Y₂] [f₁ f₂] ; cbn in *.
      apply path_prod' ; [apply F₁ | apply F₂].
    - intros [W₁ W₂] [X₁ X₂] [Y₁ Y₂] [Z₁ Z₂] [h₁ h₂] [g₁ g₂] [f₁ f₂].
      apply path_prod' ; [apply F₁ | apply F₂].
  Qed.

  Definition lax_pair : LaxFunctor (prod C₁ C₂) (prod D₁ D₂)
    := Build_LaxFunctor lax_pair_d lax_pair_d_is_lax.

  Global Instance pseudo_pair
         `{@is_pseudo_functor _ _ _ F₁} `{@is_pseudo_functor _ _ _ F₂}
    : is_pseudo_functor lax_pair.
  Proof.
    split ; apply _.
  Defined.
End PairFunctor.