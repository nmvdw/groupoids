Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory bicategory.examples.prod
     lax_functor.lax_functor.

Section ProdFunctor.
  Context `{Univalence}
          {C D₁ D₂ : BiCategory}.
  Variable (F₁ : LaxFunctor C D₁) (F₂ : LaxFunctor C D₂).
  
  Definition lax_prod_comp
             (X Y Z : C)
    : NaturalTransformation
        (prod_c_m D₁ D₂ (F₁ X, F₂ X) (F₁ Y, F₂ Y) (F₁ Z, F₂ Z)
                  o (Fmor F₁ * Fmor F₂, Fmor F₁ * Fmor F₂))
        (Fmor F₁ * Fmor F₂ o c_m).
  Proof.
    pose (@Fcomp _ _ _ F₁ X Y Z) as n₁.
    pose (@Fcomp _ _ _ F₂ X Y Z) as n₂.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros [f g] ; simpl.
      exact (n₁ (f,g),n₂ (f,g)).
    - intros [f₁ g₁] [f₂ g₂] [α₁ α₂] ; simpl.
      exact (path_prod' (commutes n₁ _ _ (α₁,α₂))
                        (commutes n₂ _ _ (α₁,α₂))).
  Defined.

  Definition lax_prod_comp_inv
             `{@is_pseudo_functor _ _ _ F₁} `{@is_pseudo_functor _ _ _ F₂}
             (X Y Z : C)
    : NaturalTransformation
        (Fmor F₁ * Fmor F₂ o c_m)
        (prod_c_m D₁ D₂ (F₁ X, F₂ X) (F₁ Y, F₂ Y) (F₁ Z, F₂ Z)
                  o (Fmor F₁ * Fmor F₂, Fmor F₁ * Fmor F₂)).
  Proof.
    pose (@morphism_inverse (_ -> _) _ _ (@Fcomp _ _ _ F₁ X Y Z) Fcomp_iso) as n₁.
    pose (@morphism_inverse (_ -> _) _ _ (@Fcomp _ _ _ F₂ X Y Z) Fcomp_iso) as n₂.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros [f g] ; simpl.
      exact (n₁ (f,g),n₂ (f,g)).
    - intros [f₁ g₁] [f₂ g₂] [α₁ α₂] ; simpl.
      exact (path_prod' (commutes n₁ _ _ (α₁,α₂))
                        (commutes n₂ _ _ (α₁,α₂))).
  Defined.

  Global Instance lax_prod_comp_iso
         `{@is_pseudo_functor _ _ _ F₁} `{@is_pseudo_functor _ _ _ F₂}
         (X Y Z : C)
    : @IsIsomorphism (_ -> _) _ _ (lax_prod_comp X Y Z).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply lax_prod_comp_inv ; apply _.
    - apply path_natural_transformation.
      intros [f g] ; cbn.
      pose (@left_inverse (_ -> _) _ _ (@Fcomp _ _ _ F₁ X Y Z) Fcomp_iso) as p₁.
      pose (@left_inverse (_ -> _) _ _ (@Fcomp _ _ _ F₂ X Y Z) Fcomp_iso) as p₂.
      pose (equiv_path_natural_transformation _ _ p₁ (f,g)) as q₁.
      pose (equiv_path_natural_transformation _ _ p₂ (f,g)) as q₂.
      cbn in q₁, q₂.
      rewrite q₁, q₂.
      reflexivity.
    - apply path_natural_transformation.
      intros [f g] ; cbn.
      pose (@right_inverse (_ -> _) _ _ (@Fcomp _ _ _ F₁ X Y Z) Fcomp_iso) as p₁.
      pose (@right_inverse (_ -> _) _ _ (@Fcomp _ _ _ F₂ X Y Z) Fcomp_iso) as p₂.
      pose (equiv_path_natural_transformation _ _ p₁ (f,g)) as q₁.
      pose (equiv_path_natural_transformation _ _ p₂ (f,g)) as q₂.
      cbn in q₁, q₂.
      rewrite q₁, q₂.
      reflexivity.
  Defined.

  Definition lax_prod_d : LaxFunctor_d C (prod D₁ D₂).
  Proof.
    simple refine (Build_LaxFunctor_d _ _ _ _).
    - exact (fun z => (F₁ z,F₂ z)).
    - exact (fun X Y => Fmor F₁ * Fmor F₂)%functor.
    - intros X Y Z ; cbn.
      apply lax_prod_comp.
    - intros X.
      exact (Fid F₁ X,Fid F₂ X).
  Defined.

  Definition lax_prod_d_is_lax : is_lax lax_prod_d.
  Proof.
    repeat split.
    - intros.
      apply path_prod' ; [apply F₁ | apply F₂].
    - intros.
      apply path_prod' ; [apply F₁ | apply F₂].
    - intros.
      apply path_prod' ; [apply F₁ | apply F₂].
  Qed.

  Definition lax_prod : LaxFunctor C (prod D₁ D₂)
    := Build_LaxFunctor lax_prod_d lax_prod_d_is_lax.

  Global Instance pseudo_prod
         `{@is_pseudo_functor _ _ _ F₁} `{@is_pseudo_functor _ _ _ F₂}
    : is_pseudo_functor lax_prod.
  Proof.
    split ; apply _.
  Defined.
End ProdFunctor.