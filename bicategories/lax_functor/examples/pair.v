Require Import HoTT.
Require Import HoTT.Categories.Functor.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.examples.prod
     lax_functor.lax_functor.

Section PairFunctor.
  Context {C₁ C₂ D₁ D₂ : BiCategory}.
  Variable (F₁ : LaxFunctor C₁ D₁) (F₂ : LaxFunctor C₂ D₂).

  Definition lax_pair_d : LaxFunctor_d (prod C₁ C₂) (prod D₁ D₂).
  Proof.
    make_laxfunctor.
    - exact (functor_prod F₁ F₂).
    - exact (fun X Y => (Fmor F₁ _ _, Fmor F₂ _ _)%functor).
    - intros [X₁ X₂] [Y₁ Y₂] [Z₁ Z₂] [f₁ f₂] [g₁ g₂] ; simpl in *.
      exact (Fcomp₁ F₁ f₁ g₁, Fcomp₁ F₂ f₂ g₂).
    - intros [X₁ X₂].
      exact (Fid F₁ X₁,Fid F₂ X₂).
  Defined.
  
  Definition lax_pair_d_is_lax : is_lax lax_pair_d.
  Proof.
    make_is_lax ; intros ; (apply path_prod' ; [apply F₁ | apply F₂]).
  Qed.

  Definition lax_pair : LaxFunctor (prod C₁ C₂) (prod D₁ D₂)
    := Build_LaxFunctor lax_pair_d lax_pair_d_is_lax.
End PairFunctor.

Definition pair_is_pseudo
           `{Univalence}
           {C₁ C₂ D₁ D₂ : BiCategory}
           (F₁ : LaxFunctor C₁ D₁) (F₂ : LaxFunctor C₂ D₂)
           `{is_pseudo _ _ F₁} `{is_pseudo _ _ F₂}
  : is_pseudo (lax_pair F₁ F₂).
Proof.
  split ; apply _.
Defined.

Definition pseudo_pair
           `{Univalence}
           {C₁ C₂ D₁ D₂ : BiCategory}
           (F₁ : PseudoFunctor C₁ D₁) (F₂ : PseudoFunctor C₂ D₂)
  : PseudoFunctor (prod C₁ C₂) (prod D₁ D₂).
Proof.
  make_pseudo_functor_lax.
  - exact (lax_pair F₁ F₂).
  - exact (pair_is_pseudo F₁ F₂).
Defined.