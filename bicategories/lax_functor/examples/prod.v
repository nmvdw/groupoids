Require Import HoTT.
Require Import HoTT.Categories.Functor.
From GR.bicategories Require Import
     bicategory.bicategory bicategory.examples.prod
     lax_functor.lax_functor.

Section ProdFunctor.
  Context {C D₁ D₂ : BiCategory}.
  Variable (F₁ : LaxFunctor C D₁) (F₂ : LaxFunctor C D₂).

  Definition lax_prod_d : LaxFunctor_d C (prod D₁ D₂).
  Proof.
    make_laxfunctor.
    - exact (fun z => (F₁ z,F₂ z)).
    - exact (fun X Y => Fmor F₁ _ _ * Fmor F₂ _ _)%functor.
    - intros X Y Z g f ; simpl in *.
      exact (Fcomp₁ F₁ g f,Fcomp₁ F₂ g f).
    - intros X.
      exact (Fid F₁ X,Fid F₂ X).
  Defined.

  Definition lax_prod_d_is_lax : is_lax lax_prod_d.
  Proof.
    make_is_lax ; intros ; (apply path_prod' ; [apply F₁ | apply F₂]).
  Qed.

  Definition lax_prod : LaxFunctor C (prod D₁ D₂)
    := Build_LaxFunctor lax_prod_d lax_prod_d_is_lax.
End ProdFunctor.

Global Instance prod_is_pseudo
           `{Univalence}
           {C D₁ D₂ : BiCategory}
           (F₁ : LaxFunctor C D₁) (F₂ : LaxFunctor C D₂)
           `{is_pseudo _ _ F₁} `{is_pseudo _ _ F₂}
  : is_pseudo (lax_prod F₁ F₂).
Proof.
  split ; apply _.
Defined.

Definition pseudo_prod
           `{Univalence}
           {C D₁ D₂ : BiCategory}
           (F₁ : PseudoFunctor C D₁) (F₂ : PseudoFunctor C D₂)
  : PseudoFunctor C (prod D₁ D₂).
Proof.
  make_pseudo_functor_lax.
  - exact (lax_prod F₁ F₂).
  - exact (prod_is_pseudo F₁ F₂).
Defined.