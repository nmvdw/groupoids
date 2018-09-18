Require Import HoTT.
Require Import HoTT.Categories.Functor.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.lax_functor.

Section RestrictionFunctor.
  Context {C D : BiCategory}.
  Variable (F : LaxFunctor C D)
           (P : C -> hProp).
  
  Definition lax_restriction_d : LaxFunctor_d (full_sub C P) D.
  Proof.
    make_laxfunctor.
    - exact (fun X => Fobj F X.1).
    - intros ; simpl in *.
      exact (Fmor F X.1 Y.1).
    - intros X Y Z g f ; cbn in *.      
      exact (Fcomp₁ F g f).
    - intros ; simpl.
      exact (Fid F X.1).
  Defined.

  Definition is_lax_restriction : is_lax lax_restriction_d.
  Proof.
    make_is_lax ; intros ; apply F.
  Qed.

  Definition lax_restriction : LaxFunctor (full_sub C P) D
    := Build_LaxFunctor lax_restriction_d is_lax_restriction.
End RestrictionFunctor.

Global Instance restriction_is_pseudo
           `{Univalence}
           {C D : BiCategory}
           (F : LaxFunctor C D)
           `{is_pseudo _ _ F}
           (P : C -> hProp)
  : is_pseudo (lax_restriction F P).
Proof.
  split ; intros ; cbn in * ; apply _.
Defined.

Definition pseudo_restriction
           `{Univalence}
           {C D : BiCategory}
           (F : PseudoFunctor C D)
           (P : C -> hProp)
  : PseudoFunctor (full_sub C P) D.
Proof.
  make_pseudo_functor_lax.
  - exact (lax_restriction F P).
  - exact (restriction_is_pseudo F P).
Defined.