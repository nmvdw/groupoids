Require Import HoTT.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.examples.image
     bicategory.adjoint
     bicategory.univalent
     lax_functor.lax_functor.

Section ImageRestriction.
  Context {C D : BiCategory}.
  Variable (F : LaxFunctor C D).

  Definition restrict_image_d : LaxFunctor_d C (image F).
  Proof.
    make_laxfunctor.
    - intros X.
      simple refine (F X;_) ; simpl.
      exact (tr(X;idpath)).
    - intros X Y ; cbn.
      exact (Fmor F X Y).
    - intros X Y Z g f ; cbn.
      exact (Fcomp₁ F g f).
    - intros X ; cbn.
      exact (Fid F X).
  Defined.

  Definition restrict_image_is_lax : is_lax restrict_image_d.
  Proof.
    make_is_lax ; intros ; simpl in * ; apply F.
  Qed.

  Definition restrict_image : LaxFunctor C (image F)
    := Build_LaxFunctor restrict_image_d restrict_image_is_lax.
End ImageRestriction.

Global Instance restrict_image_is_pseudo
           `{Univalence}
           {C D : BiCategory}
           (F : LaxFunctor C D)
           `{is_pseudo _ _ F}
  : is_pseudo (restrict_image F).
Proof.
  split ; cbn ; apply _.
Defined.

Definition restrict_image_pseudo
           `{Univalence}
           {C D : BiCategory}
           (F : PseudoFunctor C D)
  : PseudoFunctor C (image F).
Proof.
  make_pseudo_functor_lax.
  - exact (restrict_image F).
  - exact (restrict_image_is_pseudo F).
Defined.