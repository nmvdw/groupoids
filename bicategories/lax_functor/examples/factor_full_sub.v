Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.lax_functor
     lax_functor.examples.identity.

Section FactorFullSub.
  Context {C D :BiCategory}.
  Variable (F : LaxFunctor C D)
           (P : D -> hProp)
           (FP : forall (X : C), P (F X)).
  
  Definition lax_factor_d : LaxFunctor_d C (full_sub D P).
  Proof.
    make_laxfunctor.
    - exact (fun X => (Fobj F X;FP X)).
    - intros ; apply (Fmor F).
    - intros X Y Z g f ; simpl in *.
      exact (Fcomp₁ F g f).
    - intros ; apply (Fid F).
  Defined.

  Definition is_lax_factor : is_lax lax_factor_d.
  Proof.
    make_is_lax ; intros ; apply F.
  Defined.

  Definition lax_factor : LaxFunctor C (full_sub D P)
    := Build_LaxFunctor lax_factor_d is_lax_factor.
End FactorFullSub.

Definition pseudo_factor
           `{Univalence}
           {C D :BiCategory}
           (F : PseudoFunctor C D)
           (P : D -> hProp)
           (FP : forall (X : C), P (F X))
  : PseudoFunctor C (full_sub D P).
Proof.
  make_pseudo_functor_lax.
  - exact (lax_factor F P FP).
  - simpl.
    split ; apply _.
Defined.