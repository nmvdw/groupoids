Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.lax_functor
     lax_functor.examples.identity.

Section FactorFullSub.
  Context `{Univalence}
          {C D :BiCategory}.
  Variable (F : LaxFunctor C D)
           (P : D -> hProp)
           (FP : forall (X : C), P (F X)).
  
  Definition lax_factor_d : LaxFunctor_d C (full_sub D P).
  Proof.
    simple refine (Build_LaxFunctor_d _ _ _ _).
    - exact (fun X => (Fobj F X;FP X)).
    - intros ; apply (Fmor F).
    - intros ; apply (Fcomp F).
    - intros ; apply (Fid F).
  Defined.

  Definition is_lax_factor : is_lax lax_factor_d.
  Proof.
    repeat split ; intros ; simpl ; apply F.
  Defined.

  Definition lax_factor : LaxFunctor C (full_sub D P)
    := Build_LaxFunctor lax_factor_d is_lax_factor.

  Global Instance lax_inclusion_pseudo
         `{@is_pseudo_functor _ _ _ F}
    : is_pseudo_functor lax_factor.
  Proof.
    simple refine {| Fcomp_iso := _ |} ; intros ; cbn in *.
    - apply Fcomp_iso.
    - apply Fid_iso.
  Defined.
End FactorFullSub.