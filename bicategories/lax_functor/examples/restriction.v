Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.lax_functor.

Section RestrictionFunctor.
  Context `{Univalence}
          {C D : BiCategory}.
  Variable (F : LaxFunctor C D)
           (P : C -> hProp).
  
  Definition lax_restriction_d : LaxFunctor_d (full_sub C P) D.
  Proof.
    simple refine (Build_LaxFunctor_d _ _ _ _) ; unfold full_sub ; simpl.
    - exact (fun X => Fobj F X.1).
    - intros ; cbn.
      apply (Fmor F).
    - intros ; cbn.
      apply Fcomp.
    - intros ; cbn.
      apply Fid.
  Defined.

  Definition is_lax_restriction : is_lax lax_restriction_d.
  Proof.
    repeat split ; intros ; simpl ; apply F.
  Qed.

  Definition lax_restriction : LaxFunctor (full_sub C P) D
    := Build_LaxFunctor lax_restriction_d is_lax_restriction.

  Global Instance lax_id_functor_pseudo
         `{@is_pseudo_functor _ _ _ F}
    : is_pseudo_functor lax_restriction.
  Proof.
    simple refine {| Fcomp_iso := _ |} ; intros ; cbn in *.
    - apply Fcomp_iso.
    - apply Fid_iso.
  Defined.
End RestrictionFunctor.