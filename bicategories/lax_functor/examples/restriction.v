Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.lax_functor.

Definition lax_restriction_d
           `{Univalence}
           {C D : BiCategory}
           (F : LaxFunctor C D)
           (P : C -> hProp)
  : LaxFunctor_d (full_sub C P) D.
Proof.
  simple refine {| Fobj_d := _ |} ; unfold full_sub ; simpl.
  - exact (fun X => Fobj F X.1).
  - intros ; cbn.
    apply (Fmor F).
  - intros ; cbn.
    apply Fcomp.
  - intros ; cbn.
    apply Fid.
Defined.

Definition is_lax_restriction
           `{Univalence}
           {C D : BiCategory}
           (F : LaxFunctor C D)
           (P : C -> hProp)
  : is_lax (lax_restriction_d F P).
Proof.
  repeat split ; intros ; simpl ; apply F.
Qed.

Definition lax_restriction
           `{Univalence}
           {C D : BiCategory}
           (F : LaxFunctor C D)
           (P : C -> hProp)
  : LaxFunctor (full_sub C P) D
  := (lax_restriction_d F P;is_lax_restriction F P).

Global Instance lax_id_functor_pseudo
           `{Univalence}
           {C D : BiCategory}
           (F : LaxFunctor C D)
           (P : C -> hProp)
           `{@is_pseudo_functor _ _ _ F}
  : is_pseudo_functor (lax_restriction F P).
Proof.
  simple refine {| Fcomp_iso := _ |} ; intros ; cbn in *.
  - apply Fcomp_iso.
  - apply Fid_iso.
Defined.