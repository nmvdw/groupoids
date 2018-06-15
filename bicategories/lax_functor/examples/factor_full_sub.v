Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.lax_functor
     lax_functor.examples.identity.

Definition lax_factor_d
           `{Univalence}
           {C D : BiCategory}
           (F : LaxFunctor C D)
           (P : D -> hProp)
           (FP : forall (X : C), P (F X))
  : LaxFunctor_d C (full_sub D P).
Proof.
  simple refine {| Fobj_d := _ |}.
  - exact (fun X => (Fobj F X;FP X)).
  - intros ; apply (Fmor F).
  - intros ; apply (Fcomp F).
  - intros ; apply (Fid F).
Defined.

Definition is_lax_factor
           `{Univalence}
           {C D : BiCategory}
           (F : LaxFunctor C D)
           (P : D -> hProp)
           (FP : forall (X : C), P (F X))
  : is_lax (lax_factor_d F P FP).
Proof.
  repeat split.
  - intros ; simpl ; apply F.
  - intros ; simpl ; apply F.
  - intros ; simpl ; apply F.
Defined.

Definition lax_factor
           `{Univalence}
           {C D : BiCategory}
           (F : LaxFunctor C D)
           (P : D -> hProp)
           (FP : forall (X : C), P (F X))
  : LaxFunctor C (full_sub D P)
  := (lax_factor_d F P FP;is_lax_factor F P FP).

Global Instance lax_inclusion_pseudo
       `{Univalence}
       {C D : BiCategory}
       (F : LaxFunctor C D)
       (P : D -> hProp)
       (FP : forall (X : C), P (Fobj F X))
       `{@is_pseudo_functor _ _ _ F}
  : is_pseudo_functor (lax_factor F P FP).
Proof.
  simple refine {| Fcomp_iso := _ |} ; intros ; cbn in *.
  - apply Fcomp_iso.
  - apply Fid_iso.
Defined.