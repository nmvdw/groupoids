Require Import HoTT.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.adjoint
     bicategory.adjoint_unique
     bicategory.equivalence
     bicategory.equiv_to_adjequiv
     bicategory.univalent
     bicategory.examples.full_sub
     bicategory.examples.precat
     bicategory.examples.cat
     bicategory.examples.image
     lax_functor.lax_functor
     lax_functor.examples.restriction
     lax_functor.examples.image_restriction.

Definition local_equivalence
           `{Funext}
           {C D : BiCategory}
           (F : LaxFunctor C D)
  : Type
  := forall (X Y : C), @is_adjoint_equivalence PreCat _ _ (Fmor F X Y).

Definition restrict_local_equivalence
           `{Funext}
           {C D : BiCategory}
           (P : C -> hProp)
           (F : LaxFunctor C D)
           (HF : local_equivalence F)
  : local_equivalence (lax_restriction F P).
Proof.
  intros X Y.
  apply HF.
Defined.

Definition essentially_surjective
           `{Funext}
           {C D : BiCategory}
           (F : LaxFunctor C D)
  : Type
  := forall (Y : D), merely {X : C & F X = Y}.

Global Instance is_hprop_essentially_surjective
       `{Funext}
       {C D : BiCategory}
       (F : LaxFunctor C D)
  : IsHProp (essentially_surjective F)
  := _.

Definition image_essentialy_surjective
           `{Funext}
           {C D : BiCategory}
           (F : LaxFunctor C D)
  : essentially_surjective (restrict_image F).
Proof.
  intros [Y HY] ; cbn in *.
  simple refine (Trunc_rec _ HY).
  intros [X HX].
  apply tr.
  refine (X;_).
  apply path_sigma_hprop ; simpl.
  apply HX.
Defined.

Definition image_local_equivalence
           `{Funext}
           {C D : BiCategory}
           (F : LaxFunctor C D)
           (HF : local_equivalence F)
  : local_equivalence (restrict_image F).
Proof.
  intros X Y.
  apply HF.
Defined.