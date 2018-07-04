Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.examples.factor_full_sub
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     general_category.

Section Factor.
  Context `{Univalence}
          {C D : BiCategory}
          {F G : LaxFunctor C D}.
  Variable (P : D -> hProp)
           (η : LaxTransformation F G)
           (FH : forall (X : C), P (F X))
           (GH : forall (X : C), P (G X)).

  Definition lax_factor_transformation_d
    : LaxTransformation_d (lax_factor F P FH) (lax_factor G P GH).
  Proof.
    simple refine (Build_LaxTransformation_d _ _).
    - exact (fun X => laxcomponent_of η X).
    - exact (fun X Y => laxnaturality_of η).
  Defined.

  Definition lax_factor_transformation_is_lax
    : is_lax_transformation lax_factor_transformation_d.
  Proof.
    split.
    - exact (fun X => Datatypes.fst η.2 X).
    - intros X Y Z f g.
      rewrite (Datatypes.snd η.2 X Y Z f g).
      repeat f_ap.
      apply Morphisms.iso_moveR_V1.
      apply iso_moveL_pV.
      rewrite left_identity.
      reflexivity.
  Qed.

  Definition lax_factor_transformation
    : LaxTransformation (lax_factor F P FH) (lax_factor G P GH)
    := Build_LaxTransformation
         lax_factor_transformation_d
         lax_factor_transformation_is_lax.

  Definition lax_factor_is_pseudo
             `{@is_pseudo_transformation _ _ _ _ _ η}
    : is_pseudo_transformation lax_factor_transformation.
  Proof.
    split ; intros ; cbn.
    apply _.
  Defined.
End Factor.