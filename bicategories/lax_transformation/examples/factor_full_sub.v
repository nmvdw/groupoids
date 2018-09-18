Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.examples.factor_full_sub
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     general_category.

Section Factor.
  Context {C D : BiCategory}
          {F G : LaxFunctor C D}.
  Variable (P : D -> hProp)
           (η : LaxTransformation F G)
           (FH : forall (X : C), P (F X))
           (GH : forall (X : C), P (G X)).

  Definition lax_factor_transformation_d
    : LaxTransformation_d (lax_factor F P FH) (lax_factor G P GH).
  Proof.
    simple refine (Build_LaxTransformation_d _ _).
    - exact (fun X => η X).
    - exact (fun X Y => laxnaturality_of η).
  Defined.

  Definition lax_factor_transformation_is_lax
    : is_lax_transformation lax_factor_transformation_d.
  Proof.
    split ; intros ; apply η.
  Qed.

  Definition lax_factor_transformation
    : LaxTransformation (lax_factor F P FH) (lax_factor G P GH)
    := Build_LaxTransformation
         lax_factor_transformation_d
         lax_factor_transformation_is_lax.
End Factor.

Global Instance factor_transformation_is_pseudo
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (P : D -> hProp)
           (η : LaxTransformation F G)
           `{is_pseudo_transformation _ _ _ _ η}
           (FH : forall (X : C), P (F X))
           (GH : forall (X : C), P (G X))
  : is_pseudo_transformation (lax_factor_transformation P η FH GH).
Proof.
  intros X Y f ; cbn ; apply _.
Defined.

Definition pseudo_factor_transformation
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (P : D -> hProp)
           (η : PseudoTransformation F G)
           (FH : forall (X : C), P (F X))
           (GH : forall (X : C), P (G X))
  : PseudoTransformation (lax_factor F P FH) (lax_factor G P GH).
Proof.
  make_pseudo_transformation_lax.
  - exact (lax_factor_transformation P η FH GH).
  - exact (factor_transformation_is_pseudo P η FH GH).
Defined.