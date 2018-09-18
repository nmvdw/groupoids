Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.examples.restriction
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     general_category.

Section Restriction.
  Context {C D : BiCategory}
          {F G : LaxFunctor C D}.
  Variable (P : C -> hProp)
           (η : LaxTransformation F G).

  Definition lax_restriction_transformation_d
    : LaxTransformation_d (lax_restriction F P) (lax_restriction G P).
  Proof.
    make_lax_transformation.
    - exact (fun X => η X.1).
    - exact (fun X Y f => laxnaturality_of η f).
  Defined.

  Definition lax_restriction_transformation_is_lax
    : is_lax_transformation lax_restriction_transformation_d.
  Proof.
    make_is_lax_transformation ; intros ; apply η.
  Qed.
 
  Definition lax_restriction_transformation
    : LaxTransformation (lax_restriction F P) (lax_restriction G P)
    := Build_LaxTransformation lax_restriction_transformation_d
                               lax_restriction_transformation_is_lax.
End Restriction.

Global Instance restriction_transformation_is_pseudo
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (P : C -> hProp)
           (η : LaxTransformation F G)
           `{is_pseudo_transformation _ _ _ _ η}
  : is_pseudo_transformation (lax_restriction_transformation P η).
Proof.
  intros X Y f ; cbn.
  apply _.
Defined.

Definition pseudo_restriction_transformation
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (P : C -> hProp)
           (η : PseudoTransformation F G)
  : PseudoTransformation (lax_restriction F P) (lax_restriction G P).
Proof.
  make_pseudo_transformation_lax.
  - exact (lax_restriction_transformation P η).
  - exact (restriction_transformation_is_pseudo P η).
Defined.