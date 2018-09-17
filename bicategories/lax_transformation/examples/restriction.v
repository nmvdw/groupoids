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

  Definition lax_restriction_is_pseudo
             `{is_pseudo_transformation _ _ _ _ η}
    : is_pseudo_transformation lax_restriction_transformation.
  Proof.
    split ; intros ; cbn.
    apply _.
  Defined.
End Restriction.