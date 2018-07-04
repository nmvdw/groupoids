Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.examples.restriction
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     general_category.

Section Restriction.
  Context `{Univalence}
          {C D : BiCategory}
          {F G : LaxFunctor C D}.
  Variable (P : C -> hProp)
           (η : LaxTransformation F G).

  Definition lax_restriction_transformation_d
    : LaxTransformation_d (lax_restriction F P) (lax_restriction G P).
  Proof.
    simple refine (Build_LaxTransformation_d _ _).
    - exact (fun X => laxcomponent_of η X.1).
    - exact (fun X Y => @laxnaturality_of _ _ _ _ _ η X.1 Y.1).
  Defined.

  Definition lax_restriction_transformation_is_lax
    : is_lax_transformation lax_restriction_transformation_d
    := ((fun X => Datatypes.fst η.2 X.1),
        (fun X Y Z f g => Datatypes.snd η.2 X.1 Y.1 Z.1 f g)).
 
  Definition lax_restriction_transformation
    : LaxTransformation (lax_restriction F P) (lax_restriction G P)
    := Build_LaxTransformation lax_restriction_transformation_d
                               lax_restriction_transformation_is_lax.

  Definition lax_restriction_is_pseudo
             `{@is_pseudo_transformation _ _ _ _ _ η}
    : is_pseudo_transformation lax_restriction_transformation.
  Proof.
    split ; intros ; cbn.
    apply _.
  Defined.
End Restriction.