Require Import HoTT.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.lax_functor
     lax_functor.examples.factor_full_sub
     lax_transformation.lax_transformation.

Section InclusionTransformation.
  Context {C D : BiCategory}
          {F G : LaxFunctor C D}.
  Variable (P : D -> hProp)
           (FP : forall (X : C), P(F X))
           (GP : forall (X : C), P(G X))
           (η : LaxTransformation (lax_factor F P FP) (lax_factor G P GP)).

  Definition lax_inclusion_transformation_d
    : LaxTransformation_d F G.
  Proof.
    make_lax_transformation.
    - exact (fun X => η X).
    - exact (fun X Y f => laxnaturality_of η f).
  Defined.

  Definition lax_inclusion_transformation_is_lax
    : is_lax_transformation lax_inclusion_transformation_d.
  Proof.
    make_is_lax_transformation ; intros ; simpl ; apply η.
  Qed.

  Definition lax_inclusion_transformation
    : LaxTransformation F G
    := Build_LaxTransformation
         lax_inclusion_transformation_d
         lax_inclusion_transformation_is_lax.

  Global Instance is_pseudo_lax_inclusion_transformation
         {H : is_pseudo_transformation η}
    : is_pseudo_transformation lax_inclusion_transformation.
  Proof.
    intros X Y f ; cbn.
    apply H.
  Defined.
End InclusionTransformation.

Definition pseudo_inclusion_transformation
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (P : D -> hProp)
           (FP : forall (X : C), P(F X))
           (GP : forall (X : C), P(G X))
           (η : PseudoTransformation (lax_factor F P FP) (lax_factor G P GP))
  : PseudoTransformation F G.
Proof.
  make_pseudo_transformation_lax.
  - exact (lax_inclusion_transformation P FP GP η).
  - apply _.
Defined.