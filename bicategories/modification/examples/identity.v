Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory lax_functor.lax_functor
     lax_transformation.lax_transformation modification.modification.

Section IdModification.
  Context {C D : BiCategory}
          {F G : LaxFunctor C D}.
  Variable (η : LaxTransformation F G).

  Definition id_modification_d : modification_d η η
    := fun A => id₂ (η A).

  Definition id_modification_is_modification : is_modification id_modification_d.
  Proof.
    intros A B f.
    unfold id_modification_d, bc_whisker_r, bc_whisker_l ; cbn.
    rewrite !hcomp_id₂.
    rewrite vcomp_left_identity, vcomp_right_identity.
    reflexivity.
  Qed.

  Definition id_modification : modification η η
    := Build_Modification id_modification_d id_modification_is_modification.

  Global Instance id_modification_is_pseudo
    : is_pseudo_modification id_modification.
  Proof.
    split ; apply _.
  Defined.
End IdModification.