Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory lax_functor.lax_functor
     lax_transformation.lax_transformation modification.modification.

Section IdModification.
  Context `{Univalence}
          {C D : BiCategory}
          {F G : LaxFunctor C D}.
  Variable (η : LaxTransformation F G).

  Definition id_modification_d : modification_d η η
    := fun _ => 1%morphism.

  Definition id_modification_is_modification : is_modification id_modification_d.
  Proof.
    intros A B f ; cbn.
    unfold bc_whisker_r, bc_whisker_l.
    exact (ap (fun z => _ o z)%morphism (identity_of _ _)
              @ right_identity _ _ _ _
              @ ((left_identity _ _ _ _)^)
              @ (ap (fun z => z o _)%morphism (identity_of _ _))^).
  Qed.

  Definition id_modification : modification η η
    := Build_Modification id_modification_d id_modification_is_modification.
End IdModification.