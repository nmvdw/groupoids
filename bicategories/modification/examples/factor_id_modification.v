Require Import HoTT.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.lax_functor
     lax_functor.examples.factor_full_sub
     lax_transformation.lax_transformation
     lax_transformation.examples.identity
     lax_transformation.examples.factor_full_sub
     modification.modification.

Section FactorIdModification.
  Context `{Univalence}
          {C D : BiCategory}.
  Variable (F : PseudoFunctor C D)
           (P : D -> hProp)
           (HP : forall (X : C), P(F X)).

  Definition factor_id_modification_d
    : Modification_d
        (identity_transformation (pseudo_factor F P HP))
        (lax_factor_transformation P (identity_transformation _) HP HP)
    := fun _ => id₂ _.

  Definition factor_id_modification_is_modification
    : is_modification factor_id_modification_d.
  Proof.
    intros X Y f.
    unfold factor_id_modification_d ; cbn.
    rewrite (hcomp_id₂ (id₁ (F Y))).
    rewrite (hcomp_id₂ _ (id₁ (F X))).
    refine ((vcomp_assoc _ _ _)
              @ _ @ (vcomp_left_identity (left_unit_inv (F ₁ f) ∘ right_unit (F ₁ f)))^).
    exact (ap (fun z => _ ∘ z) (vcomp_right_identity _)).
  Qed.

  Definition factor_id_modification
    : IsoModification
        (identity_transformation (pseudo_factor F P HP))
        (lax_factor_transformation P (identity_transformation _) HP HP).
  Proof.
    exists (Build_Modification factor_id_modification_d
                               factor_id_modification_is_modification).
    intros X ; cbn.
    apply _.
  Defined.
End FactorIdModification.