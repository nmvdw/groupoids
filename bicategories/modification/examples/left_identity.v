Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.examples.identity
     lax_transformation.examples.composition
     modification.modification.

Section LeftIdentity.
  Context `{Univalence}
          {C D : BiCategory}
          {F₁ F₂ : LaxFunctor C D}.
  Variable (η : LaxTransformation F₁ F₂).

  Local Notation left_identity_mod_d
    := (fun (A : C) => left_unit (η A) : (compose η (identity_transformation F₂) A) ==> η A).

  Definition left_identity_is_mod : is_modification left_identity_mod_d.
  Proof.
    intros A B f ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite !vcomp_assoc.
    rewrite <- (vcomp_left_identity (id₂ (η A))).
    rewrite interchange.
    rewrite !vcomp_assoc.
    rewrite triangle_r.
    rewrite !vcomp_assoc.
    rewrite assoc_left.
    rewrite vcomp_right_identity.
    rewrite <- !vcomp_assoc.
    f_ap.
    rewrite !vcomp_assoc.
    pose @left_unit_inv_assoc as p.
    unfold bc_whisker_r in p.
    rewrite p ; clear p.
    rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ z))) (vcomp_assoc _ _ _)^).
    rewrite assoc_left.
    rewrite vcomp_left_identity.
    rewrite <- !vcomp_assoc.
    pose @left_unit_assoc as p.
    unfold bc_whisker_r in p.
    rewrite p ; clear p.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite assoc_left.
    rewrite vcomp_left_identity.
    rewrite <- left_unit_inv_natural.
    rewrite <- !vcomp_assoc.
    rewrite left_unit_left.
    rewrite vcomp_left_identity.
    reflexivity.
  Qed.

  Definition left_identity_mod
    : PseudoModification (composition.compose η (identity_transformation F₂)) η.
  Proof.
    make_pseudo_modification.
    - exact (Build_Modification left_identity_mod_d left_identity_is_mod).
    - intros X ; cbn.
      apply _.
  Defined.
End LeftIdentity.
