Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.examples.identity
     lax_transformation.examples.composition
     modification.modification.

Section LeftIdentityInv.
  Context `{Univalence}
          {C D : BiCategory}
          {F₁ F₂ : LaxFunctor C D}.
  Variable (η : LaxTransformation F₁ F₂).

  Local Notation left_identity_inv_mod_d
    := (fun (A : C) =>
          left_unit_inv (η A) : (η A ==> compose η (identity_transformation F₂) A)).

  Definition left_identity_inv_is_mod : is_modification left_identity_inv_mod_d.
  Proof.
    intros A B f ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite !vcomp_assoc.
    rewrite <- (vcomp_left_identity (id₂ (η A))).
    rewrite interchange.
    rewrite !vcomp_assoc.
    rewrite triangle_r.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ (_ ∘ (_ ∘ z))))) (vcomp_assoc _ _ _)^).
    rewrite assoc_left.
    rewrite vcomp_left_identity.
    rewrite <- !vcomp_assoc.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    pose @left_unit_inv_assoc as p.
    unfold bc_whisker_r in p.
    rewrite p ; clear p.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    rewrite assoc_left.
    rewrite vcomp_left_identity.
    rewrite !vcomp_assoc.
    rewrite <- interchange.
    rewrite left_unit_left.
    rewrite vcomp_left_identity, hcomp_id₂, vcomp_right_identity.
    rewrite <- left_unit_inv_natural.
    rewrite <- !vcomp_assoc.
    rewrite <- left_unit_inv_assoc.
    reflexivity.
  Qed.

  Definition left_identity_inv_modification
    : Modification η (compose η (identity_transformation F₂))
    := Build_Modification left_identity_inv_mod_d left_identity_inv_is_mod.

  Definition left_identity_inv_modification_is_iso
    : iso_modification left_identity_inv_modification.
  Proof.
    intros X ; cbn.
    apply _.
  Qed.

  Definition left_identity_inv_mod
    : IsoModification η (compose η (identity_transformation F₂)).
  Proof.
    make_iso_modification.
    - exact left_identity_inv_modification.
    - exact left_identity_inv_modification_is_iso.
  Defined.
End LeftIdentityInv.
