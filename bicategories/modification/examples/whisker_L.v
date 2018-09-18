Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.examples.composition
     modification.modification.

Section WhiskerL.
  Context `{Funext}
          {C D : BiCategory}
          {F₁ F₂ F₃ : LaxFunctor C D}
          {η₁ η₂ : LaxTransformation F₂ F₃}.
  Variable (ε : LaxTransformation F₁ F₂)
           (m : Modification η₁ η₂).

  Local Notation whisker_L_mod_d
    := (fun (A : C) => m A ▻ ε A : compose ε η₁ A ==> compose ε η₂ A).

  Definition whisker_L_is_mod
    : is_modification whisker_L_mod_d.
  Proof.
    intros A B f ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite <- !vcomp_assoc.
    rewrite <- assoc_inv_natural.
    rewrite !vcomp_assoc.
    f_ap.
    rewrite assoc_inv_natural.
    rewrite <- !vcomp_assoc.
    rewrite hcomp_id₂.    
    f_ap.
    rewrite !vcomp_assoc.
    rewrite <- !interchange.
    rewrite (mod_commute m f).
    unfold bc_whisker_l.
    rewrite !vcomp_right_identity.
    rewrite <- !vcomp_assoc.
    rewrite <- interchange.
    rewrite vcomp_right_identity, vcomp_left_identity.
    rewrite !vcomp_assoc.
    rewrite <- (vcomp_left_identity (id₂ (ε A))).
    rewrite !interchange.
    rewrite <- !vcomp_assoc.
    rewrite vcomp_left_identity.
    f_ap.
    rewrite !vcomp_assoc.
    rewrite assoc_natural.
    rewrite <- !vcomp_assoc.
    f_ap.
    rewrite <- interchange.
    rewrite hcomp_id₂, vcomp_left_identity, vcomp_right_identity.
    reflexivity.
  Qed.

  Definition whisker_L_mod
    : Modification (compose ε η₁) (compose ε η₂)
    := Build_Modification whisker_L_mod_d whisker_L_is_mod.
End WhiskerL.

Definition whisker_L_mod_is_iso
           `{Univalence}
           {C D : BiCategory}
           {F₁ F₂ F₃ : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F₂ F₃}
           (ε : LaxTransformation F₁ F₂)
           (m : IsoModification η₁ η₂)
  : iso_modification (whisker_L_mod ε m).
Proof.
  intros X ; cbn.
  apply _.
Qed.

Definition iso_whisker_L_mod
           `{Univalence}
           {C D : BiCategory}
           {F₁ F₂ F₃ : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F₂ F₃}
           (ε : LaxTransformation F₁ F₂)
           (m : IsoModification η₁ η₂)
  : IsoModification (compose ε η₁) (compose ε η₂).
Proof.
  make_iso_modification.
  - exact (whisker_L_mod ε m).
  - exact (whisker_L_mod_is_iso ε m).
Defined.