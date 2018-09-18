Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.examples.composition
     modification.modification.

Section AssociativityInverse.
  Context `{Univalence}
          {C D : BiCategory}
          {F₁ F₂ F₃ F₄ : LaxFunctor C D}.
  Variable (η₁ : LaxTransformation F₃ F₄)
           (η₂ : LaxTransformation F₂ F₃)
           (η₃ : LaxTransformation F₁ F₂).

  Local Notation assoc_inv_mod_d
    := (fun (A : C) =>
          assoc_inv (η₁ A) (η₂ A) (η₃ A)
          : compose (compose η₃ η₂) η₁ A ==> compose η₃ (compose η₂ η₁) A).

  Definition assoc_inv_d_is_modification : is_modification assoc_inv_mod_d.
  Proof.
    intros A B f ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite !vcomp_assoc.
    repeat (rewrite <- (vcomp_left_identity (id₂ (η₁ B)))
            ; rewrite interchange
            ; rewrite vcomp_left_identity).
    rewrite !vcomp_assoc.
    repeat (rewrite <- (vcomp_left_identity (id₂ (η₃ A))) ; rewrite interchange).
    rewrite !vcomp_left_identity.
    rewrite !vcomp_assoc.
    refine (vcomp_move_L_Mp _ _ _ _).
    rewrite <- !vcomp_assoc.
    rewrite inverse_pentagon_4.
    rewrite !vcomp_assoc.
    repeat f_ap.
    rewrite <- !hcomp_id₂.
    rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    rewrite inverse_pentagon_5.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite <- assoc_inv_natural.
    rewrite <- !vcomp_assoc.
    rewrite assoc_left, vcomp_left_identity.
    rewrite !vcomp_assoc.
    repeat f_ap.
    rewrite <- !vcomp_assoc.
    rewrite assoc_natural.
    rewrite !vcomp_assoc.
    f_ap.
    rewrite <- !vcomp_assoc.
    rewrite pentagon_2.
    rewrite !vcomp_assoc.
    repeat f_ap.
    rewrite <- !vcomp_assoc.
    rewrite assoc_natural.
    rewrite !vcomp_assoc.
    f_ap.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite <- inverse_pentagon.
    rewrite <- !vcomp_assoc.
    rewrite assoc_left, vcomp_left_identity.
    reflexivity.
  Qed.

  Definition assoc_inv_modification
    : Modification
        (compose (compose η₃ η₂) η₁)
        (compose η₃ (compose η₂ η₁))
    := Build_Modification assoc_inv_mod_d assoc_inv_d_is_modification.

  Definition assoc_inv_modification_is_iso
    : iso_modification assoc_inv_modification.
  Proof.
    intros X ; cbn.
    apply _.
  Qed.

  Definition assoc_inv_mod
    : IsoModification
        (compose (compose η₃ η₂) η₁)
        (compose η₃ (compose η₂ η₁)).
  Proof.
    make_iso_modification.
    - exact assoc_inv_modification.
    - exact assoc_inv_modification_is_iso.
  Defined.
End AssociativityInverse.