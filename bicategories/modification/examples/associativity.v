Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.examples.composition
     modification.modification.

Section Associativity.
  Context `{Univalence}
          {C D : BiCategory}
          {F₁ F₂ F₃ F₄ : LaxFunctor C D}.
  Variable (η₁ : LaxTransformation F₃ F₄)
           (η₂ : LaxTransformation F₂ F₃)
           (η₃ : LaxTransformation F₁ F₂).

  Local Notation assoc_mod_d
    := (fun (A : C) =>
          assoc (η₁ A) (η₂ A) (η₃ A)
          : compose η₃ (compose η₂ η₁) A ==> compose (compose η₃ η₂) η₁ A).

  Definition assoc_d_is_modification : is_modification assoc_mod_d.
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
    rewrite vcomp_assoc.
    rewrite <- inverse_pentagon.
    rewrite !vcomp_assoc.
    f_ap.
    rewrite <- !vcomp_assoc.
    rewrite assoc_inv_natural.
    rewrite !vcomp_assoc.
    rewrite hcomp_id₂.
    f_ap.
    rewrite <- !vcomp_assoc.
    rewrite inverse_pentagon_2.
    rewrite !vcomp_assoc.
    repeat f_ap.
    rewrite <- !vcomp_assoc.
    rewrite assoc_inv_natural.
    rewrite !vcomp_assoc.
    repeat f_ap.
    refine (vcomp_move_L_Mp _ _ _ _).
    rewrite <- !vcomp_assoc.
    rewrite <- inverse_pentagon.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite assoc_right, vcomp_left_identity.
    rewrite <- inverse_pentagon_3.
    rewrite <- !vcomp_assoc.
    repeat f_ap.
    rewrite <- assoc_inv_natural.
    rewrite hcomp_id₂.
    reflexivity.
  Qed.

  Definition assoc_mod
    : PseudoModification
        (composition.compose η₃ (composition.compose η₂ η₁))
        (composition.compose (composition.compose η₃ η₂) η₁).
  Proof.
    make_pseudo_modification.
    - exact (Build_Modification assoc_mod_d assoc_d_is_modification).
    - intros X ; cbn.
      apply _.
  Defined.
End Associativity.