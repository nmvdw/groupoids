Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.examples.composition
     modification.modification.

Section WhiskerR.
  Context `{Funext}
          {C D : BiCategory}
          {F₁ F₂ F₃ : LaxFunctor C D}
          {ε₁ ε₂ : LaxTransformation F₁ F₂}.
  Variable (m : modification ε₁ ε₂)
           (η : LaxTransformation F₂ F₃).
  
  Local Notation whisker_R_mod_d
    := (fun (A : C) => η A ◅ m A : compose ε₁ η A ==> compose ε₂ η A).

  Definition whisker_R_is_mod
    : is_modification whisker_R_mod_d.
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
    rewrite !vcomp_right_identity.
    rewrite <- !vcomp_assoc.
    rewrite <- interchange.
    rewrite vcomp_right_identity, vcomp_left_identity.
    rewrite !vcomp_assoc.
    pose (mod_commute m f) as p.
    unfold bc_whisker_l, bc_whisker_r in p.
    rewrite <- p ; clear p.
    rewrite <- (vcomp_left_identity (id₂ (η B))).
    rewrite !interchange.
    rewrite vcomp_right_identity.
    rewrite !vcomp_assoc.
    f_ap.
    rewrite <- !vcomp_assoc.
    rewrite <- assoc_natural.
    rewrite !vcomp_assoc.
    rewrite <- !interchange.
    rewrite hcomp_id₂.
    rewrite vcomp_left_identity, vcomp_right_identity.
    reflexivity.
  Qed.

  Definition whisker_R_mod
    : modification (compose ε₁ η) (compose ε₂ η)
    := Build_Modification whisker_R_mod_d whisker_R_is_mod.
End WhiskerR.

Definition pseudo_whisker_R_mod
           `{Univalence}
           {C D : BiCategory}
           {F₁ F₂ F₃ : LaxFunctor C D}
           {ε₁ ε₂ : LaxTransformation F₁ F₂}
           (m : PseudoModification ε₁ ε₂)
           (η : LaxTransformation F₂ F₃)
  : PseudoModification (compose ε₁ η) (compose ε₂ η).
Proof.
  make_pseudo_modification.
  - exact (whisker_R_mod m η).
  - intros X ; cbn.
    apply _.
Defined.