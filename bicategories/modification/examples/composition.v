Require Import HoTT.
Require Import HoTT.Categories.Functor.
From GR.bicategories Require Import
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.examples.composition
     modification.modification.

Section CompositionModification.
  Context {C D : BiCategory}
          {F G : LaxFunctor C D}
          {η₁ η₂ η₃ : LaxTransformation F G}.
  Variable (σ₂ : Modification η₂ η₃)
           (σ₁ : Modification η₁ η₂).

  Local Notation comp_modification_d
    := (fun A => σ₂ A ∘ σ₁ A).

  Definition comp_modification_is_modification
    : is_modification comp_modification_d.
  Proof.
    intros A B f.
    unfold bc_whisker_l, bc_whisker_r in * ; cbn in *.
    rewrite <- (vcomp_left_identity (id₂ (G ₁ f))).
    rewrite <- (vcomp_left_identity (id₂ (F ₁ f))).
    rewrite !interchange.
    rewrite <- !vcomp_assoc.
    rewrite mod_commute.
    rewrite !vcomp_assoc.
    rewrite mod_commute.
    unfold bc_whisker_l, bc_whisker_r.
    reflexivity.
  Qed.

  Definition comp_modification : Modification η₁ η₃
    := Build_Modification comp_modification_d comp_modification_is_modification.
End CompositionModification.

Definition comp_modification_is_iso
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ η₃ : LaxTransformation F G}
           (σ₂ : IsoModification η₂ η₃)
           (σ₁ : IsoModification η₁ η₂)
  : iso_modification (comp_modification σ₂ σ₁).
Proof.
  intros X ; cbn.
  apply _.
Qed.

Definition comp_iso_modification
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ η₃ : LaxTransformation F G}
           (σ₂ : IsoModification η₂ η₃)
           (σ₁ : IsoModification η₁ η₂)
  : IsoModification η₁ η₃.
Proof.
  make_iso_modification.
  - exact (comp_modification σ₂ σ₁).
  - exact (comp_modification_is_iso σ₂ σ₁).
Defined.