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
  Variable (σ₂ : modification η₂ η₃)
           (σ₁ : modification η₁ η₂).

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

  Definition comp_modification : modification η₁ η₃
    := Build_Modification comp_modification_d comp_modification_is_modification.
End CompositionModification.

Definition pseudo_comp_modification
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ η₃ : LaxTransformation F G}
           (σ₂ : PseudoModification η₂ η₃)
           (σ₁ : PseudoModification η₁ η₂)
  : PseudoModification η₁ η₃.
Proof.
  make_pseudo_modification.
  - exact (comp_modification σ₂ σ₁).
  - intros X ; simpl.
    apply _.
Defined.