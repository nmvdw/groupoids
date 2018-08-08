Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     modification.modification.

Section CompositionModification.
  Context `{Univalence}
          {C D : BiCategory}
          {F G : LaxFunctor C D}
          {η₁ η₂ η₃ : LaxTransformation F G}.
  Variable (σ₂ : modification η₂ η₃)
           (σ₁ : modification η₁ η₂).

  Definition comp_modification_d : modification_d η₁ η₃
    := (fun A => mod_component σ₂ A o mod_component σ₁ A)%morphism.

  Definition comp_modification_is_modification
    : is_modification comp_modification_d.
  Proof.
    intros A B f.
    rewrite bc_whisker_r_compose, bc_whisker_l_compose.
    rewrite <- !associativity.
    rewrite !mod_commute.
    rewrite !associativity.
    rewrite mod_commute.
    reflexivity.
  Qed.

  Definition comp_modification : modification η₁ η₃
    := Build_Modification comp_modification_d comp_modification_is_modification.
End CompositionModification.