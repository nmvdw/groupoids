Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.lax_functor
     lax_functor.examples.identity.

Section InclusionFunctor.
  Context `{Univalence}.
  Variable (C : BiCategory)
           (P : C -> hProp).

  Definition lax_inclusion_d : LaxFunctor_d (full_sub C P) C.
  Proof.
    simple refine (Build_LaxFunctor_d _ _ _ _).
    - intros X.
      exact X.1.
    - intros X Y ; simpl.
      exact 1%functor.
    - intros X Y Z ; simpl.
      apply id_functor_c_m.
    - intros.
      unfold hcomp ; cbn.
      exact 1%morphism.
  Defined.

  Definition is_lax_inclusion : is_lax lax_inclusion_d.
  Proof.
    repeat split.
    - intros ; simpl.
      unfold hcomp.
      rewrite identity_of, !right_identity.
      reflexivity.
    - intros ; simpl.
      unfold hcomp.
      rewrite identity_of, !right_identity.
      reflexivity.
    - intros ; simpl.
      unfold hcomp.
      rewrite !identity_of, !right_identity, !left_identity.
      reflexivity.
  Qed.

  Definition lax_inclusion : LaxFunctor (full_sub C P) C
    := Build_LaxFunctor lax_inclusion_d is_lax_inclusion.

  Global Instance lax_inclusion_pseudo
    : is_pseudo_functor lax_inclusion.
  Proof.
    simple refine {| Fcomp_iso := _ |}.
  Defined.
End InclusionFunctor.