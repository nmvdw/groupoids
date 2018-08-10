Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.lax_functor
     lax_functor.examples.identity.

Section InclusionFunctor.
  Variable (C : BiCategory)
           (P : C -> hProp).

  Definition lax_inclusion_d : PseudoFunctor_d (full_sub C P) C.
  Proof.
    make_pseudo_functor.
    - exact (fun X => X.1).
    - exact (fun _ _ => idmap).
    - exact (fun _ _ _ _ => idmap).
    - intros X Y Z g f ; simpl in *.
      exact (id₂ (g · f)).
    - intros X ; simpl in *.
      exact (id₂ (id₁ X)).
    - intros X Y Z g f ; simpl in *.
      exact (id₂ (g · f)).
    - intros X ; simpl in *.
      exact (id₂ (id₁ X)).
  Defined.

  Definition inclusion_is_pseudo : is_pseudo_functor_p lax_inclusion_d.
  Proof.
    make_is_pseudo.
    - intros ; simpl in *.
      reflexivity.
    - intros ; simpl in *.
      reflexivity.
    - intros ; simpl in *.
      rewrite (@vcomp_left_identity C), (@vcomp_right_identity C).
      reflexivity.
    - intros ; simpl in *.
      rewrite (@hcomp_id₂ C), !(@vcomp_right_identity C).
      reflexivity.
    - intros ; simpl in *.
      rewrite (@hcomp_id₂ C), !(@vcomp_right_identity C).
      reflexivity.
    - intros ; simpl in *.
      rewrite !(@hcomp_id₂ C), !(@vcomp_left_identity C), !(@vcomp_right_identity C).
      reflexivity.
    - intros ; simpl in *.
      apply (@vcomp_left_identity C).
    - intros ; simpl in *.
      apply (@vcomp_left_identity C).
    - intros ; simpl in *.
      apply (@vcomp_left_identity C).
    - intros ; simpl in *.
      apply (@vcomp_left_identity C).
  Qed.

  Definition lax_inclusion : LaxFunctor (full_sub C P) C
    := Build_PseudoFunctor lax_inclusion_d inclusion_is_pseudo.

  Global Instance lax_inclusion_pseudo
    : is_pseudo lax_inclusion
    := _.
End InclusionFunctor.