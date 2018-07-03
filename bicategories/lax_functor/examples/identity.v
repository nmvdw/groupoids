Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory lax_functor.lax_functor.

Section IdentityFunctor.
  Context `{Univalence}.
  Variable (C : BiCategory).

  Definition id_functor_c_m (a b c : C)
    : NaturalTransformation (@c_m _ C a b c o (1, 1)) (1 o c_m).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - cbn ; intros [p q].
      apply identity.
    - intros [p₁ p₂] [q₁ q₂] [r₁ r₂] ; cbn in *.
      exact (left_identity _ _ _ _ @ (right_identity _ _ _ _)^).
  Defined.

  Global Instance id_functor_pp_iso (a b c : C)
    : @IsIsomorphism (_ -> _) _ _ (id_functor_c_m a b c).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - simple refine (Build_NaturalTransformation _ _ _ _) ; cbn.
      + intros [q p].
        apply identity.
      + intros [q₁ p₁] [q₂ p₂] [r₁ r₂] ; simpl in *.
        exact (left_identity _ _ _ _ @ (right_identity _ _ _ _)^).
    - apply path_natural_transformation.
      intros [q p] ; simpl in *.
      apply left_identity.
    - apply path_natural_transformation.
      intros [q p] ; simpl in *.
      apply left_identity.
  Defined.

  Definition lax_id_functor_d : LaxFunctor_d C C
    := Build_LaxFunctor_d idmap
                          (fun _ _ => 1%functor)
                          id_functor_c_m
                          (fun _ => 1%morphism).

  Definition is_lax_id : is_lax lax_id_functor_d.
  Proof.
    repeat split.
    - intros ; cbn in *.
      unfold hcomp.
      rewrite identity_of, !right_identity.
      reflexivity.
    - intros ; cbn.
      unfold hcomp.
      rewrite identity_of, !right_identity.
      reflexivity.
    - intros ; cbn.
      unfold hcomp.
      rewrite !identity_of, !right_identity, !left_identity.
      reflexivity.
  Qed.

  Definition lax_id_functor : LaxFunctor C C
    := Build_LaxFunctor lax_id_functor_d is_lax_id.

  Global Instance lax_id_functor_pseudo
    : is_pseudo_functor lax_id_functor.
  Proof.
    simple refine {| Fcomp_iso := _ |}.
  Defined.
End IdentityFunctor.