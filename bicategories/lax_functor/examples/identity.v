Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
Require Import bicategory lax_functor two_type.

Definition id_functor_c_m
           `{Univalence}
           {C : BiCategory}
           (a b c : C)
  : NaturalTransformation (@c_m _ C a b c o (1, 1)) (1 o c_m).
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - cbn ; intros [p q].
    apply identity.
  - intros [p₁ p₂] [q₁ q₂] [r₁ r₂] ; cbn in *.
    exact (left_identity _ _ _ _ @ (right_identity _ _ _ _)^).
Defined.

Global Instance id_functor_pp_iso
       `{Univalence}
       {C : BiCategory}
       (a b c : C)
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

Definition lax_id_functor_d
           `{Univalence}
           (C : BiCategory)
  : LaxFunctor_d C C.
Proof.
  simple refine {| Fobj_d := idmap ; Fmor_d := fun _ _ => 1%functor |}.
  - exact id_functor_c_m.
  - intros a ; cbn.
    apply 1%morphism.
Defined.

Definition is_lax_id
           `{Univalence}
           (C : BiCategory)
  : is_lax (lax_id_functor_d C).
Proof.
  repeat split.
  - intros a b p ; cbn in *.
    unfold hcomp.
    rewrite identity_of, !right_identity.
    reflexivity.
  - intros a b p ; cbn.
    unfold hcomp.
    rewrite identity_of, !right_identity.
    reflexivity.
  - intros a b c d p q r ; cbn.
    unfold hcomp.
    rewrite !identity_of, !right_identity, !left_identity.
    reflexivity.
Qed.

Definition lax_id_functor
           `{Univalence}
           (C : BiCategory)
  : LaxFunctor C C
  := (lax_id_functor_d C;is_lax_id C).

Global Instance lax_id_functor_pseudo
       `{Univalence}
       (C : BiCategory)    
  : is_pseudo_functor (lax_id_functor C).
Proof.
  simple refine {| Fcomp_iso := _ |}.
Defined.